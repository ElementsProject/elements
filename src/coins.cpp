// Copyright (c) 2012-2015 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "coins.h"

#include "memusage.h"
#include "random.h"

#include <assert.h>

/**
 * calculate number of bytes for the bitmask, and its number of non-zero bytes
 * each bit in the bitmask represents the availability of one output, but the
 * availabilities of the first two outputs are encoded separately
 */
void CCoins::CalcMaskSize(unsigned int &nBytes, unsigned int &nNonzeroBytes) const {
    unsigned int nLastUsedByte = 0;
    for (unsigned int b = 0; 2+b*8 < vout.size(); b++) {
        bool fZero = true;
        for (unsigned int i = 0; i < 8 && 2+b*8+i < vout.size(); i++) {
            if (!vout[2+b*8+i].IsNull()) {
                fZero = false;
                continue;
            }
        }
        if (!fZero) {
            nLastUsedByte = b + 1;
            nNonzeroBytes++;
        }
    }
    nBytes += nLastUsedByte;
}

bool CCoins::Spend(uint32_t nPos) 
{
    if (nPos >= vout.size() || vout[nPos].IsNull())
        return false;
    vout[nPos].SetNull();
    Cleanup();
    return true;
}

bool CCoinsView::GetCoins(const uint256 &txid, CCoins &coins) const { return false; }
bool CCoinsView::HaveCoins(const uint256 &txid) const { return false; }
bool CCoinsView::IsWithdrawSpent(const std::pair<uint256, COutPoint> &outpoint) const { return false; }
uint256 CCoinsView::GetBestBlock() const { return uint256(); }
bool CCoinsView::BatchWrite(CCoinsMap &mapCoins, const uint256 &hashBlock) { return false; }
CCoinsViewCursor *CCoinsView::Cursor() const { return 0; }


CCoinsViewBacked::CCoinsViewBacked(CCoinsView *viewIn) : base(viewIn) { }
bool CCoinsViewBacked::GetCoins(const uint256 &txid, CCoins &coins) const { return base->GetCoins(txid, coins); }
bool CCoinsViewBacked::HaveCoins(const uint256 &txid) const { return base->HaveCoins(txid); }
bool CCoinsViewBacked::IsWithdrawSpent(const std::pair<uint256, COutPoint> &outpoint) const { return base->IsWithdrawSpent(outpoint); }
uint256 CCoinsViewBacked::GetBestBlock() const { return base->GetBestBlock(); }
void CCoinsViewBacked::SetBackend(CCoinsView &viewIn) { base = &viewIn; }
bool CCoinsViewBacked::BatchWrite(CCoinsMap &mapCoins, const uint256 &hashBlock) { return base->BatchWrite(mapCoins, hashBlock); }
CCoinsViewCursor *CCoinsViewBacked::Cursor() const { return base->Cursor(); }

SaltedTxidHasher::SaltedTxidHasher() : k0(GetRand(std::numeric_limits<uint64_t>::max())), k1(GetRand(std::numeric_limits<uint64_t>::max())) {}

CCoinsViewCache::CCoinsViewCache(CCoinsView *baseIn) : CCoinsViewBacked(baseIn), hasModifier(false), cachedCoinsUsage(0) { }

CCoinsViewCache::~CCoinsViewCache()
{
    assert(!hasModifier);
}

size_t CCoinsViewCache::DynamicMemoryUsage() const {
    return memusage::DynamicUsage(cacheCoins) + cachedCoinsUsage;
}

static inline CCoinsMapKey make_txentry(const uint256 &txid) {
    return std::make_pair(txid, COutPoint());
}

CCoinsMap::const_iterator CCoinsViewCache::FetchCoins(const uint256 &txid) const {
    CCoinsMap::iterator it = cacheCoins.find(make_txentry(txid));
    if (it != cacheCoins.end())
        return it;
    CCoins tmp;
    if (!base->GetCoins(txid, tmp))
        return cacheCoins.end();
    CCoinsMap::iterator ret = cacheCoins.insert(std::make_pair(make_txentry(txid), CCoinsCacheEntry())).first;
    tmp.swap(ret->second.coins);
    if (ret->second.coins.IsPruned()) {
        // The parent only has an empty entry for this txid; we can consider our
        // version as fresh.
        ret->second.flags = CCoinsCacheEntry::FRESH;
    }
    cachedCoinsUsage += ret->second.coins.DynamicMemoryUsage();
    return ret;
}

bool CCoinsViewCache::GetCoins(const uint256 &txid, CCoins &coins) const {
    CCoinsMap::const_iterator it = FetchCoins(txid);
    if (it != cacheCoins.end()) {
        coins = it->second.coins;
        return true;
    }
    return false;
}

CCoinsModifier CCoinsViewCache::ModifyCoins(const uint256 &txid) {
    assert(!hasModifier);
    std::pair<CCoinsMap::iterator, bool> ret = cacheCoins.insert(std::make_pair(make_txentry(txid), CCoinsCacheEntry()));
    size_t cachedCoinUsage = 0;
    if (ret.second) {
        if (!base->GetCoins(txid, ret.first->second.coins)) {
            // The parent view does not have this entry; mark it as fresh.
            ret.first->second.coins.Clear();
            ret.first->second.flags = CCoinsCacheEntry::FRESH;
        } else if (ret.first->second.coins.IsPruned()) {
            // The parent view only has a pruned entry for this; mark it as fresh.
            ret.first->second.flags = CCoinsCacheEntry::FRESH;
        }
    } else {
        cachedCoinUsage = ret.first->second.coins.DynamicMemoryUsage();
    }
    // Assume that whenever ModifyCoins is called, the entry will be modified.
    ret.first->second.flags |= CCoinsCacheEntry::DIRTY;
    return CCoinsModifier(*this, ret.first, cachedCoinUsage);
}

// ModifyNewCoins has to know whether the new outputs its creating are for a
// coinbase or not.  If they are for a coinbase, it can not mark them as fresh.
// This is to ensure that the historical duplicate coinbases before BIP30 was
// in effect will still be properly overwritten when spent.
CCoinsModifier CCoinsViewCache::ModifyNewCoins(const uint256 &txid, bool coinbase) {
    assert(!hasModifier);
    std::pair<CCoinsMap::iterator, bool> ret = cacheCoins.insert(std::make_pair(make_txentry(txid), CCoinsCacheEntry()));
    ret.first->second.coins.Clear();
    if (!coinbase) {
        ret.first->second.flags = CCoinsCacheEntry::FRESH;
    }
    ret.first->second.flags |= CCoinsCacheEntry::DIRTY;
    return CCoinsModifier(*this, ret.first, 0);
}

const CCoins* CCoinsViewCache::AccessCoins(const uint256 &txid) const {
    CCoinsMap::const_iterator it = FetchCoins(txid);
    if (it == cacheCoins.end()) {
        return NULL;
    } else {
        return &it->second.coins;
    }
}

bool CCoinsViewCache::HaveCoins(const uint256 &txid) const {
    CCoinsMap::const_iterator it = FetchCoins(txid);
    // We're using vtx.empty() instead of IsPruned here for performance reasons,
    // as we only care about the case where a transaction was replaced entirely
    // in a reorganization (which wipes vout entirely, as opposed to spending
    // which just cleans individual outputs).
    return (it != cacheCoins.end() && !it->second.coins.vout.empty());
}

bool CCoinsViewCache::HaveCoinsInCache(const uint256 &txid) const {
    CCoinsMap::const_iterator it = cacheCoins.find(make_txentry(txid));
    return it != cacheCoins.end();
}

bool CCoinsViewCache::IsWithdrawSpent(const std::pair<uint256, COutPoint> &outpoint) const {
    assert(!outpoint.second.hash.IsNull());
    assert(!outpoint.first.IsNull());

    CCoinsMap::iterator it = cacheCoins.find(outpoint);
    if (it == cacheCoins.end()) {
        it = cacheCoins.insert(std::make_pair(outpoint, CCoinsCacheEntry())).first;
        it->second.withdrawSpent = base->IsWithdrawSpent(outpoint);
        it->second.flags |= CCoinsCacheEntry::WITHDRAW;
        if (!it->second.withdrawSpent)
            it->second.flags |= CCoinsCacheEntry::FRESH;
    }
    return it->second.withdrawSpent;
}

void CCoinsViewCache::SetWithdrawSpent(const std::pair<uint256, COutPoint> &outpoint, bool fSpent) {
    assert(!outpoint.second.hash.IsNull());
    assert(!outpoint.first.IsNull());

    CCoinsMap::iterator it = cacheCoins.find(outpoint);

    bool hadSpent;
    if (it == cacheCoins.end())
        hadSpent = base->IsWithdrawSpent(outpoint);
    else
        hadSpent = it->second.withdrawSpent;

    // If we aren't changing spentness, dont do anything at all
    if (hadSpent == fSpent)
        return;

    if (it == cacheCoins.end()) {
        it = cacheCoins.insert(std::make_pair(outpoint, CCoinsCacheEntry())).first;
        if (!hadSpent)
            it->second.flags = CCoinsCacheEntry::FRESH;
    }
    it->second.withdrawSpent = fSpent;
    it->second.flags |= CCoinsCacheEntry::WITHDRAW | CCoinsCacheEntry::DIRTY;
}

uint256 CCoinsViewCache::GetBestBlock() const {
    if (hashBlock.IsNull())
        hashBlock = base->GetBestBlock();
    return hashBlock;
}

void CCoinsViewCache::SetBestBlock(const uint256 &hashBlockIn) {
    hashBlock = hashBlockIn;
}

bool CCoinsViewCache::BatchWrite(CCoinsMap &mapCoins, const uint256 &hashBlockIn) {
    assert(!hasModifier);
    for (CCoinsMap::iterator it = mapCoins.begin(); it != mapCoins.end();) {
        if (it->second.flags & CCoinsCacheEntry::DIRTY) { // Ignore non-dirty entries (optimization).
            bool fIsWithdraw = it->second.flags & CCoinsCacheEntry::WITHDRAW;
            CCoinsMap::iterator itUs = cacheCoins.find(it->first);
            if (itUs == cacheCoins.end()) {
                // The parent cache does not have an entry, while the child does
                // We can ignore it if it's both FRESH and {pruned, spent withdraw} in the child
                if (!((it->second.flags & CCoinsCacheEntry::FRESH) &&
                        (( fIsWithdraw && !it->second.withdrawSpent) ||
                         (!fIsWithdraw &&  it->second.coins.IsPruned())))) {
                    // Otherwise we will need to create it in the parent
                    // and move the data up and mark it as dirty
                    CCoinsCacheEntry& entry = cacheCoins[it->first];
                    entry.flags = CCoinsCacheEntry::DIRTY;
                    if (fIsWithdraw) {
                        entry.withdrawSpent = it->second.withdrawSpent;
                        entry.flags |= CCoinsCacheEntry::WITHDRAW;
                    } else
                        entry.coins.swap(it->second.coins);
                    cachedCoinsUsage += entry.coins.DynamicMemoryUsage();
                    // We can mark it FRESH in the parent if it was FRESH in the child
                    // Otherwise it might have just been flushed from the parent's cache
                    // and already exist in the grandparent
                    if (it->second.flags & CCoinsCacheEntry::FRESH)
                        entry.flags |= CCoinsCacheEntry::FRESH;
                }
            } else {
                // Found the entry in the parent cache
                if ((itUs->second.flags & CCoinsCacheEntry::FRESH) &&
                        ((fIsWithdraw && !it->second.withdrawSpent) || (!fIsWithdraw && it->second.coins.IsPruned()))) {
                    // The grandparent does not have an entry, and the child is
                    // modified and being pruned. This means we can just delete
                    // it from the parent.
                    cachedCoinsUsage -= itUs->second.coins.DynamicMemoryUsage();
                    cacheCoins.erase(itUs);
                } else {
                    // A normal modification.
                    cachedCoinsUsage -= itUs->second.coins.DynamicMemoryUsage();
                    if (fIsWithdraw)
                        itUs->second.withdrawSpent = it->second.withdrawSpent;
                    else
                        itUs->second.coins.swap(it->second.coins);
                    cachedCoinsUsage += itUs->second.coins.DynamicMemoryUsage();
                    itUs->second.flags |= CCoinsCacheEntry::DIRTY;
                }
            }
        }
        CCoinsMap::iterator itOld = it++;
        mapCoins.erase(itOld);
    }
    hashBlock = hashBlockIn;
    return true;
}

bool CCoinsViewCache::Flush() {
    bool fOk = base->BatchWrite(cacheCoins, hashBlock);
    cacheCoins.clear();
    cachedCoinsUsage = 0;
    return fOk;
}

void CCoinsViewCache::Uncache(const uint256& hash)
{
    CCoinsMap::iterator it = cacheCoins.find(make_txentry(hash));
    if (it != cacheCoins.end() && it->second.flags == 0) {
        cachedCoinsUsage -= it->second.coins.DynamicMemoryUsage();
        cacheCoins.erase(it);
    }
}

unsigned int CCoinsViewCache::GetCacheSize() const {
    return cacheCoins.size();
}

const CTxOut &CCoinsViewCache::GetOutputFor(const CTxIn& input) const
{
    const CCoins* coins = AccessCoins(input.prevout.hash);
    assert(coins && coins->IsAvailable(input.prevout.n));
    return coins->vout[input.prevout.n];
}

CAmount CCoinsViewCache::GetValueIn(const CTransaction& tx) const
{
    if (tx.IsCoinBase())
        return 0;

    CAmount nResult = 0;
    for (unsigned int i = 0; i < tx.vin.size(); i++) {
        const CTxOutValue& val = GetOutputFor(tx.vin[i]).nValue;
        assert(val.IsAmount());
        nResult += val.GetAmount();
    }

    return nResult;
}

bool CCoinsViewCache::VerifyAmounts(const CTransaction& tx, const CAmount& excess) const
{
    if (!MoneyRange(excess) && !MoneyRange(-excess))
        return false;
    CAmount nInAmount = GetValueIn(tx);
    for (std::vector<CTxOut>::const_iterator it(tx.vout.begin()); it != tx.vout.end(); ++it)
    {
        assert(it->nValue.IsAmount());
        nInAmount -= it->nValue.GetAmount();;
        if (!MoneyRange(it->nValue.GetAmount()) || (!MoneyRange(nInAmount) && !MoneyRange(-nInAmount)))
            return false;
    }
    return excess == nInAmount;
}

bool CCoinsViewCache::HaveInputs(const CTransaction& tx) const
{
    if (!tx.IsCoinBase()) {
        for (unsigned int i = 0; i < tx.vin.size(); i++) {
            const COutPoint &prevout = tx.vin[i].prevout;
            const CCoins* coins = AccessCoins(prevout.hash);
            if (!coins || !coins->IsAvailable(prevout.n)) {
                return false;
            }
        }
    }
    return true;
}

double CCoinsViewCache::GetPriority(const CTransaction &tx, int nHeight, CAmount &inChainInputValue) const
{
    inChainInputValue = 0;
    if (tx.IsCoinBase())
        return 0.0;
    double dResult = 0.0;
    BOOST_FOREACH(const CTxIn& txin, tx.vin)
    {
        const CCoins* coins = AccessCoins(txin.prevout.hash);
        assert(coins);
        if (!coins->IsAvailable(txin.prevout.n)) continue;
        if (coins->nHeight <= nHeight) {
            const CTxOutValue& val = coins->vout[txin.prevout.n].nValue;
            CAmount nAmount = COIN;
            if (val.IsAmount())
                nAmount = val.GetAmount();
            dResult += nAmount * (nHeight-coins->nHeight);
            inChainInputValue += nAmount;
        }
    }
    return tx.ComputePriority(dResult);
}

CCoinsModifier::CCoinsModifier(CCoinsViewCache& cache_, CCoinsMap::iterator it_, size_t usage) : cache(cache_), it(it_), cachedCoinUsage(usage) {
    assert(!cache.hasModifier);
    cache.hasModifier = true;
}

CCoinsModifier::~CCoinsModifier()
{
    assert(cache.hasModifier);
    cache.hasModifier = false;
    it->second.coins.Cleanup();
    cache.cachedCoinsUsage -= cachedCoinUsage; // Subtract the old usage
    if ((it->second.flags & CCoinsCacheEntry::FRESH) && it->second.coins.IsPruned()) {
        cache.cacheCoins.erase(it);
    } else {
        // If the coin still exists after the modification, add the new usage
        cache.cachedCoinsUsage += it->second.coins.DynamicMemoryUsage();
    }
}

CCoinsViewCursor::~CCoinsViewCursor()
{
}
