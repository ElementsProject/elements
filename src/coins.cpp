// Copyright (c) 2012-2014 The Bitcoin developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "coins.h"

#include "random.h"

#include <assert.h>

#include <secp256k1.h>
#include <secp256k1_rangeproof.h>

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

bool CCoins::Spend(const COutPoint &out, CTxInUndo &undo) {
    if (out.n >= vout.size())
        return false;
    if (vout[out.n].IsNull())
        return false;
    undo = CTxInUndo(vout[out.n]);
    vout[out.n].SetNull();
    Cleanup();
    if (vout.size() == 0) {
        undo.nHeight = nHeight + 1;
        undo.fCoinBase = fCoinBase;
        undo.nVersion = this->nVersion;
    }
    return true;
}

bool CCoins::Spend(int nPos) {
    CTxInUndo undo;
    COutPoint out(0, nPos);
    return Spend(out, undo);
}


bool CCoinsView::GetCoins(const uint256 &txid, CCoins &coins) const { return false; }
bool CCoinsView::HaveCoins(const uint256 &txid) const { return false; }
COutPoint CCoinsView::GetWithdrawSpent(const std::pair<uint256, COutPoint> &outpoint) const { return COutPoint(); }
uint256 CCoinsView::GetBestBlock() const { return uint256(0); }
bool CCoinsView::BatchWrite(CCoinsMap &mapCoins, const uint256 &hashBlock) { return false; }
bool CCoinsView::GetStats(CCoinsStats &stats) const { return false; }


CCoinsViewBacked::CCoinsViewBacked(CCoinsView *viewIn) : base(viewIn) { }
bool CCoinsViewBacked::GetCoins(const uint256 &txid, CCoins &coins) const { return base->GetCoins(txid, coins); }
bool CCoinsViewBacked::HaveCoins(const uint256 &txid) const { return base->HaveCoins(txid); }
COutPoint CCoinsViewBacked::GetWithdrawSpent(const std::pair<uint256, COutPoint> &outpoint) const { return base->GetWithdrawSpent(outpoint); }
uint256 CCoinsViewBacked::GetBestBlock() const { return base->GetBestBlock(); }
void CCoinsViewBacked::SetBackend(CCoinsView &viewIn) { base = &viewIn; }
bool CCoinsViewBacked::BatchWrite(CCoinsMap &mapCoins, const uint256 &hashBlock) { return base->BatchWrite(mapCoins, hashBlock); }
bool CCoinsViewBacked::GetStats(CCoinsStats &stats) const { return base->GetStats(stats); }

CCoinsKeyHasher::CCoinsKeyHasher() : salt(GetRandHash()) {}

CCoinsViewCache::CCoinsViewCache(CCoinsView *baseIn) : CCoinsViewBacked(baseIn), hasModifier(false), hashBlock(0) { }

CCoinsViewCache::~CCoinsViewCache()
{
    assert(!hasModifier);
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
    if (ret.second) {
        if (!base->GetCoins(txid, ret.first->second.coins)) {
            // The parent view does not have this entry; mark it as fresh.
            ret.first->second.coins.Clear();
            ret.first->second.flags = CCoinsCacheEntry::FRESH;
        } else if (ret.first->second.coins.IsPruned()) {
            // The parent view only has a pruned entry for this; mark it as fresh.
            ret.first->second.flags = CCoinsCacheEntry::FRESH;
        }
    }
    // Assume that whenever ModifyCoins is called, the entry will be modified.
    ret.first->second.flags |= CCoinsCacheEntry::DIRTY;
    return CCoinsModifier(*this, ret.first);
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

COutPoint CCoinsViewCache::GetWithdrawSpent(const std::pair<uint256, COutPoint> &outpoint) const {
    CCoinsMap::iterator it = cacheCoins.find(outpoint);
    if (it == cacheCoins.end()) {
        it = cacheCoins.insert(std::make_pair(outpoint, CCoinsCacheEntry())).first;
        it->second.withdrawSpent = base->GetWithdrawSpent(outpoint);
        it->second.flags |= CCoinsCacheEntry::WITHDRAW;
    }
    return it->second.withdrawSpent;
}

void CCoinsViewCache::MaybeSetWithdrawSpent(const std::pair<uint256, COutPoint> &outpoint, COutPoint spender) {
    CCoinsMap::iterator it = cacheCoins.find(outpoint);

    // If its already spent - dont overwrite, unless spender IsNull
    bool hadSpent;
    if (it == cacheCoins.end())
        hadSpent = !base->GetWithdrawSpent(outpoint).IsNull();
    else
        hadSpent = !it->second.withdrawSpent.IsNull();
    if (hadSpent && !spender.IsNull())
        return;

    if (it == cacheCoins.end()) {
        it = cacheCoins.insert(std::make_pair(outpoint, CCoinsCacheEntry())).first;
        if (!hadSpent)
            it->second.flags = CCoinsCacheEntry::FRESH;
    }
    it->second.withdrawSpent = spender;
    it->second.flags |= CCoinsCacheEntry::WITHDRAW | CCoinsCacheEntry::DIRTY;
}

uint256 CCoinsViewCache::GetBestBlock() const {
    if (hashBlock == uint256(0))
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
                if ((fIsWithdraw && !it->second.withdrawSpent.IsNull()) ||
                        (!fIsWithdraw && !it->second.coins.IsPruned())) {
                    // The parent cache does not have an entry, while the child
                    // cache does have (a non-pruned) one. Move the data up, and
                    // mark it as fresh (if the grandparent did have it, we
                    // would have pulled it in at first GetCoins).
                    assert(it->second.flags & CCoinsCacheEntry::FRESH);
                    CCoinsCacheEntry& entry = cacheCoins[it->first];
                    entry.flags = CCoinsCacheEntry::DIRTY | CCoinsCacheEntry::FRESH;
                    if (fIsWithdraw) {
                        entry.withdrawSpent = it->second.withdrawSpent;
                        entry.flags |= CCoinsCacheEntry::WITHDRAW;
                    } else
                        entry.coins.swap(it->second.coins);
                }
            } else {
                if ((itUs->second.flags & CCoinsCacheEntry::FRESH) &&
                        ((fIsWithdraw && it->second.withdrawSpent.IsNull()) || (!fIsWithdraw && it->second.coins.IsPruned()))) {
                    // The grandparent does not have an entry, and the child is
                    // modified and being pruned. This means we can just delete
                    // it from the parent.
                    cacheCoins.erase(itUs);
                } else {
                    // A normal modification.
                    if (fIsWithdraw)
                        itUs->second.withdrawSpent = it->second.withdrawSpent;
                    else
                        itUs->second.coins.swap(it->second.coins);
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
    return fOk;
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

extern secp256k1_context* secp256k1_bitcoin_verify_context;

bool CCoinsViewCache::VerifyAmounts(const CTransaction& tx, const CAmount& excess) const
{
    CAmount nPlainAmount = excess;
    std::vector<unsigned char> vchData;
    std::vector<unsigned char *> vpchCommitsIn, vpchCommitsOut;
    bool fNullRangeproof = false;
    vchData.resize(CTxOutValue::nCommitmentSize * (tx.vin.size() + tx.vout.size()));
    unsigned char *p = vchData.data();
    if (!tx.IsCoinBase())
    {
        // The first input is null for asset definition transactions
        FOREACH_TXIN(txin, tx)
        {
            const CTxOut& txOut = GetOutputFor(txin);
            const CTxOutValue& val = txOut.nValue;
            if (val.IsAmount())
                nPlainAmount -= val.GetAmount();
            else
            {
                assert(val.vchCommitment.size() == CTxOutValue::nCommitmentSize);
                memcpy(p, &val.vchCommitment[0], CTxOutValue::nCommitmentSize);
                vpchCommitsIn.push_back(p);
                p += CTxOutValue::nCommitmentSize;
            }
        }
    }
    for (size_t i = 0; i < tx.vout.size(); ++i)
    {
        const CTxOutValue& val = tx.vout[i].nValue;
        assert(val.vchCommitment.size() == CTxOutValue::nCommitmentSize);
        if (val.vchNonceCommitment.size() > CTxOutValue::nCommitmentSize || val.vchRangeproof.size() > 5000)
            return false;
        if (val.IsAmount())
            nPlainAmount += val.GetAmount();
        else
        {
            memcpy(p, &val.vchCommitment[0], CTxOutValue::nCommitmentSize);
            vpchCommitsOut.push_back(p);
            p += CTxOutValue::nCommitmentSize;

            if (val.vchRangeproof.empty())
                fNullRangeproof = true;
        }
    }

    // If there are no encrypted input or output values, we can do simple math
    if (vpchCommitsIn.size() + vpchCommitsOut.size() == 0)
        return (nPlainAmount == 0);

    if (!secp256k1_pedersen_verify_tally(secp256k1_bitcoin_verify_context, vpchCommitsIn.data(), vpchCommitsIn.size(), vpchCommitsOut.data(), vpchCommitsOut.size(), nPlainAmount))
        return false;

    // Rangeproof is optional in this case
    if ((!vpchCommitsIn.empty()) && vpchCommitsOut.size() == 1 && nPlainAmount <= 0 && fNullRangeproof)
        return true;

    uint64_t min_value, max_value;
    for (size_t i = 0; i < tx.vout.size(); ++i)
    {
        const CTxOutValue& val = tx.vout[i].nValue;
        if (val.IsAmount())
            continue;
        if (!secp256k1_rangeproof_verify(secp256k1_bitcoin_verify_context, &min_value, &max_value, &val.vchCommitment[0], val.vchRangeproof.data(), val.vchRangeproof.size()))
            return false;
    }

    return true;
}

bool CCoinsViewCache::VerifyAmounts(const CTransaction& tx) const
{
    const CAmount& excess = tx.nTxFee;
    return VerifyAmounts(tx, excess);
}

bool CCoinsViewCache::HaveInputs(const CTransaction& tx) const
{
    if (!tx.IsCoinBase()) {
        // Don't check the null input in asset defintion transactions
        FOREACH_TXIN(txin, tx) {
            const COutPoint &prevout = txin.prevout;
            const CCoins* coins = AccessCoins(prevout.hash);
            if (!coins || !coins->IsAvailable(prevout.n)) {
                return false;
            }
        }
    }
    return true;
}

double CCoinsViewCache::GetPriority(const CTransaction &tx, int nHeight) const
{
    if (tx.IsCoinBase())
        return 0.0;
    double dResult = 0.0;
    FOREACH_TXIN(txin, tx)
    {
        const CCoins* coins = AccessCoins(txin.prevout.hash);
        assert(coins);
        if (!coins->IsAvailable(txin.prevout.n)) continue;
        int nOffset = 0;
        if (coins->vout[txin.prevout.n].scriptPubKey.IsWithdrawOutput() && txin.scriptSig.IsPushOnly() && txin.scriptSig.size() > 1 && txin.scriptSig.back() == OP_1) {
            // Fraud/reorg proofs get a significant priority bump
            nOffset = 10000;
        } else if (coins->vout[txin.prevout.n].scriptPubKey.IsWithdrawLock(0))
            // Coins moving to this chain get a priority bump
            nOffset = 100;
        int nCoinsHeight = coins->nHeight == 0x7fffffff ? nHeight + 1 : coins->nHeight;
        if (nCoinsHeight < nHeight + nOffset) {
            const CTxOutValue& val = coins->vout[txin.prevout.n].nValue;
            // FIXME: This assumes all blinded values are COIN
            CAmount nAmount = COIN;
            if (val.IsAmount())
                nAmount = val.GetAmount();
            dResult += double(nAmount + nOffset) * double(nHeight - nCoinsHeight + nOffset);
        }
    }
    return tx.ComputePriority(dResult);
}

CCoinsModifier::CCoinsModifier(CCoinsViewCache& cache_, CCoinsMap::iterator it_) : cache(cache_), it(it_) {
    assert(!cache.hasModifier);
    cache.hasModifier = true;
}

CCoinsModifier::~CCoinsModifier()
{
    assert(cache.hasModifier);
    cache.hasModifier = false;
    it->second.coins.Cleanup();
    if ((it->second.flags & CCoinsCacheEntry::FRESH) && it->second.coins.IsPruned()) {
        cache.cacheCoins.erase(it);
    }
}
