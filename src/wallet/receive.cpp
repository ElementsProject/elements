// Copyright (c) 2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <consensus/amount.h>
#include <consensus/consensus.h>
#include <policy/policy.h> // ELEMENTS: for policyAsset
#include <wallet/receive.h>
#include <wallet/transaction.h>
#include <wallet/wallet.h>
#include <iostream>

namespace wallet {
isminetype InputIsMine(const CWallet& wallet, const CTxIn &txin)
{
    AssertLockHeld(wallet.cs_wallet);
    return InputIsMine(wallet, txin.prevout);
}

isminetype InputIsMine(const CWallet& wallet, const COutPoint &outpoint)
{
    AssertLockHeld(wallet.cs_wallet);
    std::map<uint256, CWalletTx>::const_iterator mi = wallet.mapWallet.find(outpoint.hash);
    if (mi != wallet.mapWallet.end())
    {
        const CWalletTx& prev = (*mi).second;
        if (outpoint.n < prev.tx->vout.size())
            return wallet.IsMine(prev.tx->vout[outpoint.n]);
    }
    return ISMINE_NO;
}

bool AllInputsMine(const CWallet& wallet, const CTransaction& tx, const isminefilter& filter)
{
    LOCK(wallet.cs_wallet);

    for (const CTxIn& txin : tx.vin)
    {
        auto mi = wallet.mapWallet.find(txin.prevout.hash);
        if (mi == wallet.mapWallet.end())
            return false; // any unknown inputs can't be from us

        const CWalletTx& prev = (*mi).second;

        if (txin.prevout.n >= prev.tx->vout.size())
            return false; // invalid input!

        if (!(wallet.IsMine(prev.tx->vout[txin.prevout.n]) & filter))
            return false;
    }
    return true;
}

CAmountMap OutputGetCredit(const CWallet& wallet, const CTransaction& tx, const size_t out_index, const isminefilter& filter) {
    std::map<uint256, CWalletTx>::const_iterator mi = wallet.mapWallet.find(tx.GetHash());
    if (mi != wallet.mapWallet.end())
    {
        const CWalletTx& wtx = (*mi).second;
        if (out_index < wtx.tx->vout.size() && wallet.IsMine(wtx.tx->vout[out_index]) & filter) {
            CAmountMap amounts;
            amounts[wtx.GetOutputAsset(wallet, out_index)] = std::max<CAmount>(0, wtx.GetOutputValueOut(wallet, out_index));
            return amounts;
        }
    }
    return CAmountMap();
}

CAmountMap TxGetCredit(const CWallet& wallet, const CWalletTx& wtx, const isminefilter& filter) {
    CAmountMap nCredit;
    {
        LOCK(wallet.cs_wallet);

        for (unsigned int i = 0; i < wtx.tx->vout.size(); ++i) {
            if (wallet.IsMine(wtx.tx->vout[i]) & filter) {
                CAmount credit = std::max<CAmount>(0, wtx.GetOutputValueOut(wallet, i));
                if (!MoneyRange(credit))
                    throw std::runtime_error(std::string(__func__) + ": value out of range");

                nCredit[wtx.GetOutputAsset(wallet, i)] += credit;
                if (!MoneyRange(nCredit))
                    throw std::runtime_error(std::string(__func__) + ": value out of range");
            }
        }
    }
    return nCredit;
}

CAmountMap GetChange(const CWallet& wallet, const CWalletTx& wtx) {
    CAmountMap nChange;
    for (unsigned int i = 0; i < wtx.tx->vout.size(); ++i) {
        if (OutputIsChange(wallet, wtx.tx->vout[i])) {
            CAmount change = wtx.GetOutputValueOut(wallet, i);
            if (change < 0) {
                continue;
            }

            if (!MoneyRange(change))
                throw std::runtime_error(std::string(__func__) + ": value out of range");

            nChange[wtx.GetOutputAsset(wallet, i)] += change;
            if (!MoneyRange(nChange))
                throw std::runtime_error(std::string(__func__) + ": value out of range");
        }
    }
    return nChange;
}

bool OutputIsChange(const CWallet& wallet, const CTxOut& txout)
{
    return ScriptIsChange(wallet, txout.scriptPubKey);
}

bool ScriptIsChange(const CWallet& wallet, const CScript& script)
{
    // TODO: fix handling of 'change' outputs. The assumption is that any
    // payment to a script that is ours, but is not in the address book
    // is change. That assumption is likely to break when we implement multisignature
    // wallets that return change back into a multi-signature-protected address;
    // a better way of identifying which outputs are 'the send' and which are
    // 'the change' will need to be implemented (maybe extend CWalletTx to remember
    // which output, if any, was change).
    AssertLockHeld(wallet.cs_wallet);
    if (wallet.IsMine(script))
    {
        CTxDestination address;
        if (!ExtractDestination(script, address))
            return true;
        if (!wallet.FindAddressBookEntry(address)) {
            return true;
        }
    }
    return false;
}

CAmountMap TxGetChange(const CWallet& wallet, const CWalletTx& wtx)
{
    LOCK(wallet.cs_wallet);
    CAmountMap nChange = GetChange(wallet, wtx);
    if (!MoneyRange(nChange))
        throw std::runtime_error(std::string(__func__) + ": value out of range");
    return nChange;
}

static CAmountMap GetCachableAmount(const CWallet& wallet, const CWalletTx& wtx, CWalletTx::AmountType type, const isminefilter& filter, bool recalculate = false)
{
    auto& amount = wtx.m_amounts[type];
    if (recalculate || !amount.m_cached[filter]) {
        amount.Set(filter, type == CWalletTx::DEBIT ? wallet.GetDebit(*wtx.tx, filter) : TxGetCredit(wallet, wtx, filter));
        wtx.m_is_cache_empty = false;
    }
    return amount.m_value[filter];
}

CAmountMap CachedTxGetCredit(const CWallet& wallet, const CWalletTx& wtx, const isminefilter& filter)
{
    // Must wait until coinbase is safely deep enough in the chain before valuing it
    if (wallet.IsTxImmatureCoinBase(wtx))
        return CAmountMap();

    CAmountMap credit;
    if (filter & ISMINE_SPENDABLE) {
        // GetBalance can assume transactions in mapWallet won't change
        credit += GetCachableAmount(wallet, wtx, CWalletTx::CREDIT, ISMINE_SPENDABLE);
    }
    if (filter & ISMINE_WATCH_ONLY) {
        credit += GetCachableAmount(wallet, wtx, CWalletTx::CREDIT, ISMINE_WATCH_ONLY);
    }
    return credit;
}

CAmountMap CachedTxGetDebit(const CWallet& wallet, const CWalletTx& wtx, const isminefilter& filter)
    {
    if (wtx.tx->vin.empty())
        return CAmountMap();

    CAmountMap debit;
    if (filter & ISMINE_SPENDABLE) {
        debit += GetCachableAmount(wallet, wtx, CWalletTx::DEBIT, ISMINE_SPENDABLE);
    }
    if (filter & ISMINE_WATCH_ONLY) {
        debit += GetCachableAmount(wallet, wtx, CWalletTx::DEBIT, ISMINE_WATCH_ONLY);
    }
    return debit;
}

CAmountMap CachedTxGetChange(const CWallet& wallet, const CWalletTx& wtx)
{
    if (wtx.fChangeCached)
        return wtx.nChangeCached;
    wtx.nChangeCached = TxGetChange(wallet, wtx);
    wtx.fChangeCached = true;
    return wtx.nChangeCached;
}

CAmountMap CachedTxGetImmatureCredit(const CWallet& wallet, const CWalletTx& wtx, bool fUseCache)
{
    if (wallet.IsTxImmatureCoinBase(wtx) && wallet.IsTxInMainChain(wtx)) {
        return GetCachableAmount(wallet, wtx, CWalletTx::IMMATURE_CREDIT, ISMINE_SPENDABLE, !fUseCache);
    }

    return CAmountMap();
}

CAmountMap CachedTxGetImmatureWatchOnlyCredit(const CWallet& wallet, const CWalletTx& wtx, const bool fUseCache)
{
    if (wallet.IsTxImmatureCoinBase(wtx) && wallet.IsTxInMainChain(wtx)) {
        return GetCachableAmount(wallet, wtx, CWalletTx::IMMATURE_CREDIT, ISMINE_WATCH_ONLY, !fUseCache);
    }

    return CAmountMap();
}

CAmountMap CachedTxGetAvailableCredit(const CWallet& wallet, const CWalletTx& wtx, bool fUseCache, const isminefilter& filter)
{
    // Avoid caching ismine for NO or ALL cases (could remove this check and simplify in the future).
    bool allow_cache = (filter & ISMINE_ALL) && (filter & ISMINE_ALL) != ISMINE_ALL;

    // Must wait until coinbase is safely deep enough in the chain before valuing it
    if (wallet.IsTxImmatureCoinBase(wtx))
        return CAmountMap();

    if (fUseCache && allow_cache && wtx.m_amounts[CWalletTx::AVAILABLE_CREDIT].m_cached[filter]) {
        return wtx.m_amounts[CWalletTx::AVAILABLE_CREDIT].m_value[filter];
    }

    bool allow_used_addresses = (filter & ISMINE_USED) || !wallet.IsWalletFlagSet(WALLET_FLAG_AVOID_REUSE);
    CAmountMap nCredit;
    uint256 hashTx = wtx.GetHash();
    for (unsigned int i = 0; i < wtx.tx->vout.size(); i++)
    {
        if (!wallet.IsSpent(hashTx, i) && (allow_used_addresses || !wallet.IsSpentKey(hashTx, i))) {
            if (wallet.IsMine(wtx.tx->vout[i]) & filter) {
                CAmount credit = std::max<CAmount>(0, wtx.GetOutputValueOut(wallet, i));
                if (!MoneyRange(credit))
                    throw std::runtime_error(std::string(__func__) + ": value out of range");

                nCredit[wtx.GetOutputAsset(wallet, i)] += std::max<CAmount>(0, wtx.GetOutputValueOut(wallet, i));
                if (!MoneyRange(nCredit))
                    throw std::runtime_error(std::string(__func__) + ": value out of range");
            }
        }
    }

    if (allow_cache) {
        wtx.m_amounts[CWalletTx::AVAILABLE_CREDIT].Set(filter, nCredit);
        wtx.m_is_cache_empty = false;
    }

    return nCredit;
}

void CachedTxGetAmounts(const CWallet& wallet, const CWalletTx& wtx,
                  std::list<COutputEntry>& listReceived,
                  std::list<COutputEntry>& listSent, CAmount& nFee, const isminefilter& filter)
{
    nFee = 0;
    listReceived.clear();
    listSent.clear();

    // Compute fee:
    CAmountMap mapDebit = CachedTxGetDebit(wallet, wtx, filter);
    if (mapDebit > CAmountMap()) // debit>0 means we signed/sent this transaction
    {
        nFee = -GetFeeMap(*wtx.tx)[::policyAsset];
    }

    LOCK(wallet.cs_wallet);
    // Sent/received.
    for (unsigned int i = 0; i < wtx.tx->vout.size(); ++i)
    {
        const CTxOut& txout = wtx.tx->vout[i];
        CAmount output_value = wtx.GetOutputValueOut(wallet, i);
        // Don't list unknown assets
        isminetype fIsMine = output_value != -1 ?  wallet.IsMine(txout) : ISMINE_NO;
        // Only need to handle txouts if AT LEAST one of these is true:
        //   1) they debit from us (sent)
        //   2) the output is to us (received)
        if (mapDebit > CAmountMap())
        {
            // Don't report 'change' txouts
            if (OutputIsChange(wallet, txout))
                continue;
        }
        else if (!(fIsMine & filter))
            continue;

        // In either case, we need to get the destination address
        CTxDestination address;

        if (!ExtractDestination(txout.scriptPubKey, address) && !txout.scriptPubKey.IsUnspendable())
        {
            wallet.WalletLogPrintf("CWalletTx::GetAmounts: Unknown transaction type found, txid %s\n",
                                    wtx.GetHash().ToString());
            address = CNoDestination();
        }

        COutputEntry output = {address, output_value, (int)i, wtx.GetOutputAsset(wallet, i), wtx.GetOutputAmountBlindingFactor(wallet, i), wtx.GetOutputAssetBlindingFactor(wallet, i)};

        // If we are debited by the transaction, add the output as a "sent" entry
        if (mapDebit > CAmountMap() && !txout.IsFee())
            listSent.push_back(output);

        // If we are receiving the output, add it as a "received" entry
        if (fIsMine & filter)
            listReceived.push_back(output);
    }

}

bool CachedTxIsFromMe(const CWallet& wallet, const CWalletTx& wtx, const isminefilter& filter)
{
    return (CachedTxGetDebit(wallet, wtx, filter) > CAmountMap());
}

bool CachedTxIsTrusted(const CWallet& wallet, const CWalletTx& wtx, std::set<uint256>& trusted_parents)
{
    AssertLockHeld(wallet.cs_wallet);
    int nDepth = wallet.GetTxDepthInMainChain(wtx);
    if (nDepth >= 1) return true;
    if (nDepth < 0) return false;
    // using wtx's cached debit
    if (!wallet.m_spend_zero_conf_change || !CachedTxIsFromMe(wallet, wtx, ISMINE_ALL)) return false;

    // Don't trust unconfirmed transactions from us unless they are in the mempool.
    if (!wtx.InMempool()) return false;

    // Trusted if all inputs are from us and are in the mempool:
    for (const CTxIn& txin : wtx.tx->vin)
    {
        // Transactions not sent by us: not trusted
        const CWalletTx* parent = wallet.GetWalletTx(txin.prevout.hash);
        if (parent == nullptr) return false;
        const CTxOut& parentOut = parent->tx->vout[txin.prevout.n];
        // Check that this specific input being spent is trusted
        if (wallet.IsMine(parentOut) != ISMINE_SPENDABLE) return false;
        // If we've already trusted this parent, continue
        if (trusted_parents.count(parent->GetHash())) continue;
        // Recurse to check that the parent is also trusted
        if (!CachedTxIsTrusted(wallet, *parent, trusted_parents)) return false;
        trusted_parents.insert(parent->GetHash());
    }
    return true;
}

bool CachedTxIsTrusted(const CWallet& wallet, const CWalletTx& wtx)
{
    std::set<uint256> trusted_parents;
    LOCK(wallet.cs_wallet);
    return CachedTxIsTrusted(wallet, wtx, trusted_parents);
}

Balance GetBalance(const CWallet& wallet, const int min_depth, bool avoid_reuse)
{
    Balance ret;
    isminefilter reuse_filter = avoid_reuse ? ISMINE_NO : ISMINE_USED;
    {
        LOCK(wallet.cs_wallet);
        std::set<uint256> trusted_parents;
        for (const auto& entry : wallet.mapWallet)
        {
            const CWalletTx& wtx = entry.second;
            const bool is_trusted{CachedTxIsTrusted(wallet, wtx, trusted_parents)};
            const int tx_depth{wallet.GetTxDepthInMainChain(wtx)};
            const CAmountMap tx_credit_mine{CachedTxGetAvailableCredit(wallet, wtx, /* fUseCache */ true, ISMINE_SPENDABLE | reuse_filter)};
            const CAmountMap tx_credit_watchonly{CachedTxGetAvailableCredit(wallet, wtx, /* fUseCache */ true, ISMINE_WATCH_ONLY | reuse_filter)};
            if (is_trusted && tx_depth >= min_depth) {
                ret.m_mine_trusted += tx_credit_mine;
                ret.m_watchonly_trusted += tx_credit_watchonly;
            }
            if (!is_trusted && tx_depth == 0 && wtx.InMempool()) {
                ret.m_mine_untrusted_pending += tx_credit_mine;
                ret.m_watchonly_untrusted_pending += tx_credit_watchonly;
            }
            ret.m_mine_immature += CachedTxGetImmatureCredit(wallet, wtx);
            ret.m_watchonly_immature += CachedTxGetImmatureWatchOnlyCredit(wallet, wtx);
        }
    }
    return ret;
}

std::map<CTxDestination, CAmount> GetAddressBalances(const CWallet& wallet)
{
    std::map<CTxDestination, CAmount> balances;

    {
        LOCK(wallet.cs_wallet);
        std::set<uint256> trusted_parents;
        for (const auto& walletEntry : wallet.mapWallet)
        {
            const CWalletTx& wtx = walletEntry.second;

            if (!CachedTxIsTrusted(wallet, wtx, trusted_parents))
                continue;

            if (wallet.IsTxImmatureCoinBase(wtx))
                continue;

            int nDepth = wallet.GetTxDepthInMainChain(wtx);
            if (nDepth < (CachedTxIsFromMe(wallet, wtx, ISMINE_ALL) ? 0 : 1))
                continue;

            for (unsigned int i = 0; i < wtx.tx->vout.size(); i++)
            {
                CTxDestination addr;
                if (!wallet.IsMine(wtx.tx->vout[i]))
                    continue;
                if(!ExtractDestination(wtx.tx->vout[i].scriptPubKey, addr))
                    continue;

                CAmount n = wallet.IsSpent(walletEntry.first, i) ? 0 : wtx.GetOutputValueOut(wallet, i);
                if (n < 0) {
                    continue;
                }
                balances[addr] += n;
            }
        }
    }

    return balances;
}

std::set< std::set<CTxDestination> > GetAddressGroupings(const CWallet& wallet)
{
    AssertLockHeld(wallet.cs_wallet);
    std::set< std::set<CTxDestination> > groupings;
    std::set<CTxDestination> grouping;

    for (const auto& walletEntry : wallet.mapWallet)
    {
        const CWalletTx& wtx = walletEntry.second;

        if (wtx.tx->vin.size() > 0)
        {
            bool any_mine = false;
            // group all input addresses with each other
            for (const CTxIn& txin : wtx.tx->vin)
            {
                CTxDestination address;
                if(!InputIsMine(wallet, txin)) /* If this input isn't mine, ignore it */
                    continue;
                if(!ExtractDestination(wallet.mapWallet.at(txin.prevout.hash).tx->vout[txin.prevout.n].scriptPubKey, address))
                    continue;
                grouping.insert(address);
                any_mine = true;
            }

            // group change with input addresses
            if (any_mine)
            {
               for (const CTxOut& txout : wtx.tx->vout)
                   if (OutputIsChange(wallet, txout))
                   {
                       CTxDestination txoutAddr;
                       if(!ExtractDestination(txout.scriptPubKey, txoutAddr))
                           continue;
                       grouping.insert(txoutAddr);
                   }
            }
            if (grouping.size() > 0)
            {
                groupings.insert(grouping);
                grouping.clear();
            }
        }

        // group lone addrs by themselves
        for (const auto& txout : wtx.tx->vout)
            if (wallet.IsMine(txout))
            {
                CTxDestination address;
                if(!ExtractDestination(txout.scriptPubKey, address))
                    continue;
                grouping.insert(address);
                groupings.insert(grouping);
                grouping.clear();
            }
    }

    std::set< std::set<CTxDestination>* > uniqueGroupings; // a set of pointers to groups of addresses
    std::map< CTxDestination, std::set<CTxDestination>* > setmap;  // map addresses to the unique group containing it
    for (std::set<CTxDestination> _grouping : groupings)
    {
        // make a set of all the groups hit by this new group
        std::set< std::set<CTxDestination>* > hits;
        std::map< CTxDestination, std::set<CTxDestination>* >::iterator it;
        for (const CTxDestination& address : _grouping)
            if ((it = setmap.find(address)) != setmap.end())
                hits.insert((*it).second);

        // merge all hit groups into a new single group and delete old groups
        std::set<CTxDestination>* merged = new std::set<CTxDestination>(_grouping);
        for (std::set<CTxDestination>* hit : hits)
        {
            merged->insert(hit->begin(), hit->end());
            uniqueGroupings.erase(hit);
            delete hit;
        }
        uniqueGroupings.insert(merged);

        // update setmap
        for (const CTxDestination& element : *merged)
            setmap[element] = merged;
    }

    std::set< std::set<CTxDestination> > ret;
    for (const std::set<CTxDestination>* uniqueGrouping : uniqueGroupings)
    {
        ret.insert(*uniqueGrouping);
        delete uniqueGrouping;
    }

    return ret;
}

// ELEMENTS
CAmountMap CWalletTx::GetIssuanceAssets(const CWallet& wallet, unsigned int input_index) const {
    CAmountMap ret;
    CAsset asset, token;
    GetIssuanceAssets(input_index, &asset, &token);
    if (!asset.IsNull()) {
        ret[asset] = GetIssuanceAmount(wallet, input_index, false);
    }
    if (!token.IsNull()) {
        ret[token] = GetIssuanceAmount(wallet, input_index, true);
    }
    return ret;
}
// end ELEMENTS
} // namespace wallet
