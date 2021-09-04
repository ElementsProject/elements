// Copyright (c) 2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <consensus/consensus.h>
#include <policy/policy.h> // ELEMENTS: for policyAsset
#include <wallet/receive.h>
#include <wallet/transaction.h>
#include <wallet/wallet.h>

isminetype CWallet::IsMine(const CTxIn& txin) const
{
    AssertLockHeld(cs_wallet);
    return IsMine(txin.prevout);
}

isminetype CWallet::IsMine(const COutPoint &outpoint) const
{
    AssertLockHeld(cs_wallet);
    std::map<uint256, CWalletTx>::const_iterator mi = mapWallet.find(outpoint.hash);
    if (mi != mapWallet.end())
    {
        const CWalletTx& prev = (*mi).second;
        if (outpoint.n < prev.tx->vout.size())
            return IsMine(prev.tx->vout[outpoint.n]);
    }
    return ISMINE_NO;
}

bool CWallet::IsAllFromMe(const CTransaction& tx, const isminefilter& filter) const
{
    LOCK(cs_wallet);

    for (const CTxIn& txin : tx.vin)
    {
        auto mi = mapWallet.find(txin.prevout.hash);
        if (mi == mapWallet.end())
            return false; // any unknown inputs can't be from us

        const CWalletTx& prev = (*mi).second;

        if (txin.prevout.n >= prev.tx->vout.size())
            return false; // invalid input!

        if (!(IsMine(prev.tx->vout[txin.prevout.n]) & filter))
            return false;
    }
    return true;
}

CAmountMap CWallet::GetCredit(const CWalletTx& wtx, const isminefilter& filter) const {
    CAmountMap nCredit;
    for (unsigned int i = 0; i < wtx.tx->vout.size(); ++i) {
        if (IsMine(wtx.tx->vout[i]) & filter) {
            CAmount credit = std::max<CAmount>(0, wtx.GetOutputValueOut(i));
            if (!MoneyRange(credit))
                throw std::runtime_error(std::string(__func__) + ": value out of range");

            nCredit[wtx.GetOutputAsset(i)] += credit;
            if (!MoneyRange(nCredit))
                throw std::runtime_error(std::string(__func__) + ": value out of range");
        }
    }
    return nCredit;
}

CAmountMap CWallet::GetChange(const CWalletTx& wtx) const {
    CAmountMap nChange;
    for (unsigned int i = 0; i < wtx.tx->vout.size(); ++i) {
        if (IsChange(wtx.tx->vout[i])) {
            CAmount change = wtx.GetOutputValueOut(i);
            if (change < 0) {
                continue;
            }

            if (!MoneyRange(change))
                throw std::runtime_error(std::string(__func__) + ": value out of range");

            nChange[wtx.GetOutputAsset(i)] += change;
            if (!MoneyRange(nChange))
                throw std::runtime_error(std::string(__func__) + ": value out of range");
        }
    }
    return nChange;
}

CAmountMap CWallet::GetChange(const CTransaction& tx) const
{
    LOCK(cs_wallet);
    CAmountMap nChange;
    for (const CTxOut& txout : tx.vout)
    {
        nChange += GetChange(txout);
        if (!MoneyRange(nChange))
            throw std::runtime_error(std::string(__func__) + ": value out of range");
    }
    return nChange;
}

bool CWallet::IsChange(const CTxOut& txout) const
{
    return IsChange(txout.scriptPubKey);
}

bool CWallet::IsChange(const CScript& script) const
{
    // TODO: fix handling of 'change' outputs. The assumption is that any
    // payment to a script that is ours, but is not in the address book
    // is change. That assumption is likely to break when we implement multisignature
    // wallets that return change back into a multi-signature-protected address;
    // a better way of identifying which outputs are 'the send' and which are
    // 'the change' will need to be implemented (maybe extend CWalletTx to remember
    // which output, if any, was change).
    AssertLockHeld(cs_wallet);
    if (IsMine(script))
    {
        CTxDestination address;
        if (!ExtractDestination(script, address))
            return true;
        if (!FindAddressBookEntry(address)) {
            return true;
        }
    }
    return false;
}

CAmountMap CWallet::GetChange(const CTxOut& txout) const
{
    AssertLockHeld(cs_wallet);

    CAmountMap change;
    change[txout.nAsset.GetAsset()] = txout.nValue.GetAmount();
    if (!MoneyRange(change))
        throw std::runtime_error(std::string(__func__) + ": value out of range");
    return (IsChange(txout) ? change : CAmountMap());
}

CAmountMap CWalletTx::GetCachableAmount(AmountType type, const isminefilter& filter, bool recalculate) const
{
    auto& amount = m_amounts[type];
    if (recalculate || !amount.m_cached[filter]) {
        amount.Set(filter, type == DEBIT ? pwallet->GetDebit(*tx, filter) : pwallet->GetCredit(*this, filter));
        m_is_cache_empty = false;
    }
    return amount.m_value[filter];
}

CAmountMap CWalletTx::GetCredit(const isminefilter& filter) const
{
    // Must wait until coinbase is safely deep enough in the chain before valuing it
    if (IsImmatureCoinBase())
        return CAmountMap();

    CAmountMap credit;
    if (filter & ISMINE_SPENDABLE) {
        // GetBalance can assume transactions in mapWallet won't change
        credit += GetCachableAmount(CREDIT, ISMINE_SPENDABLE);
    }
    if (filter & ISMINE_WATCH_ONLY) {
        credit += GetCachableAmount(CREDIT, ISMINE_WATCH_ONLY);
    }
    return credit;
}

CAmountMap CWallet::GetCredit(const CTransaction& tx, const size_t out_index, const isminefilter& filter) const
{
    {
        LOCK(cs_wallet);
        std::map<uint256, CWalletTx>::const_iterator mi = mapWallet.find(tx.GetHash());
        if (mi != mapWallet.end())
        {
            const CWalletTx& wtx = (*mi).second;
            if (out_index < wtx.tx->vout.size() && IsMine(wtx.tx->vout[out_index]) & filter) {
                CAmountMap amounts;
                amounts[wtx.GetOutputAsset(out_index)] = std::max<CAmount>(0, wtx.GetOutputValueOut(out_index));
                return amounts;
            }
        }
    }
    return CAmountMap();
}

CAmountMap CWalletTx::GetDebit(const isminefilter& filter) const
{
    if (tx->vin.empty())
        return CAmountMap();

    CAmountMap debit;
    if (filter & ISMINE_SPENDABLE) {
        debit += GetCachableAmount(DEBIT, ISMINE_SPENDABLE);
    }
    if (filter & ISMINE_WATCH_ONLY) {
        debit += GetCachableAmount(DEBIT, ISMINE_WATCH_ONLY);
    }
    return debit;
}

CAmountMap CWalletTx::GetChange() const
{
    if (fChangeCached)
        return nChangeCached;
    nChangeCached = pwallet->GetChange(*this);
    fChangeCached = true;
    return nChangeCached;
}

CAmountMap CWalletTx::GetImmatureCredit(bool fUseCache) const
{
    if (IsImmatureCoinBase() && IsInMainChain()) {
        return GetCachableAmount(IMMATURE_CREDIT, ISMINE_SPENDABLE, !fUseCache);
    }

    return CAmountMap();
}

CAmountMap CWalletTx::GetImmatureWatchOnlyCredit(const bool fUseCache) const
{
    if (IsImmatureCoinBase() && IsInMainChain()) {
        return GetCachableAmount(IMMATURE_CREDIT, ISMINE_WATCH_ONLY, !fUseCache);
    }

    return CAmountMap();
}

CAmountMap CWalletTx::GetAvailableCredit(bool fUseCache, const isminefilter& filter) const
{
    if (pwallet == nullptr)
        return CAmountMap();

    // Avoid caching ismine for NO or ALL cases (could remove this check and simplify in the future).
    bool allow_cache = (filter & ISMINE_ALL) && (filter & ISMINE_ALL) != ISMINE_ALL;

    // Must wait until coinbase is safely deep enough in the chain before valuing it
    if (IsImmatureCoinBase())
        return CAmountMap();

    if (fUseCache && allow_cache && m_amounts[AVAILABLE_CREDIT].m_cached[filter]) {
        return m_amounts[AVAILABLE_CREDIT].m_value[filter];
    }

    bool allow_used_addresses = (filter & ISMINE_USED) || !pwallet->IsWalletFlagSet(WALLET_FLAG_AVOID_REUSE);
    CAmountMap nCredit;
    uint256 hashTx = GetHash();
    for (unsigned int i = 0; i < tx->vout.size(); i++)
    {
        if (!pwallet->IsSpent(hashTx, i) && (allow_used_addresses || !pwallet->IsSpentKey(hashTx, i))) {
            if (pwallet->IsMine(tx->vout[i]) & filter) {
                CAmount credit = std::max<CAmount>(0, GetOutputValueOut(i));
                if (!MoneyRange(credit))
                    throw std::runtime_error(std::string(__func__) + ": value out of range");

                nCredit[GetOutputAsset(i)] += std::max<CAmount>(0, GetOutputValueOut(i));
                if (!MoneyRange(nCredit))
                    throw std::runtime_error(std::string(__func__) + ": value out of range");
            }
        }
    }

    if (allow_cache) {
        m_amounts[AVAILABLE_CREDIT].Set(filter, nCredit);
        m_is_cache_empty = false;
    }

    return nCredit;
}

void CWalletTx::GetAmounts(std::list<COutputEntry>& listReceived,
                           std::list<COutputEntry>& listSent, CAmount& nFee, const isminefilter& filter) const
{
    nFee = 0;
    listReceived.clear();
    listSent.clear();

    // Compute fee:
    CAmountMap mapDebit = GetDebit(filter);
    if (mapDebit > CAmountMap()) // debit>0 means we signed/sent this transaction
    {
        nFee = -GetFeeMap(*tx)[::policyAsset];
    }

    LOCK(pwallet->cs_wallet);
    // Sent/received.
    for (unsigned int i = 0; i < tx->vout.size(); ++i)
    {
        const CTxOut& txout = tx->vout[i];
        CAmount output_value = GetOutputValueOut(i);
        // Don't list unknown assets
        isminetype fIsMine = output_value != -1 ?  pwallet->IsMine(txout) : ISMINE_NO;
        // Only need to handle txouts if AT LEAST one of these is true:
        //   1) they debit from us (sent)
        //   2) the output is to us (received)
        if (mapDebit > CAmountMap())
        {
            // Don't report 'change' txouts
            if (pwallet->IsChange(txout))
                continue;
        }
        else if (!(fIsMine & filter))
            continue;

        // In either case, we need to get the destination address
        CTxDestination address;

        if (!ExtractDestination(txout.scriptPubKey, address) && !txout.scriptPubKey.IsUnspendable())
        {
            pwallet->WalletLogPrintf("CWalletTx::GetAmounts: Unknown transaction type found, txid %s\n",
                                    this->GetHash().ToString());
            address = CNoDestination();
        }

        COutputEntry output = {address, output_value, (int)i, GetOutputAsset(i), GetOutputAmountBlindingFactor(i), GetOutputAssetBlindingFactor(i)};

        // If we are debited by the transaction, add the output as a "sent" entry
        if (mapDebit > CAmountMap() && !txout.IsFee())
            listSent.push_back(output);

        // If we are receiving the output, add it as a "received" entry
        if (fIsMine & filter)
            listReceived.push_back(output);
    }

}

bool CWallet::IsTrusted(const CWalletTx& wtx, std::set<uint256>& trusted_parents) const
{
    AssertLockHeld(cs_wallet);
    // Quick answer in most cases
    if (!chain().checkFinalTx(*wtx.tx)) return false;
    int nDepth = wtx.GetDepthInMainChain();
    if (nDepth >= 1) return true;
    if (nDepth < 0) return false;
    // using wtx's cached debit
    if (!m_spend_zero_conf_change || !wtx.IsFromMe(ISMINE_ALL)) return false;

    // Don't trust unconfirmed transactions from us unless they are in the mempool.
    if (!wtx.InMempool()) return false;

    // Trusted if all inputs are from us and are in the mempool:
    for (const CTxIn& txin : wtx.tx->vin)
    {
        // Transactions not sent by us: not trusted
        const CWalletTx* parent = GetWalletTx(txin.prevout.hash);
        if (parent == nullptr) return false;
        const CTxOut& parentOut = parent->tx->vout[txin.prevout.n];
        // Check that this specific input being spent is trusted
        if (IsMine(parentOut) != ISMINE_SPENDABLE) return false;
        // If we've already trusted this parent, continue
        if (trusted_parents.count(parent->GetHash())) continue;
        // Recurse to check that the parent is also trusted
        if (!IsTrusted(*parent, trusted_parents)) return false;
        trusted_parents.insert(parent->GetHash());
    }
    return true;
}

bool CWalletTx::IsTrusted() const
{
    std::set<uint256> trusted_parents;
    LOCK(pwallet->cs_wallet);
    return pwallet->IsTrusted(*this, trusted_parents);
}

CWallet::Balance CWallet::GetBalance(const int min_depth, bool avoid_reuse) const
{
    Balance ret;
    isminefilter reuse_filter = avoid_reuse ? ISMINE_NO : ISMINE_USED;
    {
        LOCK(cs_wallet);
        std::set<uint256> trusted_parents;
        for (const auto& entry : mapWallet)
        {
            const CWalletTx& wtx = entry.second;
            const bool is_trusted{IsTrusted(wtx, trusted_parents)};
            const int tx_depth{wtx.GetDepthInMainChain()};
            const CAmountMap tx_credit_mine{wtx.GetAvailableCredit(/* fUseCache */ true, ISMINE_SPENDABLE | reuse_filter)};
            const CAmountMap tx_credit_watchonly{wtx.GetAvailableCredit(/* fUseCache */ true, ISMINE_WATCH_ONLY | reuse_filter)};
            if (is_trusted && tx_depth >= min_depth) {
                ret.m_mine_trusted += tx_credit_mine;
                ret.m_watchonly_trusted += tx_credit_watchonly;
            }
            if (!is_trusted && tx_depth == 0 && wtx.InMempool()) {
                ret.m_mine_untrusted_pending += tx_credit_mine;
                ret.m_watchonly_untrusted_pending += tx_credit_watchonly;
            }
            ret.m_mine_immature += wtx.GetImmatureCredit();
            ret.m_watchonly_immature += wtx.GetImmatureWatchOnlyCredit();
        }
    }
    return ret;
}

std::map<CTxDestination, CAmount> CWallet::GetAddressBalances() const
{
    std::map<CTxDestination, CAmount> balances;

    {
        LOCK(cs_wallet);
        std::set<uint256> trusted_parents;
        for (const auto& walletEntry : mapWallet)
        {
            const CWalletTx& wtx = walletEntry.second;

            if (!IsTrusted(wtx, trusted_parents))
                continue;

            if (wtx.IsImmatureCoinBase())
                continue;

            int nDepth = wtx.GetDepthInMainChain();
            if (nDepth < (wtx.IsFromMe(ISMINE_ALL) ? 0 : 1))
                continue;

            for (unsigned int i = 0; i < wtx.tx->vout.size(); i++)
            {
                CTxDestination addr;
                if (!IsMine(wtx.tx->vout[i]))
                    continue;
                if(!ExtractDestination(wtx.tx->vout[i].scriptPubKey, addr))
                    continue;

                CAmount n = IsSpent(walletEntry.first, i) ? 0 : wtx.GetOutputValueOut(i);
                if (n < 0) {
                    continue;
                }
                balances[addr] += n;
            }
        }
    }

    return balances;
}

std::set< std::set<CTxDestination> > CWallet::GetAddressGroupings() const
{
    AssertLockHeld(cs_wallet);
    std::set< std::set<CTxDestination> > groupings;
    std::set<CTxDestination> grouping;

    for (const auto& walletEntry : mapWallet)
    {
        const CWalletTx& wtx = walletEntry.second;

        if (wtx.tx->vin.size() > 0)
        {
            bool any_mine = false;
            // group all input addresses with each other
            for (const CTxIn& txin : wtx.tx->vin)
            {
                CTxDestination address;
                if(!IsMine(txin)) /* If this input isn't mine, ignore it */
                    continue;
                if(!ExtractDestination(mapWallet.at(txin.prevout.hash).tx->vout[txin.prevout.n].scriptPubKey, address))
                    continue;
                grouping.insert(address);
                any_mine = true;
            }

            // group change with input addresses
            if (any_mine)
            {
               for (const CTxOut& txout : wtx.tx->vout)
                   if (IsChange(txout))
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
            if (IsMine(txout))
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
CAmountMap CWalletTx::GetIssuanceAssets(unsigned int input_index) const {
    CAmountMap ret;
    CAsset asset, token;
    GetIssuanceAssets(input_index, &asset, &token);
    if (!asset.IsNull()) {
        ret[asset] = GetIssuanceAmount(input_index, false);
    }
    if (!token.IsNull()) {
        ret[token] = GetIssuanceAmount(input_index, true);
    }
    return ret;
}
// end ELEMENTS

