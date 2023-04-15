// Copyright (c) 2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_WALLET_RECEIVE_H
#define BITCOIN_WALLET_RECEIVE_H

#include <amount.h>
#include <wallet/ismine.h>
#include <wallet/transaction.h>
#include <wallet/wallet.h>

isminetype InputIsMine(const CWallet& wallet, const CTxIn& txin) EXCLUSIVE_LOCKS_REQUIRED(wallet.cs_wallet);
isminetype InputIsMine(const CWallet& wallet, const COutPoint& txin) EXCLUSIVE_LOCKS_REQUIRED(wallet.cs_wallet);

/** Returns whether all of the inputs match the filter */
bool AllInputsMine(const CWallet& wallet, const CTransaction& tx, const isminefilter& filter);

CAmountMap OutputGetCredit(const CWallet& wallet, const CTransaction& tx, const size_t out_index, const isminefilter& filter);
CAmountMap TxGetCredit(const CWallet& wallet, const CTransaction& tx, const isminefilter& filter);

bool ScriptIsChange(const CWallet& wallet, const CScript& script) EXCLUSIVE_LOCKS_REQUIRED(wallet.cs_wallet);
bool OutputIsChange(const CWallet& wallet, const CTxOut& txout) EXCLUSIVE_LOCKS_REQUIRED(wallet.cs_wallet);
CAmountMap OutputGetChange(const CWallet& wallet, const CTxOut& txout) EXCLUSIVE_LOCKS_REQUIRED(wallet.cs_wallet);
CAmountMap TxGetChange(const CWallet& wallet, const CTransaction& tx);
// ELEMENTS:
CAmountMap GetCredit(const CWallet& wallet, const CWalletTx& wtx, const isminefilter& filter) EXCLUSIVE_LOCKS_REQUIRED(wallet.cs_wallet);
CAmountMap GetChange(const CWallet& wallet, const CWalletTx& wtx) EXCLUSIVE_LOCKS_REQUIRED(wallet.cs_wallet);

CAmountMap CachedTxGetCredit(const CWallet& wallet, const CWalletTx& wtx, const isminefilter& filter);
//! filter decides which addresses will count towards the debit
CAmountMap CachedTxGetDebit(const CWallet& wallet, const CWalletTx& wtx, const isminefilter& filter);
// TODO: Remove "NO_THREAD_SAFETY_ANALYSIS" and replace it with the correct
// annotation "EXCLUSIVE_LOCKS_REQUIRED(pwallet->cs_wallet)". The
// annotation "NO_THREAD_SAFETY_ANALYSIS" was temporarily added to avoid
// having to resolve the issue of member access into incomplete type CWallet.
CAmountMap CachedTxGetChange(const CWallet& wallet, const CWalletTx& wtx) NO_THREAD_SAFETY_ANALYSIS;
CAmountMap CachedTxGetImmatureCredit(const CWallet& wallet, const CWalletTx& wtx, bool fUseCache = true);
CAmountMap CachedTxGetImmatureWatchOnlyCredit(const CWallet& wallet, const CWalletTx& wtx, const bool fUseCache = true);
// TODO: Remove "NO_THREAD_SAFETY_ANALYSIS" and replace it with the correct
// annotation "EXCLUSIVE_LOCKS_REQUIRED(pwallet->cs_wallet)". The
// annotation "NO_THREAD_SAFETY_ANALYSIS" was temporarily added to avoid
// having to resolve the issue of member access into incomplete type CWallet.
CAmountMap CachedTxGetAvailableCredit(const CWallet& wallet, const CWalletTx& wtx, bool fUseCache = true, const isminefilter& filter = ISMINE_SPENDABLE) NO_THREAD_SAFETY_ANALYSIS;
struct COutputEntry
{
    CTxDestination destination;
    CAmount amount;
    int vout;
    CAsset asset;
    uint256 amount_blinding_factor;
    uint256 asset_blinding_factor;
};
void CachedTxGetAmounts(const CWallet& wallet, const CWalletTx& wtx,
                        std::list<COutputEntry>& listReceived,
                        std::list<COutputEntry>& listSent,
                        CAmount& nFee, const isminefilter& filter);
bool CachedTxIsFromMe(const CWallet& wallet, const CWalletTx& wtx, const isminefilter& filter);
bool CachedTxIsTrusted(const CWallet& wallet, const CWalletTx& wtx, std::set<uint256>& trusted_parents) EXCLUSIVE_LOCKS_REQUIRED(wallet.cs_wallet);
bool CachedTxIsTrusted(const CWallet& wallet, const CWalletTx& wtx);

struct Balance {
    CAmountMap m_mine_trusted;           //!< Trusted, at depth=GetBalance.min_depth or more
    CAmountMap m_mine_untrusted_pending; //!< Untrusted, but in mempool (pending)
    CAmountMap m_mine_immature;          //!< Immature coinbases in the main chain
    CAmountMap m_watchonly_trusted;
    CAmountMap m_watchonly_untrusted_pending;
    CAmountMap m_watchonly_immature;
};
Balance GetBalance(const CWallet& wallet, int min_depth = 0, bool avoid_reuse = true);

std::map<CTxDestination, CAmount> GetAddressBalances(const CWallet& wallet);
std::set<std::set<CTxDestination>> GetAddressGroupings(const CWallet& wallet) EXCLUSIVE_LOCKS_REQUIRED(wallet.cs_wallet);

#endif // BITCOIN_WALLET_RECEIVE_H
