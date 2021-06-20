// Copyright (c) 2017-2019 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_WALLET_COINSELECTION_H
#define BITCOIN_WALLET_COINSELECTION_H

#include <amount.h>
#include <chainparams.h>
#include <policy/feerate.h>
#include <primitives/transaction.h>
#include <primitives/bitcoin/transaction.h>
#include <random.h>

//! target minimum change amount
static constexpr CAmount MIN_CHANGE{COIN / 100};
//! final minimum change amount after paying for fees
static const CAmount MIN_FINAL_CHANGE = MIN_CHANGE/2;

class CWalletTx;
class uint256;

class CInputCoin {
public:
    CInputCoin(const CWalletTx* wtx, unsigned int i);

    CInputCoin(const CWalletTx* wtx, unsigned int i, int input_bytes) : CInputCoin(wtx, i)
    {
        m_input_bytes = input_bytes;
    }

    CInputCoin(const COutPoint& outpoint_in, const CTxOut& txout_in)
    {
        outpoint = outpoint_in;
        txout = txout_in;
        if (txout.nValue.IsExplicit()) {
            effective_value = txout_in.nValue.GetAmount();
            value = txout.nValue.GetAmount();
            asset = txout.nAsset.GetAsset();
        } else {
            effective_value = 0;
        }
    }

    CInputCoin(const COutPoint& outpoint_in, const CTxOut& txout_in, int input_bytes) : CInputCoin(outpoint_in, txout_in)
    {
        m_input_bytes = input_bytes;
    }

    CInputCoin(const COutPoint& outpoint_in, const Sidechain::Bitcoin::CTxOut& txout_in)
    {
        outpoint = outpoint_in;
        effective_value = txout_in.nValue;
        txout.SetNull();
        txout.scriptPubKey = txout_in.scriptPubKey;
        txout.nValue.SetToAmount(txout_in.nValue);
        txout.nAsset.SetToAsset(Params().GetConsensus().pegged_asset);
        asset = Params().GetConsensus().pegged_asset;
        value = txout_in.nValue;
    }

    CInputCoin(const COutPoint& outpoint_in, const Sidechain::Bitcoin::CTxOut& txout_in, int input_bytes) : CInputCoin(outpoint_in, txout_in)
    {
        m_input_bytes = input_bytes;
    }

    COutPoint outpoint;
    CTxOut txout;
    CAmount effective_value;
    CAmount m_fee{0};
    CAmount m_long_term_fee{0};
    // ELEMENTS:
    CAmount value;
    CAsset asset;
    uint256 bf_value;
    uint256 bf_asset;

    /** Pre-computed estimated size of this output as a fully-signed input in a transaction. Can be -1 if it could not be calculated */
    int m_input_bytes{-1};

    bool operator<(const CInputCoin& rhs) const {
        return outpoint < rhs.outpoint;
    }

    bool operator!=(const CInputCoin& rhs) const {
        return outpoint != rhs.outpoint;
    }

    bool operator==(const CInputCoin& rhs) const {
        return outpoint == rhs.outpoint;
    }
};

struct CoinEligibilityFilter
{
    const int conf_mine;
    const int conf_theirs;
    const uint64_t max_ancestors;
    const uint64_t max_descendants;
    const bool m_include_partial_groups{false}; //! Include partial destination groups when avoid_reuse and there are full groups

    CoinEligibilityFilter(int conf_mine, int conf_theirs, uint64_t max_ancestors) : conf_mine(conf_mine), conf_theirs(conf_theirs), max_ancestors(max_ancestors), max_descendants(max_ancestors) {}
    CoinEligibilityFilter(int conf_mine, int conf_theirs, uint64_t max_ancestors, uint64_t max_descendants) : conf_mine(conf_mine), conf_theirs(conf_theirs), max_ancestors(max_ancestors), max_descendants(max_descendants) {}
    CoinEligibilityFilter(int conf_mine, int conf_theirs, uint64_t max_ancestors, uint64_t max_descendants, bool include_partial) : conf_mine(conf_mine), conf_theirs(conf_theirs), max_ancestors(max_ancestors), max_descendants(max_descendants), m_include_partial_groups(include_partial) {}
};

struct OutputGroup
{
    std::vector<CInputCoin> m_outputs;
    bool m_from_me{true};
    CAmount m_value{0};
    int m_depth{999};
    size_t m_ancestors{0};
    size_t m_descendants{0};
    CAmount effective_value{0};
    CAmount fee{0};
    CFeeRate m_effective_feerate{0};
    CAmount long_term_fee{0};
    CFeeRate m_long_term_feerate{0};

    OutputGroup() {}
    OutputGroup(const CFeeRate& effective_feerate, const CFeeRate& long_term_feerate) :
        m_effective_feerate(effective_feerate),
        m_long_term_feerate(long_term_feerate)
    {}

    void Insert(const CInputCoin& output, int depth, bool from_me, size_t ancestors, size_t descendants, bool positive_only);
    bool EligibleForSpending(const CoinEligibilityFilter& eligibility_filter) const;
};

bool SelectCoinsBnB(std::vector<OutputGroup>& utxo_pool, const CAmount& target_value, const CAmount& cost_of_change, std::set<CInputCoin>& out_set, CAmount& value_ret, CAmount not_input_fees);

// Original coin selection algorithm as a fallback
bool KnapsackSolver(const CAmount& nTargetValue, std::vector<OutputGroup>& groups, std::set<CInputCoin>& setCoinsRet, CAmount& nValueRet);

// ELEMENTS:
// Knapsack that delegates for every asset individually.
bool KnapsackSolver(const CAmountMap& mapTargetValue, std::vector<OutputGroup>& groups, std::set<CInputCoin>& setCoinsRet, CAmountMap& mapValueRet);

#endif // BITCOIN_WALLET_COINSELECTION_H
