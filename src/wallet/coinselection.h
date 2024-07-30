// Copyright (c) 2017-2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_WALLET_COINSELECTION_H
#define BITCOIN_WALLET_COINSELECTION_H

#include <chainparams.h>
#include <consensus/amount.h>
#include <policy/feerate.h>
#include <policy/policy.h>
#include <primitives/transaction.h>
#include <primitives/bitcoin/transaction.h>
#include <random.h>

#include <optional>


// class CWallet;
// class CWalletTx;
// class uint256;

namespace wallet {
//! lower bound for randomly-chosen target change amount
static constexpr CAmount CHANGE_LOWER{50000};
//! upper bound for randomly-chosen target change amount
static constexpr CAmount CHANGE_UPPER{1000000};

class CWallet;
class CWalletTx;

/** A UTXO under consideration for use in funding a new transaction. */
struct COutput {
    /** The outpoint identifying this UTXO */
    COutPoint outpoint;

    /** The output itself */
    CTxOut txout;

    /**
     * Depth in block chain.
     * If > 0: the tx is on chain and has this many confirmations.
     * If = 0: the tx is waiting confirmation.
     * If < 0: a conflicting tx is on chain and has this many confirmations. */
    int depth;

    /** Pre-computed estimated size of this output as a fully-signed input in a transaction. Can be -1 if it could not be calculated */
    int input_bytes;

    /** Whether we have the private keys to spend this output */
    bool spendable;

    /** Whether we know how to spend this output, ignoring the lack of keys */
    bool solvable;

    /**
     * Whether this output is considered safe to spend. Unconfirmed transactions
     * from outside keys and unconfirmed replacement transactions are considered
     * unsafe and will not be used to fund new spending transactions.
     */
    bool safe;

    /** The time of the transaction containing this output as determined by CWalletTx::nTimeSmart */
    int64_t time;

    /** Whether the transaction containing this output is sent from the owning wallet */
    bool from_me;

    /** The output's value minus fees required to spend it. Initialized as the output's absolute value. */
    CAmount effective_value;

    /** The fee required to spend this output at the transaction's target feerate. */
    CAmount fee{0};

    /** The fee required to spend this output at the consolidation feerate. */
    CAmount long_term_fee{0};

    // ELEMENTS: input-specific details which are not needed in bitcoin

    /** ELEMENTS: the value of the output */
    CAmount value;
    /** ELEMENTS: the asset of the output */
    CAsset asset{Params().GetConsensus().pegged_asset};
    /** ELEMENTS: the blinding factor for the value */
    uint256 bf_value;
    /** ELEMENTS: the blinding factor for the asset */
    uint256 bf_asset;

    // ELEMENTS: the implementation logic for this constructor is inside of coinselection.cpp, since it is more detailed than bitcoin's version
    COutput(const COutPoint& outpoint, const CTxOut& txout, int depth, int input_bytes, bool spendable, bool solvable, bool safe, int64_t time, bool from_me);

    // ELEMENTS: use this constructor to set the value and asset info (when wallet and wtx are available).
    COutput(const CWallet& wallet, const CWalletTx& wtx, const COutPoint& outpoint, const CTxOut& txout, int depth, int input_bytes, bool spendable, bool solvable, bool safe, int64_t time, bool from_me);

    std::string ToString() const;

    bool operator<(const COutput& rhs) const
    {
        return outpoint < rhs.outpoint;
    }
};

/** Parameters for one iteration of Coin Selection. */
struct CoinSelectionParams {
    /** Randomness to use in the context of coin selection. */
    FastRandomContext& rng_fast;
    /** Size of a change output in bytes, determined by the output type. */
    size_t change_output_size = 0;
    /** Size of the input to spend a change output in virtual bytes. */
    size_t change_spend_size = 0;
    /** Mininmum change to target in Knapsack solver: select coins to cover the payment and
     * at least this value of change. */
    CAmount m_min_change_target{0};
    /** Cost of creating the change output. */
    CAmount m_change_fee{0};
    /** The pre-determined minimum value to target when funding a change output. */
    CAmount m_change_target{0};
    /** Cost of creating the change output + cost of spending the change output in the future. */
    CAmount m_cost_of_change{0};
    /** The targeted feerate of the transaction being built. */
    CFeeRate m_effective_feerate;
    /** The feerate estimate used to estimate an upper bound on what should be sufficient to spend
     * the change output sometime in the future. */
    CFeeRate m_long_term_feerate;
    /** If the cost to spend a change output at the discard feerate exceeds its value, drop it to fees. */
    CFeeRate m_discard_feerate;
    /** Size of the transaction before coin selection, consisting of the header and recipient
     * output(s), excluding the inputs and change output(s). */
    size_t tx_noinputs_size = 0;
    /** Indicate that we are subtracting the fee from outputs */
    bool m_subtract_fee_outputs = false;
    /** When true, always spend all (up to OUTPUT_GROUP_MAX_ENTRIES) or none of the outputs
     * associated with the same address. This helps reduce privacy leaks resulting from address
     * reuse. Dust outputs are not eligible to be added to output groups and thus not considered. */
    bool m_avoid_partial_spends = false;

    CoinSelectionParams(FastRandomContext& rng_fast, size_t change_output_size, size_t change_spend_size,
                        CAmount min_change_target, CFeeRate effective_feerate,
                        CFeeRate long_term_feerate, CFeeRate discard_feerate, size_t tx_noinputs_size, bool avoid_partial)
        : rng_fast{rng_fast},
          change_output_size(change_output_size),
          change_spend_size(change_spend_size),
          m_min_change_target(min_change_target),
          m_effective_feerate(effective_feerate),
          m_long_term_feerate(long_term_feerate),
          m_discard_feerate(discard_feerate),
          tx_noinputs_size(tx_noinputs_size),
          m_avoid_partial_spends(avoid_partial)
    {
    }
    CoinSelectionParams(FastRandomContext& rng_fast)
        : rng_fast{rng_fast} {}
};

/** Parameters for filtering which OutputGroups we may use in coin selection.
 * We start by being very selective and requiring multiple confirmations and
 * then get more permissive if we cannot fund the transaction. */
struct CoinEligibilityFilter
{
    /** Minimum number of confirmations for outputs that we sent to ourselves.
     * We may use unconfirmed UTXOs sent from ourselves, e.g. change outputs. */
    const int conf_mine;
    /** Minimum number of confirmations for outputs received from a different wallet. */
    const int conf_theirs;
    /** Maximum number of unconfirmed ancestors aggregated across all UTXOs in an OutputGroup. */
    const uint64_t max_ancestors;
    /** Maximum number of descendants that a single UTXO in the OutputGroup may have. */
    const uint64_t max_descendants;
    /** When avoid_reuse=true and there are full groups (OUTPUT_GROUP_MAX_ENTRIES), whether or not to use any partial groups.*/
    const bool m_include_partial_groups{false};

    CoinEligibilityFilter(int conf_mine, int conf_theirs, uint64_t max_ancestors) : conf_mine(conf_mine), conf_theirs(conf_theirs), max_ancestors(max_ancestors), max_descendants(max_ancestors) {}
    CoinEligibilityFilter(int conf_mine, int conf_theirs, uint64_t max_ancestors, uint64_t max_descendants) : conf_mine(conf_mine), conf_theirs(conf_theirs), max_ancestors(max_ancestors), max_descendants(max_descendants) {}
    CoinEligibilityFilter(int conf_mine, int conf_theirs, uint64_t max_ancestors, uint64_t max_descendants, bool include_partial) : conf_mine(conf_mine), conf_theirs(conf_theirs), max_ancestors(max_ancestors), max_descendants(max_descendants), m_include_partial_groups(include_partial) {}
};

/** A group of UTXOs paid to the same output script. */
struct OutputGroup
{
    /** The list of UTXOs contained in this output group. */
    std::vector<COutput> m_outputs;
    /** Whether the UTXOs were sent by the wallet to itself. This is relevant because we may want at
     * least a certain number of confirmations on UTXOs received from outside wallets while trusting
     * our own UTXOs more. */
    bool m_from_me{true};
    /** The total value of the UTXOs in sum. */
    CAmount m_value{0};
    /** The minimum number of confirmations the UTXOs in the group have. Unconfirmed is 0. */
    int m_depth{999};
    /** The aggregated count of unconfirmed ancestors of all UTXOs in this
     * group. Not deduplicated and may overestimate when ancestors are shared. */
    size_t m_ancestors{0};
    /** The maximum count of descendants of a single UTXO in this output group. */
    size_t m_descendants{0};
    /** The value of the UTXOs after deducting the cost of spending them at the effective feerate. */
    CAmount effective_value{0};
    /** The fee to spend these UTXOs at the effective feerate. */
    CAmount fee{0};
    /** The target feerate of the transaction we're trying to build. */
    CFeeRate m_effective_feerate{0};
    /** The fee to spend these UTXOs at the long term feerate. */
    CAmount long_term_fee{0};
    /** The feerate for spending a created change output eventually (i.e. not urgently, and thus at
     * a lower feerate). Calculated using long term fee estimate. This is used to decide whether
     * it could be economical to create a change output. */
    CFeeRate m_long_term_feerate{0};
    /** Indicate that we are subtracting the fee from outputs.
     * When true, the value that is used for coin selection is the UTXO's real value rather than effective value */
    bool m_subtract_fee_outputs{false};

    OutputGroup() {}
    OutputGroup(const CoinSelectionParams& params) :
        m_effective_feerate(params.m_effective_feerate),
        m_long_term_feerate(params.m_long_term_feerate),
        m_subtract_fee_outputs(params.m_subtract_fee_outputs)
    {}

    void Insert(const COutput& output, size_t ancestors, size_t descendants, bool positive_only);
    bool EligibleForSpending(const CoinEligibilityFilter& eligibility_filter) const;
    CAmount GetSelectionAmount() const;
};

/** Compute the waste for this result given the cost of change
 * and the opportunity cost of spending these inputs now vs in the future.
 * If change exists, waste = change_cost + inputs * (effective_feerate - long_term_feerate)
 * If no change, waste = excess + inputs * (effective_feerate - long_term_feerate)
 * where excess = selected_effective_value - target
 * change_cost = effective_feerate * change_output_size + long_term_feerate * change_spend_size
 *
 * Note this function is separate from SelectionResult for the tests.
 *
 * @param[in] inputs The selected inputs
 * @param[in] change_cost The cost of creating change and spending it in the future.
 *                        Only used if there is change, in which case it must be positive.
 *                        Must be 0 if there is no change.
 * @param[in] target The amount targeted by the coin selection algorithm.
 * @param[in] use_effective_value Whether to use the input's effective value (when true) or the real value (when false).
 * @return The waste
 */
[[nodiscard]] CAmount GetSelectionWaste(const std::set<COutput>& inputs, CAmount change_cost, CAmount target, bool use_effective_value = true);


/** Choose a random change target for each transaction to make it harder to fingerprint the Core
 * wallet based on the change output values of transactions it creates.
 * The random value is between 50ksat and min(2 * payment_value, 1milsat)
 * When payment_value <= 25ksat, the value is just 50ksat.
 *
 * Making change amounts similar to the payment value may help disguise which output(s) are payments
 * are which ones are change. Using double the payment value may increase the number of inputs
 * needed (and thus be more expensive in fees), but breaks analysis techniques which assume the
 * coins selected are just sufficient to cover the payment amount ("unnecessary input" heuristic).
 *
 * @param[in]   payment_value   Average payment value of the transaction output(s).
 */
[[nodiscard]] CAmount GenerateChangeTarget(CAmount payment_value, FastRandomContext& rng);

struct SelectionResult
{
private:
    /** Set of inputs selected by the algorithm to use in the transaction */
    std::set<COutput> m_selected_inputs;
    /** The target the algorithm selected for. Note that this may not be equal to the recipient amount as it can include non-input fees */
    const CAmountMap m_target;
    /** Whether the input values for calculations should be the effective value (true) or normal value (false) */
    bool m_use_effective{false};
    /** The computed waste */
    std::optional<CAmount> m_waste;

public:
    explicit SelectionResult(const CAmountMap target)
        : m_target(target) {}

    SelectionResult() = delete;

    /** Get the sum of the input values */
    [[nodiscard]] CAmountMap GetSelectedValue() const;

    void Clear();

    void AddInput(const OutputGroup& group);
    // ELEMENTS
    void AddInput(const SelectionResult& result);

    /** Calculates and stores the waste for this selection via GetSelectionWaste */
    void ComputeAndSetWaste(CAmount change_cost);
    [[nodiscard]] CAmount GetWaste() const;

    /** Get m_selected_inputs */
    const std::set<COutput>& GetInputSet() const;
    /** Get the vector of COutputs that will be used to fill in a CTransaction's vin */
    std::vector<COutput> GetShuffledInputVector() const;

    bool operator<(SelectionResult other) const;
};

std::optional<SelectionResult> SelectCoinsBnB(std::vector<OutputGroup>& utxo_pool, const CAmount& selection_target, const CAmount& cost_of_change);

/** Select coins by Single Random Draw. OutputGroups are selected randomly from the eligible
 * outputs until the target is satisfied
 *
 * @param[in]  utxo_pool    The positive effective value OutputGroups eligible for selection
 * @param[in]  target_value The target value to select for
 * @returns If successful, a SelectionResult, otherwise, std::nullopt
 */
std::optional<SelectionResult> SelectCoinsSRD(const std::vector<OutputGroup>& utxo_pool, CAmount target_value, FastRandomContext& rng);

// Original coin selection algorithm as a fallback
std::optional<SelectionResult> KnapsackSolver(std::vector<OutputGroup>& groups, const CAmount& nTargetValue,
                                              CAmount change_target, FastRandomContext& rng, const CAsset& asset = ::policyAsset);

// ELEMENTS:
// Knapsack that delegates for every asset individually.
std::optional<SelectionResult> KnapsackSolver(std::vector<OutputGroup>& groups, const CAmountMap& mapTargetValue,
                                              CAmount change_target, FastRandomContext& rng);

// Get coin selection waste for a map of asset->amount.
[[nodiscard]] CAmount GetSelectionWaste(const std::set<COutput>& inputs, CAmount change_cost, const CAmountMap& target_map, bool use_effective_value);
} // namespace wallet

#endif // BITCOIN_WALLET_COINSELECTION_H
