// Copyright (c) 2017-2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <wallet/coinselection.h>
#include <wallet/wallet.h>

#include <policy/feerate.h>
#include <policy/policy.h>
#include <util/system.h>
#include <util/moneystr.h>

#include <optional>

CInputCoin::CInputCoin(const CWalletTx* wtx, unsigned int i) {
    if (!wtx || !wtx->tx)
        throw std::invalid_argument("tx should not be null");
    if (i >= wtx->tx->vout.size())
        throw std::out_of_range("The output index is out of range");

    outpoint = COutPoint(wtx->tx->GetHash(), i);
    txout = wtx->tx->vout[i];
    effective_value = std::max<CAmount>(0, wtx->GetOutputValueOut(i));
    value = wtx->GetOutputValueOut(i);
    asset = wtx->GetOutputAsset(i);
    bf_value = wtx->GetOutputAmountBlindingFactor(i);
    bf_asset = wtx->GetOutputAssetBlindingFactor(i);
}

// Descending order comparator
struct {
    bool operator()(const OutputGroup& a, const OutputGroup& b) const
    {
        return a.GetSelectionAmount() > b.GetSelectionAmount();
    }
} descending;

/*
 * This is the Branch and Bound Coin Selection algorithm designed by Murch. It searches for an input
 * set that can pay for the spending target and does not exceed the spending target by more than the
 * cost of creating and spending a change output. The algorithm uses a depth-first search on a binary
 * tree. In the binary tree, each node corresponds to the inclusion or the omission of a UTXO. UTXOs
 * are sorted by their effective values and the trees is explored deterministically per the inclusion
 * branch first. At each node, the algorithm checks whether the selection is within the target range.
 * While the selection has not reached the target range, more UTXOs are included. When a selection's
 * value exceeds the target range, the complete subtree deriving from this selection can be omitted.
 * At that point, the last included UTXO is deselected and the corresponding omission branch explored
 * instead. The search ends after the complete tree has been searched or after a limited number of tries.
 *
 * The search continues to search for better solutions after one solution has been found. The best
 * solution is chosen by minimizing the waste metric. The waste metric is defined as the cost to
 * spend the current inputs at the given fee rate minus the long term expected cost to spend the
 * inputs, plus the amount the selection exceeds the spending target:
 *
 * waste = selectionTotal - target + inputs × (currentFeeRate - longTermFeeRate)
 *
 * The algorithm uses two additional optimizations. A lookahead keeps track of the total value of
 * the unexplored UTXOs. A subtree is not explored if the lookahead indicates that the target range
 * cannot be reached. Further, it is unnecessary to test equivalent combinations. This allows us
 * to skip testing the inclusion of UTXOs that match the effective value and waste of an omitted
 * predecessor.
 *
 * The Branch and Bound algorithm is described in detail in Murch's Master Thesis:
 * https://murch.one/wp-content/uploads/2016/11/erhardt2016coinselection.pdf
 *
 * @param const std::vector<CInputCoin>& utxo_pool The set of UTXOs that we are choosing from.
 *        These UTXOs will be sorted in descending order by effective value and the CInputCoins'
 *        values are their effective values.
 * @param const CAmount& selection_target This is the value that we want to select. It is the lower
 *        bound of the range.
 * @param const CAmount& cost_of_change This is the cost of creating and spending a change output.
 *        This plus selection_target is the upper bound of the range.
 * @param std::set<CInputCoin>& out_set -> This is an output parameter for the set of CInputCoins
 *        that have been selected.
 * @param CAmount& value_ret -> This is an output parameter for the total value of the CInputCoins
 *        that were selected.
 */

static const size_t TOTAL_TRIES = 100000;

bool SelectCoinsBnB(std::vector<OutputGroup>& utxo_pool, const CAmount& selection_target, const CAmount& cost_of_change, std::set<CInputCoin>& out_set, CAmount& value_ret)
{
    out_set.clear();
    CAmount curr_value = 0;

    std::vector<bool> curr_selection; // select the utxo at this index
    curr_selection.reserve(utxo_pool.size());

    // Calculate curr_available_value
    CAmount curr_available_value = 0;
    for (const OutputGroup& utxo : utxo_pool) {
        // Assert that this utxo is not negative. It should never be negative, effective value calculation should have removed it
        assert(utxo.GetSelectionAmount() > 0);
        curr_available_value += utxo.GetSelectionAmount();
    }
    if (curr_available_value < selection_target) {
        return false;
    }

    // Sort the utxo_pool
    std::sort(utxo_pool.begin(), utxo_pool.end(), descending);

    CAmount curr_waste = 0;
    std::vector<bool> best_selection;
    CAmount best_waste = MAX_MONEY;

    // Depth First search loop for choosing the UTXOs
    for (size_t i = 0; i < TOTAL_TRIES; ++i) {
        // Conditions for starting a backtrack
        bool backtrack = false;
        if (curr_value + curr_available_value < selection_target ||                // Cannot possibly reach target with the amount remaining in the curr_available_value.
            curr_value > selection_target + cost_of_change ||    // Selected value is out of range, go back and try other branch
            (curr_waste > best_waste && (utxo_pool.at(0).fee - utxo_pool.at(0).long_term_fee) > 0)) { // Don't select things which we know will be more wasteful if the waste is increasing
            backtrack = true;
        } else if (curr_value >= selection_target) {       // Selected value is within range
            curr_waste += (curr_value - selection_target); // This is the excess value which is added to the waste for the below comparison
            // Adding another UTXO after this check could bring the waste down if the long term fee is higher than the current fee.
            // However we are not going to explore that because this optimization for the waste is only done when we have hit our target
            // value. Adding any more UTXOs will be just burning the UTXO; it will go entirely to fees. Thus we aren't going to
            // explore any more UTXOs to avoid burning money like that.
            if (curr_waste <= best_waste) {
                best_selection = curr_selection;
                best_selection.resize(utxo_pool.size());
                best_waste = curr_waste;
                if (best_waste == 0) {
                    break;
                }
            }
            curr_waste -= (curr_value - selection_target); // Remove the excess value as we will be selecting different coins now
            backtrack = true;
        }

        // Backtracking, moving backwards
        if (backtrack) {
            // Walk backwards to find the last included UTXO that still needs to have its omission branch traversed.
            while (!curr_selection.empty() && !curr_selection.back()) {
                curr_selection.pop_back();
                curr_available_value += utxo_pool.at(curr_selection.size()).GetSelectionAmount();
            }

            if (curr_selection.empty()) { // We have walked back to the first utxo and no branch is untraversed. All solutions searched
                break;
            }

            // Output was included on previous iterations, try excluding now.
            curr_selection.back() = false;
            OutputGroup& utxo = utxo_pool.at(curr_selection.size() - 1);
            curr_value -= utxo.GetSelectionAmount();
            curr_waste -= utxo.fee - utxo.long_term_fee;
        } else { // Moving forwards, continuing down this branch
            OutputGroup& utxo = utxo_pool.at(curr_selection.size());

            // Remove this utxo from the curr_available_value utxo amount
            curr_available_value -= utxo.GetSelectionAmount();

            // Avoid searching a branch if the previous UTXO has the same value and same waste and was excluded. Since the ratio of fee to
            // long term fee is the same, we only need to check if one of those values match in order to know that the waste is the same.
            if (!curr_selection.empty() && !curr_selection.back() &&
                utxo.GetSelectionAmount() == utxo_pool.at(curr_selection.size() - 1).GetSelectionAmount() &&
                utxo.fee == utxo_pool.at(curr_selection.size() - 1).fee) {
                curr_selection.push_back(false);
            } else {
                // Inclusion branch first (Largest First Exploration)
                curr_selection.push_back(true);
                curr_value += utxo.GetSelectionAmount();
                curr_waste += utxo.fee - utxo.long_term_fee;
            }
        }
    }

    // Check for solution
    if (best_selection.empty()) {
        return false;
    }

    // Set output set
    value_ret = 0;
    for (size_t i = 0; i < best_selection.size(); ++i) {
        if (best_selection.at(i)) {
            util::insert(out_set, utxo_pool.at(i).m_outputs);
            value_ret += utxo_pool.at(i).m_value;
        }
    }

    return true;
}

static void ApproximateBestSubset(const std::vector<OutputGroup>& groups, const CAmount& nTotalLower, const CAmount& nTargetValue,
                                  std::vector<char>& vfBest, CAmount& nBest, int iterations = 1000)
{
    std::vector<char> vfIncluded;

    vfBest.assign(groups.size(), true);
    nBest = nTotalLower;

    FastRandomContext insecure_rand;

    for (int nRep = 0; nRep < iterations && nBest != nTargetValue; nRep++)
    {
        vfIncluded.assign(groups.size(), false);
        CAmount nTotal = 0;
        bool fReachedTarget = false;
        for (int nPass = 0; nPass < 2 && !fReachedTarget; nPass++)
        {
            for (unsigned int i = 0; i < groups.size(); i++)
            {
                //The solver here uses a randomized algorithm,
                //the randomness serves no real security purpose but is just
                //needed to prevent degenerate behavior and it is important
                //that the rng is fast. We do not use a constant random sequence,
                //because there may be some privacy improvement by making
                //the selection random.
                if (nPass == 0 ? insecure_rand.randbool() : !vfIncluded[i])
                {
                    nTotal += groups[i].m_value;
                    vfIncluded[i] = true;
                    if (nTotal >= nTargetValue)
                    {
                        fReachedTarget = true;
                        if (nTotal < nBest)
                        {
                            nBest = nTotal;
                            vfBest = vfIncluded;
                        }
                        nTotal -= groups[i].m_value;
                        vfIncluded[i] = false;
                    }
                }
            }
        }
    }
}

// ELEMENTS:
bool KnapsackSolver(const CAmountMap& mapTargetValue, std::vector<OutputGroup>& groups, std::set<CInputCoin>& setCoinsRet, CAmountMap& mapValueRet) {
    setCoinsRet.clear();
    mapValueRet.clear();

    std::vector<OutputGroup> inner_groups;
    std::set<CInputCoin> inner_coinsret;
    CAmount non_policy_effective_value = 0;
    bool subtract_fee_outputs = false;

    // Perform the standard Knapsack solver for every non-policy asset individually.
    for(std::map<CAsset, CAmount>::const_iterator it = mapTargetValue.begin(); it != mapTargetValue.end(); ++it) {
        inner_groups.clear();
        inner_coinsret.clear();

        if (it->second == 0) {
            continue;
        }
        if (it->first == ::policyAsset) {
            continue;
        }

        // We filter the groups on two conditions:
        // - only groups that have (exclusively) coins of the asset we're solving for
        // - no groups that are already used in setCoinsRet
        for (const OutputGroup& g : groups) {
            bool add = true;
            for (const CInputCoin& c : g.m_outputs) {
                if (setCoinsRet.find(c) != setCoinsRet.end()) {
                    add = false;
                    break;
                }

                if (c.asset != it->first) {
                    add = false;
                    break;
                }
            }

            if (add) {
                inner_groups.push_back(g);
            }

            // ELEMENTS: assigning this within this loop is a hack. What we really want
            //  is params.m_subtract_fee_outputs, but we don't have access to `params`
            //  from within this function..
            subtract_fee_outputs = g.m_subtract_fee_outputs;
        }

        if (inner_groups.size() == 0) {
            // No output groups for this asset.
            return false;
        }

        CAmount outValue;
        if (!KnapsackSolver(it->second, inner_groups, inner_coinsret, outValue)) {
            return false;
        }
        mapValueRet[it->first] = outValue;
        for (const CInputCoin& ic : inner_coinsret) {
            if (!subtract_fee_outputs) {
                non_policy_effective_value += ic.effective_value;
            }
            setCoinsRet.insert(ic);
        }
    }

    // Perform the standard Knapsack solver for the policy asset
    CAmount policy_target = non_policy_effective_value + mapTargetValue.at(::policyAsset);
    if (policy_target > 0) {
        inner_groups.clear();
        inner_coinsret.clear();

        // We filter the groups on two conditions:
        // - only groups that have (exclusively) coins of the asset we're solving for
        // - no groups that are already used in setCoinsRet
        for (const OutputGroup& g : groups) {
            bool add = true;
            for (const CInputCoin& c : g.m_outputs) {
                if (setCoinsRet.find(c) != setCoinsRet.end()) {
                    add = false;
                    break;
                }

                if (c.asset != ::policyAsset) {
                    add = false;
                    break;
                }
            }

            if (add) {
                inner_groups.push_back(g);
            }
        }

        if (inner_groups.size() == 0) {
            // No output groups for this asset.
            return false;
        }

        CAmount outValue;
        if (!KnapsackSolver(policy_target, inner_groups, inner_coinsret, outValue)) {
            return false;
        }
        mapValueRet[::policyAsset] = outValue;
        for (const CInputCoin& ic : inner_coinsret) {
            setCoinsRet.insert(ic);
        }
    }

    return true;
}

bool KnapsackSolver(const CAmount& nTargetValue, std::vector<OutputGroup>& groups, std::set<CInputCoin>& setCoinsRet, CAmount& nValueRet)
{
    setCoinsRet.clear();
    nValueRet = 0;

    // List of values less than target
    std::optional<OutputGroup> lowest_larger;
    std::vector<OutputGroup> applicable_groups;
    CAmount nTotalLower = 0;

    Shuffle(groups.begin(), groups.end(), FastRandomContext());

    for (const OutputGroup& group : groups) {
        if (group.GetSelectionAmount() == nTargetValue) {
            util::insert(setCoinsRet, group.m_outputs);
            nValueRet += group.m_value;
            return true;
        } else if (group.GetSelectionAmount() < nTargetValue + MIN_CHANGE) {
            applicable_groups.push_back(group);
            nTotalLower += group.GetSelectionAmount();
        } else if (!lowest_larger || group.GetSelectionAmount() < lowest_larger->GetSelectionAmount()) {
            lowest_larger = group;
        }
    }

    if (nTotalLower == nTargetValue) {
        for (const auto& group : applicable_groups) {
            util::insert(setCoinsRet, group.m_outputs);
            nValueRet += group.m_value;
        }
        return true;
    }

    if (nTotalLower < nTargetValue) {
        if (!lowest_larger) return false;
        util::insert(setCoinsRet, lowest_larger->m_outputs);
        nValueRet += lowest_larger->m_value;
        return true;
    }

    // Solve subset sum by stochastic approximation
    std::sort(applicable_groups.begin(), applicable_groups.end(), descending);
    std::vector<char> vfBest;
    CAmount nBest;

    ApproximateBestSubset(applicable_groups, nTotalLower, nTargetValue, vfBest, nBest);
    if (nBest != nTargetValue && nTotalLower >= nTargetValue + MIN_CHANGE) {
        ApproximateBestSubset(applicable_groups, nTotalLower, nTargetValue + MIN_CHANGE, vfBest, nBest);
    }

    // If we have a bigger coin and (either the stochastic approximation didn't find a good solution,
    //                                   or the next bigger coin is closer), return the bigger coin
    if (lowest_larger &&
        ((nBest != nTargetValue && nBest < nTargetValue + MIN_CHANGE) || lowest_larger->GetSelectionAmount() <= nBest)) {
        util::insert(setCoinsRet, lowest_larger->m_outputs);
        nValueRet += lowest_larger->m_value;
    } else {
        for (unsigned int i = 0; i < applicable_groups.size(); i++) {
            if (vfBest[i]) {
                util::insert(setCoinsRet, applicable_groups[i].m_outputs);
                nValueRet += applicable_groups[i].m_value;
            }
        }

        if (LogAcceptCategory(BCLog::SELECTCOINS)) {
            LogPrint(BCLog::SELECTCOINS, "SelectCoins() best subset: "); /* Continued */
            for (unsigned int i = 0; i < applicable_groups.size(); i++) {
                if (vfBest[i]) {
                    LogPrint(BCLog::SELECTCOINS, "%s ", FormatMoney(applicable_groups[i].m_value)); /* Continued */
                }
            }
            LogPrint(BCLog::SELECTCOINS, "total %s\n", FormatMoney(nBest));
        }
    }

    return true;
}

/******************************************************************************

 OutputGroup

 ******************************************************************************/

void OutputGroup::Insert(const CInputCoin& output, int depth, bool from_me, size_t ancestors, size_t descendants, bool positive_only) {
    // Compute the effective value first
    const CAmount coin_fee = output.m_input_bytes < 0 ? 0 : m_effective_feerate.GetFee(output.m_input_bytes);
    // ELEMENTS: "effective value" only comes from the policy asset
    const CAmount ev = output.value * (output.asset == ::policyAsset) - coin_fee;

    // Filter for positive only here before adding the coin
    if (positive_only && ev <= 0) return;

    m_outputs.push_back(output);
    CInputCoin& coin = m_outputs.back();

    coin.m_fee = coin_fee;
    fee += coin.m_fee;

    coin.m_long_term_fee = coin.m_input_bytes < 0 ? 0 : m_long_term_feerate.GetFee(coin.m_input_bytes);
    long_term_fee += coin.m_long_term_fee;

    coin.effective_value = ev;
    effective_value += coin.effective_value;

    m_from_me &= from_me;
    m_value += output.value;
    m_depth = std::min(m_depth, depth);
    // ancestors here express the number of ancestors the new coin will end up having, which is
    // the sum, rather than the max; this will overestimate in the cases where multiple inputs
    // have common ancestors
    m_ancestors += ancestors;
    // descendants is the count as seen from the top ancestor, not the descendants as seen from the
    // coin itself; thus, this value is counted as the max, not the sum
    m_descendants = std::max(m_descendants, descendants);
}

bool OutputGroup::EligibleForSpending(const CoinEligibilityFilter& eligibility_filter) const
{
    return m_depth >= (m_from_me ? eligibility_filter.conf_mine : eligibility_filter.conf_theirs)
        && m_ancestors <= eligibility_filter.max_ancestors
        && m_descendants <= eligibility_filter.max_descendants;
}

CAmount OutputGroup::GetSelectionAmount() const
{
    // ELEMENTS: non-policy assets always use `m_value`. Their (negative)
    //  `effective_value` will be added to the target for the policy asset
    if (!m_outputs.empty() && m_outputs[0].asset != ::policyAsset) {
        return m_value;
    }
    return m_subtract_fee_outputs ? m_value : effective_value;
}
