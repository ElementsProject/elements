// Copyright (c) 2021-2022 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <blind.h> // ELEMENTS: for MAX_RANGEPROOF_SIZE
#include <consensus/amount.h>
#include <consensus/validation.h>
#include <interfaces/chain.h>
#include <issuance.h> // ELEMENTS: for GenerateAssetEntropy and others
#include <algorithm>
#include <numeric>
#include <policy/policy.h>
#include <rpc/util.h>  // for GetDestinationBlindingKey and IsBlindDestination
#include <script/pegins.h>
#include <primitives/transaction.h>
#include <script/signingprovider.h>
#include <util/check.h>
#include <util/fees.h>
#include <util/moneystr.h>
#include <util/rbf.h>
#include <util/trace.h>
#include <util/translation.h>
#include <wallet/coincontrol.h>
#include <wallet/fees.h>
#include <wallet/receive.h>
#include <wallet/spend.h>
#include <wallet/transaction.h>
#include <wallet/wallet.h>

#include <cmath>

using interfaces::FoundBlock;

namespace wallet {
static constexpr size_t OUTPUT_GROUP_MAX_ENTRIES{100};

int CalculateMaximumSignedInputSize(const CTxOut& txout, const COutPoint outpoint, const SigningProvider* provider, bool can_grind_r, const CCoinControl* coin_control) {
    CMutableTransaction txn;
    txn.vin.push_back(CTxIn(outpoint));
    if (!provider || !DummySignInput(*provider, txn, 0, txout, can_grind_r, coin_control)) {
        return -1;
    }
    return GetVirtualTransactionInputSize(CTransaction(txn));
}

int CalculateMaximumSignedInputSize(const CTxOut& txout, const CWallet* wallet, const CCoinControl* coin_control)
{
    const std::unique_ptr<SigningProvider> provider = wallet->GetSolvingProvider(txout.scriptPubKey);
    return CalculateMaximumSignedInputSize(txout, COutPoint(), provider.get(), wallet->CanGrindR(), coin_control);
}

// Returns pair of vsize and weight
TxSize CalculateMaximumSignedTxSize(const CTransaction &tx, const CWallet *wallet, const CCoinControl* coin_control) EXCLUSIVE_LOCKS_REQUIRED(wallet->cs_wallet)
{
    std::vector<CTxOut> txouts;
    // Look up the inputs. The inputs are either in the wallet, or in coin_control.
    for (const CTxIn& input : tx.vin) {
        const auto mi = wallet->mapWallet.find(input.prevout.hash);
        if (mi != wallet->mapWallet.end()) {
            assert(input.prevout.n < mi->second.tx->vout.size());
            txouts.emplace_back(mi->second.tx->vout[input.prevout.n]);
        } else if (coin_control) {
            CTxOut txout;
            if (!coin_control->GetExternalOutput(input.prevout, txout)) {
                return TxSize{-1, -1};
            }
            txouts.emplace_back(txout);
        } else {
            return TxSize{-1, -1};
        }
    }
    return CalculateMaximumSignedTxSize(tx, wallet, txouts, coin_control);
}

// txouts needs to be in the order of tx.vin
TxSize CalculateMaximumSignedTxSize(const CTransaction &tx, const CWallet *wallet, const std::vector<CTxOut>& txouts, const CCoinControl* coin_control)
{
    CMutableTransaction txNew(tx);
    if (!wallet->DummySignTx(txNew, txouts, coin_control)) {
        return TxSize{-1, -1};
    }
    CTransaction ctx(txNew);
    int64_t vsize = GetVirtualTransactionSize(ctx);
    int64_t weight = GetTransactionWeight(ctx);
    // ELEMENTS: use discounted vsize for CTs if enabled
    if (Params().GetCreateDiscountCT()) {
        vsize = GetDiscountVirtualTransactionSize(ctx);
    }

    return TxSize{vsize, weight};
}

size_t CoinsResult::Size() const
{
    size_t size{0};
    for (const auto& it : coins) {
        size += it.second.size();
    }
    return size;
}

std::vector<COutput> CoinsResult::All() const
{
    std::vector<COutput> all;
    all.reserve(coins.size());
    for (const auto& it : coins) {
        all.insert(all.end(), it.second.begin(), it.second.end());
    }
    return all;
}

void CoinsResult::Clear() {
    coins.clear();
}

void CoinsResult::Erase(const std::unordered_set<COutPoint, SaltedOutpointHasher>& coins_to_remove)
{
    for (auto& [type, vec] : coins) {
        auto remove_it = std::remove_if(vec.begin(), vec.end(), [&](const COutput& coin) {
            // remove it if it's on the set
            if (coins_to_remove.count(coin.outpoint) == 0) return false;

            // update cached amounts
            total_amount[coin.asset] -= coin.value;
            if (coin.HasEffectiveValue()) total_effective_amount[coin.asset] -= coin.GetEffectiveValue();
            return true;
        });
        vec.erase(remove_it, vec.end());
    }
}

void CoinsResult::Shuffle(FastRandomContext& rng_fast)
{
    for (auto& it : coins) {
        ::Shuffle(it.second.begin(), it.second.end(), rng_fast);
    }
}

void CoinsResult::Add(OutputType type, const COutput& out)
{
    coins[type].emplace_back(out);
    total_amount[out.asset] += out.value;
    if (out.HasEffectiveValue()) {
    	   total_effective_amount[out.asset] += out.GetEffectiveValue();
    }
}

static OutputType GetOutputType(TxoutType type, bool is_from_p2sh)
{
    switch (type) {
        case TxoutType::WITNESS_V1_TAPROOT:
            return OutputType::BECH32M;
        case TxoutType::WITNESS_V0_KEYHASH:
        case TxoutType::WITNESS_V0_SCRIPTHASH:
            if (is_from_p2sh) return OutputType::P2SH_SEGWIT;
            else return OutputType::BECH32;
        case TxoutType::SCRIPTHASH:
        case TxoutType::PUBKEYHASH:
            return OutputType::LEGACY;
        default:
            return OutputType::UNKNOWN;
    }
}

// Fetch and validate the coin control selected inputs.
// Coins could be internal (from the wallet) or external.
util::Result<PreSelectedInputs> FetchSelectedInputs(const CWallet& wallet, const CCoinControl& coin_control,
                                            const CoinSelectionParams& coin_selection_params) EXCLUSIVE_LOCKS_REQUIRED(wallet.cs_wallet)
{
    PreSelectedInputs result;
    std::vector<COutPoint> vPresetInputs;
    coin_control.ListSelected(vPresetInputs);
    const bool can_grind_r = wallet.CanGrindR();
    for (const COutPoint& outpoint : vPresetInputs) {
        int input_bytes = -1;
        CTxOut txout;
        if (auto ptr_wtx = wallet.GetWalletTx(outpoint.hash)) {
            // Clearly invalid input, fail
            if (ptr_wtx->tx->vout.size() <= outpoint.n) {
                return util::Error{strprintf(_("Invalid pre-selected input %s"), outpoint.ToString())};
            }
            txout = ptr_wtx->tx->vout.at(outpoint.n);
            input_bytes = CalculateMaximumSignedInputSize(txout, &wallet, &coin_control);
        } else {
            // The input is external. We did not find the tx in mapWallet.
            if (!coin_control.GetExternalOutput(outpoint, txout)) {
                return util::Error{strprintf(_("Not found pre-selected input %s"), outpoint.ToString())};
            }
        }

        if (input_bytes == -1) {
            input_bytes = CalculateMaximumSignedInputSize(txout, outpoint, &coin_control.m_external_provider, can_grind_r, &coin_control);
            // ELEMENTS: one more try to get a signed input size: for pegins,
            //  the outpoint is provided as external data but the information
            //  needed to spend is in the wallet (not the external provider,
            //  as the user is expecting the wallet to remember this information
            //  after they called getpeginaddress). So try estimating size with
            //  the wallet rather than the external provider.
            if (input_bytes == -1) {
                input_bytes = CalculateMaximumSignedInputSize(txout, &wallet, &coin_control);
            }
            if (!txout.nValue.IsExplicit() || !txout.nAsset.IsExplicit()) {
                return util::Error{strprintf(_("Value or asset is not explicit for pre-selected input %s"), outpoint.ToString())};
            }
        }

        // If available, override calculated size with coin control specified size
        if (coin_control.HasInputWeight(outpoint)) {
            input_bytes = GetVirtualTransactionSize(coin_control.GetInputWeight(outpoint), 0, 0);
        }

        if (input_bytes == -1) {
            return util::Error{strprintf(_("Not solvable pre-selected input %s"), outpoint.ToString())}; // Not solvable, can't estimate size for fee
        }

        /* Set some defaults for depth, spendable, solvable, safe, time, and from_me as these don't matter for preset inputs since no selection is being done. */
        COutput output(outpoint, txout, /*depth=*/ 0, input_bytes, /*spendable=*/ true, /*solvable=*/ true, /*safe=*/ true, /*time=*/ 0, /*from_me=*/ false, coin_selection_params.m_effective_feerate);
        // ELEMENTS: use the extended COutput constructor if possible
        if (auto wtx = wallet.GetWalletTx(outpoint.hash)) {
            output = COutput(wallet, *wtx, outpoint, txout, /*depth=*/0, input_bytes, /*spendable=*/true, /*solvable=*/true, /*safe=*/true, /*time=*/0, /*from_me=*/false, coin_selection_params.m_effective_feerate);
        }
        result.Insert(output, coin_selection_params.m_subtract_fee_outputs);
    }
    return result;
}

CoinsResult AvailableCoins(const CWallet& wallet,
                           const CCoinControl *coinControl,
                           std::optional<CFeeRate> feerate,
                           const CoinFilterParams& params)
{
    AssertLockHeld(wallet.cs_wallet);

    CoinsResult result;
    // Either the WALLET_FLAG_AVOID_REUSE flag is not set (in which case we always allow), or we default to avoiding, and only in the case where
    // a coin control object is provided, and has the avoid address reuse flag set to false, do we allow already used addresses
    bool allow_used_addresses = !wallet.IsWalletFlagSet(WALLET_FLAG_AVOID_REUSE) || (coinControl && !coinControl->m_avoid_address_reuse);
    const int min_depth = {coinControl ? coinControl->m_min_depth : DEFAULT_MIN_DEPTH};
    const int max_depth = {coinControl ? coinControl->m_max_depth : DEFAULT_MAX_DEPTH};
    const bool only_safe = {coinControl ? !coinControl->m_include_unsafe_inputs : true};
    const bool can_grind_r = wallet.CanGrindR();

    std::set<uint256> trusted_parents;
    for (const auto& entry : wallet.mapWallet)
    {
        const uint256& wtxid = entry.first;
        const CWalletTx& wtx = entry.second;

        if (wallet.IsTxImmatureCoinBase(wtx) && !params.include_immature_coinbase)
            continue;

        int nDepth = wallet.GetTxDepthInMainChain(wtx);
        if (nDepth < 0)
            continue;

        // We should not consider coins which aren't at least in our mempool
        // It's possible for these to be conflicted via ancestors which we may never be able to detect
        if (nDepth == 0 && !wtx.InMempool())
            continue;

        bool safeTx = CachedTxIsTrusted(wallet, wtx, trusted_parents);

        // We should not consider coins from transactions that are replacing
        // other transactions.
        //
        // Example: There is a transaction A which is replaced by bumpfee
        // transaction B. In this case, we want to prevent creation of
        // a transaction B' which spends an output of B.
        //
        // Reason: If transaction A were initially confirmed, transactions B
        // and B' would no longer be valid, so the user would have to create
        // a new transaction C to replace B'. However, in the case of a
        // one-block reorg, transactions B' and C might BOTH be accepted,
        // when the user only wanted one of them. Specifically, there could
        // be a 1-block reorg away from the chain where transactions A and C
        // were accepted to another chain where B, B', and C were all
        // accepted.
        if (nDepth == 0 && wtx.mapValue.count("replaces_txid")) {
            safeTx = false;
        }

        // Similarly, we should not consider coins from transactions that
        // have been replaced. In the example above, we would want to prevent
        // creation of a transaction A' spending an output of A, because if
        // transaction B were initially confirmed, conflicting with A and
        // A', we wouldn't want to the user to create a transaction D
        // intending to replace A', but potentially resulting in a scenario
        // where A, A', and D could all be accepted (instead of just B and
        // D, or just A and A' like the user would want).
        if (nDepth == 0 && wtx.mapValue.count("replaced_by_txid")) {
            safeTx = false;
        }

        if (only_safe && !safeTx) {
            continue;
        }

        if (nDepth < min_depth || nDepth > max_depth) {
            continue;
        }

        bool tx_from_me = CachedTxIsFromMe(wallet, wtx, ISMINE_ALL);

        for (unsigned int i = 0; i < wtx.tx->vout.size(); i++) {
            const CTxOut& output = wtx.tx->vout[i];
            const COutPoint outpoint(wtxid, i);

            CAmount outValue = wtx.GetOutputValueOut(wallet, i);
            CAsset asset = wtx.GetOutputAsset(wallet, i);
            if (params.asset && asset != *params.asset) {
                continue;
            }
            if (outValue < params.min_amount || (asset == Params().GetConsensus().pegged_asset && outValue > params.max_amount)) {
                continue;
            }

            // Skip manually selected coins (the caller can fetch them directly)
            if (coinControl && coinControl->HasSelected() && coinControl->IsSelected(outpoint))
                continue;

            if (wallet.IsLockedCoin(outpoint) && params.skip_locked)
                continue;

            if (wallet.IsSpent(outpoint))
                continue;

            isminetype mine = wallet.IsMine(output);

            if (mine == ISMINE_NO) {
                continue;
            }

            if (!allow_used_addresses && wallet.IsSpentKey(output.scriptPubKey)) {
                continue;
            }

            std::unique_ptr<SigningProvider> provider = wallet.GetSolvingProvider(output.scriptPubKey);

            int input_bytes = CalculateMaximumSignedInputSize(output, COutPoint(), provider.get(), can_grind_r, coinControl);
            bool solvable = provider ? InferDescriptor(output.scriptPubKey, *provider)->IsSolvable() : false;
            bool spendable = ((mine & ISMINE_SPENDABLE) != ISMINE_NO) || (((mine & ISMINE_WATCH_ONLY) != ISMINE_NO) && (coinControl && coinControl->fAllowWatchOnly && solvable));

            // Filter by spendable outputs only
            if (!spendable && params.only_spendable) continue;

            // Obtain script type
            std::vector<std::vector<uint8_t>> script_solutions;
            TxoutType type = Solver(output.scriptPubKey, script_solutions);

            // If the output is P2SH and solvable, we want to know if it is
            // a P2SH (legacy) or one of P2SH-P2WPKH, P2SH-P2WSH (P2SH-Segwit). We can determine
            // this from the redeemScript. If the output is not solvable, it will be classified
            // as a P2SH (legacy), since we have no way of knowing otherwise without the redeemScript
            bool is_from_p2sh{false};
            if (type == TxoutType::SCRIPTHASH && solvable) {
                CScript script;
                if (!provider->GetCScript(CScriptID(uint160(script_solutions[0])), script)) continue;
                type = Solver(script, script_solutions);
                is_from_p2sh = true;
            }

            result.Add(GetOutputType(type, is_from_p2sh),
                       COutput(wallet, wtx, outpoint, output, nDepth, input_bytes, spendable, solvable, safeTx, wtx.GetTxTime(), tx_from_me, feerate));

            // Checks the sum amount of all UTXO's.
            if (params.min_sum_amount != MAX_MONEY) {
                if (result.GetTotalAmount()[::policyAsset] >= params.min_sum_amount) { // ELEMENTS: only use mininum sum for policy asset
                    return result;
                }
            }

            // Checks the maximum number of UTXO's.
            if (params.max_count > 0 && result.Size() >= params.max_count) {
                return result;
            }
        }
    }

    return result;
}

CoinsResult AvailableCoinsListUnspent(const CWallet& wallet, const CCoinControl* coinControl, CoinFilterParams params)
{
    params.only_spendable = false;
    return AvailableCoins(wallet, coinControl, /*feerate=*/ std::nullopt, params);
}

CAmountMap GetAvailableBalance(const CWallet& wallet, const CCoinControl* coinControl)
{
    LOCK(wallet.cs_wallet);
    return AvailableCoins(wallet, coinControl).GetTotalAmount();
}

const CTxOut& FindNonChangeParentOutput(const CWallet& wallet, const COutPoint& outpoint)
{
    AssertLockHeld(wallet.cs_wallet);
    const CWalletTx* wtx{Assert(wallet.GetWalletTx(outpoint.hash))};

    const CTransaction* ptx = wtx->tx.get();
    int n = outpoint.n;
    while (OutputIsChange(wallet, ptx->vout[n]) && ptx->vin.size() > 0) {
        const COutPoint& prevout = ptx->vin[0].prevout;
        const CWalletTx* it = wallet.GetWalletTx(prevout.hash);
        if (!it || it->tx->vout.size() <= prevout.n ||
            !wallet.IsMine(it->tx->vout[prevout.n])) {
            break;
        }
        ptx = it->tx.get();
        n = prevout.n;
    }
    return ptx->vout[n];
}

std::map<CTxDestination, std::vector<COutput>> ListCoins(const CWallet& wallet) EXCLUSIVE_LOCKS_REQUIRED(wallet.cs_wallet)
{
    AssertLockHeld(wallet.cs_wallet);

    std::map<CTxDestination, std::vector<COutput>> result;

    CCoinControl coin_control;
    // Include watch-only for LegacyScriptPubKeyMan wallets without private keys
    coin_control.fAllowWatchOnly = wallet.GetLegacyScriptPubKeyMan() && wallet.IsWalletFlagSet(WALLET_FLAG_DISABLE_PRIVATE_KEYS);
    CoinFilterParams coins_params;
    coins_params.only_spendable = false;
    coins_params.skip_locked = false;
    for (const COutput& coin : AvailableCoins(wallet, &coin_control, /*feerate=*/std::nullopt, coins_params).All()) {
        CTxDestination address;

        // Retrieve the transaction from the wallet
        const CWalletTx* wtx = wallet.GetWalletTx(coin.outpoint.hash);
        if (wtx == nullptr) {
            // Skip this coin if the transaction is not found in the wallet
            continue;
        }

        if ((coin.spendable || (wallet.IsWalletFlagSet(WALLET_FLAG_DISABLE_PRIVATE_KEYS) && coin.solvable)) &&
            ExtractDestination(FindNonChangeParentOutput(wallet, coin.outpoint).scriptPubKey, address)) {
            result[address].emplace_back(coin);
        }
    }
    return result;
}

FilteredOutputGroups GroupOutputs(const CWallet& wallet,
                          const CoinsResult& coins,
                          const CoinSelectionParams& coin_sel_params,
                          const std::vector<SelectionFilter>& filters)
{
    FilteredOutputGroups filtered_groups;

    if (!coin_sel_params.m_avoid_partial_spends) {
        // Allowing partial spends means no grouping. Each COutput gets its own OutputGroup
        for (const auto& [type, outputs] : coins.coins) {
            for (const COutput& output : outputs) {
                // Get mempool info
                size_t ancestors, descendants;
                wallet.chain().getTransactionAncestry(output.outpoint.hash, ancestors, descendants);

                // Create a new group per output and add it to the all groups vector
                OutputGroup group(coin_sel_params);
                group.Insert(std::make_shared<COutput>(output), ancestors, descendants);

                // Each filter maps to a different set of groups
                for (const auto& sel_filter : filters) {
                    const auto& filter = sel_filter.filter;
                    if (!group.EligibleForSpending(filter)) continue;
                    filtered_groups[filter].Push(group, type, /*insert_positive=*/true, /*insert_mixed=*/true);
                }
            }
        }
        return filtered_groups;
    }

    // We want to combine COutputs that have the same scriptPubKey into single OutputGroups
    // except when there are more than OUTPUT_GROUP_MAX_ENTRIES COutputs grouped in an OutputGroup.
    // To do this, we maintain a map where the key is the scriptPubKey and the value is a vector of OutputGroups.
    // For each COutput, we check if the scriptPubKey is in the map, and if it is, the COutput is added
    // to the last OutputGroup in the vector for the scriptPubKey. When the last OutputGroup has
    // OUTPUT_GROUP_MAX_ENTRIES COutputs, a new OutputGroup is added to the end of the vector.
    typedef std::map<std::pair<CScript, OutputType>, std::vector<OutputGroup>> ScriptPubKeyToOutgroup;
    const auto& insert_output = [&](
            const std::shared_ptr<COutput>& output, OutputType type, size_t ancestors, size_t descendants,
            ScriptPubKeyToOutgroup& groups_map) {
        std::vector<OutputGroup>& groups = groups_map[std::make_pair(output->txout.scriptPubKey,type)];

        if (groups.size() == 0) {
            // No OutputGroups for this scriptPubKey yet, add one
            groups.emplace_back(coin_sel_params);
        }

        // Get the last OutputGroup in the vector so that we can add the COutput to it
        // A pointer is used here so that group can be reassigned later if it is full.
        OutputGroup* group = &groups.back();

        // Check if this OutputGroup is full. We limit to OUTPUT_GROUP_MAX_ENTRIES when using -avoidpartialspends
        // to avoid surprising users with very high fees.
        if (group->m_outputs.size() >= OUTPUT_GROUP_MAX_ENTRIES) {
            // The last output group is full, add a new group to the vector and use that group for the insertion
            groups.emplace_back(coin_sel_params);
            group = &groups.back();
        }

        group->Insert(output, ancestors, descendants);
    };

    ScriptPubKeyToOutgroup spk_to_groups_map;
    ScriptPubKeyToOutgroup spk_to_positive_groups_map;
    for (const auto& [type, outs] : coins.coins) {
        for (const COutput& output : outs) {
            size_t ancestors, descendants;
            wallet.chain().getTransactionAncestry(output.outpoint.hash, ancestors, descendants);

            const auto& shared_output = std::make_shared<COutput>(output);
            // Filter for positive only before adding the output
            if (output.GetEffectiveValue() > 0) {
                insert_output(shared_output, type, ancestors, descendants, spk_to_positive_groups_map);
            }

            // 'All' groups
            insert_output(shared_output, type, ancestors, descendants, spk_to_groups_map);
        }
    }

    // Now we go through the entire maps and pull out the OutputGroups
    const auto& push_output_groups = [&](const ScriptPubKeyToOutgroup& groups_map, bool positive_only) {
        for (const auto& [script, groups] : groups_map) {
            // Go through the vector backwards. This allows for the first item we deal with being the partial group.
            for (auto group_it = groups.rbegin(); group_it != groups.rend(); group_it++) {
                const OutputGroup& group = *group_it;

                // Each filter maps to a different set of groups
                for (const auto& sel_filter : filters) {
                    const auto& filter = sel_filter.filter;
                    if (!group.EligibleForSpending(filter)) continue;

                    // Don't include partial groups if there are full groups too and we don't want partial groups
                    if (group_it == groups.rbegin() && groups.size() > 1 && !filter.m_include_partial_groups) {
                        continue;
                    }

                    OutputType type = script.second;
                    // Either insert the group into the positive-only groups or the mixed ones.
                    filtered_groups[filter].Push(group, type, positive_only, /*insert_mixed=*/!positive_only);
                }
            }
        }
    };

    push_output_groups(spk_to_groups_map, /*positive_only=*/ false);
    push_output_groups(spk_to_positive_groups_map, /*positive_only=*/ true);

    return filtered_groups;
}

// Returns true if the result contains an error and the message is not empty
static bool HasErrorMsg(const util::Result<SelectionResult>& res) { return !util::ErrorString(res).empty(); }

util::Result<SelectionResult> AttemptSelection(const CAmountMap& mapTargetValue, OutputGroupTypeMap& groups,
                               const CoinSelectionParams& coin_selection_params, bool allow_mixed_output_types)
{
    // Run coin selection on each OutputType and compute the Waste Metric
    std::vector<SelectionResult> results;
    for (auto& [type, group] : groups.groups_by_type) {
        auto result{ChooseSelectionResult(mapTargetValue, group, coin_selection_params)};
        // If any specific error message appears here, then something particularly wrong happened.
        if (HasErrorMsg(result)) return result; // So let's return the specific error.
        // Append the favorable result.
        if (result) results.push_back(*result);
    }

    // If we have at least one solution for funding the transaction without mixing, choose the minimum one according to waste metric
    // and return the result
    if (results.size() > 0) return *std::min_element(results.begin(), results.end());

    // If we can't fund the transaction from any individual OutputType, run coin selection one last time
    // over all available coins, which would allow mixing
    // If TypesCount() <= 1, there is nothing to mix.
    if (allow_mixed_output_types && groups.TypesCount() > 1) {
        return ChooseSelectionResult(mapTargetValue, groups.all_groups, coin_selection_params);
    }
    // Either mixing is not allowed and we couldn't find a solution from any single OutputType, or mixing was allowed and we still couldn't
    // find a solution using all available coins
    return util::Error();
};

util::Result<SelectionResult> ChooseSelectionResult(const CAmountMap& mapTargetValue, Groups& groups, const CoinSelectionParams& coin_selection_params)
{
    // Vector of results. We will choose the best one based on waste.
    // std::vector<std::tuple<CAmount, std::set<CInputCoin>, CAmountMap>> results;
    std::vector<SelectionResult> results;

    // ELEMENTS: BnB only for policy asset?
    if (mapTargetValue.size() == 1) {
        // Note that unlike KnapsackSolver, we do not include the fee for creating a change output as BnB will not create a change output.

        // ELEMENTS:
        CAsset asset = mapTargetValue.begin()->first;
        CAmount nTargetValue = mapTargetValue.begin()->second;
        CAmount target_with_change = nTargetValue;
        // While nTargetValue includes the transaction fees for non-input things, it does not include the fee for creating a change output.
        // So we need to include that for KnapsackSolver and SRD as well, as we are expecting to create a change output.
        if (!coin_selection_params.m_subtract_fee_outputs) {
            target_with_change += coin_selection_params.m_change_fee;
        }
        // Get output groups that only contain this asset.
        std::vector<OutputGroup> asset_groups;
        for (const OutputGroup& g : groups.positive_group) {
            bool add = true;
            for (const std::shared_ptr<wallet::COutput>& c : g.m_outputs) {
                if (c->asset != asset) {
                    add = false;
                    break;
                }
            }

            if (add) {
                asset_groups.push_back(g);
            }
        }
        // END ELEMENTS

        if (auto bnb_result{SelectCoinsBnB(groups.positive_group, nTargetValue, coin_selection_params.m_cost_of_change)}) {
            results.push_back(*bnb_result);
        }

        // Include change for SRD as we want to avoid making really small change if the selection just
        // barely meets the target. Just use the lower bound change target instead of the randomly
        // generated one, since SRD will result in a random change amount anyway; avoid making the
        // target needlessly large.
        const CAmount srd_target = target_with_change + CHANGE_LOWER;
        if (auto srd_result{SelectCoinsSRD(groups.positive_group, srd_target, coin_selection_params.rng_fast)}) {
            srd_result->ComputeAndSetWaste(coin_selection_params.min_viable_change, coin_selection_params.m_cost_of_change, coin_selection_params.m_change_fee);
            results.push_back(*srd_result);
        }
    }

    // The knapsack solver has some legacy behavior where it will spend dust outputs. We retain this behavior, so don't filter for positive only here.
    // While mapTargetValue includes the transaction fees for non-input things, it does not include the fee for creating a change output.
    // So we need to include that for KnapsackSolver as well, as we are expecting to create a change output.
    CAmountMap mapTargetValue_copy = mapTargetValue;
    if (!coin_selection_params.m_subtract_fee_outputs) {
        mapTargetValue_copy[::policyAsset] += coin_selection_params.m_change_fee;
    }

    CAmountMap map_target_with_change = mapTargetValue;
    // While nTargetValue includes the transaction fees for non-input things, it does not include the fee for creating a change output.
    // So we need to include that for KnapsackSolver and SRD as well, as we are expecting to create a change output.
    if (!coin_selection_params.m_subtract_fee_outputs) {
        map_target_with_change[::policyAsset] += coin_selection_params.m_change_fee;
    }
    if (auto knapsack_result{KnapsackSolver(groups.mixed_group, mapTargetValue, coin_selection_params.m_min_change_target, coin_selection_params.rng_fast)}) {
        knapsack_result->ComputeAndSetWaste(coin_selection_params.min_viable_change, coin_selection_params.m_cost_of_change, coin_selection_params.m_change_fee);
        results.push_back(*knapsack_result);
    }

    if (results.empty()) {
        // No solution found
        return util::Error();
    }

    std::vector<SelectionResult> eligible_results;
    std::copy_if(results.begin(), results.end(), std::back_inserter(eligible_results), [coin_selection_params](const SelectionResult& result) {
        const auto initWeight{coin_selection_params.tx_noinputs_size * WITNESS_SCALE_FACTOR};
        return initWeight + result.GetWeight() <= static_cast<int>(MAX_STANDARD_TX_WEIGHT);
    });

    if (eligible_results.empty()) {
        return util::Error{_("The inputs size exceeds the maximum weight. "
                             "Please try sending a smaller amount or manually consolidating your wallet's UTXOs")};
    }

    // Choose the result with the least waste
    // If the waste is the same, choose the one which spends more inputs.
    auto& best_result = *std::min_element(eligible_results.begin(), eligible_results.end());
    return best_result;
}

util::Result<SelectionResult> SelectCoins(const CWallet& wallet, CoinsResult& available_coins, const PreSelectedInputs& pre_set_inputs,
                                          const CAmountMap& mapTargetValue, const CCoinControl& coin_control,
                                          const CoinSelectionParams& coin_selection_params)
{
    AssertLockHeld(wallet.cs_wallet);
    // Deduct preset inputs amount from the search target
    CAmountMap selection_target = mapTargetValue - pre_set_inputs.total_amount;

    // Return if automatic coin selection is disabled, and we don't cover the selection target
    if (!coin_control.m_allow_other_inputs && selection_target > CAmountMap{}) {
        return util::Error{_("The preselected coins total amount does not cover the transaction target. "
                             "Please allow other inputs to be automatically selected or include more coins manually")};
    }

    // Return if we can cover the target only with the preset inputs
    if (selection_target <= CAmountMap{}) {
        SelectionResult result(mapTargetValue, SelectionAlgorithm::MANUAL);
        result.AddInputs(pre_set_inputs.coins, coin_selection_params.m_subtract_fee_outputs);
        result.ComputeAndSetWaste(coin_selection_params.min_viable_change, coin_selection_params.m_cost_of_change, coin_selection_params.m_change_fee);
        return result;
    }

    CAmountMap available_coins_total_amount = coin_selection_params.m_subtract_fee_outputs ? available_coins.GetTotalAmount() : available_coins.GetEffectiveTotalAmount();
    if (selection_target > available_coins_total_amount) {
        return util::Error(); // Insufficient funds
    }

    // Start wallet Coin Selection procedure
    auto op_selection_result = AutomaticCoinSelection(wallet, available_coins, selection_target, coin_selection_params);
    if (!op_selection_result) return op_selection_result;

    // If needed, add preset inputs to the automatic coin selection result
    if (!pre_set_inputs.coins.empty()) {
        SelectionResult preselected(pre_set_inputs.total_amount, SelectionAlgorithm::MANUAL);
        preselected.AddInputs(pre_set_inputs.coins, coin_selection_params.m_subtract_fee_outputs);
        op_selection_result->Merge(preselected);
        op_selection_result->ComputeAndSetWaste(coin_selection_params.min_viable_change,
                                                coin_selection_params.m_cost_of_change,
                                                coin_selection_params.m_change_fee);
    }
    return op_selection_result;
}

util::Result<SelectionResult> AutomaticCoinSelection(const CWallet& wallet, CoinsResult& available_coins, const CAmountMap& value_to_select, const CoinSelectionParams& coin_selection_params)
{
    unsigned int limit_ancestor_count = 0;
    unsigned int limit_descendant_count = 0;
    wallet.chain().getPackageLimits(limit_ancestor_count, limit_descendant_count);
    const size_t max_ancestors = (size_t)std::max<int64_t>(1, limit_ancestor_count);
    const size_t max_descendants = (size_t)std::max<int64_t>(1, limit_descendant_count);
    const bool fRejectLongChains = gArgs.GetBoolArg("-walletrejectlongchains", DEFAULT_WALLET_REJECT_LONG_CHAINS);

    // ELEMENTS: filter coins for assets we are interested in; always keep policyAsset for fees
    std::unordered_set<COutPoint, SaltedOutpointHasher> outpoints;
    for (const auto& output : available_coins.All()) {
        if (output.asset != ::policyAsset  && value_to_select.find(output.asset) == value_to_select.end()) {
            outpoints.emplace(output.outpoint);
        }
    }
    available_coins.Erase(outpoints);

    // form groups from remaining coins; note that preset coins will not
    // automatically have their associated (same address) coins included
    if (coin_selection_params.m_avoid_partial_spends && available_coins.Size() > OUTPUT_GROUP_MAX_ENTRIES) {
        // Cases where we have 101+ outputs all pointing to the same destination may result in
        // privacy leaks as they will potentially be deterministically sorted. We solve that by
        // explicitly shuffling the outputs before processing
        available_coins.Shuffle(coin_selection_params.rng_fast);
    }

    // Coin Selection attempts to select inputs from a pool of eligible UTXOs to fund the
    // transaction at a target feerate. If an attempt fails, more attempts may be made using a more
    // permissive CoinEligibilityFilter.
    util::Result<SelectionResult> res = [&] {
        // Place coins eligibility filters on a scope increasing order.
        std::vector<SelectionFilter> ordered_filters{
                // If possible, fund the transaction with confirmed UTXOs only. Prefer at least six
                // confirmations on outputs received from other wallets and only spend confirmed change.
                {CoinEligibilityFilter(1, 6, 0), /*allow_mixed_output_types=*/false},
                {CoinEligibilityFilter(1, 1, 0)},
        };
        // Fall back to using zero confirmation change (but with as few ancestors in the mempool as
        // possible) if we cannot fund the transaction otherwise.
        if (wallet.m_spend_zero_conf_change) {
            ordered_filters.push_back({CoinEligibilityFilter(0, 1, 2)});
            ordered_filters.push_back({CoinEligibilityFilter(0, 1, std::min(size_t{4}, max_ancestors/3), std::min(size_t{4}, max_descendants/3))});
            ordered_filters.push_back({CoinEligibilityFilter(0, 1, max_ancestors/2, max_descendants/2)});
            // If partial groups are allowed, relax the requirement of spending OutputGroups (groups
            // of UTXOs sent to the same address, which are obviously controlled by a single wallet)
            // in their entirety.
            ordered_filters.push_back({CoinEligibilityFilter(0, 1, max_ancestors-1, max_descendants-1, /*include_partial=*/true)});
            // Try with unsafe inputs if they are allowed. This may spend unconfirmed outputs
            // received from other wallets.
            if (coin_selection_params.m_include_unsafe_inputs) {
                ordered_filters.push_back({CoinEligibilityFilter(/*conf_mine=*/0, /*conf_theirs*/0, max_ancestors-1, max_descendants-1, /*include_partial=*/true)});
            }
            // Try with unlimited ancestors/descendants. The transaction will still need to meet
            // mempool ancestor/descendant policy to be accepted to mempool and broadcasted, but
            // OutputGroups use heuristics that may overestimate ancestor/descendant counts.
            if (!fRejectLongChains) {
                ordered_filters.push_back({CoinEligibilityFilter(0, 1, std::numeric_limits<uint64_t>::max(),
                                                                   std::numeric_limits<uint64_t>::max(),
                                                                   /*include_partial=*/true)});
            }
        }

        // Group outputs and map them by coin eligibility filter
        FilteredOutputGroups filtered_groups = GroupOutputs(wallet, available_coins, coin_selection_params, ordered_filters);

        // Walk-through the filters until the solution gets found.
        // If no solution is found, return the first detailed error (if any).
        // future: add "error level" so the worst one can be picked instead.
        std::vector<util::Result<SelectionResult>> res_detailed_errors;
        for (const auto& select_filter : ordered_filters) {
            auto it = filtered_groups.find(select_filter.filter);
            if (it == filtered_groups.end()) continue;
            if (auto res{AttemptSelection(value_to_select, it->second,
                                          coin_selection_params, select_filter.allow_mixed_output_types)}) {
                return res; // result found
            } else {
                // If any specific error message appears here, then something particularly wrong might have happened.
                // Save the error and continue the selection process. So if no solutions gets found, we can return
                // the detailed error to the upper layers.
                if (HasErrorMsg(res)) res_detailed_errors.emplace_back(res);
            }
        }
        // Coin Selection failed.
        return res_detailed_errors.empty() ? util::Result<SelectionResult>(util::Error()) : res_detailed_errors.front();
    }();

    return res;
}

static bool IsCurrentForAntiFeeSniping(interfaces::Chain& chain, const uint256& block_hash)
{
    if (chain.isInitialBlockDownload()) {
        return false;
    }
    constexpr int64_t MAX_ANTI_FEE_SNIPING_TIP_AGE = 8 * 60 * 60; // in seconds
    int64_t block_time;
    CHECK_NONFATAL(chain.findBlock(block_hash, FoundBlock().time(block_time)));
    if (block_time < (GetTime() - MAX_ANTI_FEE_SNIPING_TIP_AGE)) {
        return false;
    }
    return true;
}

/**
 * Set a height-based locktime for new transactions (uses the height of the
 * current chain tip unless we are not synced with the current chain
 */
static void DiscourageFeeSniping(CMutableTransaction& tx, FastRandomContext& rng_fast,
                                 interfaces::Chain& chain, const uint256& block_hash, int block_height)
{
    // All inputs must be added by now
    assert(!tx.vin.empty());
    // Discourage fee sniping.
    //
    // For a large miner the value of the transactions in the best block and
    // the mempool can exceed the cost of deliberately attempting to mine two
    // blocks to orphan the current best block. By setting nLockTime such that
    // only the next block can include the transaction, we discourage this
    // practice as the height restricted and limited blocksize gives miners
    // considering fee sniping fewer options for pulling off this attack.
    //
    // A simple way to think about this is from the wallet's point of view we
    // always want the blockchain to move forward. By setting nLockTime this
    // way we're basically making the statement that we only want this
    // transaction to appear in the next block; we don't want to potentially
    // encourage reorgs by allowing transactions to appear at lower heights
    // than the next block in forks of the best chain.
    //
    // Of course, the subsidy is high enough, and transaction volume low
    // enough, that fee sniping isn't a problem yet, but by implementing a fix
    // now we ensure code won't be written that makes assumptions about
    // nLockTime that preclude a fix later.
    if (IsCurrentForAntiFeeSniping(chain, block_hash)) {
        tx.nLockTime = block_height;

        // Secondly occasionally randomly pick a nLockTime even further back, so
        // that transactions that are delayed after signing for whatever reason,
        // e.g. high-latency mix networks and some CoinJoin implementations, have
        // better privacy.
        if (rng_fast.randrange(10) == 0) {
            tx.nLockTime = std::max(0, int(tx.nLockTime) - int(rng_fast.randrange(100)));
        }
    } else {
        // If our chain is lagging behind, we can't discourage fee sniping nor help
        // the privacy of high-latency transactions. To avoid leaking a potentially
        // unique "nLockTime fingerprint", set nLockTime to a constant.
        tx.nLockTime = 0;
    }
    // Sanity check all values
    assert(tx.nLockTime < LOCKTIME_THRESHOLD); // Type must be block height
    assert(tx.nLockTime <= uint64_t(block_height));
    for (const auto& in : tx.vin) {
        // Can not be FINAL for locktime to work
        assert(in.nSequence != CTxIn::SEQUENCE_FINAL);
        // May be MAX NONFINAL to disable both BIP68 and BIP125
        if (in.nSequence == CTxIn::MAX_SEQUENCE_NONFINAL) continue;
        // May be MAX BIP125 to disable BIP68 and enable BIP125
        if (in.nSequence == MAX_BIP125_RBF_SEQUENCE) continue;
        // The wallet does not support any other sequence-use right now.
        assert(false);
    }
}

// Reset all non-global blinding details.
static void resetBlindDetails(BlindDetails* det, bool preserve_output_data = false) {
    det->i_amount_blinds.clear();
    det->i_asset_blinds.clear();
    det->i_assets.clear();
    det->i_amounts.clear();

    det->o_amounts.clear();
    if (!preserve_output_data) {
        det->o_pubkeys.clear();
    }
    det->o_amount_blinds.clear();
    det->o_assets.clear();
    det->o_asset_blinds.clear();

    if (!preserve_output_data) {
        det->num_to_blind = 0;
        det->change_to_blind = 0;
        det->only_recipient_blind_index = -1;
        det->only_change_pos = -1;
    }
}

static bool fillBlindDetails(BlindDetails* det, CWallet* wallet, CMutableTransaction& txNew, std::vector<std::shared_ptr<COutput>>& selected_coins, bilingual_str& error) {
    int num_inputs_blinded = 0;

    // Fill in input blinding details
    for (const std::shared_ptr<wallet::COutput>& coin : selected_coins) {
        det->i_amount_blinds.push_back(coin->bf_value);
        det->i_asset_blinds.push_back(coin->bf_asset);
        det->i_assets.push_back(coin->asset);
        det->i_amounts.push_back(coin->value);
        if (coin->txout.nValue.IsCommitment() || coin->txout.nAsset.IsCommitment()) {
            num_inputs_blinded++;
        }
    }
    // Fill in output blinding details
    for (size_t nOut = 0; nOut < txNew.vout.size(); nOut++) {
        //TODO(CA) consider removing all blind setting before BlindTransaction as they get cleared anyway
        det->o_amount_blinds.push_back(uint256());
        det->o_asset_blinds.push_back(uint256());
        det->o_assets.push_back(txNew.vout[nOut].nAsset.GetAsset());
        det->o_amounts.push_back(txNew.vout[nOut].nValue.GetAmount());
    }

    // There are a few edge-cases of blinding we need to take care of
    //
    // First, if there are blinded inputs but not outputs to blind
    // We need this to go through, even though no privacy is gained.
    if (num_inputs_blinded > 0 &&  det->num_to_blind == 0) {
        // We need to make sure to dupe an asset that is in input set
        //TODO Have blinding do some extremely minimal rangeproof
        CTxOut newTxOut(det->o_assets.back(), 0, CScript() << OP_RETURN);
        CPubKey blind_pub = wallet->GetBlindingPubKey(newTxOut.scriptPubKey); // irrelevant, just needs to be non-null
        newTxOut.nNonce.vchCommitment = std::vector<unsigned char>(blind_pub.begin(), blind_pub.end());
        txNew.vout.push_back(newTxOut);
        det->o_pubkeys.push_back(wallet->GetBlindingPubKey(newTxOut.scriptPubKey));
        det->o_amount_blinds.push_back(uint256());
        det->o_asset_blinds.push_back(uint256());
        det->o_amounts.push_back(0);
        det->o_assets.push_back(det->o_assets.back());
        det->num_to_blind++;
        wallet->WalletLogPrintf("Adding OP_RETURN output to complete blinding since there are %d blinded inputs and no blinded outputs\n", num_inputs_blinded);

        // No blinded inputs, but 1 blinded output
    } else if (num_inputs_blinded == 0 && det->num_to_blind == 1) {
        if (det->change_to_blind == 1) {
            // Only 1 blinded change, unblind the change
            //TODO Split up change instead if possible
            if (det->ignore_blind_failure) {
                det->num_to_blind--;
                det->change_to_blind--;
                txNew.vout[det->only_change_pos].nNonce.SetNull();
                det->o_pubkeys[det->only_change_pos] = CPubKey();
                det->o_amount_blinds[det->only_change_pos] = uint256();
                det->o_asset_blinds[det->only_change_pos] = uint256();
                wallet->WalletLogPrintf("Unblinding change at index %d due to lack of inputs and other outputs being blinded.\n", det->only_change_pos);
            } else {
                error = _("Change output could not be blinded as there are no blinded inputs and no other blinded outputs.");
                return false;
            }
        } else {
            // 1 blinded destination
            // TODO Attempt to get a blinded input, OR add unblinded coin to make blinded change
            assert(det->only_recipient_blind_index != -1);
            if (det->ignore_blind_failure) {
                det->num_to_blind--;
                txNew.vout[det->only_recipient_blind_index].nNonce.SetNull();
                det->o_pubkeys[det->only_recipient_blind_index] = CPubKey();
                det->o_amount_blinds[det->only_recipient_blind_index] = uint256();
                det->o_asset_blinds[det->only_recipient_blind_index] = uint256();
                wallet->WalletLogPrintf("Unblinding single blinded output at index %d due to lack of inputs and other outputs being blinded.\n", det->only_recipient_blind_index);
            } else {
                error = _("Transaction output could not be blinded as there are no blinded inputs and no other blinded outputs.");
                return false;
            }
        }
    }
    // All other combinations should work.
    return true;
}

static util::Result<CreatedTransactionResult> CreateTransactionInternal(
        CWallet& wallet,
        const std::vector<CRecipient>& vecSend,
        int change_pos,
        const CCoinControl& coin_control,
        bool sign,
        BlindDetails* blind_details,
        const IssuanceDetails* issuance_details) EXCLUSIVE_LOCKS_REQUIRED(wallet.cs_wallet)
{
    if (blind_details || issuance_details) {
        assert(g_con_elementsmode);
    }

    if (blind_details) {
        // Clear out previous blinding/data info as needed
        resetBlindDetails(blind_details);
    }

    AssertLockHeld(wallet.cs_wallet);

    // out variables, to be packed into returned result structure
    int nChangePosInOut = change_pos;

    FastRandomContext rng_fast;
    CMutableTransaction txNew; // The resulting transaction that we make

    CoinSelectionParams coin_selection_params{rng_fast}; // Parameters for coin selection, init with dummy
    coin_selection_params.m_avoid_partial_spends = coin_control.m_avoid_partial_spends;
    coin_selection_params.m_include_unsafe_inputs = coin_control.m_include_unsafe_inputs;

    CScript dummy_script = CScript() << 0x00;
    CAmountMap map_recipients_sum;
    // Always assume that we are at least sending policyAsset.
    map_recipients_sum[::policyAsset] = 0;
    std::vector<std::unique_ptr<ReserveDestination>> reservedest;
    // Set the long term feerate estimate to the wallet's consolidate feerate
    coin_selection_params.m_long_term_feerate = wallet.m_consolidate_feerate;
    const OutputType change_type = wallet.TransactionChangeType(coin_control.m_change_type ? *coin_control.m_change_type : wallet.m_default_change_type, vecSend);
    reservedest.emplace_back(new ReserveDestination(&wallet, change_type)); // policy asset

    std::set<CAsset> assets_seen;
    unsigned int outputs_to_subtract_fee_from = 0; // The number of outputs which we are subtracting the fee from
    for (const auto& recipient : vecSend)
    {
        // Pad change keys to cover total possible number of assets
        // One already exists(for policyAsset), so one for each destination
        if (assets_seen.insert(recipient.asset).second) {
            reservedest.emplace_back(new ReserveDestination(&wallet, change_type));
        }

        // Skip over issuance outputs, no need to select those coins
        if (recipient.asset == CAsset(uint256S("1")) || recipient.asset == CAsset(uint256S("2"))) {
            continue;
        }

        map_recipients_sum[recipient.asset] += recipient.nAmount;

        if (recipient.fSubtractFeeFromAmount) {
            outputs_to_subtract_fee_from++;
            coin_selection_params.m_subtract_fee_outputs = true;
        }
    }

    // Create change script that will be used if we need change
    // ELEMENTS: A map that keeps track of the change script for each asset and also
    // the index of the reservedest used for that script (-1 if none).
    std::map<CAsset, std::pair<int, CScript>> mapScriptChange;
    // For manually set change, we need to use the blinding pubkey associated
    // with the manually-set address rather than generating one from the wallet
    std::map<CAsset, std::optional<CPubKey>> mapBlindingKeyChange;
    bilingual_str error; // possible error str

    // coin control: send change to custom address
    if (coin_control.destChange.size() > 0) {
        for (const auto& dest : coin_control.destChange) {
            // No need to test we cover all assets.  We produce error for that later.
            mapScriptChange[dest.first] = std::pair<int, CScript>(-1, GetScriptForDestination(dest.second));
            if (IsBlindDestination(dest.second)) {
                mapBlindingKeyChange[dest.first] = GetDestinationBlindingKey(dest.second);
            } else {
                mapBlindingKeyChange[dest.first] = std::nullopt;
            }
        }
    } else { // no coin control: send change to newly generated address
        // Note: We use a new key here to keep it from being obvious which side is the change.
        //  The drawback is that by not reusing a previous key, the change may be lost if a
        //  backup is restored, if the backup doesn't have the new private key for the change.
        //  If we reused the old key, it would be possible to add code to look for and
        //  rediscover unknown transactions that were written with keys of ours to recover
        //  post-backup change.

        // One change script per output asset.
        size_t index = 0;
        for (const auto& value : map_recipients_sum) {
            // Reserve a new key pair from key pool. If it fails, provide a dummy
            // destination in case we don't need change.
            auto op_dest = reservedest[index]->GetReservedDestination(true);
            if (index >= reservedest.size() || !op_dest) {
                error = _("Transaction needs a change address, but we can't generate it.") + Untranslated(" ") + util::ErrorString(op_dest);
                // ELEMENTS: We need to put a dummy destination here. Core uses an empty script
                //  but we can't because empty scripts indicate fees (which trigger assertion
                //  failures in `BlindTransaction`). We also set the index to -1, indicating
                //  that this destination is not actually used, and therefore should not be
                //  returned by the `ReturnDestination` loop below.
                mapScriptChange[value.first] = std::pair<int, CScript>(-1, dummy_script);
            } else {
                mapScriptChange[value.first] = std::pair<int, CScript>(index, GetScriptForDestination(*op_dest));
                ++index;
            }
        }

        // Also make sure we have change scripts for the pre-selected inputs.
        std::vector<COutPoint> vPresetInputs;
        coin_control.ListSelected(vPresetInputs);
        for (const COutPoint& presetInput : vPresetInputs) {
            CAsset asset;
            const auto& it = wallet.mapWallet.find(presetInput.hash);
            CTxOut txout;
            if (it != wallet.mapWallet.end()) {
                 asset = it->second.GetOutputAsset(wallet, presetInput.n);
            } else if (coin_control.GetExternalOutput(presetInput, txout)) {
                asset = txout.nAsset.GetAsset();
            } else {
                // Ignore this here, will fail more gracefully later.
                continue;
            }

            if (mapScriptChange.find(asset) != mapScriptChange.end()) {
                // This asset already has a change script.
                continue;
            }

            auto op_dest = reservedest[index]->GetReservedDestination(true);
            if (index >= reservedest.size() || !op_dest) {
                return util::Error{_("Transaction needs a change address, but we can't generate it.") + Untranslated(" ") + util::ErrorString(op_dest)};
            }

            CScript scriptChange = GetScriptForDestination(*op_dest);
            // A valid destination implies a change script (and
            // vice-versa). An empty change script will abort later, if the
            // change keypool ran out, but change is required.
            CHECK_NONFATAL(IsValidDestination(*op_dest) != (scriptChange == dummy_script));
            mapScriptChange[asset] = std::pair<int, CScript>(index, scriptChange);
            ++index;
        }
    }
    assert(mapScriptChange.size() > 0);
    CTxOut change_prototype_txout(mapScriptChange.begin()->first, 0, mapScriptChange.begin()->second.second);
    // TODO CA: Set this for each change output
    coin_selection_params.change_output_size = GetSerializeSize(change_prototype_txout);
    if (g_con_elementsmode) {
        if (blind_details) {
            change_prototype_txout.nAsset.vchCommitment.resize(33);
            change_prototype_txout.nValue.vchCommitment.resize(33);
            change_prototype_txout.nNonce.vchCommitment.resize(33);
            coin_selection_params.change_output_size = GetSerializeSize(change_prototype_txout);
            coin_selection_params.change_output_size += (MAX_RANGEPROOF_SIZE + DEFAULT_SURJECTIONPROOF_SIZE + WITNESS_SCALE_FACTOR - 1)/WITNESS_SCALE_FACTOR;
        } else {
            change_prototype_txout.nAsset.vchCommitment.resize(33);
            change_prototype_txout.nValue.vchCommitment.resize(9);
            change_prototype_txout.nNonce.vchCommitment.resize(1);
            coin_selection_params.change_output_size = GetSerializeSize(change_prototype_txout);
        }
    }

    // Get size of spending the change output
    int change_spend_size = CalculateMaximumSignedInputSize(change_prototype_txout, &wallet, /*coin_control=*/nullptr);
    // If the wallet doesn't know how to sign change output, assume p2sh-p2wpkh
    // as lower-bound to allow BnB to do it's thing
    if (change_spend_size == -1) {
        coin_selection_params.change_spend_size = DUMMY_NESTED_P2WPKH_INPUT_SIZE;
    } else {
        coin_selection_params.change_spend_size = (size_t)change_spend_size;
    }

    // Set discard feerate
    coin_selection_params.m_discard_feerate = GetDiscardRate(wallet);

    // Get the fee rate to use effective values in coin selection
    FeeCalculation feeCalc;
    coin_selection_params.m_effective_feerate = GetMinimumFeeRate(wallet, coin_control, &feeCalc);
    // Do not, ever, assume that it's fine to change the fee rate if the user has explicitly
    // provided one
    if (coin_control.m_feerate && coin_selection_params.m_effective_feerate > *coin_control.m_feerate) {
        return util::Error{strprintf(_("Fee rate (%s) is lower than the minimum fee rate setting (%s)"), coin_control.m_feerate->ToString(FeeEstimateMode::SAT_VB), coin_selection_params.m_effective_feerate.ToString(FeeEstimateMode::SAT_VB))};
    }
    if (feeCalc.reason == FeeReason::FALLBACK && !wallet.m_allow_fallback_fee) {
        // eventually allow a fallback fee
        return util::Error{strprintf(_("Fee estimation failed. Fallbackfee is disabled. Wait a few blocks or enable %s."), "-fallbackfee")};
    }

    // Calculate the cost of change
    // Cost of change is the cost of creating the change output + cost of spending the change output in the future.
    // For creating the change output now, we use the effective feerate.
    // For spending the change output in the future, we use the discard feerate for now.
    // So cost of change = (change output size * effective feerate) + (size of spending change output * discard feerate)
    coin_selection_params.m_change_fee = coin_selection_params.m_effective_feerate.GetFee(coin_selection_params.change_output_size);
    coin_selection_params.m_cost_of_change = coin_selection_params.m_discard_feerate.GetFee(coin_selection_params.change_spend_size) + coin_selection_params.m_change_fee;

    // ELEMENTS FIXME: Please review the map_recipients_sum[::policyAsset] part.
    //                 In bitcoin the line just says recipients_sum (it's not a map).
    //                 I'm not sure if the policyAsset value is the right number to use.
    coin_selection_params.m_min_change_target = GenerateChangeTarget(std::floor(map_recipients_sum[::policyAsset] / vecSend.size()), coin_selection_params.m_change_fee, rng_fast);

    // The smallest change amount should be:
    // 1. at least equal to dust threshold
    // 2. at least 1 sat greater than fees to spend it at m_discard_feerate
    const auto dust = GetDustThreshold(change_prototype_txout, coin_selection_params.m_discard_feerate);
    const auto change_spend_fee = coin_selection_params.m_discard_feerate.GetFee(coin_selection_params.change_spend_size);
    coin_selection_params.min_viable_change = std::max(change_spend_fee + 1, dust);

    // Static vsize overhead + outputs vsize. 4 nVersion, 4 nLocktime, 1 input count, 1 witness overhead (dummy, flag, stack size)
    coin_selection_params.tx_noinputs_size = 10 + GetSizeOfCompactSize(vecSend.size()); // bytes for output count

    // vouts to the payees
    if (g_con_elementsmode) {
        coin_selection_params.tx_noinputs_size += 46; // fee output: 9 bytes value, 1 byte scriptPubKey, 33 bytes asset, 1 byte nonce, 1 byte each for null rangeproof/surjectionproof
    }

    // ELEMENTS: If we have blinded inputs but no blinded outputs (which, since the wallet
    //  makes an effort to not produce change, is a common case) then we need to add a
    //  dummy output.
    bool may_need_blinded_dummy = !!blind_details;
    for (const auto& recipient : vecSend)
    {
        CTxOut txout(recipient.asset, recipient.nAmount, recipient.scriptPubKey);
        txout.nNonce.vchCommitment = std::vector<unsigned char>(recipient.confidentiality_key.begin(), recipient.confidentiality_key.end());

        // Include the fee cost for outputs.
        coin_selection_params.tx_noinputs_size += ::GetSerializeSize(txout, PROTOCOL_VERSION);

        if (recipient.asset == policyAsset && IsDust(txout, wallet.chain().relayDustFee()))
        {
            return util::Error{_("Transaction amount too small")};
        }
        txNew.vout.push_back(txout);

        // ELEMENTS
        if (blind_details) {
            blind_details->o_pubkeys.push_back(recipient.confidentiality_key);
            if (blind_details->o_pubkeys.back().IsFullyValid()) {
                may_need_blinded_dummy = false;
                blind_details->num_to_blind++;
                blind_details->only_recipient_blind_index = txNew.vout.size()-1;
                if (!coin_selection_params.m_subtract_fee_outputs) {
                    coin_selection_params.tx_noinputs_size += (MAX_RANGEPROOF_SIZE + DEFAULT_SURJECTIONPROOF_SIZE + WITNESS_SCALE_FACTOR - 1)/WITNESS_SCALE_FACTOR;
                }
            }
        }
    }
    if (may_need_blinded_dummy && !coin_selection_params.m_subtract_fee_outputs) {
        // dummy output: 33 bytes value, 2 byte scriptPubKey, 33 bytes asset, 1 byte nonce, 66 bytes dummy rangeproof, 1 byte null surjectionproof
        // FIXME actually, we currently just hand off to BlindTransaction which will put
        //  a full rangeproof and surjectionproof. We should fix this when we overhaul
        //  the blinding logic.
        coin_selection_params.tx_noinputs_size += 70 + 66 +(MAX_RANGEPROOF_SIZE + DEFAULT_SURJECTIONPROOF_SIZE + WITNESS_SCALE_FACTOR - 1)/WITNESS_SCALE_FACTOR;
    }
    // If we are going to issue an asset, add the issuance data to the noinputs_size so that
    // we allocate enough coins for them.
    if (issuance_details) {
        size_t issue_count = 0;
        for (unsigned int i = 0; i < txNew.vout.size(); i++) {
            if (txNew.vout[i].nAsset.IsExplicit() && txNew.vout[i].nAsset.GetAsset() == CAsset(uint256S("1"))) {
                issue_count++;
            } else if (txNew.vout[i].nAsset.IsExplicit() && txNew.vout[i].nAsset.GetAsset() == CAsset(uint256S("2"))) {
                issue_count++;
            }
        }
        if (issue_count > 0) {
            // Allocate space for blinding nonce, entropy, and whichever of nAmount/nInflationKeys is null
            coin_selection_params.tx_noinputs_size += 2 * 32 + 2 * (2 - issue_count);
        }
        // Allocate non-null nAmount/nInflationKeys and rangeproofs
        if (issuance_details->blind_issuance) {
            coin_selection_params.tx_noinputs_size += issue_count * (33 * WITNESS_SCALE_FACTOR + MAX_RANGEPROOF_SIZE + WITNESS_SCALE_FACTOR - 1) / WITNESS_SCALE_FACTOR;
        } else {
            coin_selection_params.tx_noinputs_size += issue_count * 9;
        }
    }

    // Include the fees for things that aren't inputs, excluding the change output
    const CAmount not_input_fees = coin_selection_params.m_effective_feerate.GetFee(coin_selection_params.m_subtract_fee_outputs ? 0 : coin_selection_params.tx_noinputs_size);
    CAmountMap map_selection_target = map_recipients_sum;
    map_selection_target[policyAsset] += not_input_fees;

    // Fetch manually selected coins
    PreSelectedInputs preset_inputs;
    if (coin_control.HasSelected()) {
        auto res_fetch_inputs = FetchSelectedInputs(wallet, coin_control, coin_selection_params);
        if (!res_fetch_inputs) return util::Error{util::ErrorString(res_fetch_inputs)};
        preset_inputs = *res_fetch_inputs;
    }

    // Fetch wallet available coins if "other inputs" are
    // allowed (coins automatically selected by the wallet)
    CoinsResult available_coins;
    if (coin_control.m_allow_other_inputs) {
        available_coins = AvailableCoins(wallet, &coin_control, coin_selection_params.m_effective_feerate);
    }

    // Choose coins to use
    auto select_coins_res = SelectCoins(wallet, available_coins, preset_inputs, /*mapTargetValue=*/map_selection_target, coin_control, coin_selection_params);
    if (!select_coins_res) {
        // 'SelectCoins' either returns a specific error message or, if empty, means a general "Insufficient funds".
        const bilingual_str& err = util::ErrorString(select_coins_res);
        return util::Error{err.empty() ?_("Insufficient funds") : err};
    }
    const SelectionResult& result = *select_coins_res;
    TRACE5(coin_selection, selected_coins, wallet.GetName().c_str(), GetAlgorithmName(result.GetAlgo()).c_str(), result.GetTarget(), result.GetWaste(), result.GetSelectedValue());

    // If all of our inputs are explicit, we don't need a blinded dummy
    if (may_need_blinded_dummy) {
        may_need_blinded_dummy = false;
        for (const auto& coin : result.GetInputSet()) {
            if (!coin->txout.nValue.IsExplicit()) {
                may_need_blinded_dummy = true;
                break;
            }
        }
    }

    // Always make a change output
    // We will reduce the fee from this change output later, and remove the output if it is too small.
    // ELEMENTS: wrap this all in a loop, set nChangePosInOut specifically for policy asset
    CAmountMap map_change_and_fee = result.GetSelectedValue() - map_recipients_sum;
    // Zero out any non-policy assets which have zero change value
    for (auto it = map_change_and_fee.begin(); it != map_change_and_fee.end(); ) {
        if (it->first != policyAsset && it->second == 0) {
            it = map_change_and_fee.erase(it);
        } else {
            ++it;
        }
    }

    // Uniformly randomly place change outputs for all assets, except that the policy-asset
    // change may have a fixed position.
    std::vector<std::optional<CAsset>> fixed_change_pos{txNew.vout.size() + map_change_and_fee.size()};
    if (nChangePosInOut == -1) {
       // randomly set policyasset change position
    } else if ((unsigned int)nChangePosInOut >= fixed_change_pos.size()) {
        return util::Error{_("Transaction change output index out of range")};
    } else {
        fixed_change_pos[nChangePosInOut] = policyAsset;
    }

    for (const auto& asset_change_and_fee : map_change_and_fee) {
        // No need to randomly set the policyAsset change if has been set manually
        if (nChangePosInOut >= 0 && asset_change_and_fee.first == policyAsset) {
            continue;
        }

        int index;
        do {
            index = rng_fast.randrange(fixed_change_pos.size());
        } while (fixed_change_pos[index]);

        fixed_change_pos[index] = asset_change_and_fee.first;
        if (asset_change_and_fee.first == policyAsset) {
            nChangePosInOut = index;
        }
    }

    // Create all the change outputs in their respective places, inserting them
    // in increasing order so that none of them affect each others' indices
    for (unsigned int i = 0; i < fixed_change_pos.size(); i++) {
        if (!fixed_change_pos[i]) {
            continue;
        }

        const CAsset& asset = *fixed_change_pos[i];
        const CAmount& change_and_fee = map_change_and_fee.at(asset);

        assert(change_and_fee >= 0);

        const std::map<CAsset, std::pair<int, CScript>>::const_iterator itScript = mapScriptChange.find(asset);
        if (itScript == mapScriptChange.end()) {
            return util::Error{Untranslated(strprintf("No change destination provided for asset %s", asset.GetHex()))};
        }
        CTxOut newTxOut(asset, change_and_fee, itScript->second.second);

        if (blind_details) {
            std::optional<CPubKey> blind_pub = std::nullopt;
            // We cannot blind zero-valued outputs, and anyway they will be dropped
            // later in this function during the dust check
            if (change_and_fee > 0) {
                const auto itBlindingKey = mapBlindingKeyChange.find(asset);
                if (itBlindingKey != mapBlindingKeyChange.end()) {
                    // If the change output was specified, use the blinding key that
                    // came with the specified address (if any)
                    blind_pub = itBlindingKey->second;
                } else {
                    // Otherwise, we generated it from our own wallet, so get the
                    // blinding key from our own wallet.
                    blind_pub = wallet.GetBlindingPubKey(itScript->second.second);
                }
            } else {
                assert(asset == policyAsset);
            }

            if (blind_pub) {
                blind_details->o_pubkeys.insert(blind_details->o_pubkeys.begin() + i, *blind_pub);
                assert(blind_pub->IsFullyValid());

                blind_details->num_to_blind++;
                blind_details->change_to_blind++;
                blind_details->only_change_pos = i;
                // Place the blinding pubkey here in case of fundraw calls
                newTxOut.nNonce.vchCommitment = std::vector<unsigned char>(blind_pub->begin(), blind_pub->end());
            } else {
                blind_details->o_pubkeys.insert(blind_details->o_pubkeys.begin() + i, CPubKey());
            }
        }
        // Insert change output
        txNew.vout.insert(txNew.vout.begin() + i, newTxOut);
    }

    // Add fee output.
    if (g_con_elementsmode) {
        CTxOut fee(::policyAsset, 0, CScript());
        assert(fee.IsFee());
        txNew.vout.push_back(fee);
        if (blind_details) {
            blind_details->o_pubkeys.push_back(CPubKey());
        }
    }
    assert(nChangePosInOut != -1);
    auto change_position = txNew.vout.begin() + nChangePosInOut;
    // end ELEMENTS

    // Set token input if reissuing
    int reissuance_index = -1;
    uint256 token_blinding;

    // Elements: Shuffle here to preserve random ordering for surjection proofs
    // selected_coins = std::vector<CInputCoin>(setCoins.begin(), setCoins.end());
    // Shuffle(selected_coins.begin(), selected_coins.end(), FastRandomContext());
    // Shuffle selected coins and fill in final vin
    std::vector<std::shared_ptr<COutput>> selected_coins = result.GetShuffledInputVector();

    // The sequence number is set to non-maxint so that DiscourageFeeSniping
    // works.
    //
    // BIP125 defines opt-in RBF as any nSequence < maxint-1, so
    // we use the highest possible value in that range (maxint-2)
    // to avoid conflicting with other possible uses of nSequence,
    // and in the spirit of "smallest possible change from prior
    // behavior."
    const uint32_t nSequence{coin_control.m_signal_bip125_rbf.value_or(wallet.m_signal_rbf) ? MAX_BIP125_RBF_SEQUENCE : CTxIn::MAX_SEQUENCE_NONFINAL};
    for (const auto& coin : selected_coins) {
        txNew.vin.push_back(CTxIn(coin->outpoint, CScript(), nSequence));

        if (issuance_details && coin->asset == issuance_details->reissuance_token) {
            reissuance_index = txNew.vin.size() - 1;
            token_blinding = coin->bf_asset;
        }
    }
    DiscourageFeeSniping(txNew, rng_fast, wallet.chain(), wallet.GetLastBlockHash(), wallet.GetLastBlockHeight());

    // ELEMENTS add issuance details and blinding details
    std::vector<CKey> issuance_asset_keys;
    std::vector<CKey> issuance_token_keys;
    if (issuance_details) {
        // Fill in issuances now that inputs are set
        assert(txNew.vin.size() > 0);
        int asset_index = -1;
        int token_index = -1;
        for (unsigned int i = 0; i < txNew.vout.size(); i++) {
            if (txNew.vout[i].nAsset.IsExplicit() && txNew.vout[i].nAsset.GetAsset() == CAsset(uint256S("1"))) {
                asset_index = i;
            } else if (txNew.vout[i].nAsset.IsExplicit() && txNew.vout[i].nAsset.GetAsset() == CAsset(uint256S("2"))) {
                token_index = i;
            }
        }
        // Initial issuance request
        if (issuance_details->reissuance_asset.IsNull() && issuance_details->reissuance_token.IsNull() && (asset_index != -1 || token_index != -1)) {
            uint256 entropy;
            CAsset asset;
            CAsset token;
            // Initial issuance always uses vin[0]
            GenerateAssetEntropy(entropy, txNew.vin[0].prevout, issuance_details->contract_hash);
            CalculateAsset(asset, entropy);
            CalculateReissuanceToken(token, entropy, issuance_details->blind_issuance);
            CScript blindingScript(CScript() << OP_RETURN << std::vector<unsigned char>(txNew.vin[0].prevout.hash.begin(), txNew.vin[0].prevout.hash.end()) << txNew.vin[0].prevout.n);
            txNew.vin[0].assetIssuance.assetEntropy = issuance_details->contract_hash;
            // We're making asset outputs, fill out asset type and issuance input
            if (asset_index != -1) {
                txNew.vin[0].assetIssuance.nAmount = txNew.vout[asset_index].nValue;

                txNew.vout[asset_index].nAsset = asset;
                if (issuance_details->blind_issuance && blind_details) {
                    issuance_asset_keys.push_back(wallet.GetBlindingKey(&blindingScript));
                    blind_details->num_to_blind++;
                }
            }
            // We're making reissuance token outputs
            if (token_index != -1) {
                txNew.vin[0].assetIssuance.nInflationKeys = txNew.vout[token_index].nValue;
                txNew.vout[token_index].nAsset = token;
                if (issuance_details->blind_issuance && blind_details) {
                    issuance_token_keys.push_back(wallet.GetBlindingKey(&blindingScript));
                    blind_details->num_to_blind++;

                    // If we're blinding a token issuance and no assets, we must make
                    // the asset issuance a blinded commitment to 0
                    if (asset_index == -1) {
                        txNew.vin[0].assetIssuance.nAmount = 0;
                        issuance_asset_keys.push_back(wallet.GetBlindingKey(&blindingScript));
                        blind_details->num_to_blind++;
                    }
                }
            }
        // Asset being reissued with explicitly named asset/token
        } else if (asset_index != -1) {
            assert(reissuance_index != -1);
            // Fill in output with issuance
            txNew.vout[asset_index].nAsset = issuance_details->reissuance_asset;

            // Fill in issuance
            // Blinding revealing underlying asset
            txNew.vin[reissuance_index].assetIssuance.assetBlindingNonce = token_blinding;
            txNew.vin[reissuance_index].assetIssuance.assetEntropy = issuance_details->entropy;
            txNew.vin[reissuance_index].assetIssuance.nAmount = txNew.vout[asset_index].nValue;

            // If blinded token derivation, blind the issuance
            CAsset temp_token;
            CalculateReissuanceToken(temp_token, issuance_details->entropy, true);
            if (temp_token == issuance_details->reissuance_token && blind_details) {
            CScript blindingScript(CScript() << OP_RETURN << std::vector<unsigned char>(txNew.vin[reissuance_index].prevout.hash.begin(), txNew.vin[reissuance_index].prevout.hash.end()) << txNew.vin[reissuance_index].prevout.n);
                issuance_asset_keys.resize(reissuance_index);
                issuance_asset_keys.push_back(wallet.GetBlindingKey(&blindingScript));
                blind_details->num_to_blind++;
            }
        }
    }

    // Do "initial blinding" for fee estimation purposes
    TxSize tx_sizes;
    CMutableTransaction tx_blinded = txNew;
    if (blind_details) {
        if (!fillBlindDetails(blind_details, &wallet, tx_blinded, selected_coins, error)) {
            return util::Error{error};
        }
        txNew = tx_blinded; // sigh, `fillBlindDetails` may have modified txNew
        // Update the change position to the new tx
        change_position = txNew.vout.begin() + nChangePosInOut;

        int ret = BlindTransaction(blind_details->i_amount_blinds, blind_details->i_asset_blinds, blind_details->i_assets, blind_details->i_amounts, blind_details->o_amount_blinds, blind_details->o_asset_blinds, blind_details->o_pubkeys, issuance_asset_keys, issuance_token_keys, tx_blinded);
        assert(ret != -1);
        if (ret != blind_details->num_to_blind) {
            return util::Error{_("Unable to blind the transaction properly. This should not happen.")};
        }

        tx_sizes = CalculateMaximumSignedTxSize(CTransaction(tx_blinded), &wallet, &coin_control);
    } else {
        tx_sizes = CalculateMaximumSignedTxSize(CTransaction(txNew), &wallet, &coin_control);
    }
    // end ELEMENTS

    // Calculate the transaction fee
    int nBytes = tx_sizes.vsize;
    if (nBytes == -1) {
        return util::Error{_("Missing solving data for estimating transaction size")};
    }

    // Subtract fee from the change output if not subtracting it from recipient outputs
    CAmount fee_needed = coin_selection_params.m_effective_feerate.GetFee(nBytes);
    CAmount current_fee = fee_needed;

    if (!coin_selection_params.m_subtract_fee_outputs) {
        change_position->nValue = change_position->nValue.GetAmount() - fee_needed;
    }

    // We want to drop the change to fees if:
    // 1. The change output would be dust
    // 2. The change is within the (almost) exact match window, i.e. it is less than or equal to the cost of the change output (cost_of_change)
    CAmount change_amount = change_position->nValue.GetAmount();
    if (IsDust(*change_position, coin_selection_params.m_discard_feerate) || change_amount <= coin_selection_params.m_cost_of_change)
    {
        bool was_blinded = blind_details && blind_details->o_pubkeys[nChangePosInOut].IsValid();

        // If the change was blinded, and was the only blinded output, we cannot drop it
        // without causing the transaction to fail to balance. So keep it, and merely
        // zero it out.
        if (was_blinded && blind_details->num_to_blind == 1) {
            assert (may_need_blinded_dummy);
            change_position->scriptPubKey = CScript() << OP_RETURN;
            change_position->nValue = 0;
        } else {
            txNew.vout.erase(change_position);

            fixed_change_pos[nChangePosInOut] = std::nullopt;
            tx_blinded.vout.erase(tx_blinded.vout.begin() + nChangePosInOut);
            if (tx_blinded.witness.vtxoutwit.size() > (unsigned) nChangePosInOut) {
                tx_blinded.witness.vtxoutwit.erase(tx_blinded.witness.vtxoutwit.begin() + nChangePosInOut);
            }
            if (blind_details) {

                blind_details->o_amounts.erase(blind_details->o_amounts.begin() + nChangePosInOut);
                blind_details->o_assets.erase(blind_details->o_assets.begin() + nChangePosInOut);
                blind_details->o_pubkeys.erase(blind_details->o_pubkeys.begin() + nChangePosInOut);
                // If change_amount == 0, we did not increment num_to_blind initially
                // and therefore do not need to decrement it here.
                if (was_blinded) {
                    blind_details->num_to_blind--;
                    blind_details->change_to_blind--;

                    // FIXME: If we drop the change *and* this means we have only one
                    //  blinded output *and* we have no blinded inputs, then this puts
                    //  us in a situation where BlindTransaction will fail. This is
                    //  prevented in fillBlindDetails, which adds an OP_RETURN output
                    //  to handle this case. So do this ludicrous hack to accomplish
                    //  this. This whole lump of un-followable-logic needs to be replaced
                    //  by a complete rewriting of the wallet blinding logic.
                    if (blind_details->num_to_blind < 2) {
                        resetBlindDetails(blind_details, true /* don't wipe output data */);
                        if (!fillBlindDetails(blind_details, &wallet, txNew, selected_coins, error)) {
                            return util::Error{error};
                        }
                    }
                }
            }
        }
        change_amount = 0;
        nChangePosInOut = -1;

        // Because we have dropped this change, the tx size and required fee will be different, so let's recalculate those
        tx_sizes = CalculateMaximumSignedTxSize(CTransaction(tx_blinded), &wallet, &coin_control);
        nBytes = tx_sizes.vsize;
        fee_needed = coin_selection_params.m_effective_feerate.GetFee(nBytes);
    }

    // The only time that fee_needed should be less than the amount available for fees (in change_and_fee - change_amount) is when
    // we are subtracting the fee from the outputs. If this occurs at any other time, it is a bug.
    if (!coin_selection_params.m_subtract_fee_outputs && fee_needed > map_change_and_fee.at(policyAsset) - change_amount) {
        wallet.WalletLogPrintf("ERROR: not enough coins to cover for fee (needed: %d, total: %d, change: %d)\n",
            fee_needed, map_change_and_fee.at(policyAsset), change_amount);
        return util::Error{Untranslated(STR_INTERNAL_BUG("Fee needed > fee paid"))};
    }

    // Sanity check that the fee cannot be negative as that means we have more output value than input value
    if (current_fee < 0) {
        return util::Error{Untranslated(STR_INTERNAL_BUG("Fee paid < 0"))};
    }

    // If there is a change output and we overpay the fees then increase the change to match the fee needed
    if (fee_needed <= map_change_and_fee.at(policyAsset) - change_amount) {
        current_fee = map_change_and_fee.at(policyAsset) - change_amount;
    }

    // Reduce output values for subtractFeeFromAmount
    if (coin_selection_params.m_subtract_fee_outputs) {
        CAmount to_reduce = fee_needed + change_amount - map_change_and_fee.at(policyAsset);
        int i = 0;
        bool fFirst = true;
        for (const auto& recipient : vecSend)
        {
            if (i == nChangePosInOut) {
                ++i;
            }
            CTxOut& txout = txNew.vout[i];

            if (recipient.fSubtractFeeFromAmount)
            {
                CAmount value = txout.nValue.GetAmount();
                if (recipient.asset != policyAsset) {
                    return util::Error{Untranslated(strprintf("Wallet does not support more than one type of fee at a time, therefore can not subtract fee from address amount, which is of a different asset id. fee asset: %s recipient asset: %s", policyAsset.GetHex(), recipient.asset.GetHex()))};
                }

                value -= to_reduce / outputs_to_subtract_fee_from; // Subtract fee equally from each selected recipient

                if (fFirst) // first receiver pays the remainder not divisible by output count
                {
                    fFirst = false;
                    value -= to_reduce % outputs_to_subtract_fee_from;
                }

                // Error if this output is reduced to be below dust
                if (IsDust(txout, wallet.chain().relayDustFee())) {
                    if (value < 0) {
                        return util::Error{_("The transaction amount is too small to pay the fee")};
                    } else {
                        return util::Error{_("The transaction amount is too small to send after the fee has been deducted")};
                    }
                }

                txout.nValue = value;
            }
            ++i;
        }
        current_fee = result.GetSelectedValue()[::policyAsset] - CalculateOutputValue(txNew, ::policyAsset);
        if (fee_needed != current_fee) {
            return util::Error{Untranslated(STR_INTERNAL_BUG("SFFO: Fee needed != fee paid"))};
        }
    }

    // fee_needed should now always be less than or equal to the current fees that we pay.
    // If it is not, it is a bug.
    if (fee_needed > current_fee) {
        return util::Error{Untranslated(STR_INTERNAL_BUG("Fee needed > fee paid"))};
    }

    // ELEMENTS: Give up if change keypool ran out and change is required
    for (const auto& maybe_change_asset : fixed_change_pos) {
        if (maybe_change_asset) {
            auto used = mapScriptChange.extract(*maybe_change_asset);
            if (used.mapped().second == dummy_script) {
                return util::Error{error};
            }
        }
    }

    // ELEMENTS update fee output
    if (g_con_elementsmode) {
        for (auto& txout : txNew.vout) {
            if (txout.IsFee()) {
                txout.nValue = current_fee;
                break;
            }
        }
    }

    // ELEMENTS do actual blinding
    if (blind_details) {
        // Print blinded transaction info before we possibly blow it away when !sign.
        std::string summary = "CreateTransaction created blinded transaction:\nIN: ";
        for (unsigned int i = 0; i < selected_coins.size(); ++i) {
            if (i > 0) {
                summary += "    ";
            }
            summary += strprintf("#%d: %s [%s] (%s [%s])\n", i,
                selected_coins[i]->value,
                selected_coins[i]->txout.nValue.IsExplicit() ? "explicit" : "blinded",
                selected_coins[i]->asset.GetHex(),
                selected_coins[i]->txout.nAsset.IsExplicit() ? "explicit" : "blinded"
            );
        }
        summary += "OUT: ";
        for (unsigned int i = 0; i < txNew.vout.size(); ++i) {
            if (i > 0) {
                summary += "     ";
            }
            const CTxOut& unblinded = txNew.vout[i];
            summary += strprintf("#%d: %s%s [%s] (%s [%s])\n", i,
                txNew.vout[i].IsFee() ? "[fee] " : "",
                unblinded.nValue.GetAmount(),
                blind_details->o_pubkeys[i].IsValid() ? "blinded" : "explicit",
                unblinded.nAsset.GetAsset().GetHex(),
                blind_details->o_pubkeys[i].IsValid() ? "blinded" : "explicit"
            );
        }
        wallet.WalletLogPrintf(summary+"\n");

        // Wipe output blinding factors and start over
        blind_details->o_amount_blinds.clear();
        blind_details->o_asset_blinds.clear();
        for (unsigned int i = 0; i < txNew.vout.size(); i++) {
            blind_details->o_amounts[i] = txNew.vout[i].nValue.GetAmount();
            assert(blind_details->o_assets[i] == txNew.vout[i].nAsset.GetAsset());
        }

        if (sign) {
            int ret = BlindTransaction(blind_details->i_amount_blinds, blind_details->i_asset_blinds, blind_details->i_assets, blind_details->i_amounts, blind_details->o_amount_blinds, blind_details->o_asset_blinds,  blind_details->o_pubkeys, issuance_asset_keys, issuance_token_keys, txNew);
            assert(ret != -1);
            if (ret != blind_details->num_to_blind) {
                wallet.WalletLogPrintf("ERROR: tried to blind %d outputs but only blinded %d\n", (int) blind_details->num_to_blind, (int) ret);
                return util::Error{_("Unable to blind the transaction properly. This should not happen.")};
            }
        }
    }

    // Release any change keys that we didn't use.
    for (const auto& it : mapScriptChange) {
        int index = it.second.first;
        if (index < 0) {
            continue;
        }

        reservedest[index]->ReturnDestination();
    }


    if (sign) {
        if (!wallet.SignTransaction(txNew)) {
            return util::Error{_("Signing transaction failed")};
        }
    }

    // Normalize the witness in case it is not serialized before mempool
    if (!txNew.HasWitness()) {
        txNew.witness.SetNull();
    }

    // Return the constructed transaction data.
    CTransactionRef tx = MakeTransactionRef(std::move(txNew));

    // Limit size
    if ((sign && GetTransactionWeight(*tx) > MAX_STANDARD_TX_WEIGHT) ||
        (!sign && tx_sizes.weight > MAX_STANDARD_TX_WEIGHT))
    {
        return util::Error{_("Transaction too large")};
    }

    if (current_fee > wallet.m_default_max_tx_fee) {
        return util::Error{TransactionErrorString(TransactionError::MAX_FEE_EXCEEDED)};
    }

    if (gArgs.GetBoolArg("-walletrejectlongchains", DEFAULT_WALLET_REJECT_LONG_CHAINS)) {
        // Lastly, ensure this tx will pass the mempool's chain limits
        if (!wallet.chain().checkChainLimits(tx)) {
            return util::Error{_("Transaction has too long of a mempool chain")};
        }
    }

    // Before we return success, we assume any change key will be used to prevent
    // accidental re-use.
    for (auto& reservedest_ : reservedest) {
        reservedest_->KeepDestination();
    }

    wallet.WalletLogPrintf("Fee Calculation: Fee:%d Bytes:%u Tgt:%d (requested %d) Reason:\"%s\" Decay %.5f: Estimation: (%g - %g) %.2f%% %.1f/(%.1f %d mem %.1f out) Fail: (%g - %g) %.2f%% %.1f/(%.1f %d mem %.1f out)\n",
              current_fee, nBytes, feeCalc.returnedTarget, feeCalc.desiredTarget, StringForFeeReason(feeCalc.reason), feeCalc.est.decay,
              feeCalc.est.pass.start, feeCalc.est.pass.end,
              (feeCalc.est.pass.totalConfirmed + feeCalc.est.pass.inMempool + feeCalc.est.pass.leftMempool) > 0.0 ? 100 * feeCalc.est.pass.withinTarget / (feeCalc.est.pass.totalConfirmed + feeCalc.est.pass.inMempool + feeCalc.est.pass.leftMempool) : 0.0,
              feeCalc.est.pass.withinTarget, feeCalc.est.pass.totalConfirmed, feeCalc.est.pass.inMempool, feeCalc.est.pass.leftMempool,
              feeCalc.est.fail.start, feeCalc.est.fail.end,
              (feeCalc.est.fail.totalConfirmed + feeCalc.est.fail.inMempool + feeCalc.est.fail.leftMempool) > 0.0 ? 100 * feeCalc.est.fail.withinTarget / (feeCalc.est.fail.totalConfirmed + feeCalc.est.fail.inMempool + feeCalc.est.fail.leftMempool) : 0.0,
              feeCalc.est.fail.withinTarget, feeCalc.est.fail.totalConfirmed, feeCalc.est.fail.inMempool, feeCalc.est.fail.leftMempool);
    return CreatedTransactionResult(tx, current_fee, nChangePosInOut, feeCalc);
}

util::Result<CreatedTransactionResult> CreateTransaction(
        CWallet& wallet,
        const std::vector<CRecipient>& vecSend,
        int change_pos,
        const CCoinControl& coin_control,
        bool sign,
        BlindDetails* blind_details,
        const IssuanceDetails* issuance_details)
{
    if (vecSend.empty()) {
        return util::Error{_("Transaction must have at least one recipient")};
    }

    if (std::any_of(vecSend.cbegin(), vecSend.cend(), [](const auto& recipient){ return recipient.nAmount < 0; })) {
        return util::Error{_("Transaction amounts must not be negative")};
    }

    // ELEMENTS
    if (g_con_elementsmode) {
        if (std::any_of(vecSend.cbegin(), vecSend.cend(), [](const auto& recipient){ return recipient.asset.IsNull(); })) {
            return util::Error{_("No asset provided for recipient")};
        }
    }

    LOCK(wallet.cs_wallet);

    auto res = CreateTransactionInternal(wallet, vecSend, change_pos, coin_control, sign, blind_details, issuance_details);
    TRACE4(coin_selection, normal_create_tx_internal, wallet.GetName().c_str(), bool(res),
           res ? res->fee : 0, res ? res->change_pos : 0);
    if (!res) return res;
    const auto& txr_ungrouped = *res;
    // try with avoidpartialspends unless it's enabled already
    if (txr_ungrouped.fee > 0 /* 0 means non-functional fee rate estimation */ && wallet.m_max_aps_fee > -1 && !coin_control.m_avoid_partial_spends) {
        TRACE1(coin_selection, attempting_aps_create_tx, wallet.GetName().c_str());
        CCoinControl tmp_cc = coin_control;
        tmp_cc.m_avoid_partial_spends = true;

        // ELEMENTS: only for unblinded transactions
        // Re-use the change destination from the first creation attempt to avoid skipping BIP44 indexes
        const int ungrouped_change_pos = txr_ungrouped.change_pos;
        if (ungrouped_change_pos != -1 && !blind_details) {
            const CAsset& asset = txr_ungrouped.tx->vout[ungrouped_change_pos].nAsset.GetAsset();
            ExtractDestination(txr_ungrouped.tx->vout[ungrouped_change_pos].scriptPubKey, tmp_cc.destChange[asset]);
        }

        BlindDetails blind_details2;
        BlindDetails *blind_details2_ptr = blind_details ? &blind_details2 : nullptr;
        auto txr_grouped = CreateTransactionInternal(wallet, vecSend, change_pos, tmp_cc, sign, blind_details2_ptr, issuance_details);
        // if fee of this alternative one is within the range of the max fee, we use this one
        const bool use_aps{txr_grouped.has_value() ? (txr_grouped->fee <= txr_ungrouped.fee + wallet.m_max_aps_fee) : false};
        TRACE5(coin_selection, aps_create_tx_internal, wallet.GetName().c_str(), use_aps, txr_grouped.has_value(),
               txr_grouped.has_value() ? txr_grouped->fee : 0, txr_grouped.has_value() ? txr_grouped->change_pos : 0);
        if (txr_grouped) {
            wallet.WalletLogPrintf("Fee non-grouped = %lld, grouped = %lld, using %s\n",
                txr_ungrouped.fee, txr_grouped->fee, use_aps ? "grouped" : "non-grouped");
            if (use_aps) {
                if (blind_details) {
                    *blind_details = blind_details2;
                }
                return txr_grouped;
            }
        }
    }
    return res;
}

bool FundTransaction(CWallet& wallet, CMutableTransaction& tx, CAmount& nFeeRet, int& nChangePosInOut, bilingual_str& error, bool lockUnspents, const std::set<int>& setSubtractFeeFromOutputs, CCoinControl coinControl)
{
    std::vector<CRecipient> vecSend;

    // Turn the txout set into a CRecipient vector.
    for (size_t idx = 0; idx < tx.vout.size(); idx++) {
        const CTxOut& txOut = tx.vout[idx];

        // ELEMENTS:
        if (!txOut.nValue.IsExplicit() || !txOut.nAsset.IsExplicit()) {
            error = _("Pre-funded amounts must be non-blinded");
            return false;
        }

        // Fee outputs should not be added to avoid overpayment of fees
        if (txOut.IsFee()) {
            continue;
        }

        CRecipient recipient = {txOut.scriptPubKey, txOut.nValue.GetAmount(), txOut.nAsset.GetAsset(), CPubKey(txOut.nNonce.vchCommitment), setSubtractFeeFromOutputs.count(idx) == 1};
        vecSend.push_back(recipient);
    }

    // Acquire the locks to prevent races to the new locked unspents between the
    // CreateTransaction call and LockCoin calls (when lockUnspents is true).
    LOCK(wallet.cs_wallet);

    // Check any existing inputs for peg-in data and add to external txouts if so
    // Fetch specified UTXOs from the UTXO set to get the scriptPubKeys and values of the outputs being selected
    // and to match with the given solving_data. Only used for non-wallet outputs.
    const auto& fedpegscripts = GetValidFedpegScripts(wallet.chain().getTip(), Params().GetConsensus(), true /* nextblock_validation */);
    std::map<COutPoint, Coin> coins;
    for (unsigned int i = 0; i < tx.vin.size(); ++i ) {
        const CTxIn& txin = tx.vin[i];
        coins[txin.prevout]; // Create empty map entry keyed by prevout.
        if (txin.m_is_pegin) {
            std::string err;
            if (tx.witness.vtxinwit.size() != tx.vin.size() || !IsValidPeginWitness(tx.witness.vtxinwit[i].m_pegin_witness, fedpegscripts, txin.prevout, err, false)) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Transaction contains invalid peg-in input: %s", err));
            }
            CScriptWitness& pegin_witness = tx.witness.vtxinwit[i].m_pegin_witness;
            CTxOut txout = GetPeginOutputFromWitness(pegin_witness);
            coinControl.SelectExternal(txin.prevout, txout);
        }
    }
    wallet.chain().findCoins(coins);

    for (const CTxIn& txin : tx.vin) {
        const auto& outPoint = txin.prevout;
        if (wallet.IsMine(outPoint)) {
            // The input was found in the wallet, so select as internal
            coinControl.Select(outPoint);
        } else if (txin.m_is_pegin) {
            // ELEMENTS: input is pegin so nothing to select
        } else if (coins[outPoint].out.IsNull()) {
            error = _("Unable to find UTXO for external input");
            return false;
        } else {
            // The input was not in the wallet, but is in the UTXO set, so select as external
            coinControl.SelectExternal(outPoint, coins[outPoint].out);
        }
    }

    auto blind_details = g_con_elementsmode ? std::make_unique<BlindDetails>() : nullptr;
    auto res = CreateTransaction(wallet, vecSend, nChangePosInOut, coinControl, false, blind_details.get());
    if (!res) {
        error = util::ErrorString(res);
        return false;
    }
    const auto& txr = *res;
    CTransactionRef tx_new = txr.tx;
    nFeeRet = txr.fee;
    nChangePosInOut = txr.change_pos;

    // Wipe outputs and output witness and re-add one by one
    tx.vout.clear();
    tx.witness.vtxoutwit.clear();
    for (unsigned int i = 0; i < tx_new->vout.size(); i++) {
        const CTxOut& out = tx_new->vout[i];
        tx.vout.push_back(out);
        if (tx_new->witness.vtxoutwit.size() > i) {
            // We want to re-add previously existing outwitnesses
            // even though we don't create any new ones
            const CTxOutWitness& outwit = tx_new->witness.vtxoutwit[i];
            tx.witness.vtxoutwit.push_back(outwit);
        }
    }

    // Add new txins while keeping original txin scriptSig/order.
    for (const CTxIn& txin : tx_new->vin) {
        if (!coinControl.IsSelected(txin.prevout)) {
            tx.vin.push_back(txin);

        }
        if (lockUnspents) {
            wallet.LockCoin(txin.prevout);
        }

    }

    return true;
}
} // namespace wallet
