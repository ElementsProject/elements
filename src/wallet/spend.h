// Copyright (c) 2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_WALLET_SPEND_H
#define BITCOIN_WALLET_SPEND_H

#include <consensus/amount.h>
#include <wallet/coincontrol.h>
#include <policy/fees.h> // for FeeCalculation
#include <util/result.h>
#include <wallet/coinselection.h>
#include <wallet/transaction.h>
#include <wallet/wallet.h>

#include <optional>

namespace wallet {
struct CRecipient;
/** Get the marginal bytes if spending the specified output from this transaction.
 * Use CoinControl to determine whether to expect signature grinding when calculating the size of the input spend. */
int CalculateMaximumSignedInputSize(const CTxOut& txout, const CWallet* pwallet, const CCoinControl* coin_control = nullptr);
int CalculateMaximumSignedInputSize(const CTxOut& txout, const COutPoint outpoint, const SigningProvider* pwallet, const CCoinControl* coin_control = nullptr);
struct TxSize {
    int64_t vsize{-1};
    int64_t weight{-1};
};

/** Calculate the size of the transaction using CoinControl to determine
 * whether to expect signature grinding when calculating the size of the input spend. */
TxSize CalculateMaximumSignedTxSize(const CTransaction& tx, const CWallet* wallet, const std::vector<CTxOut>& txouts, const CCoinControl* coin_control = nullptr);
TxSize CalculateMaximumSignedTxSize(const CTransaction& tx, const CWallet* wallet, const CCoinControl* coin_control = nullptr);

/**
 * COutputs available for spending, stored by OutputType.
 * This struct is really just a wrapper around OutputType vectors with a convenient
 * method for concatenating and returning all COutputs as one vector.
 *
 * Size(), Clear(), Erase(), Shuffle(), and Add() methods are implemented to
 * allow easy interaction with the struct.
 */
struct CoinsResult {
    std::map<OutputType, std::vector<COutput>> coins;

    /** Concatenate and return all COutputs as one vector */
    std::vector<COutput> All() const;

    /** The following methods are provided so that CoinsResult can mimic a vector,
     * i.e., methods can work with individual OutputType vectors or on the entire object */
    size_t Size() const;
    void Clear();
    void Erase(std::set<COutPoint>& preset_coins);
    void Shuffle(FastRandomContext& rng_fast);
    void Add(OutputType type, const COutput& out);

    /** Sum of all available coins */
    // ELEMENTS: for each asset
    CAmountMap total_amount;
};

struct CoinFilterParams {
    // Outputs below the minimum amount will not get selected
    CAmount min_amount{1};
    // Outputs above the maximum amount will not get selected
    CAmount max_amount{MAX_MONEY};
    // Return outputs until the minimum sum amount is covered
    CAmount min_sum_amount{MAX_MONEY};
    // Maximum number of outputs that can be returned
    uint64_t max_count{0};
    // By default, return only spendable outputs
    bool only_spendable{true};
    // By default, do not include immature coinbase outputs
    bool include_immature_coinbase{false};
    // ELEMENTS: by default include all assets
    std::optional<CAsset> asset;
};

/**
 * Populate the CoinsResult struct with vectors of available COutputs, organized by OutputType.
 */
CoinsResult AvailableCoins(const CWallet& wallet,
                           const CCoinControl* coinControl = nullptr,
                           std::optional<CFeeRate> feerate = std::nullopt,
                           const CoinFilterParams& params = {}) EXCLUSIVE_LOCKS_REQUIRED(wallet.cs_wallet);

/**
 * Wrapper function for AvailableCoins which skips the `feerate` and `CoinFilterParams::only_spendable` parameters. Use this function
 * to list all available coins (e.g. listunspent RPC) while not intending to fund a transaction.
 */
CoinsResult AvailableCoinsListUnspent(const CWallet& wallet, const CCoinControl* coinControl = nullptr, CoinFilterParams params = {}) EXCLUSIVE_LOCKS_REQUIRED(wallet.cs_wallet);

CAmountMap GetAvailableBalance(const CWallet& wallet, const CCoinControl* coinControl = nullptr);

/**
 * Find non-change parent output.
 */
const CTxOut& FindNonChangeParentOutput(const CWallet& wallet, const CTransaction& tx, int output) EXCLUSIVE_LOCKS_REQUIRED(wallet.cs_wallet);
const CTxOut& FindNonChangeParentOutput(const CWallet& wallet, const COutPoint& outpoint) EXCLUSIVE_LOCKS_REQUIRED(wallet.cs_wallet);

/**
 * Return list of available coins and locked coins grouped by non-change output address.
 */
std::map<CTxDestination, std::vector<COutput>> ListCoins(const CWallet& wallet);

std::vector<OutputGroup> GroupOutputs(const CWallet& wallet, const std::vector<COutput>& outputs, const CoinSelectionParams& coin_sel_params, const CoinEligibilityFilter& filter, bool positive_only);
/**
 * Attempt to find a valid input set that preserves privacy by not mixing OutputTypes.
 * `ChooseSelectionResult()` will be called on each OutputType individually and the best
 * the solution (according to the waste metric) will be chosen. If a valid input cannot be found from any
 * single OutputType, fallback to running `ChooseSelectionResult()` over all available coins.
 *
 * param@[in]  wallet                    The wallet which provides solving data for the coins
 * param@[in]  nTargetValue              The target value
 * param@[in]  eligilibity_filter        A filter containing rules for which coins are allowed to be included in this selection
 * param@[in]  available_coins           The struct of coins, organized by OutputType, available for selection prior to filtering
 * param@[in]  coin_selection_params     Parameters for the coin selection
 * param@[in]  allow_mixed_output_types  Relax restriction that SelectionResults must be of the same OutputType
 * returns                               If successful, a SelectionResult containing the input set
 *                                       If failed, a nullopt
 */
std::optional<SelectionResult> AttemptSelection(const CWallet& wallet, const CAmountMap& mapTargetValue, const CoinEligibilityFilter& eligibility_filter, const CoinsResult& available_coins,
                        const CoinSelectionParams& coin_selection_params, bool allow_mixed_output_types);

/**
 * Attempt to find a valid input set that meets the provided eligibility filter and target.
 * Multiple coin selection algorithms will be run and the input set that produces the least waste
 * (according to the waste metric) will be chosen.
 *
 * param@[in]  wallet                    The wallet which provides solving data for the coins
 * param@[in]  nTargetValue              The target value
 * param@[in]  eligilibity_filter        A filter containing rules for which coins are allowed to be included in this selection
 * param@[in]  available_coins           The struct of coins, organized by OutputType, available for selection prior to filtering
 * param@[in]  coin_selection_params     Parameters for the coin selection
 * returns                               If successful, a SelectionResult containing the input set
 *                                       If failed, a nullopt
 */
std::optional<SelectionResult> ChooseSelectionResult(const CWallet& wallet, const CAmountMap& mapTargetValue, const CoinEligibilityFilter& eligibility_filter, const std::vector<COutput>& available_coins,
                        const CoinSelectionParams& coin_selection_params);

// User manually selected inputs that must be part of the transaction
struct PreSelectedInputs
{
    std::set<COutput> coins;
    // If subtract fee from outputs is disabled, the 'total_amount'
    // will be the sum of each output effective value
    // instead of the sum of the outputs amount
    CAmountMap total_amount{{::policyAsset, 0}};

    void Insert(const COutput& output, bool subtract_fee_outputs)
    {
        if (subtract_fee_outputs) {
            total_amount[output.asset] += output.value;
        } else {
            total_amount[output.asset] += output.GetEffectiveValue();
        }
        coins.insert(output);
    }
};

/**
 * Fetch and validate coin control selected inputs.
 * Coins could be internal (from the wallet) or external.
*/
util::Result<PreSelectedInputs> FetchSelectedInputs(const CWallet& wallet, const CCoinControl& coin_control,
                                                    const CoinSelectionParams& coin_selection_params) EXCLUSIVE_LOCKS_REQUIRED(wallet.cs_wallet);

/**
 * Select a set of coins such that nTargetValue is met; never select unconfirmed coins if they are not ours
 * param@[in]   wallet                 The wallet which provides data necessary to spend the selected coins
 * param@[in]   available_coins        The struct of coins, organized by OutputType, available for selection prior to filtering
 * param@[in]   nTargetValue           The target value
 * param@[in]   coin_selection_params  Parameters for this coin selection such as feerates, whether to avoid partial spends,
 *                                     and whether to subtract the fee from the outputs.
 * returns                             If successful, a SelectionResult containing the selected coins
 *                                     If failed, a nullopt.
 */
std::optional<SelectionResult> AutomaticCoinSelection(const CWallet& wallet, CoinsResult& available_coins, const CAmountMap& mapTargetValue, const CCoinControl& coin_control,
                 const CoinSelectionParams& coin_selection_params) EXCLUSIVE_LOCKS_REQUIRED(wallet.cs_wallet);

/**
 * Select all coins from coin_control, and if coin_control 'm_allow_other_inputs=true', call 'AutomaticCoinSelection' to
 * select a set of coins such that nTargetValue - pre_set_inputs.total_amount is met.
 */
std::optional<SelectionResult> SelectCoins(const CWallet& wallet, CoinsResult& available_coins, const PreSelectedInputs& pre_set_inputs,
                                           const CAmountMap& mapTargetValue, const CCoinControl& coin_control,
                                           const CoinSelectionParams& coin_selection_params) EXCLUSIVE_LOCKS_REQUIRED(wallet.cs_wallet);

struct CreatedTransactionResult
{
    CTransactionRef tx;
    CAmount fee;
    FeeCalculation fee_calc;
    int change_pos;

    CreatedTransactionResult(CTransactionRef _tx, CAmount _fee, int _change_pos, const FeeCalculation& _fee_calc)
        : tx(_tx), fee(_fee), fee_calc(_fee_calc), change_pos(_change_pos) {}
};

/**
 * Create a new transaction paying the recipients with a set of coins
 * selected by SelectCoins(); Also create the change output, when needed
 * @note passing change_pos as -1 will result in setting a random position
 */
util::Result<CreatedTransactionResult> CreateTransaction(CWallet& wallet, const std::vector<CRecipient>& vecSend, int change_pos, const CCoinControl& coin_control, bool sign = true, BlindDetails* blind_details = nullptr, const IssuanceDetails* issuance_details = nullptr);

/**
 * Insert additional inputs into the transaction by
 * calling CreateTransaction();
 */
bool FundTransaction(CWallet& wallet, CMutableTransaction& tx, CAmount& nFeeRet, int& nChangePosInOut, bilingual_str& error, bool lockUnspents, const std::set<int>& setSubtractFeeFromOutputs, CCoinControl);
} // namespace wallet

#endif // BITCOIN_WALLET_SPEND_H
