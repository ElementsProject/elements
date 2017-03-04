#ifndef BITCOIN_BLIND_H_
#define BITCOIN_BLIND_H_ 1

#include "key.h"
#include "pubkey.h"
#include "primitives/transaction.h"

bool UnblindOutput(const CKey& blinding_key, const CTxOut& txout, CAmount& amount_out, uint256& blinding_factor_out, CAssetID& asset_id_out, uint256& asset_blinding_factor_out);

/* Returns the number of ouputs that were successfully blinded.
 * In many cases a `0` can be fixed by adding an additional output.
 * @param[in]   input_blinding_factors - A vector of input blinding factors that will be used to create the balanced output blinding factors
 * @param[in]   input_asset_blinding_factors - A vector of input asset blinding factors that will be used to create the balanced output blinding factors
 * @param[in]   input_asset_ids - the asset ids of each corresponding input
 * @param[in]   input_amounts - the unblinded amounts of each input. This is required only for calls with already-blinded inputs for sum calculations.
 * @param[in/out]   output_blinding_factors - A vector of blinding factors. Null uint256 values are used to signal to the callee that a new blinding is needed. New blinds then replace the blank values.
 * @param[in/out]   output_asset_blinding_factors - A vector of asset blinding factors. Null uint256 values are used to signal to the callee that a new blinding is needed. New blinds then replace the blank values. These values being blind/unblind should correspond to output_blinding_factors.
 * @param[in]   output_pubkeys - If non-null, these pubkeys will be used in conjunction with the non-null passed in output blinding factors.
 * @param[in/out]   tx - The transaction to be modified.
 */
int BlindOutputs(std::vector<uint256 >& input_blinding_factors, const std::vector<uint256 >& input_asset_blinding_factors, const std::vector<CAssetID >& input_asset_ids, const std::vector<CAmount >& input_amounts, std::vector<uint256 >& output_blinding_factors, std::vector<uint256 >& output_asset_blinding_factors, const std::vector<CPubKey>& output_pubkeys, CMutableTransaction& tx);

#endif
