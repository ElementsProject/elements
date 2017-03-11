#ifndef BITCOIN_BLIND_H_
#define BITCOIN_BLIND_H_ 1

#include "key.h"
#include "pubkey.h"
#include "primitives/transaction.h"

bool UnblindOutput(const CKey& blinding_key, const CTxOut& txout, const CTxOutWitness& txoutwit, CAmount& amount_out, uint256& blinding_factor_out, CAsset& asset_out, uint256& asset_blinding_factor_out);

/* Returns the number of ouputs that were successfully blinded.
 * In many cases a `0` can be fixed by adding an additional output.
 * @param[in]   input_blinding_factors - A vector of input blinding factors that will be used to create the balanced output blinding factors
 * @param[in]   input_asset_blinding_factors - A vector of input asset blinding factors that will be used to create the balanced output blinding factors
 * @param[in]   input_assets - the asset of each corresponding input
 * @param[in]   input_amounts - the unblinded amounts of each input. Required for owned blinded inputs
 * @param[in/out]   output_blinding_factors - A vector of blinding factors. New blinding factors will replace these values.
 * @param[in/out]   output_asset_blinding_factors - A vector of asset blinding factors. New blinding factors will replace these values.
 * @param[in]   output_pubkeys - If valid, corresponding output must be unblinded, and will result in fully blinded output, modifying the output blinding arguments as well.
 * @param[in/out]   tx - The transaction to be modified.
 * @param[in] auxiliary_generators - a list of generators to create surjection proofs when inputs are not owned by caller
 */
int BlindOutputs(std::vector<uint256 >& input_blinding_factors, const std::vector<uint256 >& input_asset_blinding_factors, const std::vector<CAsset >& input_assets, const std::vector<CAmount >& input_amounts, std::vector<uint256 >& output_blinding_factors, std::vector<uint256 >& output_asset_blinding_factors, const std::vector<CPubKey>& output_pubkeys, CMutableTransaction& tx, std::vector<std::vector<unsigned char> >* auxiliary_generators = NULL);

#endif
