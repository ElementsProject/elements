#ifndef BITCOIN_BLIND_H_
#define BITCOIN_BLIND_H_ 1

#include "key.h"
#include "pubkey.h"
#include "primitives/transaction.h"

#include <secp256k1.h>
#include <secp256k1_rangeproof.h>
#include <secp256k1_surjectionproof.h>

bool GenerateRangeproof(std::vector<unsigned char>& vchRangeproof, const std::vector<unsigned char*>& blindptrs, const uint256& nonce, const CAmount amount, const CScript& scriptPubKey, const secp256k1_pedersen_commitment& commit, const secp256k1_generator& gen, const CAsset& asset, std::vector<const unsigned char*>& assetblindptrs);

bool SurjectOutput(CTxOutWitness& txoutwit, const std::vector<secp256k1_fixed_asset_tag>& inputAssets, const std::vector<secp256k1_generator>& inputAssetGenerators, const std::vector<uint256 >& input_asset_blinding_factors, const std::vector<const unsigned char*> assetblindptrs, const secp256k1_generator& gen, const CAsset& asset);

uint256 GenerateOutputRangeproofNonce(CTxOut& out, const CPubKey output_pubkey);

void BlindAsset(CConfidentialAsset& confAsset, secp256k1_generator& gen, const CAsset& asset, const unsigned char* assetblindptr);

void CreateValueCommitment(CConfidentialValue& value, secp256k1_pedersen_commitment& commit, const unsigned char* blindptr, const secp256k1_generator& gen, const CAmount amount);

/*
 * blinding_key is used to create the nonce to rewind the rangeproof in conjunction with the nNonce commitment. In the case of a 0-length nNonce, the blinding key is directly used as the nonce.
 * Currently there is only a sidechannel message in the rangeproof so a valid rangeproof must
 * be included in the pair to recover value and asset data.
 */
bool UnblindConfidentialPair(const CKey& blinding_key, const CConfidentialValue& value, const CConfidentialAsset& asset, const CConfidentialNonce& nNonce, const CScript& committedScript, const std::vector<unsigned char>& vchRangeproof, CAmount& amount_out, uint256& blinding_factor_out, CAsset& asset_out, uint256& asset_blinding_factor_out);

/* Returns the number of ouputs that were successfully blinded.
 * In many cases a `0` can be fixed by adding an additional output.
 * @param[in]   input_blinding_factors - A vector of input blinding factors that will be used to create the balanced output blinding factors
 * @param[in]   input_asset_blinding_factors - A vector of input asset blinding factors that will be used to create the balanced output blinding factors
 * @param[in]   input_assets - the asset of each corresponding input
 * @param[in]   input_amounts - the unblinded amounts of each input. Required for owned blinded inputs
 * @param[in/out]   output_blinding_factors - A vector of blinding factors. New blinding factors will replace these values.
 * @param[in/out]   output_asset_blinding_factors - A vector of asset blinding factors. New blinding factors will replace these values.
 * @param[in]   output_pubkeys - If valid, corresponding output must be unblinded, and will result in fully blinded output, modifying the output blinding arguments as well.
 * @param[in]   vBlindIssuanceAsset - List of keys to use as nonces for issuance asset blinding.
 * @param[in]   vBlindIssuanceToken - List of keys to use as nonces for issuance token blinding.
 * @param[in/out]   tx - The transaction to be modified.
 * @param[in] auxiliary_generators - a list of generators to create surjection proofs when inputs are not owned by caller. Passing in non-empty ocean results in ignoring of other input arguments for that index
 */
int BlindTransaction(std::vector<uint256 >& input_blinding_factors, const std::vector<uint256 >& input_asset_blinding_factors, const std::vector<CAsset >& input_assets, const std::vector<CAmount >& input_amounts, std::vector<uint256 >& output_blinding_factors, std::vector<uint256 >& output_asset_blinding_factors, const std::vector<CPubKey>& output_pubkeys, const std::vector<CKey>& vBlindIssuanceAsset, const std::vector<CKey>& vBlindIssuanceToken, CMutableTransaction& tx, std::vector<std::vector<unsigned char> >* auxiliary_generators = NULL);

#endif
