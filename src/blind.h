// Copyright (c) 2017-2019 The Elements Core developers
// // Distributed under the MIT software license, see the accompanying
// // file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_BLIND_H
#define BITCOIN_BLIND_H

#include <key.h>
#include <pubkey.h>
#include <primitives/transaction.h>
#include <primitives/confidential.h>

#include <secp256k1.h>
#include <secp256k1_rangeproof.h>
#include <secp256k1_surjectionproof.h>

//! ELEMENTS:
// 52-bit rangeproof size
static const size_t DEFAULT_RANGEPROOF_SIZE = 4174;
// 64-bit rangeproof size
static const size_t MAX_RANGEPROOF_SIZE = 5126;
// 3-input ASP size
static const size_t DEFAULT_SURJECTIONPROOF_SIZE = 135;
// 32 bytes of asset type, 32 bytes of asset blinding factor in sidechannel
static const size_t SIDECHANNEL_MSG_SIZE = 64;
// Maximum number of inputs to select for surjection proof
static const size_t MAX_SURJECTION_TARGETS = 3;

// Blinding context
extern secp256k1_context* secp256k1_blind_context;

/*
 * Verify a pair of confidential asset and value, given the blinding factors for both.
 * Unlike UnblindConfidentialPair, this does _not_ require the recipient's blinding
 * key, but it _does_ require the blinding factors be provided (rather than extracting
 * them from the rangeproof.)
*/
bool VerifyConfidentialPair(const CConfidentialValue& conf_value, const CConfidentialAsset& conf_asset, const CAmount& claimed_value, const CAsset& claimed_asset, const uint256& value_blinding_factor, const uint256& asset_blinding_factor);

/*
 * Unblind a pair of confidential asset and value.
 * Note that unblinded data will only be outputted if *BOTH* asset and value could be unblinded.
 *
 * blinding_key is used to create the nonce to rewind the rangeproof in conjunction with the nNonce commitment. In the case of a 0-length nNonce, the blinding key is directly used as the nonce.
 * Currently there is only a sidechannel message in the rangeproof so a valid rangeproof must
 * be included in the pair to recover value and asset data.
 */
bool UnblindConfidentialPair(const CKey& blinding_key, const CConfidentialValue& conf_value, const CConfidentialAsset& conf_asset, const CConfidentialNonce& nonce_commitment, const CScript& committedScript, const std::vector<unsigned char>& vchRangeproof, CAmount& amount_out, uint256& blinding_factor_out, CAsset& asset_out, uint256& asset_blinding_factor_out);

bool GenerateRangeproof(std::vector<unsigned char>& rangeproof, const std::vector<unsigned char*>& value_blindptrs, const uint256& nonce, const CAmount amount, const CScript& scriptPubKey, const secp256k1_pedersen_commitment& value_commit, const secp256k1_generator& gen, const CAsset& asset, std::vector<const unsigned char*>& asset_blindptrs);

bool SurjectOutput(CTxOutWitness& txoutwit, const std::vector<secp256k1_fixed_asset_tag>& surjection_targets, const std::vector<secp256k1_generator>& target_asset_generators, const std::vector<uint256 >& target_asset_blinders, const std::vector<const unsigned char*> asset_blindptrs, const secp256k1_generator& output_asset_gen, const CAsset& asset);

uint256 GenerateOutputRangeproofNonce(CTxOut& out, const CPubKey output_pubkey);

void BlindAsset(CConfidentialAsset& conf_asset, secp256k1_generator& asset_gen, const CAsset& asset, const unsigned char* asset_blindptr);

void CreateValueCommitment(CConfidentialValue& conf_value, secp256k1_pedersen_commitment& value_commit, const unsigned char* value_blindptr, const secp256k1_generator& asset_gen, const CAmount amount);

/* Returns the number of outputs that were successfully blinded.
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
 * @param[in] auxiliary_generators - a list of generators to create surjection proofs when inputs are not owned by caller. Passing in non-empty elements results in ignoring of other input arguments for that index
 */
int BlindTransaction(std::vector<uint256 >& input_value_blinding_factors, const std::vector<uint256 >& input_asset_blinding_factors, const std::vector<CAsset >& input_assets, const std::vector<CAmount >& input_amounts, std::vector<uint256 >& out_val_blind_factors, std::vector<uint256 >& out_asset_blind_factors, const std::vector<CPubKey>& output_pubkeys, const std::vector<CKey>& issuance_blinding_privkey, const std::vector<CKey>& token_blinding_privkey, CMutableTransaction& tx, std::vector<std::vector<unsigned char> >* auxiliary_generators = nullptr);

/*
 * Extract pubkeys from nonce commitment placeholders, fill out vector of blank output blinding data
 */
void RawFillBlinds(CMutableTransaction& tx, std::vector<uint256>& output_value_blinds, std::vector<uint256>& output_asset_blinds, std::vector<CPubKey>& output_pubkeys);

#endif //BITCOIN_BLIND_H
