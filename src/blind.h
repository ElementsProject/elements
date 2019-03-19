// Copyright (c) 2017-2019 The Elements Core developers
// // Distributed under the MIT software license, see the accompanying
// // file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_WALLET_BLIND_H
#define BITCOIN_WALLET_BLIND_H

#include <key.h>
#include <pubkey.h>
#include <primitives/transaction.h>
#include <primitives/confidential.h>

#include <secp256k1.h>
#include <secp256k1_rangeproof.h>
#include <secp256k1_surjectionproof.h>

//! ELEMENTS: 36-bit rangeproof size
static const size_t DEFAULT_RANGEPROOF_SIZE = 2893;

/*
 * Unblind a pair of confidental asset and value.
 * Note that unblinded data will only be outputted if *BOTH* asset and value could be unblinded.
 *
 * blinding_key is used to create the nonce to rewind the rangeproof in conjunction with the nNonce commitment. In the case of a 0-length nNonce, the blinding key is directly used as the nonce.
 * Currently there is only a sidechannel message in the rangeproof so a valid rangeproof must
 * be included in the pair to recover value and asset data.
 */
bool UnblindConfidentialPair(const CKey& blinding_key, const CConfidentialValue& conf_value, const CConfidentialAsset& conf_asset, const CConfidentialNonce& nonce_commitment, const CScript& committedScript, const std::vector<unsigned char>& vchRangeproof, CAmount& amount_out, uint256& blinding_factor_out, CAsset& asset_out, uint256& asset_blinding_factor_out);

bool GenerateRangeproof(std::vector<unsigned char>& rangeproof, const std::vector<unsigned char*>& value_blindptrs, const uint256& nonce, const CAmount amount, const CScript& scriptPubKey, const secp256k1_pedersen_commitment& value_commit, const secp256k1_generator& gen, const CAsset& asset, std::vector<const unsigned char*>& asset_blindptrs);

bool SurjectOutput(CTxOutWitness& txoutwit, const std::vector<secp256k1_fixed_asset_tag>& surjection_targets, const std::vector<secp256k1_generator>& target_asset_generators, const std::vector<uint256 >& target_asset_blinders, const std::vector<const unsigned char*> asset_blindptrs, const secp256k1_generator& output_asset_gen, const CAsset& asset);

void BlindAsset(CConfidentialAsset& conf_asset, secp256k1_generator& asset_gen, const CAsset& asset, const unsigned char* asset_blindptr);

void CreateValueCommitment(CConfidentialValue& conf_value, secp256k1_pedersen_commitment& value_commit, const unsigned char* value_blindptr, const secp256k1_generator& asset_gen, const CAmount amount);

#endif //BITCOIN_WALLET_BLIND_H
