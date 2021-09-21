// Copyright (c) 2020 The Elements Core developers
// // Distributed under the MIT software license, see the accompanying
// // file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_BLINDPSBT_H
#define BITCOIN_BLINDPSBT_H

#include <blind.h>
#include <key.h>
#include <pubkey.h>
#include <primitives/transaction.h>
#include <primitives/confidential.h>

#include <secp256k1.h>
#include <secp256k1_rangeproof.h>
#include <secp256k1_surjectionproof.h>

struct PartiallySignedTransaction;
struct PSBTOutput;

enum class BlindingStatus
{
    OK, //!< No error
    NEEDS_UTXOS,
    INVALID_ASSET,
    INVALID_ASSET_COMMITMENT,
    SCALAR_UNABLE,
    INVALID_BLINDER,
    ASP_UNABLE,
    NO_BLIND_OUTPUTS,
};

enum class BlindProofResult {
    OK,
    NOT_FULLY_BLINDED,
    MISSING_VALUE_PROOF,
    MISSING_ASSET_PROOF,
    INVALID_VALUE_PROOF,
    INVALID_ASSET_PROOF,
};

std::string GetBlindingStatusError(const BlindingStatus& status);

bool CreateAssetSurjectionProof(std::vector<unsigned char>& output_proof, const std::vector<secp256k1_fixed_asset_tag>& fixed_input_tags, const std::vector<secp256k1_generator>& ephemeral_input_tags, const std::vector<uint256>& input_asset_blinders, const uint256& output_asset_blinder, const secp256k1_generator& output_asset_tag, const CAsset& asset, size_t num_targets = MAX_SURJECTION_TARGETS);
uint256 GenerateRangeproofECDHKey(CPubKey& ephemeral_pubkey, const CPubKey blinding_pubkey);
bool CreateValueRangeProof(std::vector<unsigned char>& rangeproof, const uint256& value_blinder, const uint256& nonce, const CAmount amount, const CScript& scriptPubKey, const secp256k1_pedersen_commitment& value_commit, const secp256k1_generator& gen, const CAsset& asset, const uint256& asset_blinder);
void CreateAssetCommitment(CConfidentialAsset& conf_asset, secp256k1_generator& asset_gen, const CAsset& asset, const uint256& asset_blinder);
void CreateValueCommitment(CConfidentialValue& conf_value, secp256k1_pedersen_commitment& value_commit, const uint256& value_blinder, const secp256k1_generator& asset_gen, const CAmount amount);
BlindingStatus BlindPSBT(PartiallySignedTransaction& psbt, std::map<uint32_t, std::tuple<CAmount, CAsset, uint256, uint256>> our_input_data, std::map<uint32_t, std::pair<CKey, CKey>> our_issuances_to_blind);
BlindProofResult VerifyBlindProofs(const PSBTOutput& o);

#endif //BITCOIN_BLINDPSBT_H
