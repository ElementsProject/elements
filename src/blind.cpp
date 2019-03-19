// Copyright (c) 2017-2019 The Elements Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <blind.h>

#include <hash.h>
#include <primitives/transaction.h>
#include <primitives/confidential.h>
#include <issuance.h>
#include <random.h>
#include <util.h>

static secp256k1_context* secp256k1_blind_context = NULL;

class Blind_ECC_Init {
public:
    Blind_ECC_Init() {
        assert(secp256k1_blind_context == NULL);

        secp256k1_context *ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);
        assert(ctx != NULL);

        secp256k1_blind_context = ctx;
    }

    ~Blind_ECC_Init() {
        secp256k1_context *ctx = secp256k1_blind_context;
        secp256k1_blind_context = NULL;

        if (ctx) {
            secp256k1_context_destroy(ctx);
        }
    }
};

static Blind_ECC_Init ecc_init_on_load;

bool UnblindConfidentialPair(const CKey& blinding_key, const CConfidentialValue& conf_value, const CConfidentialAsset& conf_asset, const CConfidentialNonce& nonce_commitment, const CScript& committedScript, const std::vector<unsigned char>& vchRangeproof, CAmount& amount_out, uint256& blinding_factor_out, CAsset& asset_out, uint256& asset_blinding_factor_out)
{
    if (!blinding_key.IsValid() || vchRangeproof.size() == 0) {
        return false;
    }
    CPubKey ephemeral_key(nonce_commitment.vchCommitment);
    if (nonce_commitment.vchCommitment.size() > 0 && !ephemeral_key.IsFullyValid()) {
        return false;
    }

    // ECDH or not depending on if nonce commitment is non-empty
    uint256 nonce;
    bool blank_nonce = false;
    if (nonce_commitment.vchCommitment.size() > 0) {
        nonce = blinding_key.ECDH(ephemeral_key);
        CSHA256().Write(nonce.begin(), 32).Finalize(nonce.begin());
    } else {
        // Use blinding key directly, and don't commit to a scriptpubkey
        // This is used for issuance inputs.
        blank_nonce = true;
        nonce = uint256(std::vector<unsigned char>(blinding_key.begin(), blinding_key.end()));
    }

    // API-prescribed sidechannel maximum size, though we only use 64 bytes
    unsigned char msg[4096] = {0};
    // 32 bytes of asset type, 32 bytes of asset blinding factor in sidechannel
    size_t msg_size = 64;

    // If value is unblinded, we don't support unblinding just the asset
    if (!conf_value.IsCommitment()) {
        return false;
    }

    // Valid asset commitment?
    secp256k1_generator observed_gen;
    if (conf_asset.IsCommitment()) {
        if (secp256k1_generator_parse(secp256k1_blind_context, &observed_gen, &conf_asset.vchCommitment[0]) != 1)
            return false;
    } else if (conf_asset.IsExplicit()) {
        if (secp256k1_generator_generate(secp256k1_blind_context, &observed_gen, conf_asset.GetAsset().begin()) != 1)
            return false;
    }

    // Valid value commitment?
    secp256k1_pedersen_commitment value_commit;
    if (secp256k1_pedersen_commitment_parse(secp256k1_blind_context, &value_commit, conf_value.vchCommitment.data()) != 1) {
        return false;
    }

    // Rewind rangeproof
    uint64_t min_value, max_value, amount;
    if (!secp256k1_rangeproof_rewind(secp256k1_blind_context, blinding_factor_out.begin(), &amount, msg, &msg_size, nonce.begin(), &min_value, &max_value, &value_commit, &vchRangeproof[0], vchRangeproof.size(), (committedScript.size() && !blank_nonce)? &committedScript.front(): NULL, blank_nonce ? 0 : committedScript.size(), &observed_gen)) {
        return false;
    }

    // Value sidechannel must be a transaction-valid amount (should be belt-and-suspenders check)
    if (amount > (uint64_t)MAX_MONEY || !MoneyRange((CAmount)amount)) {
        return false;
    }

    // Convienience pointers to starting point of each recovered 32 byte message
    unsigned char *asset_type = msg;
    unsigned char *asset_blinder = msg+32;

    // Asset sidechannel of asset type + asset blinder
    secp256k1_generator recalculated_gen;
    if (msg_size != 64 || secp256k1_generator_generate_blinded(secp256k1_blind_context, &recalculated_gen, asset_type, asset_blinder) != 1) {
        return false;
    }

    // Serialize both generators then compare
    unsigned char observed_generator[33];
    unsigned char derived_generator[33];
    secp256k1_generator_serialize(secp256k1_blind_context, observed_generator, &observed_gen);
    secp256k1_generator_serialize(secp256k1_blind_context, derived_generator, &recalculated_gen);
    if (memcmp(observed_generator, derived_generator, sizeof(observed_generator))) {
        return false;
    }

    amount_out = (CAmount)amount;
    asset_out = CAsset(std::vector<unsigned char>(asset_type, asset_type+32));
    asset_blinding_factor_out = uint256(std::vector<unsigned char>(asset_blinder, asset_blinder+32));
    return true;
}

// Create surjection proof
bool SurjectOutput(CTxOutWitness& txoutwit, const std::vector<secp256k1_fixed_asset_tag>& surjection_targets, const std::vector<secp256k1_generator>& target_asset_generators, const std::vector<uint256 >& target_asset_blinders, const std::vector<const unsigned char*> asset_blindptrs, const secp256k1_generator& output_asset_gen, const CAsset& asset)
{
    int ret;
    // 1 to 3 targets
    size_t nInputsToSelect = std::min((size_t)3, surjection_targets.size());
    unsigned char randseed[32];
    GetStrongRandBytes(randseed, 32);
    size_t input_index;
    secp256k1_surjectionproof proof;
    secp256k1_fixed_asset_tag tag;
    memcpy(&tag, asset.begin(), 32);
    // Find correlation between asset tag and listed input tags
    if (secp256k1_surjectionproof_initialize(secp256k1_blind_context, &proof, &input_index, &surjection_targets[0], surjection_targets.size(), nInputsToSelect, &tag, 100, randseed) == 0) {
        return false;
    }
    // Using the input chosen, build proof
    ret = secp256k1_surjectionproof_generate(secp256k1_blind_context, &proof, target_asset_generators.data(), target_asset_generators.size(), &output_asset_gen, input_index, target_asset_blinders[input_index].begin(), asset_blindptrs[asset_blindptrs.size()-1]);
    assert(ret == 1);
    // Double-check answer
    ret = secp256k1_surjectionproof_verify(secp256k1_blind_context, &proof, target_asset_generators.data(), target_asset_generators.size(), &output_asset_gen);
    assert(ret != 0);

    // Serialize into output witness structure
    size_t output_len = secp256k1_surjectionproof_serialized_size(secp256k1_blind_context, &proof);
    txoutwit.vchSurjectionproof.resize(output_len);
    secp256k1_surjectionproof_serialize(secp256k1_blind_context, &txoutwit.vchSurjectionproof[0], &output_len, &proof);
    assert(output_len == txoutwit.vchSurjectionproof.size());
    return true;
}

bool GenerateRangeproof(std::vector<unsigned char>& rangeproof, const std::vector<unsigned char*>& value_blindptrs, const uint256& nonce, const CAmount amount, const CScript& scriptPubKey, const secp256k1_pedersen_commitment& value_commit, const secp256k1_generator& gen, const CAsset& asset, std::vector<const unsigned char*>& asset_blindptrs)
{
    // Prep range proof
    size_t nRangeProofLen = 5134;
    rangeproof.resize(nRangeProofLen);

    // Compose sidechannel message to convey asset info (ID and asset blinds)
    unsigned char asset_message[64];
    memcpy(asset_message, asset.begin(), 32);
    memcpy(asset_message+32, asset_blindptrs[asset_blindptrs.size()-1], 32);

    // Sign rangeproof
    // If min_value is 0, scriptPubKey must be unspendable
    int res = secp256k1_rangeproof_sign(secp256k1_blind_context, rangeproof.data(), &nRangeProofLen, scriptPubKey.IsUnspendable() ? 0 : 1, &value_commit, value_blindptrs.back(), nonce.begin(), std::min(std::max((int)gArgs.GetArg("-ct_exponent", 0), -1),18), std::min(std::max((int)gArgs.GetArg("-ct_bits", 36), 1), 51), amount, asset_message, sizeof(asset_message), scriptPubKey.size() ? &scriptPubKey.front() : NULL, scriptPubKey.size(), &gen);
    rangeproof.resize(nRangeProofLen);
    return (res == 1);
}

void BlindAsset(CConfidentialAsset& conf_asset, secp256k1_generator& asset_gen, const CAsset& asset, const unsigned char* asset_blindptr)
{
    conf_asset.vchCommitment.resize(CConfidentialAsset::nCommittedSize);
    int ret = secp256k1_generator_generate_blinded(secp256k1_blind_context, &asset_gen, asset.begin(), asset_blindptr);
    assert(ret == 1);
    ret = secp256k1_generator_serialize(secp256k1_blind_context, conf_asset.vchCommitment.data(), &asset_gen);
    assert(ret != 0);
}

void CreateValueCommitment(CConfidentialValue& conf_value, secp256k1_pedersen_commitment& value_commit, const unsigned char* value_blindptr, const secp256k1_generator& asset_gen, const CAmount amount)
{
    int ret;
    conf_value.vchCommitment.resize(CConfidentialValue::nCommittedSize);
    ret = secp256k1_pedersen_commit(secp256k1_blind_context, &value_commit, value_blindptr, amount, &asset_gen);
    assert(ret != 0);
    secp256k1_pedersen_commitment_serialize(secp256k1_blind_context, conf_value.vchCommitment.data(), &value_commit);
    assert(conf_value.IsValid());
}

size_t GetNumIssuances(const CTransaction& tx)
{
    unsigned int num_issuances = 0;
    for (unsigned int i = 0; i < tx.vin.size(); i++) {
        if (!tx.vin[i].assetIssuance.IsNull()) {
            if (!tx.vin[i].assetIssuance.nAmount.IsNull()) {
                num_issuances++;
            }
            if (!tx.vin[i].assetIssuance.nInflationKeys.IsNull()) {
                num_issuances++;
            }
        }
    }
    return num_issuances;
}

