// Copyright (c) 2017-2019 The Elements Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <blind.h>

#include <hash.h>
#include <primitives/transaction.h>
#include <primitives/confidential.h>
#include <issuance.h>
#include <random.h>
#include <util/system.h>

secp256k1_context* secp256k1_blind_context = NULL;

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

bool VerifyConfidentialPair(const CConfidentialValue& conf_value, const CConfidentialAsset& conf_asset, const CAmount& claimed_value, const CAsset& claimed_asset, const uint256& value_blinding_factor, const uint256& asset_blinding_factor) {
    if (conf_value.IsNull() || conf_asset.IsNull() || claimed_asset.IsNull()) {
        return false;
    }

    if (conf_value.IsExplicit()) {
        // Match behavior of UnblindConfidentialPair
        return false;
    }
    if (conf_asset.IsExplicit() && conf_asset.GetAsset() != claimed_asset) {
        return false;
    }

    // Just to be safe
    if (!MoneyRange(claimed_value)) {
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

    const unsigned char *asset_type = claimed_asset.id.begin();
    const unsigned char *asset_blinder = asset_blinding_factor.begin();
    secp256k1_generator recalculated_gen;
    if (secp256k1_generator_generate_blinded(secp256k1_blind_context, &recalculated_gen, asset_type, asset_blinder) != 1) {
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

    const unsigned char *value_blinder = value_blinding_factor.begin();
    secp256k1_pedersen_commitment recalculated_commit;
    if(secp256k1_pedersen_commit(secp256k1_blind_context, &recalculated_commit, value_blinder, claimed_value, &observed_gen) != 1) {
        return false;
    }

    // Serialize both value commitments then compare
    unsigned char claimed_commitment[33];
    unsigned char derived_commitment[33];
    secp256k1_pedersen_commitment_serialize(secp256k1_blind_context, claimed_commitment, &value_commit);
    secp256k1_pedersen_commitment_serialize(secp256k1_blind_context, derived_commitment, &recalculated_commit);
    if (memcmp(claimed_commitment, derived_commitment, sizeof(claimed_commitment))) {
        return false;
    }

    return true;
}

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

    unsigned char msg[SIDECHANNEL_MSG_SIZE] = {0};
    size_t msg_size = SIDECHANNEL_MSG_SIZE;

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

    // Convenience pointers to starting point of each recovered 32 byte message
    unsigned char *asset_type = msg;
    unsigned char *asset_blinder = msg+32;

    // Asset sidechannel of asset type + asset blinder
    secp256k1_generator recalculated_gen;
    if (msg_size != SIDECHANNEL_MSG_SIZE || secp256k1_generator_generate_blinded(secp256k1_blind_context, &recalculated_gen, asset_type, asset_blinder) != 1) {
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
    size_t nInputsToSelect = std::min(MAX_SURJECTION_TARGETS, surjection_targets.size());
    unsigned char randseed[32];
    GetStrongRandBytes(randseed, 32);
    size_t input_index;
    secp256k1_surjectionproof proof;
    secp256k1_fixed_asset_tag tag;
    memcpy(&tag, asset.begin(), 32);
    // FIXME [hardfork] Elements currently cannot handle surjection proofs on transactions
    //  with more than 256 inputs. The Elements verification code will always try to give
    //  secp-zkp the complete list of inputs, and if this exceeds 256 then surjectionproof_verify
    //  will always return false, so there is no way to work around this situation at signing time
    if (surjection_targets.size() > SECP256K1_SURJECTIONPROOF_MAX_N_INPUTS) {
        // We must return false here to avoid triggering an assertion within
        // secp256k1_surjectionproof_initialize on the next line.
        return false;
    }
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

// Creates ECDH nonce commitment using ephemeral key and output_pubkey
uint256 GenerateOutputRangeproofNonce(CTxOut& out, const CPubKey output_pubkey)
{
    // Generate ephemeral key for ECDH nonce generation
    CKey ephemeral_key;
    ephemeral_key.MakeNewKey(true);
    CPubKey ephemeral_pubkey = ephemeral_key.GetPubKey();
    assert(ephemeral_pubkey.size() == CConfidentialNonce::nCommittedSize);
    out.nNonce.vchCommitment.resize(ephemeral_pubkey.size());
    memcpy(&out.nNonce.vchCommitment[0], &ephemeral_pubkey[0], ephemeral_pubkey.size());
    // Generate nonce
    uint256 nonce = ephemeral_key.ECDH(output_pubkey);
    CSHA256().Write(nonce.begin(), 32).Finalize(nonce.begin());
    return nonce;
}

bool GenerateRangeproof(std::vector<unsigned char>& rangeproof, const std::vector<unsigned char*>& value_blindptrs, const uint256& nonce, const CAmount amount, const CScript& scriptPubKey, const secp256k1_pedersen_commitment& value_commit, const secp256k1_generator& gen, const CAsset& asset, std::vector<const unsigned char*>& asset_blindptrs)
{
    // Prep range proof
    size_t nRangeProofLen = 5134;
    rangeproof.resize(nRangeProofLen);

    // Compose sidechannel message to convey asset info (ID and asset blinds)
    unsigned char asset_message[SIDECHANNEL_MSG_SIZE];
    memcpy(asset_message, asset.begin(), 32);
    memcpy(asset_message+32, asset_blindptrs[asset_blindptrs.size()-1], 32);

    // Sign rangeproof
    int ct_exponent = (int)gArgs.GetArg("-ct_exponent", 0);
    int ct_bits = (int)gArgs.GetArg("-ct_bits", 52);
    // If min_value is 0, scriptPubKey must be unspendable
    uint64_t min_value = scriptPubKey.IsUnspendable() ? 0 : 1;
    int res = secp256k1_rangeproof_sign(secp256k1_blind_context, rangeproof.data(), &nRangeProofLen, min_value, &value_commit, value_blindptrs.back(), nonce.begin(), ct_exponent, ct_bits, amount, asset_message, sizeof(asset_message), scriptPubKey.size() ? &scriptPubKey.front() : NULL, scriptPubKey.size(), &gen);
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

int BlindTransaction(std::vector<uint256 >& input_value_blinding_factors, const std::vector<uint256 >& input_asset_blinding_factors, const std::vector<CAsset >& input_assets, const std::vector<CAmount >& input_amounts, std::vector<uint256 >& out_val_blind_factors, std::vector<uint256 >& out_asset_blind_factors, const std::vector<CPubKey>& output_pubkeys, const std::vector<CKey>& issuance_blinding_privkey, const std::vector<CKey>& token_blinding_privkey, CMutableTransaction& tx, std::vector<std::vector<unsigned char> >* auxiliary_generators)
{
    // Sanity check input data and output_pubkey size, clear other output data
    assert(tx.vout.size() >= output_pubkeys.size());
    assert(tx.vin.size() >= issuance_blinding_privkey.size());
    assert(tx.vin.size() >= token_blinding_privkey.size());
    out_val_blind_factors.clear();
    out_val_blind_factors.resize(tx.vout.size());
    out_asset_blind_factors.clear();
    out_asset_blind_factors.resize(tx.vout.size());
    assert(tx.vin.size() == input_value_blinding_factors.size());
    assert(tx.vin.size() == input_asset_blinding_factors.size());
    assert(tx.vin.size() == input_assets.size());
    assert(tx.vin.size() == input_amounts.size());

    std::vector<unsigned char*> value_blindptrs;
    std::vector<const unsigned char*> asset_blindptrs;
    std::vector<uint64_t> blinded_amounts;
    value_blindptrs.reserve(tx.vout.size() + tx.vin.size());
    asset_blindptrs.reserve(tx.vout.size() + tx.vin.size());

    int ret;
    int num_blind_attempts = 0, num_issuance_blind_attempts = 0, num_blinded = 0;

    //Surjection proof prep

    // Needed to surj init, only matches to output asset matters, rest can be garbage
    std::vector<secp256k1_fixed_asset_tag> surjection_targets;

    // Needed to construct the proof itself. Generators must match final transaction to be valid
    std::vector<secp256k1_generator> target_asset_generators;

    // maxTargets is a strict upper-bound for the size of target vectors.
    // The vectors will be shrunk later according to final count of totalTargets
    size_t maxTargets = tx.vin.size()*3;
    if (auxiliary_generators) {
        assert(auxiliary_generators->size() >= tx.vin.size());
        maxTargets += auxiliary_generators->size() - tx.vin.size();
    }
    surjection_targets.resize(maxTargets);
    target_asset_generators.resize(maxTargets);

    // input_asset_blinding_factors is only for inputs, not for issuances(0 by def)
    // but we need to create surjection proofs against this list so we copy and insert 0's
    // where issuances occur.
    std::vector<uint256> target_asset_blinders;

    size_t totalTargets = 0;
    for (size_t i = 0; i < tx.vin.size(); i++) {
        // For each input we either need the asset/blinds or the generator
        if (input_assets[i].IsNull()) {
            // If non-empty generator exists, parse
            if (auxiliary_generators) {
                // Parse generator here
                ret = secp256k1_generator_parse(secp256k1_blind_context, &target_asset_generators[totalTargets], &(*auxiliary_generators)[i][0]);
                if (ret != 1) {
                    return -1;
                }
            } else {
                return -1;
            }
        } else {
            ret = secp256k1_generator_generate_blinded(secp256k1_blind_context, &target_asset_generators[totalTargets], input_assets[i].begin(), input_asset_blinding_factors[i].begin());
            if (ret != 1) {
                // Possibly invalid blinding factor provided by user.
                return -1;
            }
        }
        memcpy(&surjection_targets[totalTargets], input_assets[i].begin(), 32);
        target_asset_blinders.push_back(input_asset_blinding_factors[i]);
        totalTargets++;

        // Create target generators for issuances
        CAssetIssuance& issuance = tx.vin[i].assetIssuance;
        uint256 entropy;
        CAsset asset;
        CAsset token;
        if (!issuance.IsNull()) {
            if (issuance.nAmount.IsCommitment() || issuance.nInflationKeys.IsCommitment()) {
                return -1;
            }
            // New Issuance
            if (issuance.assetBlindingNonce.IsNull()) {
                bool blind_issuance = (token_blinding_privkey.size() > i && token_blinding_privkey[i].IsValid()) ? true : false;
                GenerateAssetEntropy(entropy, tx.vin[i].prevout, issuance.assetEntropy);
                CalculateAsset(asset, entropy);
                CalculateReissuanceToken(token, entropy, blind_issuance);
            } else {
                CalculateAsset(asset, issuance.assetEntropy);
            }

            if (!issuance.nAmount.IsNull()) {
                memcpy(&surjection_targets[totalTargets], asset.begin(), 32);
                ret = secp256k1_generator_generate(secp256k1_blind_context, &target_asset_generators[totalTargets], asset.begin());
                assert(ret != 0);
                // Issuance asset cannot be blinded by definition
                target_asset_blinders.push_back(uint256());
                totalTargets++;
            }
            if (!issuance.nInflationKeys.IsNull()) {
                assert(!token.IsNull());
                memcpy(&surjection_targets[totalTargets], token.begin(), 32);
                ret = secp256k1_generator_generate(secp256k1_blind_context, &target_asset_generators[totalTargets], token.begin());
                assert(ret != 0);
                // Issuance asset cannot be blinded by definition
                target_asset_blinders.push_back(uint256());
                totalTargets++;
            }
        }
    }

    if (auxiliary_generators) {
        // Process any additional targets from auxiliary_generators
        // we know nothing about it other than the generator itself
        for (size_t i = tx.vin.size(); i < auxiliary_generators->size(); i++) {
            ret = secp256k1_generator_parse(secp256k1_blind_context, &target_asset_generators[totalTargets], &(*auxiliary_generators)[i][0]);
            if (ret != 1) {
                return -1;
            }
            memset(&surjection_targets[totalTargets], 0, 32);
            target_asset_blinders.push_back(uint256());
            totalTargets++;
        }
    }

    // Resize the target surjection lists to how many actually exist
    assert(totalTargets == target_asset_blinders.size());
    surjection_targets.resize(totalTargets);
    target_asset_generators.resize(totalTargets);

    //Total blinded inputs that you own (that you are balancing against)
    int num_known_input_blinds = 0;
    //Number of outputs and issuances to blind
    int num_to_blind = 0;

    // Make sure witness lengths are correct
    tx.witness.vtxoutwit.resize(tx.vout.size());
    tx.witness.vtxinwit.resize(tx.vin.size());

    size_t txoutwitsize = tx.witness.vtxoutwit.size();
    for (size_t nIn = 0; nIn < tx.vin.size(); nIn++) {
        if (!input_value_blinding_factors[nIn].IsNull() || !input_asset_blinding_factors[nIn].IsNull()) {
            if (input_amounts[nIn] < 0) {
                return -1;
            }
            value_blindptrs.push_back(input_value_blinding_factors[nIn].begin());
            asset_blindptrs.push_back(input_asset_blinding_factors[nIn].begin());
            blinded_amounts.push_back(input_amounts[nIn]);
            num_known_input_blinds++;
        }

        // Count number of issuance pseudo-inputs to blind
        CAssetIssuance& issuance = tx.vin[nIn].assetIssuance;
        if (!issuance.IsNull()) {
            // Marked for blinding
            if (issuance_blinding_privkey.size() > nIn && issuance_blinding_privkey[nIn].IsValid()) {
                if(issuance.nAmount.IsExplicit() && tx.witness.vtxinwit[nIn].vchIssuanceAmountRangeproof.empty()) {
                    num_to_blind++;
                } else {
                    return -1;
                }
            }
            if (token_blinding_privkey.size() > nIn && token_blinding_privkey[nIn].IsValid()) {
                if(issuance.nInflationKeys.IsExplicit() && tx.witness.vtxinwit[nIn].vchInflationKeysRangeproof.empty()) {
                    num_to_blind++;
                } else {
                    return -1;
                }
            }
        }
    }

    for (size_t nOut = 0; nOut < output_pubkeys.size(); nOut++) {
        if (output_pubkeys[nOut].IsValid()) {
            // Keys must be valid and outputs completely unblinded or else call fails
            if (!output_pubkeys[nOut].IsFullyValid() ||
                (!tx.vout[nOut].nValue.IsExplicit() || !tx.vout[nOut].nAsset.IsExplicit()) ||
                   (txoutwitsize > nOut && !tx.witness.vtxoutwit[nOut].IsNull())
                        || tx.vout[nOut].IsFee()) {
                return -1;
            }
            num_to_blind++;
         }
    }


    //Running total of newly blinded outputs
    static const unsigned char diff_zero[32] = {0};
    assert(num_to_blind <= 10000); // More than 10k outputs? Stop spamming.
    unsigned char blind[10000][32];
    unsigned char asset_blind[10000][32];
    secp256k1_pedersen_commitment value_commit;
    secp256k1_generator asset_gen;
    CAsset asset;

    // First blind issuance pseudo-inputs
    for (size_t nIn = 0; nIn < tx.vin.size(); nIn++) {
        for (size_t nPseudo = 0; nPseudo < 2; nPseudo++) {
            if ((nPseudo == 0 && issuance_blinding_privkey.size() > nIn && issuance_blinding_privkey[nIn].IsValid()) ||
                    (nPseudo == 1 && token_blinding_privkey.size() > nIn && token_blinding_privkey[nIn].IsValid())) {
                num_blind_attempts++;
                num_issuance_blind_attempts++;
                CAssetIssuance& issuance = tx.vin[nIn].assetIssuance;
                // First iteration does issuance asset, second inflation keys
                CConfidentialValue& conf_value = nPseudo ? issuance.nInflationKeys : issuance.nAmount;
                if (conf_value.IsNull()) {
                    continue;
                }
                CAmount amount = conf_value.GetAmount();
                blinded_amounts.push_back(amount);

                // Derive the asset of the issuance asset/token
                if (issuance.assetBlindingNonce.IsNull()) {
                    uint256 entropy;
                    GenerateAssetEntropy(entropy, tx.vin[nIn].prevout, issuance.assetEntropy);
                    if (nPseudo == 0) {
                        CalculateAsset(asset, entropy);
                    } else {
                        bool blind_issuance = (token_blinding_privkey.size() > nIn && token_blinding_privkey[nIn].IsValid()) ? true : false;
                        CalculateReissuanceToken(asset, entropy, blind_issuance);
                    }
                } else {
                    if (nPseudo == 0) {
                        CalculateAsset(asset, issuance.assetEntropy);
                    } else {
                        // Re-issuance only has one pseudo-input maximum
                        continue;
                    }
                }

                // Fill out the value blinders and blank asset blinder
                GetStrongRandBytes(&blind[num_blind_attempts-1][0], 32);
                // Issuances are not asset-blinded
                memset(&asset_blind[num_blind_attempts-1][0], 0, 32);
                value_blindptrs.push_back(&blind[num_blind_attempts-1][0]);
                asset_blindptrs.push_back(&asset_blind[num_blind_attempts-1][0]);

                if (num_blind_attempts == num_to_blind) {
                    // All outputs we own are unblinded, we don't support this type of blinding
                    // though it is possible. No privacy gained here, incompatible with secp api
                    return num_blinded;
                }

                if (tx.witness.vtxinwit.size() <= nIn) {
                    tx.witness.vtxinwit.resize(tx.vin.size());
                }
                CTxInWitness& txinwit = tx.witness.vtxinwit[nIn];

                // Create unblinded generator. We throw away all but `asset_gen`
                CConfidentialAsset conf_asset;
                BlindAsset(conf_asset, asset_gen, asset, asset_blindptrs.back());

                // Create value commitment
                CreateValueCommitment(conf_value, value_commit, value_blindptrs.back(), asset_gen, amount);

                // nonce should just be blinding key
                uint256 nonce = nPseudo ? uint256(std::vector<unsigned char>(token_blinding_privkey[nIn].begin(), token_blinding_privkey[nIn].end())) : uint256(std::vector<unsigned char>(issuance_blinding_privkey[nIn].begin(), issuance_blinding_privkey[nIn].end()));

                // Generate rangeproof, no script committed for issuances
                bool rangeresult = GenerateRangeproof((nPseudo ? txinwit.vchInflationKeysRangeproof : txinwit.vchIssuanceAmountRangeproof), value_blindptrs, nonce, amount, CScript(), value_commit, asset_gen, asset, asset_blindptrs);
                assert(rangeresult);

                // Successfully blinded this issuance
                num_blinded++;
            }
        }
    }

    // This section of code *only* deals with unblinded outputs
    // that we want to blind
    for (size_t nOut = 0; nOut < output_pubkeys.size(); nOut++) {
        if (output_pubkeys[nOut].IsFullyValid()) {
            CTxOut& out = tx.vout[nOut];
            num_blind_attempts++;
            CConfidentialAsset& conf_asset = out.nAsset;
            CConfidentialValue& conf_value = out.nValue;
            CAmount amount = conf_value.GetAmount();
            asset = out.nAsset.GetAsset();
            blinded_amounts.push_back(conf_value.GetAmount());

            GetStrongRandBytes(&blind[num_blind_attempts-1][0], 32);
            GetStrongRandBytes(&asset_blind[num_blind_attempts-1][0], 32);
            value_blindptrs.push_back(&blind[num_blind_attempts-1][0]);
            asset_blindptrs.push_back(&asset_blind[num_blind_attempts-1][0]);

            // Last blinding factor r' is set as -(output's (vr + r') - input's (vr + r')).
            // Before modifying the transaction or return arguments we must
            // ensure the final blinding factor to not be its corresponding -vr (aka unblinded),
            // or 0, in the case of 0-value output, insisting on additional output to blind.
            if (num_blind_attempts == num_to_blind) {

                // Can't successfully blind in this case, since -vr = r
                // This check is assuming blinds are generated randomly
                // Adversary would need to create all input blinds
                // therefore would already know all your summed output amount anyways.
                if (num_blind_attempts == 1 && num_known_input_blinds == 0) {
                    return num_blinded;
                }

                // Generate value we intend to insert
                ret = secp256k1_pedersen_blind_generator_blind_sum(secp256k1_blind_context, &blinded_amounts[0], &asset_blindptrs[0], &value_blindptrs[0], num_blind_attempts + num_known_input_blinds, num_issuance_blind_attempts + num_known_input_blinds);
                if (!ret) {
                    // Possibly invalid blinding factor provided by user.
                    return -1;
                }

                // Resulting blinding factor can sometimes be 0
                // where inputs are the negations of each other
                // and the unblinded value of the output is 0.
                // e.g. 1 unblinded input to 2 blinded outputs,
                // then spent to 1 unblinded output. (vr + r')
                // becomes just (r'), if this is 0, we can just
                // abort and not blind and the math adds up.
                // Count as success(to signal caller that nothing wrong) and return early
                if (memcmp(diff_zero, &blind[num_blind_attempts-1][0], 32) == 0) {
                    return ++num_blinded;
                }
            }

            CTxOutWitness& txoutwit = tx.witness.vtxoutwit[nOut];

            out_val_blind_factors[nOut] = uint256(std::vector<unsigned char>(value_blindptrs[value_blindptrs.size()-1], value_blindptrs[value_blindptrs.size()-1]+32));
            out_asset_blind_factors[nOut] = uint256(std::vector<unsigned char>(asset_blindptrs[asset_blindptrs.size()-1], asset_blindptrs[asset_blindptrs.size()-1]+32));

            // Blind the asset ID
            BlindAsset(conf_asset, asset_gen, asset, asset_blindptrs.back());

            // Create value commitment
            CreateValueCommitment(conf_value, value_commit, value_blindptrs.back(), asset_gen, amount);

            // Generate nonce for rewind by owner
            uint256 nonce = GenerateOutputRangeproofNonce(out, output_pubkeys[nOut]);

            // Generate rangeproof
            bool rangeresult = GenerateRangeproof(txoutwit.vchRangeproof, value_blindptrs, nonce, amount, out.scriptPubKey, value_commit, asset_gen, asset, asset_blindptrs);
            assert(rangeresult);

            // Create surjection proof for this output
            if (!SurjectOutput(txoutwit, surjection_targets, target_asset_generators, target_asset_blinders, asset_blindptrs, asset_gen, asset)) {
                continue;
            }

            // Successfully blinded this output
            num_blinded++;
        }
    }

    return num_blinded;
}

void RawFillBlinds(CMutableTransaction& tx, std::vector<uint256>& output_value_blinds, std::vector<uint256>& output_asset_blinds, std::vector<CPubKey>& output_pubkeys) {
    for (size_t nOut = 0; nOut < tx.vout.size(); nOut++) {
        // Any place-holder blinding pubkeys are extracted
        if (tx.vout[nOut].nValue.IsExplicit()) {
            CPubKey pubkey(tx.vout[nOut].nNonce.vchCommitment);
            if (pubkey.IsFullyValid()) {
                output_pubkeys.push_back(pubkey);
            } else {
                output_pubkeys.push_back(CPubKey());
            }
        } else {
            output_pubkeys.push_back(CPubKey());
        }
        // No way to unblind anything, just fill out
        output_value_blinds.push_back(uint256());
        output_asset_blinds.push_back(uint256());
    }
    assert(output_pubkeys.size() == tx.vout.size());
    // We cannot unwind issuance inputs because there is no nonce placeholder for pubkeys
}
