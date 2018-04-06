#include "blind.h"

#include "hash.h"
#include "primitives/transaction.h"
#include "random.h"
#include "util.h"
#include "issuance.h"

#include <secp256k1.h>
#include <secp256k1_rangeproof.h>
#include <secp256k1_surjectionproof.h>

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

bool UnblindConfidentialPair(const CKey &key, const CConfidentialValue& confValue, const CConfidentialAsset& confAsset, const CConfidentialNonce& nNonce, const CScript& committedScript, const std::vector<unsigned char>& vchRangeproof, CAmount& amount_out, uint256& blinding_factor_out, CAsset& asset_out, uint256& asset_blinding_factor_out)
{
    if (!key.IsValid() || vchRangeproof.size() == 0) {
        return false;
    }
    CPubKey ephemeral_key(nNonce.vchCommitment);
    if (nNonce.vchCommitment.size() > 0 && !ephemeral_key.IsValid()) {
        return false;
    }

    // ECDH or not depending on if nonce commitment is non-empty
    uint256 nonce;
    bool fBlankNonce = false;
    if (nNonce.vchCommitment.size() > 0) {
        nonce = key.ECDH(ephemeral_key);
        CSHA256().Write(nonce.begin(), 32).Finalize(nonce.begin());
    } else {
        // Use blinding key directly, and don't commit to a scriptpubkey
        fBlankNonce = true;
        nonce = uint256(std::vector<unsigned char>(key.begin(), key.end()));
    }
    unsigned char msg[4096];
    size_t msg_size = 64;
    uint64_t min_value, max_value, amount;
    secp256k1_pedersen_commitment commit;
    if (!confValue.IsCommitment()) {
        return false;
    }

    secp256k1_generator gen;
    if (confAsset.IsCommitment()) {
        if (secp256k1_generator_parse(secp256k1_blind_context, &gen, &confAsset.vchCommitment[0]) != 1)
            return false;
    }
    else if (confAsset.IsExplicit()) {
        if (secp256k1_generator_generate(secp256k1_blind_context, &gen, confAsset.GetAsset().begin()) != 1)
            return false;
    }

    if (secp256k1_pedersen_commitment_parse(secp256k1_blind_context, &commit, &confValue.vchCommitment[0]) != 1)
        return false;
    int res = secp256k1_rangeproof_rewind(secp256k1_blind_context, blinding_factor_out.begin(), &amount, msg, &msg_size, nonce.begin(), &min_value, &max_value, &commit, &vchRangeproof[0], vchRangeproof.size(), (committedScript.size() && !fBlankNonce)? &committedScript.front(): NULL, fBlankNonce ? 0 : committedScript.size(), &gen);
    secp256k1_generator recoveredGen;

    if (!res || amount > (uint64_t)MAX_MONEY || !MoneyRange((CAmount)amount) || msg_size != 64 || secp256k1_generator_generate_blinded(secp256k1_blind_context, &recoveredGen, msg+32, msg+64) != 1 || !memcmp(&gen, &recoveredGen, 33)) {
        amount_out = 0;
        blinding_factor_out = uint256();
        asset_out.SetNull();
        asset_blinding_factor_out = uint256();
        return false;
    } else {
        amount_out = (CAmount)amount;
        asset_out = CAsset(std::vector<unsigned char>(msg, msg+32));
        asset_blinding_factor_out = uint256(std::vector<unsigned char>(msg+32, msg+64));
        return true;
    }
}

// Create surjection proof
bool SurjectOutput(CTxOutWitness& txoutwit, const std::vector<secp256k1_fixed_asset_tag>& surjectionTargets, const std::vector<secp256k1_generator>& targetAssetGenerators, const std::vector<uint256 >& targetAssetBlinders, const std::vector<const unsigned char*> assetblindptrs, const secp256k1_generator& gen, const CAsset& asset)
{
    int ret;
    size_t nInputsToSelect = std::min((size_t)3, surjectionTargets.size());
    unsigned char randseed[32];
    GetRandBytes(randseed, 32);
    size_t input_index;
    secp256k1_surjectionproof proof;
    secp256k1_fixed_asset_tag tag;
    memcpy(&tag, asset.begin(), 32);
    if (secp256k1_surjectionproof_initialize(secp256k1_blind_context, &proof, &input_index, &surjectionTargets[0], surjectionTargets.size(), nInputsToSelect, &tag, 100, randseed) == 0) {
        return false;
    }
    ret = secp256k1_surjectionproof_generate(secp256k1_blind_context, &proof, &targetAssetGenerators[0], targetAssetGenerators.size(), &gen, input_index, targetAssetBlinders[input_index].begin(), assetblindptrs[assetblindptrs.size()-1]);
    assert(ret == 1);
    ret = secp256k1_surjectionproof_verify(secp256k1_blind_context, &proof, &targetAssetGenerators[0], targetAssetGenerators.size(), &gen);
    assert(ret != 0);

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

bool GenerateRangeproof(std::vector<unsigned char>& vchRangeproof, const std::vector<unsigned char*>& blindptrs, const uint256& nonce, const CAmount amount, const CScript& scriptPubKey, const secp256k1_pedersen_commitment& commit, const secp256k1_generator& gen, const CAsset& asset, std::vector<const unsigned char*>& assetblindptrs)
{
    // Prep range proof
    size_t nRangeProofLen = 5134;
    // TODO: smarter min_value selection
    vchRangeproof.resize(nRangeProofLen);

    // Compose sidechannel message to convey asset info (ID and asset blinds)
    unsigned char assetsMessage[64];
    memcpy(assetsMessage, asset.begin(), 32);
    memcpy(assetsMessage+32, assetblindptrs[assetblindptrs.size()-1], 32);

    // Sign rangeproof
    // If min_value is 0, scriptPubKey must be unspendable
    int res = secp256k1_rangeproof_sign(secp256k1_blind_context, &vchRangeproof[0], &nRangeProofLen, scriptPubKey.IsUnspendable() ? 0 : 1, &commit, blindptrs.back(), nonce.begin(), std::min(std::max((int)GetArg("-ct_exponent", 0), -1),18), std::min(std::max((int)GetArg("-ct_bits", 32), 1), 51), amount, assetsMessage, sizeof(assetsMessage), scriptPubKey.size() ? &scriptPubKey.front() : NULL, scriptPubKey.size(), &gen);
    vchRangeproof.resize(nRangeProofLen);
    // TODO: do something smarter here
    return (res == 1);
}

void BlindAsset(CConfidentialAsset& confAsset, secp256k1_generator& gen, const CAsset& asset, const unsigned char* assetblindptr)
{
    confAsset.vchCommitment.resize(CConfidentialAsset::nCommittedSize);
    int ret = secp256k1_generator_generate_blinded(secp256k1_blind_context, &gen, asset.begin(), assetblindptr);
    assert(ret == 1);
    ret = secp256k1_generator_serialize(secp256k1_blind_context, &confAsset.vchCommitment[0], &gen);
    assert(ret != 0);
}

void CreateValueCommitment(CConfidentialValue& confValue, secp256k1_pedersen_commitment& commit, const unsigned char* blindptr, const secp256k1_generator& gen, const CAmount amount)
{
    int ret;
    confValue.vchCommitment.resize(CConfidentialValue::nCommittedSize);
    ret = secp256k1_pedersen_commit(secp256k1_blind_context, &commit, blindptr, amount, &gen);
    assert(ret != 0);
    secp256k1_pedersen_commitment_serialize(secp256k1_blind_context, &confValue.vchCommitment[0], &commit);
    assert(confValue.IsValid());
}

int BlindTransaction(std::vector<uint256 >& input_blinding_factors, const std::vector<uint256 >& input_asset_blinding_factors, const std::vector<CAsset >& input_assets, const std::vector<CAmount >& input_amounts, std::vector<uint256 >& output_blinding_factors, std::vector<uint256 >& output_asset_blinding_factors, const std::vector<CPubKey>& output_pubkeys, const std::vector<CKey>& vBlindIssuanceAsset, const std::vector<CKey>& vBlindIssuanceToken, CMutableTransaction& tx, std::vector<std::vector<unsigned char> >* auxiliary_generators)
{
    // Sanity check input data and output_pubkey size, clear other output data
    assert(tx.vout.size() >= output_pubkeys.size());
    assert(tx.vin.size() >= vBlindIssuanceAsset.size());
    assert(tx.vin.size() >= vBlindIssuanceToken.size());
    output_blinding_factors.clear();
    output_blinding_factors.resize(tx.vout.size());
    output_asset_blinding_factors.clear();
    output_asset_blinding_factors.resize(tx.vout.size());
    assert(tx.vin.size() == input_blinding_factors.size());
    assert(tx.vin.size() == input_asset_blinding_factors.size());
    assert(tx.vin.size() == input_assets.size());
    assert(tx.vin.size() == input_amounts.size());
    if (auxiliary_generators) {
        assert(auxiliary_generators->size() >= tx.vin.size());
    }

    std::vector<unsigned char*> blindptrs;
    std::vector<const unsigned char*> assetblindptrs;
    std::vector<uint64_t> blindedAmounts;
    blindptrs.reserve(tx.vout.size() + tx.vin.size());
    assetblindptrs.reserve(tx.vout.size() + tx.vin.size());

    int ret;
    int nBlindAttempts = 0, nIssuanceBlindAttempts = 0, nSuccessfullyBlinded = 0;

    //Surjection proof prep

    // Needed to surj init, only matches to output asset matters, rest can be garbage
    std::vector<secp256k1_fixed_asset_tag> surjectionTargets;

    // Needed to construct the proof itself. Generators must match final transaction to be valid
    std::vector<secp256k1_generator> targetAssetGenerators;
    surjectionTargets.resize(tx.vin.size()*3);
    targetAssetGenerators.resize(tx.vin.size()*3);

    // input_asset_blinding_factors is only for inputs, not for issuances(0 by def)
    // but we need to create surjection proofs against this list so we copy and insert 0's
    // where issuances occur.
    std::vector<uint256> targetAssetBlinders;

    size_t totalTargets = 0;
    for (size_t i = 0; i < tx.vin.size(); i++) {
        // For each input we either need the asset/blinds or the generator
        if (input_assets[i].IsNull()) {
            // If non-empty generator exists, parse
            if (auxiliary_generators) {
                // Parse generator here
                ret = secp256k1_generator_parse(secp256k1_blind_context, &targetAssetGenerators[totalTargets], &(*auxiliary_generators)[i][0]);
                if (ret != 1) {
                    return -1;
                }
            } else {
                return -1;
            }
        } else {
            ret = secp256k1_generator_generate_blinded(secp256k1_blind_context, &targetAssetGenerators[totalTargets], input_assets[i].begin(), input_asset_blinding_factors[i].begin());
            assert(ret == 1);
        }
        memcpy(&surjectionTargets[totalTargets], input_assets[i].begin(), 32);
        targetAssetBlinders.push_back(input_asset_blinding_factors[i]);
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
                bool assetToBlind = (vBlindIssuanceAsset.size() > i && vBlindIssuanceAsset[i].IsValid()) ? true : false;
                GenerateAssetEntropy(entropy, tx.vin[0].prevout, issuance.assetEntropy);
                CalculateAsset(asset, entropy);
                CalculateReissuanceToken(token, entropy, assetToBlind);
            } else {
                CalculateAsset(asset, issuance.assetEntropy);
            }

            if (!issuance.nAmount.IsNull()) {
                memcpy(&surjectionTargets[totalTargets], asset.begin(), 32);
                ret = secp256k1_generator_generate(secp256k1_blind_context, &targetAssetGenerators[totalTargets], asset.begin());
                assert(ret != 0);
                // Issuance asset cannot be blinded by definition
                targetAssetBlinders.push_back(uint256());
                totalTargets++;
            }
            if (!issuance.nInflationKeys.IsNull()) {
                assert(!token.IsNull());
                memcpy(&surjectionTargets[totalTargets], token.begin(), 32);
                ret = secp256k1_generator_generate(secp256k1_blind_context, &targetAssetGenerators[totalTargets], token.begin());
                assert(ret != 0);
                // Issuance asset cannot be blinded by definition
                targetAssetBlinders.push_back(uint256());
                totalTargets++;
            }
        }
    }

    if (auxiliary_generators) {
        // Process any additional targets from auxiliary_generators
        // we know nothing about it other than the generator itself
        for (size_t i = tx.vin.size(); i < auxiliary_generators->size(); i++) {
            ret = secp256k1_generator_parse(secp256k1_blind_context, &targetAssetGenerators[totalTargets], &(*auxiliary_generators)[i][0]);
            if (ret != 1) {
                return -1;
            }
            memset(&surjectionTargets[totalTargets], 0, 32);
            targetAssetBlinders.push_back(uint256());
            totalTargets++;
        }
    }

    // Resize the target surjection lists to how many actually exist
    assert(totalTargets == targetAssetBlinders.size());
    surjectionTargets.resize(totalTargets);
    targetAssetGenerators.resize(totalTargets);

    //Total blinded inputs that you own (that you are balancing against)
    int nBlindsIn = 0;
    //Number of outputs and issuances to blind
    int nToBlind = 0;
    size_t txinwitsize = tx.wit.vtxinwit.size();
    size_t txoutwitsize = tx.wit.vtxoutwit.size();
    for (size_t nIn = 0; nIn < tx.vin.size(); nIn++) {
        if (!input_blinding_factors[nIn].IsNull() || !input_asset_blinding_factors[nIn].IsNull()) {
            if (input_amounts[nIn] < 0) {
                return -1;
            }
            blindptrs.push_back(input_blinding_factors[nIn].begin());
            assetblindptrs.push_back(input_asset_blinding_factors[nIn].begin());
            blindedAmounts.push_back(input_amounts[nIn]);
            nBlindsIn++;
        }

        // Count number of issuance pseudo-inputs to blind
        CAssetIssuance& issuance = tx.vin[nIn].assetIssuance;
        if (!issuance.IsNull()) {
            // Marked for blinding
            if (vBlindIssuanceAsset.size() > nIn && vBlindIssuanceAsset[nIn].IsValid()) {
                if(issuance.nAmount.IsExplicit() && (txinwitsize <= nIn || tx.wit.vtxinwit[nIn].vchIssuanceAmountRangeproof.empty())) {
                    nToBlind++;
                } else {
                    return -1;
                }
            }
            if (vBlindIssuanceToken.size() > nIn && vBlindIssuanceToken[nIn].IsValid()) {
                if(issuance.nInflationKeys.IsExplicit() && (txinwitsize <= nIn || tx.wit.vtxinwit[nIn].vchInflationKeysRangeproof.empty())) {
                    nToBlind++;
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
                   (txoutwitsize > nOut && !tx.wit.vtxoutwit[nOut].IsNull())
                        || tx.vout[nOut].IsFee()) {
                return -1;
            }
            nToBlind++;
         }
    }


    //Running total of newly blinded outputs
    static const unsigned char diff_zero[32] = {0};
    unsigned char blind[nToBlind][32];
    unsigned char asset_blind[nToBlind][32];
    secp256k1_pedersen_commitment commit;
    secp256k1_generator gen;
    CAsset asset;

    // First blind issuance pseudo-inputs
    for (size_t nIn = 0; nIn < tx.vin.size(); nIn++) {
        for (size_t nPseudo = 0; nPseudo < 2; nPseudo++) {
            if ((nPseudo == 0 && vBlindIssuanceAsset.size() > nIn && vBlindIssuanceAsset[nIn].IsValid()) ||
                    (nPseudo == 1 && vBlindIssuanceToken.size() > nIn && vBlindIssuanceToken[nIn].IsValid())) {
                nBlindAttempts++;
                nIssuanceBlindAttempts++;
                CAssetIssuance& issuance = tx.vin[nIn].assetIssuance;
                // First iteration does issuance asset, second inflation keys
                CConfidentialValue& confValue = nPseudo ? issuance.nInflationKeys : issuance.nAmount;
                if (confValue.IsNull()) {
                    continue;
                }
                CAmount amount = confValue.GetAmount();
                blindedAmounts.push_back(amount);

                // Derive the asset of the issuance asset/token
                if (issuance.assetBlindingNonce.IsNull()) {
					uint256 entropy;
                    GenerateAssetEntropy(entropy, tx.vin[nIn].prevout, issuance.assetEntropy);
                    if (nPseudo == 0) {
                        CalculateAsset(asset, entropy);
                    } else {
                        bool assetToBlind = (vBlindIssuanceAsset.size() > nIn && vBlindIssuanceAsset[nIn].IsValid()) ? true : false;
                        CalculateReissuanceToken(asset, entropy, assetToBlind);
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
                GetRandBytes(&blind[nBlindAttempts-1][0], 32);
                // Issuances are not asset-blinded
                memset(&asset_blind[nBlindAttempts-1][0], 0, 32);
                blindptrs.push_back(&blind[nBlindAttempts-1][0]);
                assetblindptrs.push_back(&asset_blind[nBlindAttempts-1][0]);

                if (nBlindAttempts == nToBlind) {
                    // All outputs we own are unblinded, we don't support this type of blinding
                    // though it is possible. No privacy gained here, incompatible with secp api
                    return nSuccessfullyBlinded;
                }

                if (tx.wit.vtxinwit.size() <= nIn) {
                    tx.wit.vtxinwit.resize(tx.vin.size());
                }
                CTxInWitness& txinwit = tx.wit.vtxinwit[nIn];

                // TODO Store the blinding factors of issuance

                // Create unblinded generator. We throw away all but `gen`
                CConfidentialAsset confAsset;
                BlindAsset(confAsset, gen, asset, assetblindptrs.back());

                // Create value commitment
                CreateValueCommitment(confValue, commit, blindptrs.back(), gen, amount);

                // nonce should just be blinding key
                uint256 nonce = nPseudo ? uint256(std::vector<unsigned char>(vBlindIssuanceToken[nIn].begin(), vBlindIssuanceToken[nIn].end())) : uint256(std::vector<unsigned char>(vBlindIssuanceAsset[nIn].begin(), vBlindIssuanceAsset[nIn].end()));

                // Generate rangeproof, no script committed for issuances
                bool rangeresult = GenerateRangeproof((nPseudo ? txinwit.vchInflationKeysRangeproof : txinwit.vchIssuanceAmountRangeproof), blindptrs, nonce, amount, CScript(), commit, gen, asset, assetblindptrs);
                assert(rangeresult);

                // Successfully blinded this issuance
                nSuccessfullyBlinded++;

            }
        }
    }

    // This section of code *only* deals with unblinded outputs
    // that we want to blind
    for (size_t nOut = 0; nOut < output_pubkeys.size(); nOut++) {
        if (output_pubkeys[nOut].IsFullyValid()) {
            CTxOut& out = tx.vout[nOut];
            nBlindAttempts++;
            CConfidentialAsset& confAsset = out.nAsset;
            CConfidentialValue& confValue = out.nValue;
            CAmount amount = confValue.GetAmount();
            asset = out.nAsset.GetAsset();
            blindedAmounts.push_back(confValue.GetAmount());

            GetRandBytes(&blind[nBlindAttempts-1][0], 32);
            GetRandBytes(&asset_blind[nBlindAttempts-1][0], 32);
            blindptrs.push_back(&blind[nBlindAttempts-1][0]);
            assetblindptrs.push_back(&asset_blind[nBlindAttempts-1][0]);

            // Last blinding factor r' is set as -(output's (vr + r') - input's (vr + r')).
            // Before modifying the transaction or return arguments we must
            // ensure the final blinding factor to not be its corresponding -vr (aka unblinded),
            // or 0, in the case of 0-value output, insisting on additional output to blind.
            if (nBlindAttempts == nToBlind) {

                // Can't successfully blind in this case, since -vr = r
                // This check is assuming blinds are generated randomly
                // Adversary would need to create all input blinds
                // therefore would already know all your summed output amount anyways.
                if (nBlindAttempts == 1 && nBlindsIn == 0) {
                    return nSuccessfullyBlinded;
                }

                // Generate value we intend to insert
                ret = secp256k1_pedersen_blind_generator_blind_sum(secp256k1_blind_context, &blindedAmounts[0], &assetblindptrs[0], &blindptrs[0], nBlindAttempts + nBlindsIn, nIssuanceBlindAttempts + nBlindsIn);
                assert(ret);

                // Resulting blinding factor can sometimes be 0
                // where inputs are the negations of each other
                // and the unblinded value of the output is 0.
                // e.g. 1 unblinded input to 2 blinded outputs,
                // then spent to 1 unblinded output. (vr + r')
                // becomes just (r'), if this is 0, we can just
                // abort and not blind and the math adds up.
                // Count as success(to signal caller that nothing wrong) and return early
                if (memcmp(diff_zero, &blind[nBlindAttempts-1][0], 32) == 0) {
                   return ++nSuccessfullyBlinded;
                }
            }

            if (tx.wit.vtxoutwit.size() <= nOut) {
                tx.wit.vtxoutwit.resize(tx.vout.size());
            }
            CTxOutWitness& txoutwit = tx.wit.vtxoutwit[nOut];

            output_blinding_factors[nOut] = uint256(std::vector<unsigned char>(blindptrs[blindptrs.size()-1], blindptrs[blindptrs.size()-1]+32));
            output_asset_blinding_factors[nOut] = uint256(std::vector<unsigned char>(assetblindptrs[assetblindptrs.size()-1], assetblindptrs[assetblindptrs.size()-1]+32));

            //Blind the asset ID
            BlindAsset(confAsset, gen, asset, assetblindptrs.back());

            // Create value commitment
            CreateValueCommitment(confValue, commit, blindptrs.back(), gen, amount);

            // Generate nonce for rewind by owner
            uint256 nonce = GenerateOutputRangeproofNonce(out, output_pubkeys[nOut]);

            // Generate rangeproof
            bool rangeresult = GenerateRangeproof(txoutwit.vchRangeproof, blindptrs, nonce, amount, out.scriptPubKey, commit, gen, asset, assetblindptrs);
            assert(rangeresult);

            // Create surjection proof for this output
            if (!SurjectOutput(txoutwit, surjectionTargets, targetAssetGenerators, targetAssetBlinders, assetblindptrs, gen, asset)) {
                continue;
            }

            // Successfully blinded this output
            nSuccessfullyBlinded++;
        }
    }

    return nSuccessfullyBlinded;
}
