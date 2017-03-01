#include "blind.h"

#include "hash.h"
#include "primitives/transaction.h"
#include "random.h"
#include "util.h"

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

bool UnblindOutput(const CKey &key, const CTxOut& txout, CAmount& amount_out, uint256& blinding_factor_out, uint256& asset_id_out, uint256& asset_blinding_factor_out)
{
    if (!key.IsValid()) {
        return false;
    }
    CPubKey ephemeral_key(txout.nValue.vchNonceCommitment);
    if (!ephemeral_key.IsValid()) {
        return false;
    }
    uint256 nonce = key.ECDH(ephemeral_key);
    CSHA256().Write(nonce.begin(), 32).Finalize(nonce.begin());
    unsigned char msg[4096];
    size_t msg_size = 64;
    uint64_t min_value, max_value, amount;
    secp256k1_pedersen_commitment commit;
    if (!txout.nAsset.IsAssetCommitment() || txout.nValue.IsAmount())
        return false;

    secp256k1_generator gen;
    if (secp256k1_generator_parse(secp256k1_blind_context, &gen, &txout.nAsset.vchAssetTag[0]) != 1)
        return false;
    if (secp256k1_pedersen_commitment_parse(secp256k1_blind_context, &commit, &txout.nValue.vchCommitment[0]) != 1)
        return false;
    int res = secp256k1_rangeproof_rewind(secp256k1_blind_context, blinding_factor_out.begin(), &amount, msg, &msg_size, nonce.begin(), &min_value, &max_value, &commit, &txout.nValue.vchRangeproof[0], txout.nValue.vchRangeproof.size(), txout.scriptPubKey.size() ? &txout.scriptPubKey.front() : NULL, txout.scriptPubKey.size(), &gen);
    secp256k1_generator recoveredGen;

    if (!res || amount > (uint64_t)MAX_MONEY || !MoneyRange((CAmount)amount) || msg_size != 64 || secp256k1_generator_generate_blinded(secp256k1_blind_context, &recoveredGen, msg+32, msg+64) != 1 || !memcmp(&gen, &recoveredGen, 33)) {
        amount_out = 0;
        blinding_factor_out = uint256();
        asset_id_out = uint256();
        asset_blinding_factor_out = uint256();
        return false;
    } else {
        amount_out = (CAmount)amount;
        asset_id_out = uint256(std::vector<unsigned char>(msg, msg+32));
        asset_blinding_factor_out = uint256(std::vector<unsigned char>(msg+32, msg+64));
        return true;
    }
}

bool BlindOutputs(std::vector<uint256 >& input_blinding_factors, const std::vector<uint256 >& input_asset_blinding_factors, const std::vector<uint256 >& input_asset_ids, const std::vector<CAmount >& input_amounts, std::vector<uint256 >& output_blinding_factors, std::vector<uint256 >& output_asset_blinding_factors, const std::vector<CPubKey>& output_pubkeys, CMutableTransaction& tx)
{
    assert(tx.vout.size() == output_blinding_factors.size());
    assert(tx.vout.size() == output_pubkeys.size());
    assert(tx.vout.size() == output_asset_blinding_factors.size());
    assert(tx.vin.size() == input_blinding_factors.size());
    assert(tx.vin.size() == input_asset_blinding_factors.size());
    assert(tx.vin.size() == input_asset_ids.size());
    assert(tx.vin.size() == input_amounts.size());

    std::vector<unsigned char*> blindptrs;
    std::vector<const unsigned char*> assetblindptrs;
    std::vector<uint64_t> blindedAmounts;
    blindptrs.reserve(tx.vout.size() + tx.vin.size());
    assetblindptrs.reserve(tx.vout.size() + tx.vin.size());

    int ret;

    //Surjection proof prep
    std::vector<secp256k1_fixed_asset_tag> inputAssetIDs;
    std::vector<secp256k1_generator> inputAssetGenerators;
    inputAssetIDs.resize(tx.vin.size());
    inputAssetGenerators.resize(tx.vin.size());
    for (size_t i = 0; i < tx.vin.size(); i++) {
        memcpy(&inputAssetIDs[i], input_asset_ids[i].begin(), 32);
        ret = secp256k1_generator_generate_blinded(secp256k1_blind_context, &inputAssetGenerators[i], input_asset_ids[i].begin(), input_asset_blinding_factors[i].begin());
        assert(ret == 1);
    }

    //Total blinded inputs
    int nBlindsIn = 0;
    for (size_t nIn = 0; nIn < tx.vin.size(); nIn++) {
        if (input_blinding_factors[nIn] != uint256()) {
            assert(input_blinding_factors[nIn].size() == 32);
            assert(input_asset_blinding_factors[nIn].size() == 32);
            blindptrs.push_back(input_blinding_factors[nIn].begin());
            assetblindptrs.push_back(input_asset_blinding_factors[nIn].begin());
            blindedAmounts.push_back(input_amounts[nIn]);
            nBlindsIn++;
        }
    }

    //Running total of blinded outputs
    int nBlindsOut = 0;
    //Number of outputs to newly blind
    int nToBlind = 0;
    for (size_t nOut = 0; nOut < tx.vout.size(); nOut++) {
        CTxOut& out = tx.vout[nOut];
        // Wallet only understands all-blinded or all-unblinded
        assert((output_blinding_factors[nOut] != uint256()) == !out.nValue.IsAmount());
        assert(out.nValue.IsAmount() == out.nAsset.IsAssetID() || out.nValue.IsAmount() == out.nAsset.IsAssetGeneration());
        assert(out.nAsset.IsAssetCommitment() == !out.nAsset.vchSurjectionproof.empty());
        if (output_blinding_factors[nOut] != uint256()) {
            assert(output_asset_blinding_factors[nOut] != uint256());
            blindptrs.push_back(output_blinding_factors[nOut].begin());
            assetblindptrs.push_back(output_asset_blinding_factors[nOut].begin());
            blindedAmounts.push_back(tx.vout[nOut].nValue.GetAmount());
            nBlindsOut++;

            //Assert-check surjective proofs
            secp256k1_generator gen;
            secp256k1_surjectionproof proof;
            assert(secp256k1_generator_parse(secp256k1_blind_context, &gen, &out.nAsset.vchAssetTag[0]) == 1);
            assert(secp256k1_surjectionproof_parse(secp256k1_blind_context, &proof, &out.nAsset.vchSurjectionproof[0], out.nAsset.vchSurjectionproof.size()) == 1);
            assert(secp256k1_surjectionproof_verify(secp256k1_blind_context, &proof, &inputAssetGenerators[0], inputAssetGenerators.size(), &gen) == 1);
         } else {
             if (output_pubkeys[nOut].IsFullyValid()) {
                 nToBlind++;
             }
         }
    }

    //Running total of newly blinded outputs
    static const unsigned char diff_zero[32] = {0};
    int nBlinded = 0;
    unsigned char blind[tx.vout.size()][32];
    unsigned char asset_blind[tx.vout.size()][32];
    secp256k1_pedersen_commitment commit;
    secp256k1_generator gen;
    uint256 assetID;

    for (size_t nOut = 0; nOut < tx.vout.size(); nOut++) {
        CTxOut& out = tx.vout[nOut];
        if (out.nValue.IsAmount() && output_pubkeys[nOut].IsFullyValid()) {
            CTxOutValue& value = out.nValue;
            CTxOutAsset& asset = out.nAsset;
            CAmount amount = value.GetAmount();
            out.nAsset.GetAssetID(assetID);
            blindedAmounts.push_back(value.GetAmount());

            GetRandBytes(&blind[nBlinded][0], 32);
            GetRandBytes(&asset_blind[nBlinded][0], 32);
            blindptrs.push_back(&blind[nBlinded][0]);
            assetblindptrs.push_back(&asset_blind[nBlinded][0]);

            nBlindsOut++;

            // Last blinding factor r' is set as -(output's (vr + r') - input's (vr + r')).
            // Before modifying the transaction or return arguments we must
            // ensure the final blinding factor to not be its corresponding -vr (aka unblinded),
            // or 0, in the case of 0-value output, insisting on additional output to blind.
            if (nBlinded + 1 == nToBlind) {

                // Can't successfully blind in this case, since -vr = r
                // This check is assuming blinds are generated randomly
                // Adversary would need to create all input blinds
                // therefore would already know all your summed output amount anyways.
                if (nBlindsOut == 1 && nBlindsIn == 0) {
                    return false;
                }

                // Generate value we intend to insert
                ret = secp256k1_pedersen_blind_generator_blind_sum(secp256k1_blind_context, &blindedAmounts[0], &assetblindptrs[0], &blindptrs[0], nBlindsOut + nBlindsIn, nBlindsIn);
                assert(ret);

                // Resulting blinding factor shouldn't be 0
                if (memcmp(diff_zero, &blind[nBlinded][0], 32) == 0) {
                   return false;
                }
            }

            nBlinded++;

            output_blinding_factors[nOut] = uint256(std::vector<unsigned char>(blindptrs[blindptrs.size()-1], blindptrs[blindptrs.size()-1]+32));
            output_asset_blinding_factors[nOut] = uint256(std::vector<unsigned char>(assetblindptrs[assetblindptrs.size()-1], assetblindptrs[assetblindptrs.size()-1]+32));

            //Blind the asset ID
            ret = secp256k1_generator_generate_blinded(secp256k1_blind_context, &gen, assetID.begin(), assetblindptrs[assetblindptrs.size()-1]);
            assert(ret == 1);
            ret = secp256k1_generator_serialize(secp256k1_blind_context, &asset.vchAssetTag[0], &gen);
            assert(ret != 0);

            // Create value commitment
            value.vchCommitment.resize(CTxOutValue::nCommittedSize);
            ret = secp256k1_pedersen_commit(secp256k1_blind_context, &commit, (unsigned char*)blindptrs.back(), amount, &gen);
            assert(ret != 0);
            secp256k1_pedersen_commitment_serialize(secp256k1_blind_context, &value.vchCommitment[0], &commit);
            assert(value.IsValid());

            // Generate ephemeral key for ECDH nonce generation
            CKey ephemeral_key;
            ephemeral_key.MakeNewKey(true);
            CPubKey ephemeral_pubkey = ephemeral_key.GetPubKey();
            value.vchNonceCommitment.resize(33);
            memcpy(&value.vchNonceCommitment[0], &ephemeral_pubkey[0], 33);
            // Generate nonce
            uint256 nonce = ephemeral_key.ECDH(output_pubkeys[nOut]);
            CSHA256().Write(nonce.begin(), 32).Finalize(nonce.begin());

            // Prep range proof
            size_t nRangeProofLen = 5134;
            // TODO: smarter min_value selection
            value.vchRangeproof.resize(nRangeProofLen);

            // Compose sidechannel message to convey asset info (ID and asset blinds)
            unsigned char assetsMessage[64];
            memcpy(assetsMessage, assetID.begin(), 32);
            memcpy(assetsMessage+32,  assetblindptrs[assetblindptrs.size()-1], 32);

            // Sign rangeproof
            int res = secp256k1_rangeproof_sign(secp256k1_blind_context, &value.vchRangeproof[0], &nRangeProofLen, 0, &commit, blindptrs.back(), nonce.begin(), std::min(std::max((int)GetArg("-ct_exponent", 0), -1),18), std::min(std::max((int)GetArg("-ct_bits", 32), 1), 51), amount, assetsMessage, sizeof(assetsMessage), out.scriptPubKey.size() ? &out.scriptPubKey.front() : NULL, out.scriptPubKey.size(), &gen);
            value.vchRangeproof.resize(nRangeProofLen);
            // TODO: do something smarter here
            assert(res);

            // Create surjection proof
            size_t nInputsToSelect = std::min((size_t)3, input_asset_ids.size());
            unsigned char randseed[32];
            GetRandBytes(randseed, 32);
            size_t input_index;
            secp256k1_surjectionproof proof;
            secp256k1_fixed_asset_tag tag;
            memcpy(&tag, assetID.begin(), 32);
            if (secp256k1_surjectionproof_initialize(secp256k1_blind_context, &proof, &input_index, &inputAssetIDs[0], input_asset_ids.size(), nInputsToSelect, &tag, 100, randseed) == 0) {
                return false;
            }
            ret = secp256k1_surjectionproof_generate(secp256k1_blind_context, &proof, &inputAssetGenerators[0], inputAssetGenerators.size(), &gen, input_index, input_asset_blinding_factors[input_index].begin(), assetblindptrs[assetblindptrs.size()-1]);
            assert(ret == 1);
            ret = secp256k1_surjectionproof_verify(secp256k1_blind_context, &proof, &inputAssetGenerators[0], inputAssetGenerators.size(), &gen);
            assert(ret != 0);

            size_t output_len = secp256k1_surjectionproof_serialized_size(secp256k1_blind_context, &proof);
            tx.vout[nOut].nAsset.vchSurjectionproof.resize(output_len);
            secp256k1_surjectionproof_serialize(secp256k1_blind_context, &asset.vchSurjectionproof[0], &output_len, &proof);
        }
    }

    // No known blinding means the blinding attempt is vacuously successful
    if (nBlindsOut == 0) {
        return true;
    }

    // Check blinding(even if nothing has been done)
    unsigned char tempFinalBlind[32];
    memcpy(tempFinalBlind, blindptrs.back(), 32);
    memset(blindptrs.back(), 0, 32);
    ret = secp256k1_pedersen_blind_generator_blind_sum(secp256k1_blind_context, &blindedAmounts[0], &assetblindptrs[0], &blindptrs[0], nBlindsOut + nBlindsIn, nBlindsIn);
    assert(ret != 0);
    if (memcmp(blindptrs.back(), tempFinalBlind, 32))
        return false;

    return true;
}
