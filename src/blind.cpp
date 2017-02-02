#include "blind.h"

#include "hash.h"
#include "primitives/transaction.h"
#include "random.h"
#include "util.h"

#include <secp256k1.h>
#include <secp256k1_rangeproof.h>

static secp256k1_context* secp256k1_blind_context = NULL;

class Blind_ECC_Init {
public:
    Blind_ECC_Init() {
        assert(secp256k1_blind_context == NULL);

        secp256k1_context *ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);
        assert(ctx != NULL);
        secp256k1_pedersen_context_initialize(ctx);
        secp256k1_rangeproof_context_initialize(ctx);

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

bool UnblindOutput(const CKey &key, const CTxOut& txout, CAmount& amount_out, uint256& blinding_factor_out)
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
    int msg_size;
    uint64_t min_value, max_value, amount;
    int res = secp256k1_rangeproof_rewind(secp256k1_blind_context, blinding_factor_out.begin(), &amount, msg, &msg_size, nonce.begin(), &min_value, &max_value, &txout.nValue.vchCommitment[0], &txout.nValue.vchRangeproof[0], txout.nValue.vchRangeproof.size());
    if (!res || amount > (uint64_t)MAX_MONEY || !MoneyRange((CAmount)amount)) {
        amount_out = 0;
        blinding_factor_out = uint256();
        return false;
    } else {
        amount_out = (CAmount)amount;
        return true;
    }
}

bool BlindOutputs(const std::vector<uint256 >& input_blinding_factors, std::vector<uint256 >& output_blinding_factors, const std::vector<CPubKey>& output_pubkeys, CMutableTransaction& tx)
{
    assert(tx.vout.size() == output_blinding_factors.size());
    assert(tx.vout.size() == output_pubkeys.size());
    assert(tx.vin.size() == input_blinding_factors.size());

    std::vector<const unsigned char*> blindptrs;
    blindptrs.reserve(tx.vout.size() + tx.vin.size());

    //Total blinded inputs
    int nBlindsIn = 0;
    for (size_t nIn = 0; nIn < tx.vin.size(); nIn++) {
        if (input_blinding_factors[nIn] != uint256()) {
            assert(input_blinding_factors[nIn].size() == 32);
            blindptrs.push_back(input_blinding_factors[nIn].begin());
            nBlindsIn++;
        }
    }

    //Running total of blinded outputs
    int nBlindsOut = 0;
    //Number of outputs to newly blind
    int nToBlind = 0;
    for (size_t nOut = 0; nOut < tx.vout.size(); nOut++) {
        assert((output_blinding_factors[nOut] != uint256()) == !tx.vout[nOut].nValue.IsAmount());
        if (output_blinding_factors[nOut] != uint256()) {
            blindptrs.push_back(output_blinding_factors[nOut].begin());
            nBlindsOut++;
         } else {
             if (output_pubkeys[nOut].IsValid()) {
                 nToBlind++;
             }
         }
    }

    static const unsigned char diff_zero[32] = {0};
    if (nToBlind == 0) {
        unsigned char diff[32];
        // If there is no place to put a blinding factor anymore, the existing input blinding factors must equal the outputs
        bool ret = secp256k1_pedersen_blind_sum(secp256k1_blind_context, diff, &blindptrs[0], nBlindsOut + nBlindsIn, nBlindsIn);
        assert(ret);
        if (memcmp(diff_zero, diff, 32)) {
            return false;
        }
    }

    //Running total of newly blinded outputs
    int nBlinded = 0;
    unsigned char blind[tx.vout.size()][32];

    for (size_t nOut = 0; nOut < tx.vout.size(); nOut++) {
        if (tx.vout[nOut].nValue.IsAmount() && output_pubkeys[nOut].IsValid()) {
            assert(output_pubkeys[nOut].IsValid());
            if (nBlinded + 1 == nToBlind) {
                // Last to-be-blinded value: compute from all other blinding factors.
                assert(secp256k1_pedersen_blind_sum(secp256k1_blind_context, &blind[nBlinded][0], &blindptrs[0], nBlindsOut + nBlindsIn, nBlindsIn));
                // Never permit producting a blinding factor 0, but insist a new output is added.
                if (memcmp(diff_zero, &blind[nBlinded][0], 32) == 0) {
                    return false;
                }
                blindptrs.push_back(&blind[nBlinded++][0]);
            } else {
                GetRandBytes(&blind[nBlinded][0], 32);
                blindptrs.push_back(&blind[nBlinded++][0]);
            }
            output_blinding_factors[nOut] = uint256(std::vector<unsigned char>(blindptrs[blindptrs.size()-1], blindptrs[blindptrs.size()-1]+32));
            nBlindsOut++;
            // Create blinded value
            CTxOutValue& value = tx.vout[nOut].nValue;
            CAmount amount = value.GetAmount();
            assert(secp256k1_pedersen_commit(secp256k1_blind_context, &value.vchCommitment[0], (unsigned char*)blindptrs.back(), amount));
            // Generate ephemeral key for ECDH nonce generation
            CKey ephemeral_key;
            ephemeral_key.MakeNewKey(true);
            CPubKey ephemeral_pubkey = ephemeral_key.GetPubKey();
            value.vchNonceCommitment.resize(33);
            memcpy(&value.vchNonceCommitment[0], &ephemeral_pubkey[0], 33);
            // Generate nonce
            uint256 nonce = ephemeral_key.ECDH(output_pubkeys[nOut]);
            CSHA256().Write(nonce.begin(), 32).Finalize(nonce.begin());
            // Create range proof
            int nRangeProofLen = 5134;
            // TODO: smarter min_value selection
            value.vchRangeproof.resize(nRangeProofLen);
            int res = secp256k1_rangeproof_sign(secp256k1_blind_context, &value.vchRangeproof[0], &nRangeProofLen, 0, &value.vchCommitment[0], blindptrs.back(), nonce.begin(), std::min(std::max((int)GetArg("-ct_exponent", 0), -1),18), std::min(std::max((int)GetArg("-ct_bits", 32), 1), 51), amount);
            value.vchRangeproof.resize(nRangeProofLen);
            // TODO: do something smarter here
            assert(res);
        }
    }

    return true;
}
