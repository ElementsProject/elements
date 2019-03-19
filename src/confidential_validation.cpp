
#include <confidential_validation.h>
#include <issuance.h>
#include <pegins.h>
#include <script/sigcache.h>
#include <blind.h>

namespace {
static secp256k1_context *secp256k1_ctx_verify_amounts;

class CSecp256k1Init {
public:
    CSecp256k1Init() {
        assert(secp256k1_ctx_verify_amounts == NULL);
        secp256k1_ctx_verify_amounts = secp256k1_context_create(SECP256K1_CONTEXT_VERIFY | SECP256K1_CONTEXT_SIGN);
        assert(secp256k1_ctx_verify_amounts != NULL);
    }
    ~CSecp256k1Init() {
        assert(secp256k1_ctx_verify_amounts != NULL);
        secp256k1_context_destroy(secp256k1_ctx_verify_amounts);
        secp256k1_ctx_verify_amounts = NULL;
    }
};
static CSecp256k1Init instance_of_csecp256k1;
}

bool CRangeCheck::operator()() {
    if (val->IsExplicit()) {
        return true;
    }

    if (!CachingRangeProofChecker(store).VerifyRangeProof(rangeproof, val->vchCommitment, assetCommitment, scriptPubKey, secp256k1_ctx_verify_amounts)) {
        error = SCRIPT_ERR_RANGEPROOF;
        return false;
    }

    return true;
};

bool CBalanceCheck::operator()() {
    if (!secp256k1_pedersen_verify_tally(secp256k1_ctx_verify_amounts, vpCommitsIn.data(), vpCommitsIn.size(), vpCommitsOut.data(), vpCommitsOut.size())) {
        error = SCRIPT_ERR_PEDERSEN_TALLY;
        return false;
    }

    return true;
}

bool CSurjectionCheck::operator()() {
    return CachingSurjectionProofChecker(store).VerifySurjectionProof(proof, vTags, gen, secp256k1_ctx_verify_amounts, wtxid);
}

// Destroys the check in the case of no queue, or passes its ownership to the queue.
ScriptError QueueCheck(std::vector<CCheck*>* queue, CCheck* check) {
    if (queue != NULL) {
        queue->push_back(check);
        return SCRIPT_ERR_OK;
    }
    bool success = (*check)();
    ScriptError err = check->GetScriptError();
    delete check;
    return success ? SCRIPT_ERR_OK : err;
}

// Helper function for VerifyAmount(), not exported
static bool VerifyIssuanceAmount(secp256k1_pedersen_commitment& value_commit, secp256k1_generator& asset_gen,
                    const CAsset& asset, const CConfidentialValue& value, const std::vector<unsigned char>& rangeproof,
                    std::vector<CCheck*>* checks, const bool store_result)
{
    // This is used to add in the explicit values
    unsigned char explicit_blinds[32];
    memset(explicit_blinds, 0, sizeof(explicit_blinds));
    int ret;

    ret = secp256k1_generator_generate(secp256k1_ctx_verify_amounts, &asset_gen, asset.begin());
    assert(ret == 1);

    // Build value commitment
    if (value.IsExplicit()) {
        if (!MoneyRange(value.GetAmount()) || value.GetAmount() == 0) {
            return false;
        }
        if (!rangeproof.empty()) {
            return false;
        }


        ret = secp256k1_pedersen_commit(secp256k1_ctx_verify_amounts, &value_commit, explicit_blinds, value.GetAmount(), &asset_gen);
        // The explicit_blinds are all 0, and the amount is not 0. So secp256k1_pedersen_commit does not fail.
        assert(ret == 1);
    } else if (value.IsCommitment()) {
        // Verify range proof
        std::vector<unsigned char> vchAssetCommitment(CConfidentialAsset::nExplicitSize);
        secp256k1_generator_serialize(secp256k1_ctx_verify_amounts, vchAssetCommitment.data(), &asset_gen);
        if (QueueCheck(checks, new CRangeCheck(&value, rangeproof, vchAssetCommitment, CScript(), store_result)) != SCRIPT_ERR_OK) {
            return false;
        }

        if (secp256k1_pedersen_commitment_parse(secp256k1_ctx_verify_amounts, &value_commit, value.vchCommitment.data()) != 1) {
            return false;
        }
    } else {
        return false;
    }

    return true;
}
