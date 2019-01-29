
#ifndef BITCOIN_CONFIDENTIAL_VALIDATION_H
#define BITCOIN_CONFIDENTIAL_VALIDATION_H

#include <amount.h>
#include <asset.h>
#include <coins.h>
#include <primitives/confidential.h>
#include <primitives/transaction.h>
#include <script/script_error.h>
#include <secp256k1.h>
#include <secp256k1_rangeproof.h>
#include <secp256k1_surjectionproof.h>
#include <uint256.h>


// Check if explicit TX fees overflow or are negative
bool HasValidFee(const CTransaction& tx);

// Compute the fee from the explicit fee outputs. Must call HasValidFee first
CAmountMap GetFeeMap(const CTransaction& tx);

/**
 * ELEMENTS:
 * Closure representing one verification, either script or range checks.
 * Note that this stores references to the spending transaction 
 */
class CCheck
 {
 protected:
     ScriptError error;

 public:
     CCheck() : error(SCRIPT_ERR_UNKNOWN_ERROR) {}
     virtual ~CCheck() {}

     virtual bool operator()() = 0;

     ScriptError GetScriptError() const { return error; }
};

/** Closure representing one output range check. */
class CRangeCheck : public CCheck 
{
private:
    const CConfidentialValue* val;
    const std::vector<unsigned char>& rangeproof;
    // *Must* be a commitment, not an explicit value
    const std::vector<unsigned char> assetCommitment;
    const CScript scriptPubKey;
    const bool store;

public:
    CRangeCheck(const CConfidentialValue* val_, const std::vector<unsigned char>& rangeproof_, const std::vector<unsigned char>& assetCommitment_, const CScript& scriptPubKey_, const bool storeIn) : val(val_), rangeproof(rangeproof_), assetCommitment(assetCommitment_), scriptPubKey(scriptPubKey_), store(storeIn) {}

    bool operator()();
};

/** Closure representing a transaction amount balance check. */
class CBalanceCheck : public CCheck
{
private:
    std::vector<secp256k1_pedersen_commitment> vData;
    std::vector<secp256k1_pedersen_commitment *> vpCommitsIn, vpCommitsOut;

public:
    CBalanceCheck(std::vector<secp256k1_pedersen_commitment>& vData_, std::vector<secp256k1_pedersen_commitment*>& vpCommitsIn_, std::vector<secp256k1_pedersen_commitment*>& vpCommitsOut_)  {
        vData.swap(vData_);
        vpCommitsIn.swap(vpCommitsIn_);
        vpCommitsOut.swap(vpCommitsOut_);
    }

    bool operator()();
};

class CSurjectionCheck : public CCheck
{
private:
    secp256k1_surjectionproof proof;
    std::vector<secp256k1_generator> vTags;
    secp256k1_generator gen;
    uint256 wtxid;
    const bool store;
public:
    CSurjectionCheck(secp256k1_surjectionproof& proof_in, std::vector<secp256k1_generator>& tags_in, secp256k1_generator& gen_in, uint256& wtxid_in, const bool store_in) : proof(proof_in), vTags(tags_in), gen(gen_in), wtxid(wtxid_in), store(store_in) {}

    bool operator()();
};

ScriptError QueueCheck(std::vector<CCheck*>* queue, CCheck* check);

bool VerifyAmounts(const std::vector<CTxOut>& inputs, const CTransaction& tx, std::vector<CCheck*>* pvChecks, const bool cacheStore);

bool VerifyCoinbaseAmount(const CTransaction& tx, const CAmountMap& mapFees);


#endif // BITCOIN_CONFIDENTIAL_VALIDATION_H
