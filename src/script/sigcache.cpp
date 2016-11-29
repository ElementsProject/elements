// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2015 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "sigcache.h"

#include "memusage.h"
#include "pubkey.h"
#include "random.h"
#include "uint256.h"
#include "util.h"

#include <boost/thread.hpp>
#include <boost/unordered_set.hpp>

namespace {

/**
 * We're hashing a nonce into the entries themselves, so we don't need extra
 * blinding in the set hash computation.
 */
class CSignatureCacheHasher
{
public:
    size_t operator()(const uint256& key) const {
        return key.GetCheapHash();
    }
};

/**
 * Valid signature cache, to avoid doing expensive ECDSA signature checking
 * twice for every transaction (once when accepted into memory pool, and
 * again when accepted into the block chain)
 */
class CSignatureCache
{
private:
     //! Entries are SHA256(nonce || signature hash || public key || signature):
    uint256 nonce;
    typedef boost::unordered_set<uint256, CSignatureCacheHasher> map_type;
    map_type setValid;
    boost::shared_mutex cs_sigcache;


public:
    CSignatureCache()
    {
        GetRandBytes(nonce.begin(), 32);
    }

    void
    ComputeEntry(uint256& entry, const uint256 &hash, const std::vector<unsigned char>& vchSig, const CPubKey& pubkey)
    {
        CSHA256().Write(nonce.begin(), 32).Write(hash.begin(), 32).Write(&pubkey[0], pubkey.size()).Write(&vchSig[0], vchSig.size()).Finalize(entry.begin());
    }

    bool
    Get(const uint256& entry)
    {
        boost::shared_lock<boost::shared_mutex> lock(cs_sigcache);
        return setValid.count(entry);
    }

    void Erase(const uint256& entry)
    {
        boost::unique_lock<boost::shared_mutex> lock(cs_sigcache);
        setValid.erase(entry);
    }

    void Set(const uint256& entry)
    {
        size_t nMaxCacheSize = GetArg("-maxsigcachesize", DEFAULT_MAX_SIG_CACHE_SIZE) * ((size_t) 1 << 20);
        if (nMaxCacheSize <= 0) return;

        boost::unique_lock<boost::shared_mutex> lock(cs_sigcache);
        while (memusage::DynamicUsage(setValid) > nMaxCacheSize)
        {
            map_type::size_type s = GetRand(setValid.bucket_count());
            map_type::local_iterator it = setValid.begin(s);
            if (it != setValid.end(s)) {
                setValid.erase(*it);
            }
        }

        setValid.insert(entry);
    }
};

}

bool CachingTransactionSignatureChecker::VerifySignature(const std::vector<unsigned char>& vchSig, const CPubKey& pubkey, const uint256& sighash) const
{
    static CSignatureCache signatureCache;

    uint256 entry;
    signatureCache.ComputeEntry(entry, sighash, vchSig, pubkey);

    if (signatureCache.Get(entry)) {
        if (!store) {
            signatureCache.Erase(entry);
        }
        return true;
    }

    if (!TransactionSignatureChecker::VerifySignature(vchSig, pubkey, sighash))
        return false;

    if (store) {
        signatureCache.Set(entry);
    }
    return true;
}

bool CachingRangeProofChecker::VerifyRangeProof(const std::vector<unsigned char>& vchRangeProof, const std::vector<unsigned char>& vchCommitment, const std::vector<unsigned char>& vchAssetTag, const secp256k1_context* secp256k1_ctx_verify_amounts) const
{
    static CSignatureCache rangeProofCache;

    CPubKey pubkey(vchCommitment);
    uint256 entry;
    rangeProofCache.ComputeEntry(entry, uint256(), vchRangeProof, pubkey);

    if (rangeProofCache.Get(entry)) {
        if (!store) {
            rangeProofCache.Erase(entry);
        }
        return true;
    }

    uint64_t min_value, max_value;
    secp256k1_pedersen_commitment commit;
    if (secp256k1_pedersen_commitment_parse(secp256k1_ctx_verify_amounts, &commit, &vchCommitment[0]) != 1)
            return false;

    secp256k1_generator tag;
    if (secp256k1_generator_parse(secp256k1_ctx_verify_amounts, &tag, &vchAssetTag[0]) != 1)
        return false;

    if (!secp256k1_rangeproof_verify(secp256k1_ctx_verify_amounts, &min_value, &max_value, &commit, vchRangeProof.data(), vchRangeProof.size(), NULL, 0, &tag)) {
        return false;
    }

    if (store) {
        rangeProofCache.Set(entry);
    }
    return true;

}

bool CachingSurjectionProofChecker::VerifySurjectionProof(secp256k1_surjectionproof& proof, std::vector<secp256k1_generator>& vTags, secp256k1_generator& gen, const secp256k1_context* secp256k1_ctx_verify_amounts) const
{
    static CSignatureCache surjectionProofCache;

    std::vector<unsigned char> vchproof;
    size_t proof_len = 0;
    vchproof.resize(secp256k1_surjectionproof_serialized_size(secp256k1_ctx_verify_amounts, &proof));
    secp256k1_surjectionproof_serialize(secp256k1_ctx_verify_amounts, &vchproof[0], &proof_len, &proof);

    std::vector<unsigned char> vchGen;
    vchGen.resize(CTxOutValue::nCommittedSize);
    secp256k1_generator_serialize(secp256k1_ctx_verify_amounts, &vchGen[0], &gen);

    CPubKey pubkey(vchGen);
    uint256 entry;
    surjectionProofCache.ComputeEntry(entry, uint256(), vchproof, pubkey);

    if (surjectionProofCache.Get(entry)) {
        if (!store) {
            surjectionProofCache.Erase(entry);
        }
        return true;
    }

    if (secp256k1_surjectionproof_verify(secp256k1_ctx_verify_amounts, &proof, vTags.data(), vTags.size(), &gen) != 1) {
        return false;
    }

    if (store) {
        surjectionProofCache.Set(entry);
    }
    return true;
}
