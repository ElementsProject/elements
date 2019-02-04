// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "sigcache.h"

#include "memusage.h"
#include "pubkey.h"
#include "random.h"
#include "uint256.h"
#include "util.h"

#include "cuckoocache.h"
#include <boost/thread.hpp>

namespace {

/**
 * We're hashing a nonce into the entries themselves, so we don't need extra
 * blinding in the set hash computation.
 *
 * This may exhibit platform endian dependent behavior but because these are
 * nonced hashes (random) and this state is only ever used locally it is safe.
 * All that matters is local consistency.
 */
class SignatureCacheHasher
{
public:
    template <uint8_t hash_select>
    uint32_t operator()(const uint256& key) const
    {
        static_assert(hash_select <8, "SignatureCacheHasher only has 8 hashes available.");
        uint32_t u;
        std::memcpy(&u, key.begin()+4*hash_select, 4);
        return u;
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
     //! Entries are SHA256(nonce || signature hash || public key || signature || additional commit || CScript). They are used in various ways for different checks
    uint256 nonce;
    typedef CuckooCache::cache<uint256, SignatureCacheHasher> map_type;
    map_type setValid;
    boost::shared_mutex cs_sigcache;

public:
    CSignatureCache()
    {
        GetRandBytes(nonce.begin(), 32);
    }

    void
    ComputeEntry(uint256& entry, const uint256 &hash, const std::vector<unsigned char>& vchSig, const CPubKey& pubkey, const std::vector<unsigned char>& vchCommitment, const CScript& scriptPubKey)
    {
        CSHA256().Write(nonce.begin(), 32).Write(hash.begin(), 32).Write(&pubkey[0], pubkey.size()).Write(&vchSig[0], vchSig.size()).Write(&vchCommitment[0], vchCommitment.size()).Write(&scriptPubKey[0], scriptPubKey.size()).Finalize(entry.begin());
    }

    bool
    Get(const uint256& entry, const bool erase)
    {
        boost::shared_lock<boost::shared_mutex> lock(cs_sigcache);
        return setValid.contains(entry, erase);
    }

    void Set(uint256& entry)
    {
        boost::unique_lock<boost::shared_mutex> lock(cs_sigcache);
        setValid.insert(entry);
    }
    uint32_t setup_bytes(size_t n)
    {
        return setValid.setup_bytes(n);
    }
};

/* In previous versions of this code, signatureCache was a local static variable
 * in CachingTransactionSignatureChecker::VerifySignature.  We initialize
 * signatureCache outside of VerifySignature to avoid the atomic operation per
 * call overhead associated with local static variables even though
 * signatureCache could be made local to VerifySignature.
*/
static CSignatureCache signatureCache;

static CSignatureCache rangeProofCache;

static CSignatureCache surjectionProofCache;


}

// To be called once in AppInit2/TestingSetup to initialize the signatureCache
void InitSignatureCache()
{
    // nMaxCacheSize is unsigned. If -maxsigcachesize is set to zero,
    // setup_bytes creates the minimum possible cache (2 ocean).
    size_t nMaxCacheSize = std::min(std::max((int64_t)0, GetArg("-maxsigcachesize", DEFAULT_MAX_SIG_CACHE_SIZE)), MAX_MAX_SIG_CACHE_SIZE) * ((size_t) 1 << 20);
    size_t nElems = signatureCache.setup_bytes(nMaxCacheSize);
    LogPrintf("Using %zu MiB out of %zu requested for signature cache, able to store %zu ocean\n",
            (nElems*sizeof(uint256)) >>20, nMaxCacheSize>>20, nElems);
}

// To be called once in AppInit2/TestingSetup to initialize the rangeproof cache
void InitRangeproofCache()
{
    // nMaxCacheSize is unsigned. If -maxsigcachesize is set to zero,
    // setup_bytes creates the minimum possible cache (2 ocean).
    size_t nMaxCacheSize = std::min(std::max((int64_t)0, GetArg("-maxsigcachesize", DEFAULT_MAX_SIG_CACHE_SIZE)), MAX_MAX_SIG_CACHE_SIZE) * ((size_t) 1 << 20);
    size_t nElems = rangeProofCache.setup_bytes(nMaxCacheSize);
    LogPrintf("Using %zu MiB out of %zu requested for rangeproof cache, able to store %zu ocean\n",
            (nElems*sizeof(uint256)) >>20, nMaxCacheSize>>20, nElems);
}

// To be called once in AppInit2/TestingSetup to initialize the surjectionrproof cache
void InitSurjectionproofCache()
{
    // nMaxCacheSize is unsigned. If -maxsigcachesize is set to zero,
    // setup_bytes creates the minimum possible cache (2 ocean).
    size_t nMaxCacheSize = std::min(std::max((int64_t)0, GetArg("-maxsigcachesize", DEFAULT_MAX_SIG_CACHE_SIZE)), MAX_MAX_SIG_CACHE_SIZE) * ((size_t) 1 << 20);
    size_t nElems = surjectionProofCache.setup_bytes(nMaxCacheSize);
    LogPrintf("Using %zu MiB out of %zu requested for surjectionproof cache, able to store %zu ocean\n",
            (nElems*sizeof(uint256)) >>20, nMaxCacheSize>>20, nElems);
}


bool CachingTransactionSignatureChecker::VerifySignature(const std::vector<unsigned char>& vchSig, const CPubKey& pubkey, const uint256& sighash) const
{
    uint256 entry;
    signatureCache.ComputeEntry(entry, sighash, vchSig, pubkey, vchSig, CScript());
    if (signatureCache.Get(entry, !store))
        return true;
    if (!TransactionSignatureChecker::VerifySignature(vchSig, pubkey, sighash))
        return false;
    if (store)
        signatureCache.Set(entry);
    return true;
}

bool CachingRangeProofChecker::VerifyRangeProof(const std::vector<unsigned char>& vchRangeProof, const std::vector<unsigned char>& vchValueCommitment, const std::vector<unsigned char>& vchAssetCommitment, const CScript& scriptPubKey, const secp256k1_context* secp256k1_ctx_verify_amounts) const
{
    CPubKey pubkey(vchValueCommitment);
    uint256 entry;
    rangeProofCache.ComputeEntry(entry, uint256(), vchRangeProof, pubkey, vchAssetCommitment, scriptPubKey);

    if (rangeProofCache.Get(entry, !store)) {
        return true;
    }

    if (vchRangeProof.size() == 0) {
        return false;
    }

    uint64_t min_value, max_value;
    secp256k1_pedersen_commitment commit;
    if (secp256k1_pedersen_commitment_parse(secp256k1_ctx_verify_amounts, &commit, &vchValueCommitment[0]) != 1)
            return false;

    secp256k1_generator tag;
    if (secp256k1_generator_parse(secp256k1_ctx_verify_amounts, &tag, &vchAssetCommitment[0]) != 1)
        return false;

    if (!secp256k1_rangeproof_verify(secp256k1_ctx_verify_amounts, &min_value, &max_value, &commit, vchRangeProof.data(), vchRangeProof.size(), scriptPubKey.size() ? &scriptPubKey.front() : NULL, scriptPubKey.size(), &tag)) {
        return false;
    }

    // An rangeproof is not valid if the output is spendable but the minimum number
    // is 0. This is to prevent people passing 0-value tokens around, or conjuring
    // reissuance tokens from nothing then attempting to reissue an asset.
    // ie reissuance doesn't require revealing value of reissuance output
    // Issuances proofs are always "unspendable" as they commit to an empty script.
    if (min_value == 0 && !scriptPubKey.IsUnspendable()) {
        return false;
    }

    return true;
}

bool CachingSurjectionProofChecker::VerifySurjectionProof(secp256k1_surjectionproof& proof, std::vector<secp256k1_generator>& vTags, secp256k1_generator& gen, const secp256k1_context* secp256k1_ctx_verify_amounts) const
{
    // Serialize objects
    std::vector<unsigned char> vchproof;
    size_t proof_len = 0;
    vchproof.resize(secp256k1_surjectionproof_serialized_size(secp256k1_ctx_verify_amounts, &proof));
    secp256k1_surjectionproof_serialize(secp256k1_ctx_verify_amounts, &vchproof[0], &proof_len, &proof);

    std::vector<unsigned char> tagCommit;
    tagCommit.resize(33);
    CSHA256 sha2;
    for (unsigned int i = 0; i <vTags.size(); i++) {
        secp256k1_generator_serialize(secp256k1_ctx_verify_amounts, tagCommit.data(), &vTags[i]);
        sha2.Write(tagCommit.data(), tagCommit.size());
    }
    tagCommit.resize(32);
    sha2.Finalize(tagCommit.data());

    std::vector<unsigned char> vchGen;
    vchGen.resize(CConfidentialValue::nCommittedSize);
    secp256k1_generator_serialize(secp256k1_ctx_verify_amounts, &vchGen[0], &gen);

    CPubKey pubkey(vchGen);
    uint256 entry;
    surjectionProofCache.ComputeEntry(entry, uint256(tagCommit), vchproof, pubkey, vchGen, CScript());

    if (surjectionProofCache.Get(entry, !store)) {
        return true;
    }

    if (secp256k1_surjectionproof_verify(secp256k1_ctx_verify_amounts, &proof, vTags.data(), vTags.size(), &gen) != 1) {
        return false;
    }

    return true;
}
