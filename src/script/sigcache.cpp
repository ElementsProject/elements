// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <script/sigcache.h>

#include <pubkey.h>
#include <random.h>
#include <uint256.h>
#include <util/system.h>
#include <hash.h>

#include <cuckoocache.h>

#include <algorithm>
#include <mutex>
#include <shared_mutex>
#include <vector>

namespace {
/**
 * Valid signature cache, to avoid doing expensive ECDSA signature checking
 * twice for every transaction (once when accepted into memory pool, and
 * again when accepted into the block chain)
 */
class CSignatureCache
{
private:
    //! Salted SHA256 midstates, domain-separated by signature or proof type.
    CSHA256 m_salted_hasher_ecdsa;
    CSHA256 m_salted_hasher_schnorr;
    CHashWriter m_salted_hasher_range_proof;
    CHashWriter m_salted_hasher_surjection_proof;
    typedef CuckooCache::cache<uint256, SignatureCacheHasher> map_type;
    map_type setValid;
    std::shared_mutex cs_sigcache;

public:
    CSignatureCache():
        m_salted_hasher_range_proof(SER_GETHASH,0),
        m_salted_hasher_surjection_proof(SER_GETHASH,0)
    {
        uint256 nonce = GetRandHash();
        // Use 64-byte, type-specific salted midstates so later hash computations
        // can start after the first SHA256 chunk.
        static constexpr unsigned char PADDING_ECDSA[32] = {'E'};
        static constexpr unsigned char PADDING_SCHNORR[32] = {'S'};
        static constexpr unsigned char PADDING_RANGE_PROOF[32] = {'r'};
        static constexpr unsigned char PADDING_SURJECTION_PROOF[32] = {'s'};
        m_salted_hasher_ecdsa.Write(nonce.begin(), 32);
        m_salted_hasher_ecdsa.Write(PADDING_ECDSA, 32);
        m_salted_hasher_schnorr.Write(nonce.begin(), 32);
        m_salted_hasher_schnorr.Write(PADDING_SCHNORR, 32);
        m_salted_hasher_range_proof << nonce << PADDING_RANGE_PROOF;
        m_salted_hasher_surjection_proof << nonce << PADDING_SURJECTION_PROOF;
    }

    void
    ComputeEntryECDSA(uint256& entry, const uint256 &hash, const std::vector<unsigned char>& vchSig, const CPubKey& pubkey) const
    {
        CSHA256 hasher = m_salted_hasher_ecdsa;
        hasher.Write(hash.begin(), 32).Write(pubkey.data(), pubkey.size()).Write(vchSig.data(), vchSig.size()).Finalize(entry.begin());
    }

    void
    ComputeEntrySchnorr(uint256& entry, const uint256 &hash, Span<const unsigned char> sig, const XOnlyPubKey& pubkey) const
    {
        CSHA256 hasher = m_salted_hasher_schnorr;
        hasher.Write(hash.begin(), 32).Write(pubkey.data(), pubkey.size()).Write(sig.data(), sig.size()).Finalize(entry.begin());
    }

    // ELEMENTS:
    void ComputeEntryRangeProof(uint256& entry,
                                const std::vector<unsigned char>& proof,
                                const std::vector<unsigned char>& commitment,
                                const std::vector<unsigned char>& asset_commitment,
                                const CScript& script_pub_key) const
    {
        CHashWriter hasher = m_salted_hasher_range_proof;
        // We commit to both commitments and the scriptPubKey because these are
        // committed to by the rangeproof itself; a change in any of them would
        // invalidate the proof. Since these are exactly the arguments to
        // CachingRangeProofChecker::VerifyRangeProof (below), there is no
        // additional data that could affect the rangeproof's validity.
        // Serialization length-prefixes every field, including the variable-length
        // proof and script, so distinct argument tuples cannot share an encoding.
        hasher << proof << commitment << asset_commitment << script_pub_key;
        entry = hasher.GetSHA256();
    }
    void ComputeEntrySurjectionProof(uint256& entry, const uint256 &hash, const std::vector<unsigned char>& proof, const std::vector<unsigned char>& commitment, const std::vector<secp256k1_generator>& vTags) const {
        CHashWriter hasher = m_salted_hasher_surjection_proof;
        // We hash all arguments passed to CachingSurjectionProofChecker::VerifySurjectionProof,
        // to ensure that any change in the way that the verification function is called will
        // trigger a cache miss and explicit verification. However, we note that the `wtxid`
        // (hash) commits to all the other data such that we could technically hash only it.
        // We retain the other data as a defense against future refactorings.
        //
        // Serialize vTags as a flat byte vector (each secp256k1_generator is 64 bytes).
        std::vector<unsigned char> vTagsBytes;
        vTagsBytes.reserve(vTags.size() * 64);
        for (const auto& tag : vTags) {
            vTagsBytes.insert(vTagsBytes.end(), std::begin(tag.data), std::end(tag.data));
        }
        hasher << hash << proof << commitment << vTagsBytes;
        entry = hasher.GetSHA256();
    }

    bool
    Get(const uint256& entry, const bool erase)
    {
        std::shared_lock<std::shared_mutex> lock(cs_sigcache);
        return setValid.contains(entry, erase);
    }

    void Set(const uint256& entry)
    {
        std::unique_lock<std::shared_mutex> lock(cs_sigcache);
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

// ELEMENTS:
static CSignatureCache rangeProofCache;
static CSignatureCache surjectionProofCache;

} // namespace

// To be called once in AppInitMain/BasicTestingSetup to initialize the
// signatureCache.
void InitSignatureCache()
{
    // nMaxCacheSize is unsigned. If -maxsigcachesize is set to zero,
    // setup_bytes creates the minimum possible cache (2 elements).
    size_t nMaxCacheSize = std::min(std::max((int64_t)0, gArgs.GetIntArg("-maxsigcachesize", DEFAULT_MAX_SIG_CACHE_SIZE) / 4), MAX_MAX_SIG_CACHE_SIZE) * ((size_t) 1 << 20);
    size_t nElems = signatureCache.setup_bytes(nMaxCacheSize);
    LogPrintf("Using %zu MiB out of %zu/4 requested for signature cache, able to store %zu elements\n",
            (nElems*sizeof(uint256)) >>20, (nMaxCacheSize*2)>>20, nElems);
}

bool CachingTransactionSignatureChecker::VerifyECDSASignature(const std::vector<unsigned char>& vchSig, const CPubKey& pubkey, const uint256& sighash) const
{
    uint256 entry;
    signatureCache.ComputeEntryECDSA(entry, sighash, vchSig, pubkey);
    if (signatureCache.Get(entry, !store))
        return true;
    if (!TransactionSignatureChecker::VerifyECDSASignature(vchSig, pubkey, sighash))
        return false;
    if (store)
        signatureCache.Set(entry);
    return true;
}

bool CachingTransactionSignatureChecker::VerifySchnorrSignature(Span<const unsigned char> sig, const XOnlyPubKey& pubkey, const uint256& sighash) const
{
    uint256 entry;
    signatureCache.ComputeEntrySchnorr(entry, sighash, sig, pubkey);
    if (signatureCache.Get(entry, !store)) return true;
    if (!TransactionSignatureChecker::VerifySchnorrSignature(sig, pubkey, sighash)) return false;
    if (store) signatureCache.Set(entry);
    return true;
}

//
// ELEMENTS CACHES

// To be called once in AppInit2/TestingSetup to initialize the rangeproof cache
void InitRangeproofCache()
{
    if (!gArgs.GetBoolArg("-rangeproofcache", true)) {
        LogPrintf("Range proof cache disabled via -norangeproofcache\n");
        return;
    }
    // nMaxCacheSize is unsigned. If -maxsigcachesize is set to zero,
    // setup_bytes creates the minimum possible cache (2 elements).
    size_t nMaxCacheSize = std::min(std::max((int64_t)0, gArgs.GetIntArg("-maxsigcachesize", DEFAULT_MAX_SIG_CACHE_SIZE) / 4), MAX_MAX_SIG_CACHE_SIZE) * ((size_t) 1 << 20);
    size_t nElems = rangeProofCache.setup_bytes(nMaxCacheSize);
    LogPrintf("Using %zu MiB out of %zu/4 requested for rangeproof cache, able to store %zu elements\n",
            (nElems*sizeof(uint256)) >>20, nMaxCacheSize>>20, nElems);
}

// To be called once in AppInit2/TestingSetup to initialize the surjectionrproof cache
void InitSurjectionproofCache()
{
    // nMaxCacheSize is unsigned. If -maxsigcachesize is set to zero,
    // setup_bytes creates the minimum possible cache (2 elements).
    size_t nMaxCacheSize = std::min(std::max((int64_t)0, gArgs.GetIntArg("-maxsigcachesize", DEFAULT_MAX_SIG_CACHE_SIZE) / 4), MAX_MAX_SIG_CACHE_SIZE) * ((size_t) 1 << 20);
    size_t nElems = surjectionProofCache.setup_bytes(nMaxCacheSize);
    LogPrintf("Using %zu MiB out of %zu/4 requested for surjectionproof cache, able to store %zu elements\n",
            (nElems*sizeof(uint256)) >>20, nMaxCacheSize>>20, nElems);
}

bool CachingRangeProofChecker::VerifyRangeProof(const std::vector<unsigned char>& vchRangeProof, const std::vector<unsigned char>& vchValueCommitment, const std::vector<unsigned char>& vchAssetCommitment, const CScript& scriptPubKey, const secp256k1_context* secp256k1_ctx_verify_amounts) const
{
    // ELEMENTS: NOTE FOR FUTURE EDITORS: every argument to this function that
    // carries data (i.e. everything except the secp256k1 context, which is
    // stateless) MUST be included in ComputeEntryRangeProof. Omitting any
    // argument risks returning a cached positive result for a proof that was
    // verified with different inputs.
    uint256 entry;
    const bool useCache = gArgs.GetBoolArg("-rangeproofcache", true);
    if (useCache) {
        rangeProofCache.ComputeEntryRangeProof(entry, vchRangeProof, vchValueCommitment, vchAssetCommitment, scriptPubKey);
        if (rangeProofCache.Get(entry, !store)) {
            return true;
        }
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

    if (useCache && store) {
        rangeProofCache.Set(entry);
    }

    return true;
}

bool CachingSurjectionProofChecker::VerifySurjectionProof(secp256k1_surjectionproof& proof, std::vector<secp256k1_generator>& vTags, secp256k1_generator& gen, const secp256k1_context* secp256k1_ctx_verify_amounts, const uint256& wtxid) const
{

    // Serialize proof
    std::vector<unsigned char> vchproof;
    size_t proof_len = secp256k1_surjectionproof_serialized_size(secp256k1_ctx_verify_amounts, &proof);
    vchproof.resize(proof_len);
    assert(secp256k1_surjectionproof_serialize(secp256k1_ctx_verify_amounts, vchproof.data(), &proof_len, &proof) == 1);

    // wtxid commits to all data including surj targets
    // we need to specify the proof and output asset point to be unique
    uint256 entry;
    surjectionProofCache.ComputeEntrySurjectionProof(entry, wtxid, vchproof, std::vector<unsigned char>(std::begin(gen.data), std::end(gen.data)), vTags);

    if (surjectionProofCache.Get(entry, !store)) {
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

// Test-only hooks (see sigcache.h). Forward to the anonymous-namespace caches.
void TestComputeEntryRangeProof(uint256& entry,
                                const std::vector<unsigned char>& proof,
                                const std::vector<unsigned char>& commitment,
                                const std::vector<unsigned char>& asset_commitment,
                                const CScript& script_pub_key)
{
    rangeProofCache.ComputeEntryRangeProof(entry, proof, commitment, asset_commitment, script_pub_key);
}

void TestComputeEntrySurjectionProof(uint256& entry,
                                     const uint256& hash,
                                     const std::vector<unsigned char>& proof,
                                     const std::vector<unsigned char>& commitment,
                                     const std::vector<secp256k1_generator>& vTags)
{
    surjectionProofCache.ComputeEntrySurjectionProof(entry, hash, proof, commitment, vTags);
}

// END ELEMENTS
//
