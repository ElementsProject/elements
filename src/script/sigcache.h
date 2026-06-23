// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2022 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_SCRIPT_SIGCACHE_H
#define BITCOIN_SCRIPT_SIGCACHE_H

#include <consensus/amount.h>
#include <crypto/sha256.h>
#include <cuckoocache.h>
#include <script/interpreter.h>
#include <random.h>
#include <span.h>
#include <uint256.h>
#include <util/hasher.h>

#include <secp256k1.h>
#include <secp256k1_rangeproof.h>
#include <secp256k1_surjectionproof.h>
#include <optional>
#include <cstddef>
#include <shared_mutex>
#include <vector>

class CPubKey;
class CTransaction;
class XOnlyPubKey;

// DoS prevention: limit cache size to 32MiB (over 1000000 entries on 64-bit
// systems). Due to how we count cache size, actual memory usage is slightly
// more (~32.25 MiB)
static constexpr size_t DEFAULT_VALIDATION_CACHE_BYTES{32 << 20};
static constexpr size_t DEFAULT_SIGNATURE_CACHE_BYTES{DEFAULT_VALIDATION_CACHE_BYTES / 2};
static constexpr size_t DEFAULT_SCRIPT_EXECUTION_CACHE_BYTES{DEFAULT_VALIDATION_CACHE_BYTES / 2};
static_assert(DEFAULT_VALIDATION_CACHE_BYTES == DEFAULT_SIGNATURE_CACHE_BYTES + DEFAULT_SCRIPT_EXECUTION_CACHE_BYTES);

/**
 * Valid signature cache, to avoid doing expensive ECDSA signature checking
 * twice for every transaction (once when accepted into memory pool, and
 * again when accepted into the block chain)
 */
class SignatureCache
{
private:
    //! Entries are SHA256(nonce || 'E' or 'S' || 31 zero bytes || signature hash || public key || signature):
    CSHA256 m_salted_hasher_ecdsa;
    CSHA256 m_salted_hasher_schnorr;
    CSHA256 m_salted_hasher_range_proof;
    CSHA256 m_salted_hasher_surjection_proof;
    typedef CuckooCache::cache<uint256, SignatureCacheHasher> map_type;
    map_type setValid;
    std::shared_mutex cs_sigcache;

public:
    SignatureCache()
    {
        uint256 nonce = GetRandHash();
        // We want the nonce to be 64 bytes long to force the hasher to process
        // this chunk, which makes later hash computations more efficient. We
        // just write our 32-byte entropy, and then pad with 'E' for ECDSA and
        // 'S' for Schnorr (followed by 0 bytes).
        static constexpr unsigned char PADDING_ECDSA[32] = {'E'};
        static constexpr unsigned char PADDING_SCHNORR[32] = {'S'};
        static constexpr unsigned char PADDING_RANGE_PROOF[32] = {'r'};
        static constexpr unsigned char PADDING_SURJECTION_PROOF[32] = {'s'};
        m_salted_hasher_ecdsa.Write(nonce.begin(), 32);
        m_salted_hasher_ecdsa.Write(PADDING_ECDSA, 32);
        m_salted_hasher_schnorr.Write(nonce.begin(), 32);
        m_salted_hasher_schnorr.Write(PADDING_SCHNORR, 32);
        m_salted_hasher_range_proof.Write(nonce.begin(), 32);
        m_salted_hasher_range_proof.Write(PADDING_RANGE_PROOF, 32);
        m_salted_hasher_surjection_proof.Write(nonce.begin(), 32);
        m_salted_hasher_surjection_proof.Write(PADDING_SURJECTION_PROOF, 32);
    }

    SignatureCache(size_t max_size_bytes);

    SignatureCache(const SignatureCache&) = delete;
    SignatureCache& operator=(const SignatureCache&) = delete;

    void ComputeEntryECDSA(uint256& entry, const uint256 &hash, const std::vector<unsigned char>& vchSig, const CPubKey& pubkey) const;

    void ComputeEntrySchnorr(uint256& entry, const uint256 &hash, Span<const unsigned char> sig, const XOnlyPubKey& pubkey) const;

    // ELEMENTS:
    void ComputeEntryRangeProof(uint256& entry, const std::vector<unsigned char>& proof, const std::vector<unsigned char>& commitment) const;

    void ComputeEntrySurjectionProof(uint256& entry, const uint256 &hash, const std::vector<unsigned char>& proof, const std::vector<unsigned char>& commitment) const;

    bool Get(const uint256& entry, const bool erase);

    void Set(const uint256& entry);

    std::optional<std::pair<uint32_t, size_t>> setup_bytes(size_t n)
    {
        return setValid.setup_bytes(n);
    }
};

class CachingTransactionSignatureChecker : public TransactionSignatureChecker
{
private:
    bool store;
    SignatureCache& m_signature_cache;

public:
    CachingTransactionSignatureChecker(const CTransaction* txToIn, unsigned int nInIn, const CConfidentialValue& amountIn, bool storeIn, SignatureCache& signature_cache, PrecomputedTransactionData& txdataIn) : TransactionSignatureChecker(txToIn, nInIn, amountIn, txdataIn, MissingDataBehavior::ASSERT_FAIL), store(storeIn), m_signature_cache(signature_cache) {}

    bool VerifyECDSASignature(const std::vector<unsigned char>& vchSig, const CPubKey& vchPubKey, const uint256& sighash) const override;
    bool VerifySchnorrSignature(Span<const unsigned char> sig, const XOnlyPubKey& pubkey, const uint256& sighash) const override;
};

[[nodiscard]] bool InitSignatureCache(size_t max_size_bytes);

//
// ELEMENTS:

class CachingRangeProofChecker
{
private:
    bool store;
public:
    CachingRangeProofChecker(bool storeIn){
        store = storeIn;
    };

    bool VerifyRangeProof(const std::vector<unsigned char>& vchRangeProof, const std::vector<unsigned char>& vchValueCommitment, const std::vector<unsigned char>& vchAssetCommitment, const CScript& scriptPubKey, const secp256k1_context* ctx) const;

};

class CachingSurjectionProofChecker
{
private:
    bool store;
public:
    CachingSurjectionProofChecker(bool storeIn){
        store = storeIn;
    };

    bool VerifySurjectionProof(secp256k1_surjectionproof& proof, std::vector<secp256k1_generator>& vTags, secp256k1_generator& gen, const secp256k1_context* ctx, const uint256& wtxid) const;

};

[[nodiscard]] bool InitRangeproofCache(size_t max_size_bytes);
[[nodiscard]] bool InitSurjectionproofCache(size_t max_size_bytes);

// END ELEMENTS
//

#endif // BITCOIN_SCRIPT_SIGCACHE_H
