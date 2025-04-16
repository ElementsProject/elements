// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2022 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_SCRIPT_SIGCACHE_H
#define BITCOIN_SCRIPT_SIGCACHE_H

#include <script/interpreter.h>
#include <span.h>
#include <util/hasher.h>

#include <secp256k1.h>
#include <secp256k1_rangeproof.h>
#include <secp256k1_surjectionproof.h>
#include <optional>
#include <vector>

// DoS prevention: limit cache size to 32MiB (over 1000000 entries on 64-bit
// systems). Due to how we count cache size, actual memory usage is slightly
// more (~32.25 MiB)
static constexpr size_t DEFAULT_MAX_SIG_CACHE_BYTES{32 << 20};

class CPubKey;

class CachingTransactionSignatureChecker : public TransactionSignatureChecker
{
private:
    bool store;

public:
    CachingTransactionSignatureChecker(const CTransaction* txToIn, unsigned int nInIn, const CConfidentialValue& amountIn, bool storeIn, PrecomputedTransactionData& txdataIn) : TransactionSignatureChecker(txToIn, nInIn, amountIn, txdataIn, MissingDataBehavior::ASSERT_FAIL), store(storeIn) {}

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
