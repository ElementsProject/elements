// Copyright (c) 2009-2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_PSBT_H
#define BITCOIN_PSBT_H

#include <attributes.h>
#include <chainparams.h>
#include <node/transaction.h>
#include <pegins.h>
#include <policy/feerate.h>
#include <primitives/transaction.h>
#include <primitives/bitcoin/transaction.h>
#include <primitives/bitcoin/merkleblock.h>
#include <pubkey.h>
#include <script/keyorigin.h>
#include <script/sign.h>
#include <script/signingprovider.h>
#include <span.h>
#include <streams.h>

#include <bitset>
#include <optional>
#include <variant>

// Magic bytes
// static constexpr uint8_t PSBT_MAGIC_BYTES[5] = {'p', 's', 'b', 't', 0xff};
static constexpr uint8_t PSBT_ELEMENTS_MAGIC_BYTES[5] = {'p', 's', 'e', 't', 0xff};

// Global types
static constexpr uint8_t PSBT_GLOBAL_UNSIGNED_TX = 0x00;
static constexpr uint8_t PSBT_GLOBAL_XPUB = 0x01;
static constexpr uint8_t PSBT_GLOBAL_TX_VERSION = 0x02;
static constexpr uint8_t PSBT_GLOBAL_FALLBACK_LOCKTIME = 0x03;
static constexpr uint8_t PSBT_GLOBAL_INPUT_COUNT = 0x04;
static constexpr uint8_t PSBT_GLOBAL_OUTPUT_COUNT = 0x05;
static constexpr uint8_t PSBT_GLOBAL_TX_MODIFIABLE = 0x06;
static constexpr uint8_t PSBT_GLOBAL_VERSION = 0xFB;
static constexpr uint8_t PSBT_GLOBAL_PROPRIETARY = 0xFC;
// Elements proprietary types
static constexpr uint8_t PSBT_ELEMENTS_GLOBAL_SCALAR = 0x00;
static constexpr uint8_t PSBT_ELEMENTS_GLOBAL_TX_MODIFIABLE = 0x01;

// Input types
static constexpr uint8_t PSBT_IN_NON_WITNESS_UTXO = 0x00;
static constexpr uint8_t PSBT_IN_WITNESS_UTXO = 0x01;
static constexpr uint8_t PSBT_IN_PARTIAL_SIG = 0x02;
static constexpr uint8_t PSBT_IN_SIGHASH = 0x03;
static constexpr uint8_t PSBT_IN_REDEEMSCRIPT = 0x04;
static constexpr uint8_t PSBT_IN_WITNESSSCRIPT = 0x05;
static constexpr uint8_t PSBT_IN_BIP32_DERIVATION = 0x06;
static constexpr uint8_t PSBT_IN_SCRIPTSIG = 0x07;
static constexpr uint8_t PSBT_IN_SCRIPTWITNESS = 0x08;
static constexpr uint8_t PSBT_IN_PREVIOUS_TXID = 0x0e;
static constexpr uint8_t PSBT_IN_OUTPUT_INDEX = 0x0f;
static constexpr uint8_t PSBT_IN_SEQUENCE = 0x10;
static constexpr uint8_t PSBT_IN_REQUIRED_TIME_LOCKTIME = 0x11;
static constexpr uint8_t PSBT_IN_REQUIRED_HEIGHT_LOCKTIME = 0x12;
static constexpr uint8_t PSBT_IN_RIPEMD160 = 0x0A;
static constexpr uint8_t PSBT_IN_SHA256 = 0x0B;
static constexpr uint8_t PSBT_IN_HASH160 = 0x0C;
static constexpr uint8_t PSBT_IN_HASH256 = 0x0D;
static constexpr uint8_t PSBT_IN_PROPRIETARY = 0xFC;
// Elements proprietary types
static constexpr uint8_t PSBT_ELEMENTS_IN_ISSUANCE_VALUE = 0x00;
static constexpr uint8_t PSBT_ELEMENTS_IN_ISSUANCE_VALUE_COMMITMENT = 0x01;
static constexpr uint8_t PSBT_ELEMENTS_IN_ISSUANCE_VALUE_RANGEPROOF = 0x02;
static constexpr uint8_t PSBT_ELEMENTS_IN_ISSUANCE_INFLATION_KEYS_RANGEPROOF = 0x03;
static constexpr uint8_t PSBT_ELEMENTS_IN_PEG_IN_TX = 0x04;
static constexpr uint8_t PSBT_ELEMENTS_IN_PEG_IN_TXOUT_PROOF = 0x05;
static constexpr uint8_t PSBT_ELEMENTS_IN_PEG_IN_GENESIS_HASH = 0x06;
static constexpr uint8_t PSBT_ELEMENTS_IN_PEG_IN_CLAIM_SCRIPT = 0x07;
static constexpr uint8_t PSBT_ELEMENTS_IN_PEG_IN_VALUE = 0x08;
static constexpr uint8_t PSBT_ELEMENTS_IN_PEG_IN_WITNESS = 0x09;
static constexpr uint8_t PSBT_ELEMENTS_IN_ISSUANCE_INFLATION_KEYS_AMOUNT = 0x0a;
static constexpr uint8_t PSBT_ELEMENTS_IN_ISSUANCE_INFLATION_KEYS_COMMITMENT = 0x0b;
static constexpr uint8_t PSBT_ELEMENTS_IN_ISSUANCE_BLINDING_NONCE = 0x0c;
static constexpr uint8_t PSBT_ELEMENTS_IN_ISSUANCE_ASSET_ENTROPY = 0x0d;
static constexpr uint8_t PSBT_ELEMENTS_IN_UTXO_RANGEPROOF = 0x0e;
static constexpr uint8_t PSBT_ELEMENTS_IN_ISSUANCE_BLIND_VALUE_PROOF = 0x0f;
static constexpr uint8_t PSBT_ELEMENTS_IN_ISSUANCE_BLIND_INFLATION_KEYS_PROOF = 0x10;
static constexpr uint8_t PSBT_ELEMENTS_IN_EXPLICIT_VALUE = 0x11;
static constexpr uint8_t PSBT_ELEMENTS_IN_VALUE_PROOF = 0x12;
static constexpr uint8_t PSBT_ELEMENTS_IN_EXPLICIT_ASSET = 0x13;
static constexpr uint8_t PSBT_ELEMENTS_IN_ASSET_PROOF = 0x14;
static constexpr uint8_t PSBT_ELEMENTS_IN_BLINDED_ISSUANCE = 0x15;
static constexpr uint8_t PSBT_ELEMENTS_IN_ASSET_BLINDING_FACTOR = 0x16;

// Output types
static constexpr uint8_t PSBT_OUT_REDEEMSCRIPT = 0x00;
static constexpr uint8_t PSBT_OUT_WITNESSSCRIPT = 0x01;
static constexpr uint8_t PSBT_OUT_BIP32_DERIVATION = 0x02;
static constexpr uint8_t PSBT_OUT_AMOUNT = 0x03;
static constexpr uint8_t PSBT_OUT_SCRIPT = 0x04;
static constexpr uint8_t PSBT_OUT_PROPRIETARY = 0xFC;
// Elements proprietary types
static constexpr uint8_t PSBT_ELEMENTS_OUT_VALUE_COMMITMENT = 0x01;
static constexpr uint8_t PSBT_ELEMENTS_OUT_ASSET = 0x02;
static constexpr uint8_t PSBT_ELEMENTS_OUT_ASSET_COMMITMENT = 0x03;
static constexpr uint8_t PSBT_ELEMENTS_OUT_VALUE_RANGEPROOF = 0x04;
static constexpr uint8_t PSBT_ELEMENTS_OUT_ASSET_SURJECTION_PROOF = 0x05;
static constexpr uint8_t PSBT_ELEMENTS_OUT_BLINDING_PUBKEY = 0x06;
static constexpr uint8_t PSBT_ELEMENTS_OUT_ECDH_PUBKEY = 0x07;
static constexpr uint8_t PSBT_ELEMENTS_OUT_BLINDER_INDEX = 0x08;
static constexpr uint8_t PSBT_ELEMENTS_OUT_BLIND_VALUE_PROOF = 0x09;
static constexpr uint8_t PSBT_ELEMENTS_OUT_BLIND_ASSET_PROOF = 0x0a;
static constexpr uint8_t PSBT_ELEMENTS_OUT_ASSET_BLINDING_FACTOR = 0x0b;

// Proprietary type identifier string
static const std::vector<unsigned char> PSBT_ELEMENTS_ID = {'p', 's', 'e', 't'};

// The separator is 0x00. Reading this in means that the unserializer can interpret it
// as a 0 length key which indicates that this is the separator. The separator has no value.
static constexpr uint8_t PSBT_SEPARATOR = 0x00;

// BIP 174 does not specify a maximum file size, but we set a limit anyway
// to prevent reading a stream indefinitely and running out of memory.
const std::streamsize MAX_FILE_SIZE_PSBT = 100000000; // 100 MiB

// PSBT version number
static constexpr uint32_t PSBT_HIGHEST_VERSION = 2;

/** A structure for PSBT proprietary types */
struct PSBTProprietary
{
    uint64_t subtype;
    std::vector<unsigned char> identifier;
    std::vector<unsigned char> key;
    std::vector<unsigned char> value;

    bool operator<(const PSBTProprietary &b) const {
        return key < b.key;
    }
    bool operator==(const PSBTProprietary &b) const {
        return key == b.key;
    }
};

// Takes a stream and multiple arguments and serializes them as if first serialized into a vector and then into the stream
// The resulting output into the stream has the total serialized length of all of the objects followed by all objects concatenated with each other.
template<typename Stream, typename... X>
void SerializeToVector(Stream& s, const X&... args)
{
    WriteCompactSize(s, GetSerializeSizeMany(s.GetVersion(), args...));
    SerializeMany(s, args...);
}

// Takes a stream and multiple arguments and unserializes them first as a vector then each object individually in the order provided in the arguments
template<typename Stream, typename... X>
void UnserializeFromVector(Stream& s, X&... args)
{
    size_t expected_size = ReadCompactSize(s);
    if (!expected_size) {
        return; /* Zero size = no data to read */
    }
    size_t remaining_before = s.size();
    UnserializeMany(s, args...);
    size_t remaining_after = s.size();
    if (remaining_after + expected_size != remaining_before) {
        throw std::ios_base::failure("Size of value was not the stated size");
    }
}

// Deserialize an individual HD keypath to a stream
template<typename Stream>
void DeserializeHDKeypath(Stream& s, KeyOriginInfo& hd_keypath)
{
    // Read in key path
    uint64_t value_len = ReadCompactSize(s);
    if (value_len % 4 || value_len == 0) {
        throw std::ios_base::failure("Invalid length for HD key path");
    }

    s >> hd_keypath.fingerprint;
    for (unsigned int i = 4; i < value_len; i += sizeof(uint32_t)) {
        uint32_t index;
        s >> index;
        hd_keypath.path.push_back(index);
    }
}

// Deserialize HD keypaths into a map
template<typename Stream>
void DeserializeHDKeypaths(Stream& s, const std::vector<unsigned char>& key, std::map<CPubKey, KeyOriginInfo>& hd_keypaths)
{
    // Make sure that the key is the size of pubkey + 1
    if (key.size() != CPubKey::SIZE + 1 && key.size() != CPubKey::COMPRESSED_SIZE + 1) {
        throw std::ios_base::failure("Size of key was not the expected size for the type BIP32 keypath");
    }
    // Read in the pubkey from key
    CPubKey pubkey(key.begin() + 1, key.end());
    if (!pubkey.IsFullyValid()) {
       throw std::ios_base::failure("Invalid pubkey");
    }
    if (hd_keypaths.count(pubkey) > 0) {
        throw std::ios_base::failure("Duplicate Key, pubkey derivation path already provided");
    }

    KeyOriginInfo keypath;
    DeserializeHDKeypath(s, keypath);

    // Add to map
    hd_keypaths.emplace(pubkey, std::move(keypath));
}

// Serialize an individual HD keypath to a stream
template<typename Stream>
void SerializeHDKeypath(Stream& s, KeyOriginInfo hd_keypath)
{
    WriteCompactSize(s, (hd_keypath.path.size() + 1) * sizeof(uint32_t));
    s << hd_keypath.fingerprint;
    for (const auto& path : hd_keypath.path) {
        s << path;
    }
}

// Serialize HD keypaths to a stream from a map
template<typename Stream>
void SerializeHDKeypaths(Stream& s, const std::map<CPubKey, KeyOriginInfo>& hd_keypaths, CompactSizeWriter type)
{
    for (auto keypath_pair : hd_keypaths) {
        if (!keypath_pair.first.IsValid()) {
            throw std::ios_base::failure("Invalid CPubKey being serialized");
        }
        SerializeToVector(s, type, Span(keypath_pair.first));
        SerializeHDKeypath(s, keypath_pair.second);
    }
}

/** A structure for PSBTs which contain per-input information */
struct PSBTInput
{
    CTransactionRef non_witness_utxo;
    CTxOut witness_utxo;
    CScript redeem_script;
    CScript witness_script;
    CScript final_script_sig;
    CScriptWitness final_script_witness;
    std::map<CPubKey, KeyOriginInfo> hd_keypaths;
    std::map<CKeyID, SigPair> partial_sigs;
    uint256 prev_txid;
    std::optional<uint32_t> prev_out{std::nullopt};
    std::optional<uint32_t> sequence{std::nullopt};
    std::optional<uint32_t> time_locktime{std::nullopt};
    std::optional<uint32_t> height_locktime{std::nullopt};
    std::map<uint160, std::vector<unsigned char>> ripemd160_preimages;
    std::map<uint256, std::vector<unsigned char>> sha256_preimages;
    std::map<uint160, std::vector<unsigned char>> hash160_preimages;
    std::map<uint256, std::vector<unsigned char>> hash256_preimages;
    std::map<std::vector<unsigned char>, std::vector<unsigned char>> unknown;
    std::set<PSBTProprietary> m_proprietary;
    std::optional<int> sighash_type;

    uint32_t m_psbt_version;

    // Elements proprietary fields
    // Issuances
    std::optional<CAmount> m_issuance_value{std::nullopt};
    CConfidentialValue m_issuance_value_commitment;
    std::vector<unsigned char> m_issuance_rangeproof;
    std::vector<unsigned char> m_issuance_inflation_keys_rangeproof;
    std::optional<CAmount> m_issuance_inflation_keys_amount{std::nullopt};
    CConfidentialValue m_issuance_inflation_keys_commitment;
    uint256 m_issuance_blinding_nonce;
    uint256 m_issuance_asset_entropy;
    std::vector<unsigned char> m_blind_issuance_value_proof;
    std::vector<unsigned char> m_blind_issuance_inflation_keys_proof;
    std::optional<bool> m_blinded_issuance;

    // Peg-in
    std::variant<std::monostate, Sidechain::Bitcoin::CTransactionRef, CTransactionRef> m_peg_in_tx;
    std::variant<std::monostate, Sidechain::Bitcoin::CMerkleBlock, CMerkleBlock> m_peg_in_txout_proof;
    CScript m_peg_in_claim_script;
    uint256 m_peg_in_genesis_hash;
    std::optional<CAmount> m_peg_in_value{std::nullopt};
    CScriptWitness m_peg_in_witness;

    // Auxiliary elements stuff
    std::vector<unsigned char> m_utxo_rangeproof;
    std::optional<CAmount> m_explicit_value;
    std::vector<unsigned char> m_value_proof;
    uint256 m_explicit_asset;
    std::vector<unsigned char> m_asset_proof;
    std::optional<uint256> m_asset_blinding_factor{std::nullopt};

    bool IsNull() const;
    void FillSignatureData(SignatureData& sigdata) const;
    void FromSignatureData(const SignatureData& sigdata);
    bool Merge(const PSBTInput& input);
    bool GetUTXO(CTxOut& utxo) const;
    COutPoint GetOutPoint() const;
    PSBTInput(uint32_t version) : m_psbt_version(version) {}

    template <typename Stream>
    inline void Serialize(Stream& s) const {
        // Write the utxo
        if (non_witness_utxo) {
            SerializeToVector(s, CompactSizeWriter(PSBT_IN_NON_WITNESS_UTXO));
            OverrideStream<Stream> os(&s, s.GetType(), s.GetVersion() | SERIALIZE_TRANSACTION_NO_WITNESS);
            SerializeToVector(os, non_witness_utxo);
        }
        if (!witness_utxo.IsNull()) {
            SerializeToVector(s, CompactSizeWriter(PSBT_IN_WITNESS_UTXO));
            SerializeToVector(s, witness_utxo);
        }

        if (final_script_sig.empty() && final_script_witness.IsNull()) {
            // Write any partial signatures
            for (auto sig_pair : partial_sigs) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PARTIAL_SIG), Span{sig_pair.second.first});
                s << sig_pair.second.second;
            }

            // Write the sighash type
            if (sighash_type != std::nullopt) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_SIGHASH));
                SerializeToVector(s, *sighash_type);
            }

            // Write the redeem script
            if (!redeem_script.empty()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_REDEEMSCRIPT));
                s << redeem_script;
            }

            // Write the witness script
            if (!witness_script.empty()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_WITNESSSCRIPT));
                s << witness_script;
            }

            // Write any hd keypaths
            SerializeHDKeypaths(s, hd_keypaths, CompactSizeWriter(PSBT_IN_BIP32_DERIVATION));

            // Write any ripemd160 preimage
            for (const auto& [hash, preimage] : ripemd160_preimages) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_RIPEMD160), Span{hash});
                s << preimage;
            }

            // Write any sha256 preimage
            for (const auto& [hash, preimage] : sha256_preimages) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_SHA256), Span{hash});
                s << preimage;
            }

            // Write any hash160 preimage
            for (const auto& [hash, preimage] : hash160_preimages) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_HASH160), Span{hash});
                s << preimage;
            }

            // Write any hash256 preimage
            for (const auto& [hash, preimage] : hash256_preimages) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_HASH256), Span{hash});
                s << preimage;
            }
        }

        // Write script sig
        if (!final_script_sig.empty()) {
            SerializeToVector(s, CompactSizeWriter(PSBT_IN_SCRIPTSIG));
            s << final_script_sig;
        }
        // write script witness
        if (!final_script_witness.IsNull()) {
            SerializeToVector(s, CompactSizeWriter(PSBT_IN_SCRIPTWITNESS));
            SerializeToVector(s, final_script_witness.stack);
        }

        // Write PSBTv2 fields
        if (m_psbt_version >= 2) {
            // Write prev txid, vout, sequence, and lock times
            if (!prev_txid.IsNull()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PREVIOUS_TXID));
                SerializeToVector(s, prev_txid);
            }
            if (prev_out != std::nullopt) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_OUTPUT_INDEX));
                SerializeToVector(s, *prev_out);
            }
            if (sequence != std::nullopt) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_SEQUENCE));
                SerializeToVector(s, *sequence);
            }
            if (time_locktime != std::nullopt) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_REQUIRED_TIME_LOCKTIME));
                SerializeToVector(s, *time_locktime);
            }
            if (height_locktime != std::nullopt) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_REQUIRED_HEIGHT_LOCKTIME));
                SerializeToVector(s, *height_locktime);
            }

            // Elements proprietary fields are only allowed with v2
            // Issuance value + commitment
            if (m_issuance_value != std::nullopt) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_ISSUANCE_VALUE));
                SerializeToVector(s, *m_issuance_value);
            }
            if (!m_issuance_value_commitment.IsNull()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_ISSUANCE_VALUE_COMMITMENT));
                SerializeToVector(s, m_issuance_value_commitment);
            }

            // Issuance rangeproof
            if (!m_issuance_rangeproof.empty()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_ISSUANCE_VALUE_RANGEPROOF));
                s << m_issuance_rangeproof;
            }

            // Issuance inflation keys rangeproof
            if (!m_issuance_inflation_keys_rangeproof.empty()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_ISSUANCE_INFLATION_KEYS_RANGEPROOF));
                s << m_issuance_inflation_keys_rangeproof;
            }

            if (Params().GetConsensus().ParentChainHasPow()) {
                // Peg-in tx
                if (m_peg_in_tx.index() > 0) {
                    const auto peg_in_tx = std::get_if<Sidechain::Bitcoin::CTransactionRef>(&m_peg_in_tx);
                    if (peg_in_tx) {
                        SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_PEG_IN_TX));
                        OverrideStream<Stream> os(&s, s.GetType(), s.GetVersion() | SERIALIZE_TRANSACTION_NO_WITNESS);
                        SerializeToVector(os, *peg_in_tx);
                    }
                }

                // Peg-in proof
                if (m_peg_in_txout_proof.index() > 0) {
                    const auto txout_proof = std::get_if<Sidechain::Bitcoin::CMerkleBlock>(&m_peg_in_txout_proof);
                    if (txout_proof) {
                        SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_PEG_IN_TXOUT_PROOF));
                        SerializeToVector(s, *txout_proof);
                    }
                }
            } else {
                // Peg-in tx
                if (m_peg_in_tx.index() > 0) {
                    const auto peg_in_tx = std::get_if<CTransactionRef>(&m_peg_in_tx);
                    if (peg_in_tx) {
                        SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_PEG_IN_TX));
                        OverrideStream<Stream> os(&s, s.GetType(), s.GetVersion() | SERIALIZE_TRANSACTION_NO_WITNESS);
                        SerializeToVector(os, *peg_in_tx);
                    }
                }

                // Peg-in proof
                if (m_peg_in_txout_proof.index() > 0) {
                    const auto txout_proof = std::get_if<CMerkleBlock>(&m_peg_in_txout_proof);
                    if (txout_proof) {
                        SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_PEG_IN_TXOUT_PROOF));
                        SerializeToVector(s, *txout_proof);
                    }
                }
            }

            // Peg-in genesis hash
            if (!m_peg_in_genesis_hash.IsNull()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_PEG_IN_GENESIS_HASH));
                SerializeToVector(s, m_peg_in_genesis_hash);
            }

            // Peg-in claim script
            if (!m_peg_in_claim_script.empty()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_PEG_IN_CLAIM_SCRIPT));
                s << m_peg_in_claim_script;
            }

            // Peg-in value
            if (m_peg_in_value != std::nullopt) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_PEG_IN_VALUE));
                SerializeToVector(s, *m_peg_in_value);
            }

            // Peg-in witness
            if (!m_peg_in_witness.IsNull()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_PEG_IN_WITNESS));
                SerializeToVector(s, m_peg_in_witness.stack);
            }

            // Issuance inflation keys amount
            if (m_issuance_inflation_keys_amount != std::nullopt) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_ISSUANCE_INFLATION_KEYS_AMOUNT));
                SerializeToVector(s, *m_issuance_inflation_keys_amount);
            }

            // Issuance inflation keys commitment
            if (!m_issuance_inflation_keys_commitment.IsNull()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_ISSUANCE_INFLATION_KEYS_COMMITMENT));
                SerializeToVector(s, m_issuance_inflation_keys_commitment);
            }

            // Issuance blinding nonce
            if (!m_issuance_blinding_nonce.IsNull()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_ISSUANCE_BLINDING_NONCE));
                SerializeToVector(s, m_issuance_blinding_nonce);
            }

            // Issuance asset entropy
            if (!m_issuance_asset_entropy.IsNull()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_ISSUANCE_ASSET_ENTROPY));
                SerializeToVector(s, m_issuance_asset_entropy);
            }

            // UTXO rangeproof
            if (!m_utxo_rangeproof.empty()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_OUT_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_UTXO_RANGEPROOF));
                s << m_utxo_rangeproof;
            }

            // Blind issuance value proof
            if (!m_blind_issuance_value_proof.empty()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_OUT_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_ISSUANCE_BLIND_VALUE_PROOF));
                s << m_blind_issuance_value_proof;
            }

            // Blind issuance inflation keys value proof
            if (!m_blind_issuance_inflation_keys_proof.empty()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_OUT_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_ISSUANCE_BLIND_INFLATION_KEYS_PROOF));
                s << m_blind_issuance_inflation_keys_proof;
            }

            // Explicit value and its proof
            if (m_explicit_value.has_value()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_EXPLICIT_VALUE));
                SerializeToVector(s, m_explicit_value.value());
            }
            if (!m_value_proof.empty()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_VALUE_PROOF));
                s << m_value_proof;
            }

            // Explicit asset and its proof
            if (!m_explicit_asset.IsNull()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_EXPLICIT_ASSET));
                SerializeToVector(s, m_explicit_asset);
            }
            if (!m_asset_proof.empty()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_ASSET_PROOF));
                s << m_asset_proof;
            }

            if (m_blinded_issuance.has_value()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_BLINDED_ISSUANCE));
                SerializeToVector(s, *m_blinded_issuance);
            }

            // Asset blinding factor
            if (m_asset_blinding_factor.has_value()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_IN_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_IN_ASSET_BLINDING_FACTOR));
                SerializeToVector(s, m_asset_blinding_factor.value());
            }
        }

        // Write proprietary things
        for (const auto& entry : m_proprietary) {
            s << entry.key;
            s << entry.value;
        }

        // Write unknown things
        for (auto& entry : unknown) {
            s << entry.first;
            s << entry.second;
        }

        s << PSBT_SEPARATOR;
    }


    template <typename Stream>
    inline void Unserialize(Stream& s) {
        // Used for duplicate key detection
        std::set<std::vector<unsigned char>> key_lookup;

        // Read loop
        bool found_sep = false;
        while(!s.empty()) {
            // Read
            std::vector<unsigned char> key;
            s >> key;

            // the key is empty if that was actually a separator byte
            // This is a special case for key lengths 0 as those are not allowed (except for separator)
            if (key.empty()) {
                found_sep = true;
                break;
            }

            // Type is compact size uint at beginning of key
            SpanReader skey(s.GetType(), s.GetVersion(), key);
            uint64_t type = ReadCompactSize(skey);

            // Do stuff based on type
            switch(type) {
                case PSBT_IN_NON_WITNESS_UTXO:
                {
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, input non-witness utxo already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Non-witness utxo key is more than one byte type");
                    }
                    // Set the stream to unserialize with witness since this is always a valid network transaction
                    OverrideStream<Stream> os(&s, s.GetType(), s.GetVersion() & ~SERIALIZE_TRANSACTION_NO_WITNESS);
                    UnserializeFromVector(os, non_witness_utxo);
                    break;
                }
                case PSBT_IN_WITNESS_UTXO:
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, input witness utxo already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Witness utxo key is more than one byte type");
                    }
                    UnserializeFromVector(s, witness_utxo);
                    break;
                case PSBT_IN_PARTIAL_SIG:
                {
                    // Make sure that the key is the size of pubkey + 1
                    if (key.size() != CPubKey::SIZE + 1 && key.size() != CPubKey::COMPRESSED_SIZE + 1) {
                        throw std::ios_base::failure("Size of key was not the expected size for the type partial signature pubkey");
                    }
                    // Read in the pubkey from key
                    CPubKey pubkey(key.begin() + 1, key.end());
                    if (!pubkey.IsFullyValid()) {
                       throw std::ios_base::failure("Invalid pubkey");
                    }
                    if (partial_sigs.count(pubkey.GetID()) > 0) {
                        throw std::ios_base::failure("Duplicate Key, input partial signature for pubkey already provided");
                    }

                    // Read in the signature from value
                    std::vector<unsigned char> sig;
                    s >> sig;

                    // Add to list
                    partial_sigs.emplace(pubkey.GetID(), SigPair(pubkey, std::move(sig)));
                    break;
                }
                case PSBT_IN_SIGHASH:
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, input sighash type already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Sighash type key is more than one byte type");
                    }
                    int sighash;
                    UnserializeFromVector(s, sighash);
                    sighash_type = sighash;
                    break;
                case PSBT_IN_REDEEMSCRIPT:
                {
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, input redeemScript already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Input redeemScript key is more than one byte type");
                    }
                    s >> redeem_script;
                    break;
                }
                case PSBT_IN_WITNESSSCRIPT:
                {
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, input witnessScript already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Input witnessScript key is more than one byte type");
                    }
                    s >> witness_script;
                    break;
                }
                case PSBT_IN_BIP32_DERIVATION:
                {
                    DeserializeHDKeypaths(s, key, hd_keypaths);
                    break;
                }
                case PSBT_IN_SCRIPTSIG:
                {
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, input final scriptSig already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Final scriptSig key is more than one byte type");
                    }
                    s >> final_script_sig;
                    break;
                }
                case PSBT_IN_SCRIPTWITNESS:
                {
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, input final scriptWitness already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Final scriptWitness key is more than one byte type");
                    }
                    UnserializeFromVector(s, final_script_witness.stack);
                    break;
                }
                case PSBT_IN_PREVIOUS_TXID:
                {
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, previous txid is already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Previous txid key is more than one byte type");
                    } else if (m_psbt_version == 0) {
                        throw std::ios_base::failure("Previous txid is only allowed in PSBTv2");
                    }
                    UnserializeFromVector(s, prev_txid);
                    break;
                }
                case PSBT_IN_OUTPUT_INDEX:
                {
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, previous output's index is already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Previous output's index is more than one byte type");
                    } else if (m_psbt_version == 0) {
                        throw std::ios_base::failure("Previous output's index is only allowed in PSBTv2");
                    }
                    uint32_t v;
                    UnserializeFromVector(s, v);
                    prev_out = v;
                    break;
                }
                case PSBT_IN_SEQUENCE:
                {
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, sequence is already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Sequence key is more than one byte type");
                    } else if (m_psbt_version == 0) {
                        throw std::ios_base::failure("Sequence is only allowed in PSBTv2");
                    }
                    uint32_t v;
                    UnserializeFromVector(s, v);
                    sequence = v;
                    break;
                }
                case PSBT_IN_REQUIRED_TIME_LOCKTIME:
                {
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, required time based locktime is already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Required time based locktime is more than one byte type");
                    } else if (m_psbt_version == 0) {
                        throw std::ios_base::failure("Required time based locktime is only allowed in PSBTv2");
                    }
                    uint32_t v;
                    UnserializeFromVector(s, v);
                    time_locktime = v;
                    break;
                }
                case PSBT_IN_REQUIRED_HEIGHT_LOCKTIME:
                {
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, required height based locktime is already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Required height based locktime is more than one byte type");
                    } else if (m_psbt_version == 0) {
                        throw std::ios_base::failure("Required height based locktime is only allowed in PSBTv2");
                    }
                    uint32_t v;
                    UnserializeFromVector(s, v);
                    height_locktime = v;
                    break;
                }
                case PSBT_IN_RIPEMD160:
                {
                    // Make sure that the key is the size of a ripemd160 hash + 1
                    if (key.size() != CRIPEMD160::OUTPUT_SIZE + 1) {
                        throw std::ios_base::failure("Size of key was not the expected size for the type ripemd160 preimage");
                    }
                    // Read in the hash from key
                    std::vector<unsigned char> hash_vec(key.begin() + 1, key.end());
                    uint160 hash(hash_vec);
                    if (ripemd160_preimages.count(hash) > 0) {
                        throw std::ios_base::failure("Duplicate Key, input ripemd160 preimage already provided");
                    }

                    // Read in the preimage from value
                    std::vector<unsigned char> preimage;
                    s >> preimage;

                    // Add to preimages list
                    ripemd160_preimages.emplace(hash, std::move(preimage));
                    break;
                }
                case PSBT_IN_SHA256:
                {
                    // Make sure that the key is the size of a sha256 hash + 1
                    if (key.size() != CSHA256::OUTPUT_SIZE + 1) {
                        throw std::ios_base::failure("Size of key was not the expected size for the type sha256 preimage");
                    }
                    // Read in the hash from key
                    std::vector<unsigned char> hash_vec(key.begin() + 1, key.end());
                    uint256 hash(hash_vec);
                    if (sha256_preimages.count(hash) > 0) {
                        throw std::ios_base::failure("Duplicate Key, input sha256 preimage already provided");
                    }

                    // Read in the preimage from value
                    std::vector<unsigned char> preimage;
                    s >> preimage;

                    // Add to preimages list
                    sha256_preimages.emplace(hash, std::move(preimage));
                    break;
                }
                case PSBT_IN_HASH160:
                {
                    // Make sure that the key is the size of a hash160 hash + 1
                    if (key.size() != CHash160::OUTPUT_SIZE + 1) {
                        throw std::ios_base::failure("Size of key was not the expected size for the type hash160 preimage");
                    }
                    // Read in the hash from key
                    std::vector<unsigned char> hash_vec(key.begin() + 1, key.end());
                    uint160 hash(hash_vec);
                    if (hash160_preimages.count(hash) > 0) {
                        throw std::ios_base::failure("Duplicate Key, input hash160 preimage already provided");
                    }

                    // Read in the preimage from value
                    std::vector<unsigned char> preimage;
                    s >> preimage;

                    // Add to preimages list
                    hash160_preimages.emplace(hash, std::move(preimage));
                    break;
                }
                case PSBT_IN_HASH256:
                {
                    // Make sure that the key is the size of a hash256 hash + 1
                    if (key.size() != CHash256::OUTPUT_SIZE + 1) {
                        throw std::ios_base::failure("Size of key was not the expected size for the type hash256 preimage");
                    }
                    // Read in the hash from key
                    std::vector<unsigned char> hash_vec(key.begin() + 1, key.end());
                    uint256 hash(hash_vec);
                    if (hash256_preimages.count(hash) > 0) {
                        throw std::ios_base::failure("Duplicate Key, input hash256 preimage already provided");
                    }

                    // Read in the preimage from value
                    std::vector<unsigned char> preimage;
                    s >> preimage;

                    // Add to preimages list
                    hash256_preimages.emplace(hash, std::move(preimage));
                    break;
                }
                case PSBT_IN_PROPRIETARY:
                {
                    bool known = false;
                    PSBTProprietary this_prop;
                    skey >> this_prop.identifier;
                    size_t subkey_len = skey.size();
                    this_prop.subtype = ReadCompactSize(skey);

                    if (this_prop.identifier == PSBT_ELEMENTS_ID) {
                        known = true;

                        switch(this_prop.subtype) {
                            case PSBT_ELEMENTS_IN_ISSUANCE_VALUE:
                            {
                                if (m_issuance_value != std::nullopt) {
                                    throw std::ios_base::failure("Duplicate Key, input issuance value already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Input issuance value is more than one byte type");
                                }
                                CAmount amt;
                                UnserializeFromVector(s, amt);
                                m_issuance_value = amt;
                                break;
                            }
                            case PSBT_ELEMENTS_IN_ISSUANCE_VALUE_COMMITMENT:
                            {
                                if (!m_issuance_value_commitment.IsNull()) {
                                    throw std::ios_base::failure("Duplicate Key, input issuance value commitment already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Input issuance value commitment key is more than one byte type");
                                }
                                UnserializeFromVector(s, m_issuance_value_commitment);
                                break;
                            }
                            case PSBT_ELEMENTS_IN_ISSUANCE_VALUE_RANGEPROOF:
                            {
                                if (!m_issuance_rangeproof.empty()) {
                                    throw std::ios_base::failure("Duplicate Key, input issuance value rangeproof already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Input issuance value rangeproof key is more than one byte type");
                                }
                                s >> m_issuance_rangeproof;
                                break;
                            }
                            case PSBT_ELEMENTS_IN_ISSUANCE_INFLATION_KEYS_RANGEPROOF:
                            {
                                if (!m_issuance_inflation_keys_rangeproof.empty()) {
                                    throw std::ios_base::failure("Duplicate Key, input issuance inflation keys rangeproof already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Input issuance inflation keys rangeproof key is more than one byte type");
                                }
                                s >> m_issuance_inflation_keys_rangeproof;
                                break;
                            }
                            case PSBT_ELEMENTS_IN_PEG_IN_TX:
                            {
                                if (m_peg_in_tx.index() != 0) {
                                    throw std::ios_base::failure("Duplicate Key, peg-in tx already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Peg-in tx key is more than one byte type");
                                }
                                if (Params().GetConsensus().ParentChainHasPow()) {
                                    Sidechain::Bitcoin::CTransactionRef tx;
                                    OverrideStream<Stream> os(&s, s.GetType(), s.GetVersion());
                                    UnserializeFromVector(os, tx);
                                    m_peg_in_tx = tx;
                                } else {
                                    CTransactionRef tx;
                                    OverrideStream<Stream> os(&s, s.GetType(), s.GetVersion());
                                    UnserializeFromVector(os, tx);
                                    m_peg_in_tx = tx;
                                }
                                break;
                            }
                            case PSBT_ELEMENTS_IN_PEG_IN_TXOUT_PROOF:
                            {
                                if (m_peg_in_txout_proof.index() != 0) {
                                    throw std::ios_base::failure("Duplicate Key, peg-in txout proof already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Peg-in txout proof key is more than one byte type");
                                }
                                if (Params().GetConsensus().ParentChainHasPow()) {
                                    Sidechain::Bitcoin::CMerkleBlock tx_proof;
                                    UnserializeFromVector(s, tx_proof);
                                    m_peg_in_txout_proof = tx_proof;
                                } else {
                                    CMerkleBlock tx_proof;
                                    UnserializeFromVector(s, tx_proof);
                                    m_peg_in_txout_proof = tx_proof;
                                }
                                break;
                            }
                            case PSBT_ELEMENTS_IN_PEG_IN_GENESIS_HASH:
                            {
                                if (!m_peg_in_genesis_hash.IsNull()) {
                                    throw std::ios_base::failure("Duplicate Key, peg-in genesis hash already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Peg-in genesis hash is more than one byte type");
                                }
                                UnserializeFromVector(s, m_peg_in_genesis_hash);
                                break;
                            }
                            case PSBT_ELEMENTS_IN_PEG_IN_CLAIM_SCRIPT:
                            {
                                if (!m_peg_in_claim_script.empty()) {
                                    throw std::ios_base::failure("Duplicate Key, peg-in claim script already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Peg-in claim script key is more than one byte type");
                                }
                                s >> m_peg_in_claim_script;
                                break;
                            }
                            case PSBT_ELEMENTS_IN_PEG_IN_VALUE:
                            {
                                if (m_peg_in_value != std::nullopt) {
                                    throw std::ios_base::failure("Duplicate Key, input issuance value already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Input issuance value is more than one byte type");
                                }
                                CAmount amt;
                                UnserializeFromVector(s, amt);
                                m_peg_in_value = amt;
                                break;
                            }
                            case PSBT_ELEMENTS_IN_PEG_IN_WITNESS:
                            {
                                if (!m_peg_in_witness.IsNull()) {
                                    throw std::ios_base::failure("Duplicate Key, input peg-in witness already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Input peg-in witness key is more than one byte type");
                                }
                                UnserializeFromVector(s, m_peg_in_witness.stack);
                                break;
                            }
                            case PSBT_ELEMENTS_IN_ISSUANCE_INFLATION_KEYS_AMOUNT:
                            {
                                if (m_issuance_inflation_keys_amount != std::nullopt) {
                                    throw std::ios_base::failure("Duplicate Key, input issuance inflation keys already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Input issuance inflation keys is more than one byte type");
                                }
                                CAmount amt;
                                UnserializeFromVector(s, amt);
                                m_issuance_inflation_keys_amount = amt;
                                break;
                            }
                            case PSBT_ELEMENTS_IN_ISSUANCE_INFLATION_KEYS_COMMITMENT:
                            {
                                if (!m_issuance_inflation_keys_commitment.IsNull()) {
                                    throw std::ios_base::failure("Duplicate Key, input issuance inflation keys commitment already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Input issuance inflation keys commitment key is more than one byte type");
                                }
                                UnserializeFromVector(s, m_issuance_inflation_keys_commitment);
                                break;
                            }
                            case PSBT_ELEMENTS_IN_ISSUANCE_BLINDING_NONCE:
                            {
                                if (!m_issuance_blinding_nonce.IsNull()) {
                                    throw std::ios_base::failure("Duplicate Key, input issuance blinding nonce already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Input issuance blinding nonce is more than one byte type");
                                }
                                UnserializeFromVector(s, m_issuance_blinding_nonce);
                                break;
                            }
                            case PSBT_ELEMENTS_IN_ISSUANCE_ASSET_ENTROPY:
                            {
                                if (!m_issuance_asset_entropy.IsNull()) {
                                    throw std::ios_base::failure("Duplicate Key, input issuance asset entropy already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Input issuance asset entropy is more than one byte type");
                                }
                                UnserializeFromVector(s, m_issuance_asset_entropy);
                                break;
                            }
                            case PSBT_ELEMENTS_IN_UTXO_RANGEPROOF:
                            {
                                if (!m_utxo_rangeproof.empty()) {
                                    throw std::ios_base::failure("Duplicate Key, input utxo rangeproof already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Input UTXO rangeproof key is more than one byte type");
                                }
                                s >> m_utxo_rangeproof;
                                break;
                            }
                            case PSBT_ELEMENTS_IN_ISSUANCE_BLIND_VALUE_PROOF:
                            {
                                if (!m_blind_issuance_value_proof.empty()) {
                                    throw std::ios_base::failure("Duplicate Key, input blind issuance value proof already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Input blind issuance value key is more than one byte type");
                                }
                                s >> m_blind_issuance_value_proof;
                                break;
                            }
                            case PSBT_ELEMENTS_IN_ISSUANCE_BLIND_INFLATION_KEYS_PROOF:
                            {
                                if (!m_blind_issuance_inflation_keys_proof.empty()) {
                                    throw std::ios_base::failure("Duplicate Key, input blind issuance inflation keys value proof already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Input blind issuance inflation keys value proof key is more than one byte type");
                                }
                                s >> m_blind_issuance_inflation_keys_proof;
                                break;
                            }
                            case PSBT_ELEMENTS_IN_EXPLICIT_VALUE:
                            {
                                if (!key_lookup.emplace(key).second) {
                                    throw std::ios_base::failure("Duplicate Key, explicit value is already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Input explicit value is more than one byte type");
                                }
                                CAmount v;
                                UnserializeFromVector(s, v);
                                m_explicit_value = v;
                                break;
                            }
                            case PSBT_ELEMENTS_IN_VALUE_PROOF:
                            {
                                if (!key_lookup.emplace(key).second) {
                                    throw std::ios_base::failure("Duplicate Key, explicit value proof is already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Input explicit value proof is more than one byte type");
                                }
                                s >> m_value_proof;
                                break;
                            }
                            case PSBT_ELEMENTS_IN_EXPLICIT_ASSET:
                            {
                                if (!key_lookup.emplace(key).second) {
                                    throw std::ios_base::failure("Duplicate Key, explicit asset is already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Input explicit asset is more than one byte type");
                                }
                                UnserializeFromVector(s, m_explicit_asset);
                                break;
                            }
                            case PSBT_ELEMENTS_IN_ASSET_PROOF:
                            {
                                if (!key_lookup.emplace(key).second) {
                                    throw std::ios_base::failure("Duplicate Key, explicit asset proof is already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Input explicit asset proof is more than one byte type");
                                }
                                s >> m_asset_proof;
                                break;
                            }
                            case PSBT_ELEMENTS_IN_BLINDED_ISSUANCE:
                            {
                                if (!key_lookup.emplace(key).second) {
                                    throw std::ios_base::failure("Duplicate Key, issuance needs blinded flag is already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Input issuance needs blinded flag is more than one byte type");
                                }
                                bool b;
                                UnserializeFromVector(s, b);
                                m_blinded_issuance = b;
                                break;
                            }
                            case PSBT_ELEMENTS_IN_ASSET_BLINDING_FACTOR:
                            {
                                if (m_asset_blinding_factor.has_value()) {
                                    throw std::ios_base::failure("Duplicate Key, input asset blinding factor is already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Input asset blinding factor is more than one byte type");
                                }
                                uint256 u;
                                UnserializeFromVector(s, u);
                                m_asset_blinding_factor = u;
                                break;
                            }
                            default:
                            {
                                known = false;
                                break;
                            }
                        }
                    }

                    if (!known) {
                        this_prop.key = key;

                        if (m_proprietary.count(this_prop) > 0) {
                            throw std::ios_base::failure("Duplicate Key, proprietary key already found");
                        }
                        s >> this_prop.value;
                        m_proprietary.insert(this_prop);
                    }
                    break;
                }
                // Unknown stuff
                default:
                    if (unknown.count(key) > 0) {
                        throw std::ios_base::failure("Duplicate Key, key for unknown value already provided");
                    }
                    // Read in the value
                    std::vector<unsigned char> val_bytes;
                    s >> val_bytes;
                    unknown.emplace(std::move(key), std::move(val_bytes));
                    break;
            }
        }

        if (!found_sep) {
            throw std::ios_base::failure("Separator is missing at the end of an input map");
        }

        // Make sure required PSBTv2 fields are present
        if (m_psbt_version >= 2) {
            if (prev_txid.IsNull()) {
                throw std::ios_base::failure("Previous TXID is required in PSBTv2");
            }
            if (prev_out == std::nullopt) {
                throw std::ios_base::failure("Previous output's index is required in PSBTv2");
            }
            if (!m_issuance_value_commitment.IsNull() && m_issuance_rangeproof.empty()) {
                throw std::ios_base::failure("Issuance value commitment provided without value rangeproof");
            }
            if (!m_issuance_inflation_keys_commitment.IsNull() && m_issuance_inflation_keys_rangeproof.empty()) {
                throw std::ios_base::failure("Issuance inflation keys commitment provided without inflation keys rangeproof");
            }
            if ((m_explicit_value.has_value() || !m_value_proof.empty()) && (!m_explicit_value.has_value() || m_value_proof.empty())) {
                throw std::ios_base::failure("Input explicit value and value proof must be provided together");
            }
            if ((!m_explicit_asset.IsNull() || !m_asset_proof.empty()) && (m_explicit_asset.IsNull() || m_asset_proof.empty())) {
                throw std::ios_base::failure("Input explicit asset and asset proof must be provided together");
            }
        }
    }

    template <typename Stream>
    PSBTInput(deserialize_type, Stream& s) {
        Unserialize(s);
    }
};

/** A structure for PSBTs which contains per output information */
struct PSBTOutput
{
    CScript redeem_script;
    CScript witness_script;
    std::map<CPubKey, KeyOriginInfo> hd_keypaths;
    std::optional<CAmount> amount{std::nullopt};
    std::optional<CScript> script{std::nullopt};
    std::map<std::vector<unsigned char>, std::vector<unsigned char>> unknown;
    std::set<PSBTProprietary> m_proprietary;

    uint32_t m_psbt_version;

    // Elements proprietary fields
    CConfidentialValue m_value_commitment;
    uint256 m_asset;
    CConfidentialAsset m_asset_commitment;
    std::vector<unsigned char> m_value_rangeproof;
    std::vector<unsigned char> m_asset_surjection_proof;
    CPubKey m_ecdh_pubkey;
    CPubKey m_blinding_pubkey;
    std::optional<uint32_t> m_blinder_index{std::nullopt};
    std::vector<unsigned char> m_blind_value_proof;
    std::vector<unsigned char> m_blind_asset_proof;
    std::optional<uint256> m_asset_blinding_factor{std::nullopt};

    bool IsNull() const;
    void FillSignatureData(SignatureData& sigdata) const;
    void FromSignatureData(const SignatureData& sigdata);
    bool Merge(const PSBTOutput& output);
    bool IsBlinded() const; //! This output has a blinding pubkey and is or will be blinded.
    bool IsPartiallyBlinded() const; //! This output has some blinding information. This is not a good state to be in.
    bool IsFullyBlinded() const; //! This output has all of the blinding information and is actually blinded.
    CTxOut GetTxOut() const;
    PSBTOutput(uint32_t version) : m_psbt_version(version) {}

    template <typename Stream>
    inline void Serialize(Stream& s) const {
        // Write the redeem script
        if (!redeem_script.empty()) {
            SerializeToVector(s, CompactSizeWriter(PSBT_OUT_REDEEMSCRIPT));
            s << redeem_script;
        }

        // Write the witness script
        if (!witness_script.empty()) {
            SerializeToVector(s, CompactSizeWriter(PSBT_OUT_WITNESSSCRIPT));
            s << witness_script;
        }

        // Write any hd keypaths
        SerializeHDKeypaths(s, hd_keypaths, CompactSizeWriter(PSBT_OUT_BIP32_DERIVATION));

        if (m_psbt_version >= 2) {
            // Write amount and spk
            if (amount != std::nullopt) {
                SerializeToVector(s, CompactSizeWriter(PSBT_OUT_AMOUNT));
                SerializeToVector(s, *amount);
            }
            if (script.has_value()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_OUT_SCRIPT));
                s << *script;
            }

            // Elements proprietary fields are v2 only
            // Amount
            if (!m_value_commitment.IsNull()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_OUT_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_OUT_VALUE_COMMITMENT));
                SerializeToVector(s, m_value_commitment);
            }

            // Asset + commitment
            if (!m_asset.IsNull()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_OUT_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_OUT_ASSET));
                SerializeToVector(s, m_asset);
            }
            if (!m_asset_commitment.IsNull()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_OUT_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_OUT_ASSET_COMMITMENT));
                SerializeToVector(s, m_asset_commitment);
            }

            // Value rangeproof
            if (!m_value_rangeproof.empty()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_OUT_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_OUT_VALUE_RANGEPROOF));
                s << m_value_rangeproof;
            }

            // Asset surjection proof
            if (!m_asset_surjection_proof.empty()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_OUT_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_OUT_ASSET_SURJECTION_PROOF));
                s << m_asset_surjection_proof;
            }

            // Blinding pubkey
            if (m_blinding_pubkey.IsValid()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_OUT_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_OUT_BLINDING_PUBKEY));
                s << m_blinding_pubkey;
            }

            // ECDH pubkey
            if (m_ecdh_pubkey.IsValid()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_OUT_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_OUT_ECDH_PUBKEY));
                s << m_ecdh_pubkey;
            }

            // Blinder index
            if (m_blinder_index != std::nullopt) {
                SerializeToVector(s, CompactSizeWriter(PSBT_OUT_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_OUT_BLINDER_INDEX));
                SerializeToVector(s, *m_blinder_index);
            }

            // Blind value proof
            if (!m_blind_value_proof.empty()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_OUT_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_OUT_BLIND_VALUE_PROOF));
                s << m_blind_value_proof;
            }

            // Blind asset proof
            if (!m_blind_asset_proof.empty()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_OUT_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_OUT_BLIND_ASSET_PROOF));
                s << m_blind_asset_proof;
            }

            // Asset blinding factor
            if (m_asset_blinding_factor.has_value()) {
                SerializeToVector(s, CompactSizeWriter(PSBT_OUT_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_OUT_ASSET_BLINDING_FACTOR));
                SerializeToVector(s, m_asset_blinding_factor.value());
            }
        }

        // Write proprietary things
        for (const auto& entry : m_proprietary) {
            s << entry.key;
            s << entry.value;
        }

        // Write unknown things
        for (auto& entry : unknown) {
            s << entry.first;
            s << entry.second;
        }

        s << PSBT_SEPARATOR;
    }


    template <typename Stream>
    inline void Unserialize(Stream& s) {
        // Used for duplicate key detection
        std::set<std::vector<unsigned char>> key_lookup;

        // Read loop
        bool found_sep = false;
        while(!s.empty()) {
            // Read
            std::vector<unsigned char> key;
            s >> key;

            // the key is empty if that was actually a separator byte
            // This is a special case for key lengths 0 as those are not allowed (except for separator)
            if (key.empty()) {
                found_sep = true;
                break;
            }

            // Type is compact size uint at beginning of key
            SpanReader skey(s.GetType(), s.GetVersion(), key);
            uint64_t type = ReadCompactSize(skey);

            // Do stuff based on type
            switch(type) {
                case PSBT_OUT_REDEEMSCRIPT:
                {
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, output redeemScript already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Output redeemScript key is more than one byte type");
                    }
                    s >> redeem_script;
                    break;
                }
                case PSBT_OUT_WITNESSSCRIPT:
                {
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, output witnessScript already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Output witnessScript key is more than one byte type");
                    }
                    s >> witness_script;
                    break;
                }
                case PSBT_OUT_BIP32_DERIVATION:
                {
                    DeserializeHDKeypaths(s, key, hd_keypaths);
                    break;
                }
                case PSBT_OUT_AMOUNT:
                {
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, output amount is already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Output amount key is more than one byte type");
                    }
                    CAmount v;
                    UnserializeFromVector(s, v);
                    amount = v;
                    break;
                }
                case PSBT_OUT_SCRIPT:
                {
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, output script is already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Output script key is more than one byte type");
                    }
                    CScript sc;
                    s >> sc;
                    script = sc;
                    break;
                }
                case PSBT_OUT_PROPRIETARY:
                {
                    bool known = false;
                    PSBTProprietary this_prop;
                    skey >> this_prop.identifier;
                    size_t subkey_len = skey.size();
                    this_prop.subtype = ReadCompactSize(skey);

                    if (this_prop.identifier == PSBT_ELEMENTS_ID) {
                        known = true;

                        switch(this_prop.subtype) {
                            case PSBT_ELEMENTS_OUT_VALUE_COMMITMENT:
                            {
                                if (!m_value_commitment.IsNull()) {
                                    throw std::ios_base::failure("Duplicate Key, output value commitment already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Output value cmmitment key is more than one byte type");
                                }
                                UnserializeFromVector(s, m_value_commitment);
                                break;
                            }
                            case PSBT_ELEMENTS_OUT_ASSET:
                            {
                                if (!m_asset.IsNull()) {
                                    throw std::ios_base::failure("Duplicate Key, output asset already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Output asset key is more than one byte type");
                                }
                                UnserializeFromVector(s, m_asset);
                                break;
                            }
                            case PSBT_ELEMENTS_OUT_ASSET_COMMITMENT:
                            {
                                if (!m_asset_commitment.IsNull()) {
                                    throw std::ios_base::failure("Duplicate Key, output asset commitment already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Output asset commitment key is more than one byte type");
                                }
                                UnserializeFromVector(s, m_asset_commitment);
                                break;
                            }
                            case PSBT_ELEMENTS_OUT_VALUE_RANGEPROOF:
                            {
                                if (!m_value_rangeproof.empty()) {
                                    throw std::ios_base::failure("Duplicate Key, output value rangeproof already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Output value rangeproof key is more than one byte type");
                                }
                                s >> m_value_rangeproof;
                                break;
                            }
                            case PSBT_ELEMENTS_OUT_ASSET_SURJECTION_PROOF:
                            {
                                if (!m_asset_surjection_proof.empty()) {
                                    throw std::ios_base::failure("Duplicate Key, output asset surjection proof already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Output asset surjection proof key is more than one byte type");
                                }
                                s >> m_asset_surjection_proof;
                                break;
                            }
                            case PSBT_ELEMENTS_OUT_BLINDING_PUBKEY:
                            {
                                if (m_blinding_pubkey.IsValid()) {
                                    throw std::ios_base::failure("Duplicate Key, output blinding pubkey already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Output blinding pubkey key is more than one byte type");
                                }
                                s >> m_blinding_pubkey;
                                break;
                            }
                            case PSBT_ELEMENTS_OUT_ECDH_PUBKEY:
                            {
                                if (m_ecdh_pubkey.IsValid()) {
                                    throw std::ios_base::failure("Duplicate Key, output ecdh pubkey already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Output ecdh pubkey key is more than one byte type");
                                }
                                s >> m_ecdh_pubkey;
                                break;
                            }
                            case PSBT_ELEMENTS_OUT_BLINDER_INDEX:
                            {
                                if (m_blinder_index != std::nullopt) {
                                    throw std::ios_base::failure("Duplicate Key, output blinder_index already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Output blinder_index key is more than one byte type");
                                }
                                uint32_t i;
                                UnserializeFromVector(s, i);
                                m_blinder_index = i;
                                break;
                            }
                            case PSBT_ELEMENTS_OUT_BLIND_VALUE_PROOF:
                            {
                                if (!m_blind_value_proof.empty()) {
                                    throw std::ios_base::failure("Duplicate Key, output blind value proof already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Output blind value proof key is more than one byte type");
                                }
                                s >> m_blind_value_proof;
                                break;
                            }
                            case PSBT_ELEMENTS_OUT_BLIND_ASSET_PROOF:
                            {
                                if (!m_blind_asset_proof.empty()) {
                                    throw std::ios_base::failure("Duplicate Key, output blind asset proof already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Output blind asset proof key is more than one byte type");
                                }
                                s >> m_blind_asset_proof;
                                break;
                            }
                            case PSBT_ELEMENTS_OUT_ASSET_BLINDING_FACTOR:
                            {
                                if (m_asset_blinding_factor.has_value()) {
                                    throw std::ios_base::failure("Duplicate Key, output asset blinding factor is already provided");
                                } else if (subkey_len != 1) {
                                    throw std::ios_base::failure("Output asset blinding factor is more than one byte type");
                                }
                                uint256 u;
                                UnserializeFromVector(s, u);
                                m_asset_blinding_factor = u;
                                break;
                            }
                            default:
                            {
                                known = false;
                                break;
                            }
                        }
                    }

                    if (!known) {
                        this_prop.key = key;

                        if (m_proprietary.count(this_prop) > 0) {
                            throw std::ios_base::failure("Duplicate Key, proprietary key already found");
                        }
                        s >> this_prop.value;
                        m_proprietary.insert(this_prop);
                    }
                    break;
                }
                // Unknown stuff
                default: {
                    if (unknown.count(key) > 0) {
                        throw std::ios_base::failure("Duplicate Key, key for unknown value already provided");
                    }
                    // Read in the value
                    std::vector<unsigned char> val_bytes;
                    s >> val_bytes;
                    unknown.emplace(std::move(key), std::move(val_bytes));
                    break;
                }
            }
        }

        if (!found_sep) {
            throw std::ios_base::failure("Separator is missing at the end of an output map");
        }

        // Make sure required PSBTv2 fields are present
        if (m_psbt_version >= 2) {
            if (amount == std::nullopt && m_value_commitment.IsNull()) {
                throw std::ios_base::failure("Output amount is required in PSBTv2");
            }
            if (script == std::nullopt) {
                throw std::ios_base::failure("Output script is required in PSBTv2");
            }
            if (m_asset.IsNull() && m_asset_commitment.IsNull()) {
                throw std::ios_base::failure("Output asset is required in PSET");
            }
            if (m_blinding_pubkey.IsValid() && m_blinder_index == std::nullopt) {
                throw std::ios_base::failure("Output is blinded but does not have a blinder index");
            }
            if (IsBlinded() && IsPartiallyBlinded() && !IsFullyBlinded()) {
                throw std::ios_base::failure("Blinded output contains some blinding data but not all, this is an invalid state");
            }
        }
    }

    template <typename Stream>
    PSBTOutput(deserialize_type, Stream& s) {
        Unserialize(s);
    }
};

/** A version of CTransaction with the PSBT format*/
struct PartiallySignedTransaction
{
    std::optional<CMutableTransaction> tx{std::nullopt};
    // We use a set of CExtPubKey in the event that there happens to be the same KeyOriginInfos for different CExtPubKeys
    // Note that this map swaps the key and values from the serialization
    std::map<KeyOriginInfo, std::set<CExtPubKey>> m_xpubs;
    std::optional<int32_t> tx_version{std::nullopt};
    std::optional<uint32_t> fallback_locktime{std::nullopt};
    std::optional<std::bitset<8>> m_tx_modifiable{std::nullopt};
    std::vector<PSBTInput> inputs;
    std::vector<PSBTOutput> outputs;
    std::map<std::vector<unsigned char>, std::vector<unsigned char>> unknown;
    std::optional<uint32_t> m_version{std::nullopt};
    std::set<PSBTProprietary> m_proprietary;

    // Elements proprietary fields
    std::set<uint256> m_scalar_offsets;

    bool IsNull() const;
    uint32_t GetVersion() const;

    /** Merge psbt into this. The two psbts must have the same underlying CTransaction (i.e. the
      * same actual Bitcoin transaction.) Returns true if the merge succeeded, false otherwise. */
    [[nodiscard]] bool Merge(const PartiallySignedTransaction& psbt);
    bool AddInput(PSBTInput& psbtin);
    bool AddOutput(const PSBTOutput& psbtout);
    void SetupFromTx(const CMutableTransaction& tx);
    void CacheUnsignedTxPieces();
    bool ComputeTimeLock(uint32_t& locktime) const;
    CMutableTransaction GetUnsignedTx(bool foce_unblinded=false) const;
    uint256 GetUniqueID() const;
    PartiallySignedTransaction() {}
    PartiallySignedTransaction(uint32_t version);
    explicit PartiallySignedTransaction(const CMutableTransaction& tx, uint32_t version = 0);
    /** Returns whether the PSBT has outputs that require blinding. Said outputs may already be blinded */
    bool IsBlinded() const;
    /** Returns whether the PSBT is fully blinded. Fully blinded means that no blinding is required, so this includes PSBTs that do not require blinding at all */
    bool IsFullyBlinded() const;

    template <typename Stream>
    inline void Serialize(Stream& s) const {

        // magic bytes
        s << PSBT_ELEMENTS_MAGIC_BYTES;

        if (GetVersion() == 0) {
            // unsigned tx flag
            SerializeToVector(s, CompactSizeWriter(PSBT_GLOBAL_UNSIGNED_TX));

            // Write serialized tx to a stream
            OverrideStream<Stream> os(&s, s.GetType(), s.GetVersion() | SERIALIZE_TRANSACTION_NO_WITNESS);
            SerializeToVector(os, GetUnsignedTx());
        }

        // Write xpubs
        for (const auto& xpub_pair : m_xpubs) {
            for (const auto& xpub : xpub_pair.second) {
                unsigned char ser_xpub[BIP32_EXTKEY_WITH_VERSION_SIZE];
                xpub.EncodeWithVersion(ser_xpub);
                // Note that the serialization swaps the key and value
                // The xpub is the key (for uniqueness) while the path is the value
                SerializeToVector(s, PSBT_GLOBAL_XPUB, ser_xpub);
                SerializeHDKeypath(s, xpub_pair.first);
            }
        }

        if (GetVersion() >= 2) {
            // Write PSBTv2 tx version, locktime, counts, etc.
            SerializeToVector(s, CompactSizeWriter(PSBT_GLOBAL_TX_VERSION));
            SerializeToVector(s, *tx_version);

            if (fallback_locktime != std::nullopt) {
                SerializeToVector(s, CompactSizeWriter(PSBT_GLOBAL_FALLBACK_LOCKTIME));
                SerializeToVector(s, *fallback_locktime);
            }

            SerializeToVector(s, CompactSizeWriter(PSBT_GLOBAL_INPUT_COUNT));
            SerializeToVector(s, CompactSizeWriter(inputs.size()));
            SerializeToVector(s, CompactSizeWriter(PSBT_GLOBAL_OUTPUT_COUNT));
            SerializeToVector(s, CompactSizeWriter(outputs.size()));

            if (m_tx_modifiable != std::nullopt) {
                SerializeToVector(s, CompactSizeWriter(PSBT_GLOBAL_TX_MODIFIABLE));
                SerializeToVector(s, static_cast<uint8_t>(m_tx_modifiable->to_ulong()));
            }

            // Elements proprietary fields
            // Scalar offsets
            for (const uint256& scalar : m_scalar_offsets) {
                SerializeToVector(s, CompactSizeWriter(PSBT_GLOBAL_PROPRIETARY), PSBT_ELEMENTS_ID, CompactSizeWriter(PSBT_ELEMENTS_GLOBAL_SCALAR), scalar);
                s << PSBT_SEPARATOR; /* Zero length data value */
            }
        }

        // PSBT version
        if (GetVersion() > 0) {
            SerializeToVector(s, CompactSizeWriter(PSBT_GLOBAL_VERSION));
            SerializeToVector(s, *m_version);
        }

        // Write proprietary things
        for (const auto& entry : m_proprietary) {
            s << entry.key;
            s << entry.value;
        }

        // Write the unknown things
        for (auto& entry : unknown) {
            s << entry.first;
            s << entry.second;
        }

        // Separator
        s << PSBT_SEPARATOR;

        // Write inputs
        for (const PSBTInput& input : inputs) {
            s << input;
        }
        // Write outputs
        for (const PSBTOutput& output : outputs) {
            s << output;
        }
    }


    template <typename Stream>
    inline void Unserialize(Stream& s) {
        // Read the magic bytes
        uint8_t magic[5];
        s >> magic;
        if (!std::equal(magic, magic + 5, PSBT_ELEMENTS_MAGIC_BYTES)) {
            throw std::ios_base::failure("Invalid PSBT magic bytes");
        }

        // Used for duplicate key detection
        std::set<std::vector<unsigned char>> key_lookup;

        // Track the global xpubs we have already seen. Just for sanity checking
        std::set<CExtPubKey> global_xpubs;

        // Read global data
        bool found_sep = false;
        uint64_t input_count = 0;
        uint64_t output_count = 0;
        bool found_input_count = false;
        bool found_output_count = false;
        while(!s.empty()) {
            // Read
            std::vector<unsigned char> key;
            s >> key;

            // the key is empty if that was actually a separator byte
            // This is a special case for key lengths 0 as those are not allowed (except for separator)
            if (key.empty()) {
                found_sep = true;
                break;
            }

            // Type is compact size uint at beginning of key
            SpanReader skey(s.GetType(), s.GetVersion(), key);
            uint64_t type = ReadCompactSize(skey);

            // Do stuff based on type
            switch(type) {
                case PSBT_GLOBAL_UNSIGNED_TX:
                {
                    if (g_con_elementsmode) {
                        throw std::ios_base::failure("Unsigned tx is not allowed in PSET");
                    }
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, unsigned tx already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Global unsigned tx key is more than one byte type");
                    }
                    CMutableTransaction mtx;
                    // Set the stream to serialize with non-witness since this should always be non-witness
                    OverrideStream<Stream> os(&s, s.GetType(), s.GetVersion() | SERIALIZE_TRANSACTION_NO_WITNESS);
                    UnserializeFromVector(os, mtx);
                    tx = std::move(mtx);
                    // Make sure that all scriptSigs and scriptWitnesses are empty
                    for (unsigned int i = 0; i < tx->vin.size(); i++) {
                        const CTxIn& txin = tx->vin[i];
                        if (!txin.scriptSig.empty() || !tx->witness.vtxinwit[i].scriptWitness.IsNull()) {
                            throw std::ios_base::failure("Unsigned tx does not have empty scriptSigs and scriptWitnesses.");
                        }
                    }
                    // Set the input and output counts
                    input_count = tx->vin.size();
                    output_count = tx->vout.size();
                    break;
                }
                case PSBT_GLOBAL_TX_VERSION:
                {
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, global transaction version is already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Global transaction version key is more than one byte type");
                    }
                    uint32_t v;
                    UnserializeFromVector(s, v);
                    tx_version = v;
                    break;
                }
                case PSBT_GLOBAL_FALLBACK_LOCKTIME:
                {
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, global fallback locktime is already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Global fallback locktime key is more than one byte type");
                    }
                    uint32_t v;
                    UnserializeFromVector(s, v);
                    fallback_locktime = v;
                    break;
                }
                case PSBT_GLOBAL_INPUT_COUNT:
                {
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, global input count is already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Global input count key is more than one byte type");
                    }
                    CompactSizeReader reader(input_count);
                    UnserializeFromVector(s, reader);
                    found_input_count = true;
                    break;
                }
                case PSBT_GLOBAL_OUTPUT_COUNT:
                {
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, global output count is already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Global output count key is more than one byte type");
                    }
                    CompactSizeReader reader(output_count);
                    UnserializeFromVector(s, reader);
                    found_output_count = true;
                    break;
                }
                case PSBT_GLOBAL_TX_MODIFIABLE:
                {
                    if (!key_lookup.emplace(key).second) {
                        throw std::ios_base::failure("Duplicate Key, tx modifiable flags is already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Global tx modifiable flags key is more than one byte type");
                    }
                    uint8_t tx_mod;
                    UnserializeFromVector(s, tx_mod);
                    m_tx_modifiable.emplace(tx_mod);
                    break;
                }
                case PSBT_GLOBAL_XPUB:
                {
                    if (key.size() != BIP32_EXTKEY_WITH_VERSION_SIZE + 1) {
                        throw std::ios_base::failure("Size of key was not the expected size for the type global xpub");
                    }
                    // Read in the xpub from key
                    CExtPubKey xpub;
                    xpub.DecodeWithVersion(&key.data()[1]);
                    if (!xpub.pubkey.IsFullyValid()) {
                       throw std::ios_base::failure("Invalid pubkey");
                    }
                    if (global_xpubs.count(xpub) > 0) {
                       throw std::ios_base::failure("Duplicate key, global xpub already provided");
                    }
                    global_xpubs.insert(xpub);
                    // Read in the keypath from stream
                    KeyOriginInfo keypath;
                    DeserializeHDKeypath(s, keypath);

                    // Note that we store these swapped to make searches faster.
                    // Serialization uses xpub -> keypath to enqure key uniqueness
                    if (m_xpubs.count(keypath) == 0) {
                        // Make a new set to put the xpub in
                        m_xpubs[keypath] = {xpub};
                    } else {
                        // Insert xpub into existing set
                        m_xpubs[keypath].insert(xpub);
                    }
                    break;
                }
                case PSBT_GLOBAL_VERSION:
                {
                    if (m_version) {
                        throw std::ios_base::failure("Duplicate Key, version already provided");
                    } else if (key.size() != 1) {
                        throw std::ios_base::failure("Global version key is more than one byte type");
                    }
                    uint32_t v;
                    UnserializeFromVector(s, v);
                    m_version = v;
                    if (m_version > PSBT_HIGHEST_VERSION) {
                        throw std::ios_base::failure("Unsupported version number");
                    }
                    break;
                }
                case PSBT_GLOBAL_PROPRIETARY:
                {
                    bool known = false;
                    PSBTProprietary this_prop;
                    skey >> this_prop.identifier;
                    size_t subkey_len = skey.size();
                    this_prop.subtype = ReadCompactSize(skey);

                    if (this_prop.identifier == PSBT_ELEMENTS_ID) {
                        known = true;

                        switch(this_prop.subtype) {
                            case PSBT_ELEMENTS_GLOBAL_SCALAR:
                            {
                                uint256 scalar;
                                skey >> scalar;
                                if (m_scalar_offsets.count(scalar) > 0) {
                                    throw std::ios_base::failure("Duplicate key, the same scalar offset was provided multiple times");
                                } else if (subkey_len != 33) {
                                    throw std::ios_base::failure("Global scalar offset key was not the expected length");
                                }
                                std::vector<unsigned char> val;
                                UnserializeFromVector(s, val);
                                if (val.size() != 0) {
                                    throw std::ios_base::failure("Global scalar value was not empty");
                                }
                                m_scalar_offsets.insert(scalar);
                                break;
                            }
                            default:
                                known = false;
                                break;
                        }
                    }

                    if (!known) {
                        this_prop.key = key;

                        if (m_proprietary.count(this_prop) > 0) {
                            throw std::ios_base::failure("Duplicate Key, proprietary key already found");
                        }
                        s >> this_prop.value;
                        m_proprietary.insert(this_prop);
                    }
                    break;
                }
                // Unknown stuff
                default: {
                    if (unknown.count(key) > 0) {
                        throw std::ios_base::failure("Duplicate Key, key for unknown value already provided");
                    }
                    // Read in the value
                    std::vector<unsigned char> val_bytes;
                    s >> val_bytes;
                    unknown.emplace(std::move(key), std::move(val_bytes));
                }
            }
        }

        if (!found_sep) {
            throw std::ios_base::failure("Separator is missing at the end of the global map");
        }

        uint32_t psbt_ver = GetVersion();

        // Check PSBT version constraints
        if (psbt_ver == 0) {
            // Make sure that we got an unsigned tx for PSBTv0
            if (!tx) {
                throw std::ios_base::failure("No unsigned transcation was provided");
            }
            // Make sure no PSBTv2 fields are present
            if (tx_version != std::nullopt) {
                throw std::ios_base::failure("PSBT_GLOBAL_TX_VERSION is not allowed in PSBTv0");
            }
            if (fallback_locktime != std::nullopt) {
                throw std::ios_base::failure("PSBT_GLOBAL_FALLBACK_LOCKTIME is not allowed in PSBTv0");
            }
            if (found_input_count) {
                throw std::ios_base::failure("PSBT_GLOBAL_INPUT_COUNT is not allowed in PSBTv0");
            }
            if (found_output_count) {
                throw std::ios_base::failure("PSBT_GLOBAL_OUTPUT_COUNT is not allowed in PSBTv0");
            }
            if (m_tx_modifiable != std::nullopt) {
                throw std::ios_base::failure("PSBT_GLOBAL_TX_MODIFIABLE is not allowed in PSBTv0");
            }
        }
        // Disallow v1
        if (psbt_ver == 1) {
            throw std::ios_base::failure("There is no PSBT version 1");
        }
        if (psbt_ver >= 2) {
            // Tx version, input, and output counts are required
            if (tx_version == std::nullopt) {
                throw std::ios_base::failure("PSBT_GLOBAL_TX_VERSION is required in PSBTv2");
            }
            if (!found_input_count) {
                throw std::ios_base::failure("PSBT_GLOBAL_INPUT_COUNT is required in PSBTv2");
            }
            if (!found_output_count) {
                throw std::ios_base::failure("PSBT_GLOBAL_OUTPUT_COUNT is required in PSBTv2");
            }
            // Unsigned tx is disallowed
            if (tx) {
                throw std::ios_base::failure("PSBT_GLOBAL_UNSIGNED_TX is not allowed in PSBTv2");
            }
        }

        // Read input data
        unsigned int i = 0;
        while (!s.empty() && i < input_count) {
            PSBTInput input(psbt_ver);
            s >> input;
            inputs.push_back(input);

            // Make sure the non-witness utxo matches the outpoint
            if (input.non_witness_utxo && ((tx != std::nullopt && input.non_witness_utxo->GetHash() != tx->vin[i].prevout.hash) || (!input.prev_txid.IsNull() && input.non_witness_utxo->GetHash() != input.prev_txid))) {
                throw std::ios_base::failure("Non-witness UTXO does not match outpoint hash");
            }
            ++i;
        }
        // Make sure that the number of inputs matches the number of inputs in the transaction
        if (inputs.size() != input_count) {
            throw std::ios_base::failure("Inputs provided does not match the number of inputs in transaction.");
        }

        // Read output data
        i = 0;
        while (!s.empty() && i < output_count) {
            PSBTOutput output(psbt_ver);
            s >> output;
            outputs.push_back(output);
            ++i;
        }
        // Make sure that the number of outputs matches the number of outputs in the transaction
        if (outputs.size() != output_count) {
            throw std::ios_base::failure("Outputs provided does not match the number of outputs in transaction.");
        }

        CacheUnsignedTxPieces();
    }

    template <typename Stream>
    PartiallySignedTransaction(deserialize_type, Stream& s) {
        Unserialize(s);
    }
};

enum class PSBTRole {
    CREATOR,
    UPDATER,
    BLINDER,
    SIGNER,
    FINALIZER,
    EXTRACTOR
};

std::string PSBTRoleName(PSBTRole role);

/** Compute a PrecomputedTransactionData object from a psbt. */
PrecomputedTransactionData PrecomputePSBTData(const PartiallySignedTransaction& psbt);

/** Checks whether a PSBTInput is already signed. */
bool PSBTInputSigned(const PSBTInput& input);

/** Signs a PSBTInput, verifying that all provided data matches what is being signed.
 *
 * txdata should be the output of PrecomputePSBTData (which can be shared across
 * multiple SignPSBTInput calls). If it is nullptr, a dummy signature will be created.
 **/
bool SignPSBTInput(const SigningProvider& provider, PartiallySignedTransaction& psbt, int index, const PrecomputedTransactionData* txdata, int sighash = SIGHASH_ALL, SignatureData* out_sigdata = nullptr, bool finalize = true);

/** Counts the unsigned inputs of a PSBT. */
size_t CountPSBTUnsignedInputs(const PartiallySignedTransaction& psbt);

/** Updates a PSBTOutput with information from provider.
 *
 * This fills in the redeem_script, witness_script, and hd_keypaths where possible.
 */
void UpdatePSBTOutput(const SigningProvider& provider, PartiallySignedTransaction& psbt, int index);

/**
 * Finalizes a PSBT if possible, combining partial signatures.
 *
 * @param[in,out] psbtx PartiallySignedTransaction to finalize
 * return True if the PSBT is now complete, false otherwise
 */
bool FinalizePSBT(PartiallySignedTransaction& psbtx);

/**
 * Finalizes a PSBT if possible, and extracts it to a CMutableTransaction if it could be finalized.
 *
 * @param[in]  psbtx PartiallySignedTransaction
 * @param[out] result CMutableTransaction representing the complete transaction, if successful
 * @return True if we successfully extracted the transaction, false otherwise
 */
bool FinalizeAndExtractPSBT(PartiallySignedTransaction& psbtx, CMutableTransaction& result);

/**
 * Combines PSBTs with the same underlying transaction, resulting in a single PSBT with all partial signatures from each input.
 *
 * @param[out] out   the combined PSBT, if successful
 * @param[in]  psbtxs the PSBTs to combine
 * @return error (OK if we successfully combined the transactions, other error if they were not compatible)
 */
[[nodiscard]] TransactionError CombinePSBTs(PartiallySignedTransaction& out, const std::vector<PartiallySignedTransaction>& psbtxs);

//! Decode a base64ed PSBT into a PartiallySignedTransaction
[[nodiscard]] bool DecodeBase64PSBT(PartiallySignedTransaction& decoded_psbt, const std::string& base64_psbt, std::string& error);
//! Decode a raw (binary blob) PSBT into a PartiallySignedTransaction
[[nodiscard]] bool DecodeRawPSBT(PartiallySignedTransaction& decoded_psbt, const std::string& raw_psbt, std::string& error);

std::string EncodePSBT(const PartiallySignedTransaction& psbt);

#endif // BITCOIN_PSBT_H
