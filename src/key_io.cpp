// Copyright (c) 2014-2019 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <key_io.h>

#include <base58.h>
#include <bech32.h>
#include <blech32.h>
#include <chainparams.h>
#include <util/strencodings.h>

#include <algorithm>
#include <assert.h>
#include <string.h>

/// Maximum witness length for Bech32 addresses.
static constexpr std::size_t BECH32_WITNESS_PROG_MAX_LEN = 40;

namespace {
class DestinationEncoder
{
private:
    const CChainParams& m_params;
    // ELEMENTS:
    const bool for_parent;

public:
    explicit DestinationEncoder(const CChainParams& params, const bool for_parent) : m_params(params), for_parent(for_parent) {}

    std::string operator()(const PKHash& id) const
    {
        if (id.blinding_pubkey.IsFullyValid()) {
            std::vector<unsigned char> data = m_params.Base58Prefix(CChainParams::BLINDED_ADDRESS);
            // Blinded addresses have the actual address type prefix inside the payload.
            std::vector<unsigned char> prefix = m_params.Base58Prefix(CChainParams::PUBKEY_ADDRESS);
            data.insert(data.end(), prefix.begin(), prefix.end());
            data.insert(data.end(), id.blinding_pubkey.begin(), id.blinding_pubkey.end());
            data.insert(data.end(), id.begin(), id.end());
            return EncodeBase58Check(data);
        }

        CChainParams::Base58Type type = for_parent ? CChainParams::PARENT_PUBKEY_ADDRESS : CChainParams::PUBKEY_ADDRESS;
        std::vector<unsigned char> data = m_params.Base58Prefix(type);
        data.insert(data.end(), id.begin(), id.end());
        return EncodeBase58Check(data);
    }

    std::string operator()(const ScriptHash& id) const
    {
        if (id.blinding_pubkey.IsFullyValid()) {
            std::vector<unsigned char> data = m_params.Base58Prefix(CChainParams::BLINDED_ADDRESS);
            // Blinded addresses have the actual address type prefix inside the payload.
            std::vector<unsigned char> prefix = m_params.Base58Prefix(CChainParams::SCRIPT_ADDRESS);
            data.insert(data.end(), prefix.begin(), prefix.end());
            data.insert(data.end(), id.blinding_pubkey.begin(), id.blinding_pubkey.end());
            data.insert(data.end(), id.begin(), id.end());
            return EncodeBase58Check(data);
        }

        CChainParams::Base58Type type = for_parent ? CChainParams::PARENT_SCRIPT_ADDRESS : CChainParams::SCRIPT_ADDRESS;
        std::vector<unsigned char> data = m_params.Base58Prefix(type);
        data.insert(data.end(), id.begin(), id.end());
        return EncodeBase58Check(data);
    }

    std::string operator()(const WitnessV0KeyHash& id) const
    {
        std::vector<unsigned char> data = {0};
        data.reserve(53);
        if (id.blinding_pubkey.IsFullyValid()) {
            std::vector<unsigned char> bytes(id.blinding_pubkey.begin(), id.blinding_pubkey.end());
            bytes.insert(bytes.end(), id.begin(), id.end());
            ConvertBits<8, 5, true>([&](unsigned char c) { data.push_back(c); }, bytes.begin(), bytes.end());
            const std::string& hrp = for_parent ? m_params.ParentBlech32HRP() : m_params.Blech32HRP();
            return blech32::Encode(hrp, data);
        }

        ConvertBits<8, 5, true>([&](unsigned char c) { data.push_back(c); }, id.begin(), id.end());
        const std::string& hrp = for_parent ? m_params.ParentBech32HRP() : m_params.Bech32HRP();
        return bech32::Encode(bech32::Encoding::BECH32, hrp, data);
    }

    std::string operator()(const WitnessV0ScriptHash& id) const
    {
        std::vector<unsigned char> data = {0};
        data.reserve(53);
        if (id.blinding_pubkey.IsFullyValid()) {
            std::vector<unsigned char> bytes(id.blinding_pubkey.begin(), id.blinding_pubkey.end());
            bytes.insert(bytes.end(), id.begin(), id.end());
            ConvertBits<8, 5, true>([&](unsigned char c) { data.push_back(c); }, bytes.begin(), bytes.end());
            const std::string& hrp = for_parent ? m_params.ParentBlech32HRP() : m_params.Blech32HRP();
            return blech32::Encode(hrp, data);
        }

        ConvertBits<8, 5, true>([&](unsigned char c) { data.push_back(c); }, id.begin(), id.end());
        const std::string& hrp = for_parent ? m_params.ParentBech32HRP() : m_params.Bech32HRP();
        return bech32::Encode(bech32::Encoding::BECH32, hrp, data);
    }

    std::string operator()(const WitnessV1Taproot& tap) const
    {
        std::vector<unsigned char> data = {1};
        data.reserve(53);
        ConvertBits<8, 5, true>([&](unsigned char c) { data.push_back(c); }, tap.begin(), tap.end());
        return bech32::Encode(bech32::Encoding::BECH32M, m_params.Bech32HRP(), data);
    }

    std::string operator()(const WitnessUnknown& id) const
    {
        if (id.version < 1 || id.version > 16 || id.length < 2 || id.length > 40) {
            return {};
        }
        std::vector<unsigned char> data = {(unsigned char)id.version};
        data.reserve(1 + (id.length * 8 + 4) / 5);
        if (id.blinding_pubkey.IsFullyValid()) {
            std::vector<unsigned char> bytes(id.blinding_pubkey.begin(), id.blinding_pubkey.end());
            bytes.insert(bytes.end(), id.program, id.program + id.length);
            ConvertBits<8, 5, true>([&](unsigned char c) { data.push_back(c); }, bytes.begin(), bytes.end());
            const std::string& hrp = for_parent ? m_params.ParentBlech32HRP() : m_params.Blech32HRP();
            return blech32::Encode(hrp, data);
        }

        ConvertBits<8, 5, true>([&](unsigned char c) { data.push_back(c); }, id.program, id.program + id.length);
        const std::string& hrp = for_parent ? m_params.ParentBech32HRP() : m_params.Bech32HRP();
        return bech32::Encode(bech32::Encoding::BECH32M, hrp, data);
    }

    std::string operator()(const CNoDestination& no) const { return {}; }
    std::string operator()(const NullData& null) const { return {}; }
};

CTxDestination DecodeDestination(const std::string& str, const CChainParams& params, const bool for_parent, std::string& error_str)
{
    std::vector<unsigned char> data;
    size_t pk_size = CPubKey::COMPRESSED_SIZE;
    uint160 hash;
    error_str = "";
    if (DecodeBase58Check(str, data, 55)) {
        // base58-encoded Bitcoin addresses.
        // Public-key-hash-addresses have version 0 (or 111 testnet).
        // The data vector contains RIPEMD160(SHA256(pubkey)), where pubkey is the serialized public key.

        // Blinded addresses have two prefixes: first the blinded one, then the traditional one.
        const std::vector<unsigned char>& blinded_prefix = params.Base58Prefix(CChainParams::BLINDED_ADDRESS);

        CChainParams::Base58Type type_pkh = for_parent ? CChainParams::PARENT_PUBKEY_ADDRESS : CChainParams::PUBKEY_ADDRESS;
        const std::vector<unsigned char>& pubkey_prefix = params.Base58Prefix(type_pkh);
        if (data.size() == hash.size() + pubkey_prefix.size() && std::equal(pubkey_prefix.begin(), pubkey_prefix.end(), data.begin())) {
            std::copy(data.begin() + pubkey_prefix.size(), data.end(), hash.begin());
            return PKHash(CKeyID(hash));
        } else if (data.size() == hash.size() + blinded_prefix.size() + pubkey_prefix.size() + pk_size &&
                std::equal(blinded_prefix.begin(), blinded_prefix.end(), data.begin()) &&
                std::equal(pubkey_prefix.begin(), pubkey_prefix.end(), data.begin() + blinded_prefix.size())) {
            auto payload_start = data.begin() + blinded_prefix.size() + pubkey_prefix.size();
            CPubKey pubkey;
            pubkey.Set(payload_start, payload_start + pk_size);
            std::copy(payload_start + pk_size, data.end(), hash.begin());
            return PKHash(CKeyID(hash), pubkey);
        }

        // Script-hash-addresses have version 5 (or 196 testnet).
        // The data vector contains RIPEMD160(SHA256(cscript)), where cscript is the serialized redemption script.
        CChainParams::Base58Type type_sh = for_parent ? CChainParams::PARENT_SCRIPT_ADDRESS : CChainParams::SCRIPT_ADDRESS;
        const std::vector<unsigned char>& script_prefix = params.Base58Prefix(type_sh);
        if (data.size() == hash.size() + script_prefix.size() && std::equal(script_prefix.begin(), script_prefix.end(), data.begin())) {
            std::copy(data.begin() + script_prefix.size(), data.end(), hash.begin());
            return ScriptHash(CScriptID(hash));
        } else if (data.size() == hash.size() + blinded_prefix.size() + pubkey_prefix.size() + pk_size &&
                std::equal(blinded_prefix.begin(), blinded_prefix.end(), data.begin()) &&
                std::equal(script_prefix.begin(), script_prefix.end(), data.begin() + blinded_prefix.size())) {
            auto payload_start = data.begin() + blinded_prefix.size() + script_prefix.size();
            CPubKey pubkey;
            pubkey.Set(payload_start, payload_start + pk_size);
            std::copy(payload_start + pk_size, data.end(), hash.begin());
            return ScriptHash(CScriptID(hash), pubkey);
        }

        // Set potential error message.
        // This message may be changed if the address can also be interpreted as a Bech32 address.
        error_str = "Invalid prefix for Base58-encoded address";
    }
    data.clear();
    const auto dec = bech32::Decode(str);
    const std::string& hrp = for_parent ? params.ParentBech32HRP() : params.Bech32HRP();
    if ((dec.encoding == bech32::Encoding::BECH32 || dec.encoding == bech32::Encoding::BECH32M) && dec.data.size() > 0) {
        // Bech32 decoding
        error_str = "";

        if (dec.hrp != hrp) {
            error_str = "Invalid prefix for Bech32 address";
            return CNoDestination();
        }
        int version = dec.data[0]; // The first 5 bit symbol is the witness version (0-16)
        if (version == 0 && dec.encoding != bech32::Encoding::BECH32) {
            error_str = "Version 0 witness address must use Bech32 checksum";
            return CNoDestination();
        }
        if (version != 0 && dec.encoding != bech32::Encoding::BECH32M) {
            error_str = "Version 1+ witness address must use Bech32m checksum";
            return CNoDestination();
        }
        // The rest of the symbols are converted witness program bytes.
        data.reserve(((dec.data.size() - 1) * 5) / 8);
        if (ConvertBits<5, 8, false>([&](unsigned char c) { data.push_back(c); }, dec.data.begin() + 1, dec.data.end())) {
            if (version == 0) {
                {
                    WitnessV0KeyHash keyid;
                    if (data.size() == keyid.size()) {
                        std::copy(data.begin(), data.end(), keyid.begin());
                        return keyid;
                    }
                }
                {
                    WitnessV0ScriptHash scriptid;
                    if (data.size() == scriptid.size()) {
                        std::copy(data.begin(), data.end(), scriptid.begin());
                        return scriptid;
                    }
                }

                error_str = "Invalid Bech32 v0 address data size";
                return CNoDestination();
            }

            if (version == 1 && data.size() == WITNESS_V1_TAPROOT_SIZE) {
                static_assert(WITNESS_V1_TAPROOT_SIZE == WitnessV1Taproot::size());
                WitnessV1Taproot tap;
                std::copy(data.begin(), data.end(), tap.begin());
                return tap;
            }

            if (version > 16) {
                error_str = "Invalid Bech32 address witness version";
                return CNoDestination();
            }

            if (data.size() < 2 || data.size() > BECH32_WITNESS_PROG_MAX_LEN) {
                error_str = "Invalid Bech32 address data size";
                return CNoDestination();
            }

            WitnessUnknown unk;
            unk.version = version;
            std::copy(data.begin(), data.end(), unk.program);
            unk.length = data.size();
            return unk;
        }
    }
    // ELEMENTS confidential addresses: version + 8to5(ecdhkey || witness program)
    data.clear();
    auto blech = blech32::Decode(str);
    const std::string& bl_hrp = for_parent ? params.ParentBlech32HRP() : params.Blech32HRP();
    if (blech.second.size() > 0 && blech.first == bl_hrp) {
        // Blech32 decoding
        int version = blech.second[0]; // The first 5 bit symbol is the witness version (0-16)

        data.reserve(((blech.second.size() - 1) * 5) / 8);

        // The rest of the symbols are converted blinding pubkey and witness program bytes.
        if (ConvertBits<5, 8, false>([&](unsigned char c) { data.push_back(c); }, blech.second.begin() + 1, blech.second.end())) {
            // Must be long enough for blinding key and other data taken below
            if (data.size() < 34) {
                return CNoDestination();
            }
            std::vector<unsigned char> pubkey_bytes(data.begin(), data.begin()+33);
            data = std::vector<unsigned char>(data.begin()+33, data.end());
            CPubKey blinding_pubkey(pubkey_bytes);
            if (version == 0) {
                {
                    WitnessV0KeyHash keyid;
                    if (data.size() == keyid.size()) {
                        std::copy(data.begin(), data.end(), keyid.begin());
                        keyid.blinding_pubkey = blinding_pubkey;
                        return keyid;
                    }
                }
                {
                    WitnessV0ScriptHash scriptid;
                    if (data.size() == scriptid.size()) {
                        std::copy(data.begin(), data.end(), scriptid.begin());
                        scriptid.blinding_pubkey = blinding_pubkey;
                        return scriptid;
                    }
                }
                return CNoDestination();
            }
            if (version > 16 || data.size() < 2 || data.size() > 40) {
                return CNoDestination();
            }
            WitnessUnknown unk;
            unk.version = version;
            std::copy(data.begin(), data.end(), unk.program);
            unk.blinding_pubkey = blinding_pubkey;
            unk.length = data.size();
            return unk;
        }
    }

    // Set error message if address can't be interpreted as Base58 or Bech32.
    if (error_str.empty()) error_str = "Invalid address format";

    return CNoDestination();
}
} // namespace

CKey DecodeSecret(const std::string& str)
{
    CKey key;
    std::vector<unsigned char> data;
    if (DecodeBase58Check(str, data, 34)) {
        const std::vector<unsigned char>& privkey_prefix = Params().Base58Prefix(CChainParams::SECRET_KEY);
        if ((data.size() == 32 + privkey_prefix.size() || (data.size() == 33 + privkey_prefix.size() && data.back() == 1)) &&
            std::equal(privkey_prefix.begin(), privkey_prefix.end(), data.begin())) {
            bool compressed = data.size() == 33 + privkey_prefix.size();
            key.Set(data.begin() + privkey_prefix.size(), data.begin() + privkey_prefix.size() + 32, compressed);
        }
    }
    if (!data.empty()) {
        memory_cleanse(data.data(), data.size());
    }
    return key;
}

std::string EncodeSecret(const CKey& key)
{
    assert(key.IsValid());
    std::vector<unsigned char> data = Params().Base58Prefix(CChainParams::SECRET_KEY);
    data.insert(data.end(), key.begin(), key.end());
    if (key.IsCompressed()) {
        data.push_back(1);
    }
    std::string ret = EncodeBase58Check(data);
    memory_cleanse(data.data(), data.size());
    return ret;
}

CExtPubKey DecodeExtPubKey(const std::string& str)
{
    CExtPubKey key;
    std::vector<unsigned char> data;
    if (DecodeBase58Check(str, data, 78)) {
        const std::vector<unsigned char>& prefix = Params().Base58Prefix(CChainParams::EXT_PUBLIC_KEY);
        if (data.size() == BIP32_EXTKEY_SIZE + prefix.size() && std::equal(prefix.begin(), prefix.end(), data.begin())) {
            key.Decode(data.data() + prefix.size());
        }
    }
    return key;
}

std::string EncodeExtPubKey(const CExtPubKey& key)
{
    std::vector<unsigned char> data = Params().Base58Prefix(CChainParams::EXT_PUBLIC_KEY);
    size_t size = data.size();
    data.resize(size + BIP32_EXTKEY_SIZE);
    key.Encode(data.data() + size);
    std::string ret = EncodeBase58Check(data);
    return ret;
}

CExtKey DecodeExtKey(const std::string& str)
{
    CExtKey key;
    std::vector<unsigned char> data;
    if (DecodeBase58Check(str, data, 78)) {
        const std::vector<unsigned char>& prefix = Params().Base58Prefix(CChainParams::EXT_SECRET_KEY);
        if (data.size() == BIP32_EXTKEY_SIZE + prefix.size() && std::equal(prefix.begin(), prefix.end(), data.begin())) {
            key.Decode(data.data() + prefix.size());
        }
    }
    return key;
}

std::string EncodeExtKey(const CExtKey& key)
{
    std::vector<unsigned char> data = Params().Base58Prefix(CChainParams::EXT_SECRET_KEY);
    size_t size = data.size();
    data.resize(size + BIP32_EXTKEY_SIZE);
    key.Encode(data.data() + size);
    std::string ret = EncodeBase58Check(data);
    memory_cleanse(data.data(), data.size());
    return ret;
}

std::string EncodeDestination(const CTxDestination& dest)
{
    return std::visit(DestinationEncoder(Params(), false), dest);
}

CTxDestination DecodeDestination(const std::string& str, std::string& error_msg)
{
    return DecodeDestination(str, Params(), false, error_msg);
}

CTxDestination DecodeDestination(const std::string& str)
{
    std::string error_msg;
    return DecodeDestination(str, Params(), false, error_msg);
}

bool IsValidDestinationString(const std::string& str, const CChainParams& params)
{
    std::string error_msg;
    return IsValidDestination(DecodeDestination(str, params, false, error_msg));
}

bool IsValidDestinationString(const std::string& str)
{
    std::string error_msg;
    return IsValidDestination(DecodeDestination(str, Params(), false, error_msg));
}

//
// ELEMENTS

std::string EncodeParentDestination(const CTxDestination& dest)
{
    return std::visit(DestinationEncoder(Params(), true), dest);
}

CTxDestination DecodeParentDestination(const std::string& str, std::string& error_msg)
{
    return DecodeDestination(str, Params(), true, error_msg);
}

// ELEMENTS
//
