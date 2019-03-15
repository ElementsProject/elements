// Copyright (c) 2014-2017 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <key_io.h>

#include <base58.h>
#include <bech32.h>
#include <blech32.h>
#include <chainparams.h>
#include <script/script.h>
#include <utilstrencodings.h>

#include <boost/variant/apply_visitor.hpp>
#include <boost/variant/static_visitor.hpp>

#include <assert.h>
#include <string.h>
#include <algorithm>

namespace
{
class DestinationEncoder : public boost::static_visitor<std::string>
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
            assert(!for_parent);
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
            assert(!for_parent);
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
        return bech32::Encode(hrp, data);
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
        return bech32::Encode(hrp, data);
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
        return bech32::Encode(hrp, data);
    }

    std::string operator()(const CNoDestination& no) const { return {}; }
    std::string operator()(const NullData& null) const { return {}; }
};

CTxDestination DecodeDestination(const std::string& str, const CChainParams& params, const bool for_parent)
{
    std::vector<unsigned char> data;
    size_t pk_size = CPubKey::COMPRESSED_PUBLIC_KEY_SIZE;
    uint160 hash;
    if (DecodeBase58Check(str, data)) {
        // base58-encoded Bitcoin addresses.
        // Public-key-hash-addresses have version 0 (or 111 testnet).
        // The data vector contains RIPEMD160(SHA256(pubkey)), where pubkey is the serialized public key.

        // Blinded addresses have two prefixes: first the blinded one, then the traditional one.
        const std::vector<unsigned char>& blinded_prefix = params.Base58Prefix(CChainParams::BLINDED_ADDRESS);

        CChainParams::Base58Type type_pkh = for_parent ? CChainParams::PARENT_PUBKEY_ADDRESS : CChainParams::PUBKEY_ADDRESS;
        const std::vector<unsigned char>& pubkey_prefix = params.Base58Prefix(type_pkh);
        if (data.size() == hash.size() + pubkey_prefix.size() && std::equal(pubkey_prefix.begin(), pubkey_prefix.end(), data.begin())) {
            std::copy(data.begin() + pubkey_prefix.size(), data.end(), hash.begin());
            return PKHash(hash);
        } else if (data.size() == hash.size() + blinded_prefix.size() + pubkey_prefix.size() + pk_size && 
                std::equal(blinded_prefix.begin(), blinded_prefix.end(), data.begin()) && 
                std::equal(pubkey_prefix.begin(), pubkey_prefix.end(), data.begin() + blinded_prefix.size())) {
            auto payload_start = data.begin() + blinded_prefix.size() + pubkey_prefix.size();
            CPubKey pubkey;
            pubkey.Set(payload_start, payload_start + pk_size);
            std::copy(payload_start + pk_size, data.end(), hash.begin());
            return PKHash(hash, pubkey);
        }

        // Script-hash-addresses have version 5 (or 196 testnet).
        // The data vector contains RIPEMD160(SHA256(cscript)), where cscript is the serialized redemption script.
        CChainParams::Base58Type type_sh = for_parent ? CChainParams::PARENT_SCRIPT_ADDRESS : CChainParams::SCRIPT_ADDRESS;
        const std::vector<unsigned char>& script_prefix = params.Base58Prefix(type_sh);
        if (data.size() == hash.size() + script_prefix.size() && std::equal(script_prefix.begin(), script_prefix.end(), data.begin())) {
            std::copy(data.begin() + script_prefix.size(), data.end(), hash.begin());
            return ScriptHash(hash);
        } else if (data.size() == hash.size() + blinded_prefix.size() + pubkey_prefix.size() + pk_size && 
                std::equal(blinded_prefix.begin(), blinded_prefix.end(), data.begin()) && 
                std::equal(script_prefix.begin(), script_prefix.end(), data.begin() + blinded_prefix.size())) {
            auto payload_start = data.begin() + blinded_prefix.size() + script_prefix.size();
            CPubKey pubkey;
            pubkey.Set(payload_start, payload_start + pk_size);
            std::copy(payload_start + pk_size, data.end(), hash.begin());
            return ScriptHash(hash, pubkey);
        }
    }
    data.clear();
    auto bech = bech32::Decode(str);
    const std::string& hrp = for_parent ? params.ParentBech32HRP() : params.Bech32HRP();
    if (bech.second.size() > 0 && bech.first == hrp) {
        // Bech32 decoding
        int version = bech.second[0]; // The first 5 bit symbol is the witness version (0-16)
        // The rest of the symbols are converted witness program bytes.
        data.reserve(((bech.second.size() - 1) * 5) / 8);
        if (ConvertBits<5, 8, false>([&](unsigned char c) { data.push_back(c); }, bech.second.begin() + 1, bech.second.end())) {
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
                return CNoDestination();
            }
            if (version > 16 || data.size() < 2 || data.size() > 40) {
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

    return CNoDestination();
}
} // namespace

CKey DecodeSecret(const std::string& str)
{
    CKey key;
    std::vector<unsigned char> data;
    if (DecodeBase58Check(str, data)) {
        const std::vector<unsigned char>& privkey_prefix = Params().Base58Prefix(CChainParams::SECRET_KEY);
        if ((data.size() == 32 + privkey_prefix.size() || (data.size() == 33 + privkey_prefix.size() && data.back() == 1)) &&
            std::equal(privkey_prefix.begin(), privkey_prefix.end(), data.begin())) {
            bool compressed = data.size() == 33 + privkey_prefix.size();
            key.Set(data.begin() + privkey_prefix.size(), data.begin() + privkey_prefix.size() + 32, compressed);
        }
    }
    memory_cleanse(data.data(), data.size());
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
    if (DecodeBase58Check(str, data)) {
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
    if (DecodeBase58Check(str, data)) {
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
    return boost::apply_visitor(DestinationEncoder(Params(), false), dest);
}

CTxDestination DecodeDestination(const std::string& str)
{
    return DecodeDestination(str, Params(), false);
}

bool IsValidDestinationString(const std::string& str, const CChainParams& params)
{
    return IsValidDestination(DecodeDestination(str, params, false));
}

bool IsValidDestinationString(const std::string& str)
{
    return IsValidDestination(DecodeDestination(str, Params(), false));
}

//
// ELEMENTS

std::string EncodeParentDestination(const CTxDestination& dest)
{
    return boost::apply_visitor(DestinationEncoder(Params(), true), dest);
}

CTxDestination DecodeParentDestination(const std::string& str)
{
    return DecodeDestination(str, Params(), true);
}

// ELEMENTS
//
