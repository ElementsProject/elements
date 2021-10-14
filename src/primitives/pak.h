// Copyright (c) 2018-2018 The Elements developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_PRIMITIVES_PAK_H
#define BITCOIN_PRIMITIVES_PAK_H

#include <script/script.h>
#include <secp256k1/include/secp256k1_whitelist.h>
#include <chain.h>

class CPAKList
{
private:
    std::vector<secp256k1_pubkey> m_offline_keys;
    std::vector<secp256k1_pubkey> m_online_keys;

public:
    CPAKList() {}
    /**
     * Creates a new CPAKList. Requires that the number of offline keys is the same as the number of online keys
     * and that this number is not larger than SECP256K1_WHITELIST_MAX_N_KEYS.
     */
    CPAKList(std::vector<secp256k1_pubkey> offline_keys, std::vector<secp256k1_pubkey> online_keys) :
        m_offline_keys(offline_keys), m_online_keys(online_keys) {
            assert(m_offline_keys.size() == m_online_keys.size());
            assert(m_offline_keys.size() <= SECP256K1_WHITELIST_MAX_N_KEYS);
       }

    bool operator==(const CPAKList &other) const;
    bool operator!=(const CPAKList &other) const
    {
        return !(*this == other);
    }
    bool IsReject() const
    {
        return size()==0;
    }
    std::vector<secp256k1_pubkey> OnlineKeys() const
    {
        return m_online_keys;
    }
    std::vector<secp256k1_pubkey> OfflineKeys() const
    {
        return m_offline_keys;
    }
    size_t size() const
    {
        return m_offline_keys.size();
    }

    static bool FromBytes(CPAKList &paklist, const std::vector<std::vector<unsigned char> >& offline_keys, const std::vector<std::vector<unsigned char> >& online_keys);
    void ToBytes(std::vector<std::vector<unsigned char> >& offline_keys, std::vector<std::vector<unsigned char> >& online_keys) const;
};

/**
 ** Returns true if the script includes valid pegout proof
 ** given the PAK list. Two pushes after regular pegout script:
 ** <full_pubkey> <proof>
 **/
bool ScriptHasValidPAKProof(const CScript& script, const uint256& genesis_hash, const CPAKList& paklist);

CPAKList CreatePAKListFromExtensionSpace(const std::vector<std::vector<unsigned char>>& extension_space);

CPAKList GetActivePAKList(const CBlockIndex* pblockindex, const Consensus::Params& params);

bool IsPAKValidOutput(const CTxOut& txout, const CPAKList& paklist, const uint256& parent_gen_hash, const CAsset& peg_asset);

bool IsPAKValidTx(const CTransaction& tx, const CPAKList& paklist, const uint256& parent_gen_hash, const CAsset& peg_asset);

#endif // BITCOIN_PRIMITIVES_PAK_H
