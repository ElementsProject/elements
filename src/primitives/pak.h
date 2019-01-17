// Copyright (c) 2018-2018 The Elements developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_PRIMITIVES_PAK_H
#define BITCOIN_PRIMITIVES_PAK_H

#include <script/script.h>
#include <secp256k1/include/secp256k1_whitelist.h>

class CPAKList
{
private:
    std::vector<secp256k1_pubkey> m_offline_keys;
    std::vector<secp256k1_pubkey> m_online_keys;
    bool reject;

    std::vector<CScript> GenerateCoinbasePAKCommitments() const;
    std::vector<CScript> GenerateCoinbasePAKReject() const;

public:
    CPAKList()
    {
        reject = true;
    }
    /**
     * Creates a new CPAKList. Requires that the number of offline keys is the same as the number of online keys
     * and that this number is not larger than SECP256K1_WHITELIST_MAX_N_KEYS.
     */
    CPAKList(std::vector<secp256k1_pubkey> offline_keys, std::vector<secp256k1_pubkey> online_keys, bool reject) :
        m_offline_keys(offline_keys), m_online_keys(online_keys), reject(reject) {
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
        return reject;
    }
    bool IsEmpty() const
    {
        return !reject && this->size() == 0;
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

    static CScript Magic();
    /** Produce a list of scripts to add to the coinbase to signal changes in PAK list or rejection of any pak proofs to nodes */
    void CreateCommitments(std::vector<CScript> &commitments) const;

    static bool FromBytes(CPAKList &paklist, std::vector<std::vector<unsigned char> >& offline_keys, std::vector<std::vector<unsigned char> >& online_keys, bool is_reject);
    void ToBytes(std::vector<std::vector<unsigned char> >& offline_keys, std::vector<std::vector<unsigned char> >& online_keys, bool &is_reject) const;
};

/**
 ** Returns true if the script includes valid pegout proof
 ** given the PAK list loaded. Two pushes after regular pegout script:
 ** <full_pubkey> <proof>
 **/
bool ScriptHasValidPAKProof(const CScript& script, const uint256& genesis_hash);


#endif // BITCOIN_PRIMITIVES_PAK_H
