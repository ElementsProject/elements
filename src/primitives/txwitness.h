// Copyright (c) 2016-2019 The Elements developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_PRIMITIVES_TXWITNESS_H
#define BITCOIN_PRIMITIVES_TXWITNESS_H

#include <script/script.h>
#include <uint256.h>

class CTxInWitness
{
public:
    // TODO generalize CScriptWitness into just CWitness
    //TODO(rebase) CA/CT
    //std::vector<unsigned char> vchIssuanceAmountRangeproof;
    //std::vector<unsigned char> vchInflationKeysRangeproof;
    CScriptWitness scriptWitness;
    // Re-use script witness struct to include its own witness
    CScriptWitness m_pegin_witness;

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action)
    {
        //READWRITE(vchIssuanceAmountRangeproof);
        //READWRITE(vchInflationKeysRangeproof);
        READWRITE(scriptWitness.stack);
        READWRITE(m_pegin_witness.stack);
    }

    CTxInWitness() { }

    bool IsNull() const
    {
        //return vchIssuanceAmountRangeproof.empty() && vchInflationKeysRangeproof.empty() && scriptWitness.IsNull() && m_pegin_witness.IsNull();
        return scriptWitness.IsNull() && m_pegin_witness.IsNull();
    }
    void SetNull()
    {
        //vchIssuanceAmountRangeproof.clear();
        //vchInflationKeysRangeproof.clear();
        scriptWitness.stack.clear();
        m_pegin_witness.stack.clear();
    }

    uint256 GetHash() const;

private:
//    CTxInWitness(const CTxInWitness&);
//    CTxInWitness(CTxInWitness&&);
//    CTxInWitness& operator=(const CTxInWitness&);
//    CTxInWitness& operator=(CTxInWitness&&);
};

class CTxOutWitness
{
public:
    std::vector<unsigned char> vchSurjectionproof;
    std::vector<unsigned char> vchRangeproof;

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action)
    {
        READWRITE(vchSurjectionproof);
        READWRITE(vchRangeproof);
    }

    CTxOutWitness() { }

    bool IsNull() const
    {
        return vchSurjectionproof.empty() && vchRangeproof.empty();
    }
    void SetNull()
    {
        vchSurjectionproof.clear();
        vchRangeproof.clear();
    }

    uint256 GetHash() const;

private:
//    CTxOutWitness(const CTxOutWitness&);
//    CTxOutWitness(CTxInWitness&&);
//    CTxOutWitness& operator=(const CTxOutWitness&);
//    CTxOutWitness& operator=(CTxOutWitness&&);
};

class CTxWitness
{
public:
    /** In case vtxinwit is missing, all entries are treated as if they were empty CTxInWitnesses */
    std::vector<CTxInWitness> vtxinwit;
    std::vector<CTxOutWitness> vtxoutwit;

    CTxWitness() {}

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action)
    {
        for (size_t n = 0; n < vtxinwit.size(); n++) {
            READWRITE(vtxinwit[n]);
        }
        //TODO(rebase) CA/CT
        //for (size_t n = 0; n < vtxoutwit.size(); n++) {
        //    READWRITE(vtxoutwit[n]);
        //}
        //TODO(stevenroose) re-enabled after testing
        //if (IsNull()) {
        //    /* It's illegal to encode a witness when all vtxinwit and vtxoutwit entries are empty. */
        //    throw std::ios_base::failure("Superfluous witness record");
        //}
    }

    bool IsEmpty() const
    {
        return vtxinwit.empty() && vtxoutwit.empty();
    }

    bool IsNull() const
    {
        for (size_t n = 0; n < vtxinwit.size(); n++) {
            if (!vtxinwit[n].IsNull()) {
                return false;
            }
        }
        for (size_t n = 0; n < vtxoutwit.size(); n++) {
            if (!vtxoutwit[n].IsNull()) {
                return false;
            }
        }
        return true;
    }

    void SetNull()
    {
        vtxinwit.clear();
        vtxoutwit.clear();
    }

private:
//    CTxWitness(const CTxWitness&);
//    CTxWitness(CTxWitness&&);
//    CTxWitness& operator=(const CTxWitness&);
//    CTxWitness& operator=(CTxWitness&&);
};


/*
 * Compute the Merkle root of the transactions in a block using mid-state only.
 * Note that the merkle root calculated with this method is not the same as the
 * one computed by ComputeMerkleRoot.
 */
uint256 ComputeFastMerkleRoot(const std::vector<uint256>& hashes);


#endif //BITCOIN_PRIMITIVES_TXWITNESS_H
