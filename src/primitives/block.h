// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_PRIMITIVES_BLOCK_H
#define BITCOIN_PRIMITIVES_BLOCK_H

#include <primitives/transaction.h>
#include <script/script.h>
#include <serialize.h>
#include <uint256.h>

// ELEMENTS:
// Globals to avoid circular dependencies.
extern bool g_con_blockheightinheader;
extern bool g_signed_blocks;

class CProof
{
public:
    CScript challenge;
    CScript solution;

    CProof()
    {
        SetNull();
    }
    CProof(CScript challengeIn, CScript solutionIn) : challenge(challengeIn), solution(solutionIn) {}

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action)
    {
        READWRITE(*(CScriptBase*)(&challenge));
        if (!(s.GetType() & SER_GETHASH))
            READWRITE(*(CScriptBase*)(&solution));
    }

    void SetNull()
    {
        challenge.clear();
        solution.clear();
    }

    bool IsNull() const
    {
        return challenge.empty();
    }

    std::string ToString() const;
};

/*
 * Contains all the consensus parameters that can be voted for in dynamic federations
 */
class DynaFedParamEntry
{
public:
    unsigned char m_serialize_type; // Determines how it is serialized, defaults to null
    CScript m_signblockscript;
    uint32_t m_signblock_witness_limit; // Max block signature witness serialized size
    CScript m_fedpeg_program; // The "scriptPubKey" of the fedpegscript
    CScript m_fedpegscript; // The witnessScript for witness v0 or undefined otherwise.
    // No consensus meaning to the particular bytes, currently we interpret as PAK keys, details in pak.h
    std::vector<std::vector<unsigned char>> m_extension_space;

    // Each constructor sets its own serialization type implicitly based on which
    // arguments are given
    DynaFedParamEntry() { m_signblock_witness_limit = 0; m_serialize_type = 0; };
    DynaFedParamEntry(const CScript& signblockscript_in, const uint32_t sbs_wit_limit_in) : m_signblockscript(signblockscript_in), m_signblock_witness_limit(sbs_wit_limit_in) { m_serialize_type = 1; };
    DynaFedParamEntry(const CScript& signblockscript_in, const uint32_t sbs_wit_limit_in, const CScript& fedpeg_program_in, const CScript& fedpegscript_in, const std::vector<std::vector<unsigned char>> extension_space_in) : m_signblockscript(signblockscript_in), m_signblock_witness_limit(sbs_wit_limit_in), m_fedpeg_program(fedpeg_program_in), m_fedpegscript(fedpegscript_in), m_extension_space(extension_space_in) { m_serialize_type = 2; };

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action) {
        READWRITE(m_serialize_type);
        switch(m_serialize_type) {
            case 0:
                /* Null entry, used to signal "no vote" proposal */
                break;
            case 1:
                READWRITE(m_signblockscript);
                READWRITE(m_signblock_witness_limit);
                break;
            case 2:
                READWRITE(m_signblockscript);
                READWRITE(m_signblock_witness_limit);
                READWRITE(m_fedpeg_program);
                READWRITE(m_fedpegscript);
                READWRITE(m_extension_space);
                break;
            default:
                throw std::ios_base::failure("Invalid consensus parameter entry type");
        }
    }

    uint256 CalculateRoot() const;

    bool IsNull() const
    {
        return m_serialize_type == 0 &&
            m_signblockscript.empty() &&
            m_signblock_witness_limit == 0 &&
            m_fedpeg_program.empty() &&
            m_fedpegscript.empty() &&
            m_extension_space.empty();

    }

    void SetNull()
    {
        m_serialize_type = 0;
        m_signblockscript.clear();
        m_signblock_witness_limit = 0;
        m_fedpeg_program.clear();
        m_fedpegscript.clear();
        m_extension_space.clear();
    }

    bool operator==(const DynaFedParamEntry &other) const
    {
        return m_serialize_type == other.m_serialize_type &&
            m_signblockscript == other.m_signblockscript &&
            m_signblock_witness_limit == other.m_signblock_witness_limit &&
            m_fedpeg_program == other.m_fedpeg_program &&
            m_fedpegscript == other.m_fedpegscript &&
            m_extension_space == other.m_extension_space;
    }
    bool operator!=(const DynaFedParamEntry &other) const
    {
        return !(*this == other);
    }
};

/*
 * Encapsulation of the pair of dynamic federations parameters for "current" and "proposed"
 */
class DynaFedParams
{
public:

    // Currently enforced by network, not all fields may be known
    DynaFedParamEntry m_current;
    // Proposed rules for next epoch
    DynaFedParamEntry m_proposed;

    DynaFedParams() {};
    DynaFedParams(const DynaFedParamEntry& current, const DynaFedParamEntry& proposed)  : m_current(current), m_proposed(proposed) {};

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action) {
        READWRITE(m_current);
        READWRITE(m_proposed);
    }

    uint256 CalculateRoot() const;

    bool IsNull() const
    {
        return m_current.IsNull() && m_proposed.IsNull();
    }

    void SetNull()
    {
        m_current.SetNull();
        m_proposed.SetNull();
    }
};

/** Nodes collect new transactions into a block, hash them into a hash tree,
 * and scan through nonce values to make the block's hash satisfy proof-of-work
 * requirements.  When they solve the proof-of-work, they broadcast the block
 * to everyone and the block is added to the block chain.  The first transaction
 * in the block is a special one that creates a new coin owned by the creator
 * of the block.
 */
class CBlockHeader
{
public:
    // header
    int32_t nVersion;
    uint256 hashPrevBlock;
    uint256 hashMerkleRoot;
    uint32_t nTime;
    // Height in header as well as in coinbase for easier hsm validation
    // Is set for serialization with `-con_blockheightinheader=1`
    uint32_t block_height;
    uint32_t nBits;
    uint32_t nNonce;
    // Only used pre-dynamic federation
    CProof proof;
    // Dynamic federation: Subsumes the proof field
    DynaFedParams m_dynafed_params;
    CScriptWitness m_signblock_witness;

    CBlockHeader()
    {
        SetNull();
    }

    // HF bit to detect dynamic federation blocks
    static const uint32_t DYNAFED_HF_MASK = 1 << 31;

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action) {
        const bool fAllowWitness = !(s.GetVersion() & SERIALIZE_TRANSACTION_NO_WITNESS);

        // Detect dynamic federation block serialization using "HF bit",
        // or the signed bit which is invalid in Bitcoin
        bool is_dyna = false;
        int32_t nVersion;
        if (ser_action.ForRead()) {
            READWRITE(nVersion);
            is_dyna = nVersion < 0;
            this->nVersion = ~DYNAFED_HF_MASK & nVersion;
        } else {
            nVersion = this->nVersion;
            if (!m_dynafed_params.IsNull()) {
                nVersion |= DYNAFED_HF_MASK;
                is_dyna = true;
            }
            READWRITE(nVersion);
        }

        if (is_dyna) {
            READWRITE(hashPrevBlock);
            READWRITE(hashMerkleRoot);
            READWRITE(nTime);
            READWRITE(block_height);
            READWRITE(m_dynafed_params);
            // We do not serialize witness for hashes, or weight calculation
            if (!(s.GetType() & SER_GETHASH) && fAllowWitness) {
                READWRITE(m_signblock_witness.stack);
            }
        } else {
            READWRITE(hashPrevBlock);
            READWRITE(hashMerkleRoot);
            READWRITE(nTime);
            if (g_con_blockheightinheader) {
                READWRITE(block_height);
            }
            if (g_signed_blocks) {
                READWRITE(proof);
            } else {
                READWRITE(nBits);
                READWRITE(nNonce);
            }
        }
    }

    void SetNull()
    {
        nVersion = 0;
        hashPrevBlock.SetNull();
        hashMerkleRoot.SetNull();
        nTime = 0;
        block_height = 0;
        nBits = 0;
        nNonce = 0;
        proof.SetNull();
    }

    bool IsNull() const
    {
        if (g_signed_blocks) {
            return proof.IsNull() && m_dynafed_params.IsNull();
        } else {
            return (nBits == 0);
        }
    }

    uint256 GetHash() const;

    int64_t GetBlockTime() const
    {
        return (int64_t)nTime;
    }
};


class CBlock : public CBlockHeader
{
public:
    // network and disk
    std::vector<CTransactionRef> vtx;

    // memory only
    mutable bool fChecked;

    CBlock()
    {
        SetNull();
    }

    CBlock(const CBlockHeader &header)
    {
        SetNull();
        *(static_cast<CBlockHeader*>(this)) = header;
    }

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action) {
        READWRITEAS(CBlockHeader, *this);
        READWRITE(vtx);
    }

    void SetNull()
    {
        CBlockHeader::SetNull();
        vtx.clear();
        fChecked = false;
    }

    CBlockHeader GetBlockHeader() const
    {
        CBlockHeader block;
        block.nVersion       = nVersion;
        block.hashPrevBlock  = hashPrevBlock;
        block.hashMerkleRoot = hashMerkleRoot;
        block.nTime          = nTime;
        block.block_height   = block_height;
        block.nBits          = nBits;
        block.nNonce         = nNonce;
        block.proof          = proof;
        block.m_dynafed_params  = m_dynafed_params;
        return block;
    }

    std::string ToString() const;
};

/** Describes a place in the block chain to another node such that if the
 * other node doesn't have the same branch, it can find a recent common trunk.
 * The further back it is, the further before the fork it may be.
 */
struct CBlockLocator
{
    std::vector<uint256> vHave;

    CBlockLocator() {}

    explicit CBlockLocator(const std::vector<uint256>& vHaveIn) : vHave(vHaveIn) {}

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action) {
        int nVersion = s.GetVersion();
        if (!(s.GetType() & SER_GETHASH))
            READWRITE(nVersion);
        READWRITE(vHave);
    }

    void SetNull()
    {
        vHave.clear();
    }

    bool IsNull() const
    {
        return vHave.empty();
    }
};

#endif // BITCOIN_PRIMITIVES_BLOCK_H
