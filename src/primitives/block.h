// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_PRIMITIVES_BLOCK_H
#define BITCOIN_PRIMITIVES_BLOCK_H

#include <primitives/transaction.h>
#include <script/script.h>
#include <serialize.h>
#include <uint256.h>
#include <util/time.h>

// ELEMENTS:
// Globals to avoid circular dependencies.
extern bool g_con_blockheightinheader;
extern bool g_signed_blocks;

class CProof
{
public:
    CScript challenge{};
    CScript solution{};

    CProof() {}
    CProof(CScript challengeIn, CScript solutionIn) : challenge(challengeIn), solution(solutionIn) {}

    template <typename Stream>
    inline void Serialize(Stream& s) const {
        s << *(CScriptBase*)(&challenge);
        if (!(s.GetType() & SER_GETHASH))
            s << *(CScriptBase*)(&solution);
    }

    template <typename Stream>
    inline void Unserialize(Stream& s) const {
        s >> *(CScriptBase*)(&challenge);
        if (!(s.GetType() & SER_GETHASH))
            s >> *(CScriptBase*)(&solution);
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
    // Determines how these entries are serialized and stored
    // 0 -> Null. Only used for proposed parameter "null votes"
    // 1 -> Pruned. Doesn't have non-signblockscript data. That elided data
    // is committed to in m_elided_root, and validated against chainstate.
    // 2 -> Full. Typically only consensus-legal at epoch start.
    unsigned char m_serialize_type{0};

    CScript m_signblockscript{};
    uint32_t m_signblock_witness_limit{0}; // Max block signature witness serialized size
    CScript m_fedpeg_program{}; // The "scriptPubKey" of the fedpegscript
    CScript m_fedpegscript{}; // The witnessScript for witness v0 or undefined otherwise.
    // No consensus meaning to the particular bytes, currently we interpret as PAK keys, details in pak.h
    std::vector<std::vector<unsigned char>> m_extension_space{};
    uint256 m_elided_root{}; // non-zero only when m_serialize_type == 1

    // Each constructor sets its own serialization type implicitly based on which
    // arguments are given
    DynaFedParamEntry() {};
    DynaFedParamEntry(const CScript& signblockscript_in, const uint32_t sbs_wit_limit_in, const uint256 elided_root_in) : m_signblockscript(signblockscript_in), m_signblock_witness_limit(sbs_wit_limit_in), m_elided_root(elided_root_in) { m_serialize_type = 1; };
    DynaFedParamEntry(const CScript& signblockscript_in, const uint32_t sbs_wit_limit_in, const CScript& fedpeg_program_in, const CScript& fedpegscript_in, const std::vector<std::vector<unsigned char>> extension_space_in) : m_signblockscript(signblockscript_in), m_signblock_witness_limit(sbs_wit_limit_in), m_fedpeg_program(fedpeg_program_in), m_fedpegscript(fedpegscript_in), m_extension_space(extension_space_in) { m_serialize_type = 2; };

    template <typename Stream>
    inline void Serialize(Stream& s) const {
        s << m_serialize_type;
        switch(m_serialize_type) {
            case 0:
                /* Null entry, used to signal "no vote" proposal */
                break;
            case 1:
                s << m_signblockscript;
                s << m_signblock_witness_limit;
                s << m_elided_root;
                break;
            case 2:
                s << m_signblockscript;
                s << m_signblock_witness_limit;
                s << m_fedpeg_program;
                s << m_fedpegscript;
                s << m_extension_space;
                break;
            default:
                assert(false && "Invalid consensus parameter entry type");
        }
    }

    template <typename Stream>
    inline void Unserialize(Stream& s) {
        s >> m_serialize_type;
        switch(m_serialize_type) {
            case 0:
                /* Null entry, used to signal "no vote" proposal */
                break;
            case 1:
                s >> m_signblockscript;
                s >> m_signblock_witness_limit;
                s >> m_elided_root;
                break;
            case 2:
                s >> m_signblockscript;
                s >> m_signblock_witness_limit;
                s >> m_fedpeg_program;
                s >> m_fedpegscript;
                s >> m_extension_space;
                break;
            default:
                throw std::ios_base::failure("Invalid consensus parameter entry type");
        }
    }

    uint256 CalculateRoot() const;
    // Calculates root for the non-blocksigning merkle fields
    uint256 CalculateExtraRoot() const;

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
    DynaFedParamEntry m_current{};
    // Proposed rules for next epoch
    DynaFedParamEntry m_proposed{};

    DynaFedParams() {};
    DynaFedParams(const DynaFedParamEntry& current, const DynaFedParamEntry& proposed)  : m_current(current), m_proposed(proposed) {};

    SERIALIZE_METHODS(DynaFedParams, obj) { READWRITE(obj.m_current, obj.m_proposed); }

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

    // ELEMENTS: we give explicit serialization methods so that we can
    //  mask in the dynafed bit and to selectively embed the blocktime

    // HF bit to detect dynamic federation blocks
    static const uint32_t DYNAFED_HF_MASK = 1 << 31;

    template <typename Stream>
    inline void Serialize(Stream& s) const {
        const bool fAllowWitness = !(s.GetVersion() & SERIALIZE_TRANSACTION_NO_WITNESS);

        // Detect dynamic federation block serialization using "HF bit",
        // or the signed bit which is invalid in Bitcoin
        bool is_dyna = false;
        int32_t nVersion = this->nVersion;
        if (!m_dynafed_params.IsNull()) {
            nVersion |= DYNAFED_HF_MASK;
            is_dyna = true;
        }
        s << (nVersion);

        if (is_dyna) {
            s << hashPrevBlock;
            s << hashMerkleRoot;
            s << nTime;
            s << block_height;
            s << m_dynafed_params;
            // We do not serialize witness for hashes, or weight calculation
            if (!(s.GetType() & SER_GETHASH) && fAllowWitness) {
                s << m_signblock_witness.stack;
            }
        } else {
            s << hashPrevBlock;
            s << hashMerkleRoot;
            s << nTime;
            if (g_con_blockheightinheader) {
                s << block_height;
            }
            if (g_signed_blocks) {
                s << proof;
            } else {
                s << nBits;
                s << nNonce;
            }
        }
    }

    template <typename Stream>
    inline void Unserialize(Stream& s) {
        const bool fAllowWitness = !(s.GetVersion() & SERIALIZE_TRANSACTION_NO_WITNESS);

        // Detect dynamic federation block serialization using "HF bit",
        // or the signed bit which is invalid in Bitcoin
        bool is_dyna = false;
        int32_t nVersion;
        s >> nVersion;
        is_dyna = nVersion < 0;
        this->nVersion = ~DYNAFED_HF_MASK & nVersion;

        if (is_dyna) {
            s >> hashPrevBlock;
            s >> hashMerkleRoot;
            s >> nTime;
            s >> block_height;
            s >> m_dynafed_params;
            // We do not serialize witness for hashes, or weight calculation
            if (!(s.GetType() & SER_GETHASH) && fAllowWitness) {
                s >> m_signblock_witness.stack;
            }
        } else {
            s >> hashPrevBlock;
            s >> hashMerkleRoot;
            s >> nTime;
            if (g_con_blockheightinheader) {
                s >> block_height;
            }
            if (g_signed_blocks) {
                s >> proof;
            } else {
                s >> nBits;
                s >> nNonce;
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

    NodeSeconds Time() const
    {
        return NodeSeconds{std::chrono::seconds{nTime}};
    }

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

    SERIALIZE_METHODS(CBlock, obj)
    {
        READWRITEAS(CBlockHeader, obj);
        READWRITE(obj.vtx);
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

    SERIALIZE_METHODS(CBlockLocator, obj)
    {
        int nVersion = s.GetVersion();
        if (!(s.GetType() & SER_GETHASH))
            READWRITE(nVersion);
        READWRITE(obj.vHave);
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
