// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2019 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <primitives/block.h>

#include <hash.h>
#include <tinyformat.h>


bool g_con_blockheightinheader = false;
bool g_signed_blocks = false;

std::string CProof::ToString() const
{
    return strprintf("CProof(challenge=%s, solution=%s)",
                     HexStr(challenge), HexStr(solution));
}

// ELEMENTS: GetHash manually implemented for CBlockHeader.
// SER_GETHASH removed in #28508 so CProof now always serializes `solution`.
// Only include `challenge` of CProof here, and no signblock witness
uint256 CBlockHeader::GetHash() const
{
    HashWriter s{};
    // Detect dynamic federation block serialization using "HF bit",
    // or the signed bit which is invalid in Bitcoin
    bool is_dyna = false;
    int32_t nVersion = this->nVersion;
    if (!m_dynafed_params.IsNull()) {
        nVersion |= (int32_t)DYNAFED_HF_MASK;
        is_dyna = true;
    }
    s << (nVersion);
    s << hashPrevBlock;
    s << hashMerkleRoot;
    s << nTime;

    if (is_dyna) {
        s << block_height;
        s << m_dynafed_params;
    } else {
        if (g_con_blockheightinheader) {
            s << block_height;
        }
        if (g_signed_blocks) {
            s << proof.challenge;
        } else {
            s << nBits;
            s << nNonce;
        }
    }
    return s.GetHash();
}

std::string CBlock::ToString() const
{
    std::stringstream s;
    s << strprintf("CBlock(hash=%s, ver=0x%08x, hashPrevBlock=%s, hashMerkleRoot=%s, nTime=%u, nBits=%08x, nNonce=%u, proof=%u, vtx=%u)\n",
        GetHash().ToString(),
        nVersion,
        hashPrevBlock.ToString(),
        hashMerkleRoot.ToString(),
        nTime, nBits, nNonce, proof.ToString(),
        vtx.size());
    for (const auto& tx : vtx) {
        s << "  " << tx->ToString() << "\n";
    }
    return s.str();
}

uint256 DynaFedParamEntry::CalculateRoot() const
{
    if (m_serialize_type == 0) {
        return uint256();
    }

    std::vector<uint256> compact_leaves;
    compact_leaves.push_back((HashWriter{} << m_signblockscript).GetHash());
    compact_leaves.push_back((HashWriter{} << m_signblock_witness_limit).GetHash());
    uint256 compact_root(ComputeFastMerkleRoot(compact_leaves));

    uint256 extra_root;
    if (m_serialize_type ==1 ) {
        // It's pruned, take the stored value
        extra_root = m_elided_root;
    } else if (m_serialize_type == 2) {
        // It's unpruned, compute the node value
        extra_root = CalculateExtraRoot();
    }

    std::vector<uint256> leaves;
    leaves.push_back(compact_root);
    leaves.push_back(extra_root);
    return ComputeFastMerkleRoot(leaves);
}

uint256 DynaFedParamEntry::CalculateExtraRoot() const
{
    std::vector<uint256> extra_leaves;
    extra_leaves.push_back((HashWriter{} << m_fedpeg_program).GetHash());
    extra_leaves.push_back((HashWriter{} << m_fedpegscript).GetHash());
    extra_leaves.push_back((HashWriter{} << m_extension_space).GetHash());
    return ComputeFastMerkleRoot(extra_leaves);
}

uint256 DynaFedParams::CalculateRoot() const
{
    if (IsNull()) {
        return uint256();
    }

    std::vector<uint256> leaves;
    leaves.push_back(m_current.CalculateRoot());
    leaves.push_back(m_proposed.CalculateRoot());
    return ComputeFastMerkleRoot(leaves);
}
