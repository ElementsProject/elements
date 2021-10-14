// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <pow.h>

#include <chain.h>
#include <primitives/block.h>
#include <script/interpreter.h>
#include <script/generic.hpp>

bool CheckChallenge(const CBlockHeader& block, const CBlockIndex& indexLast, const Consensus::Params& params)
{
    if (g_signed_blocks) {
        return block.proof.challenge == indexLast.proof.challenge;
    } else {
        return block.nBits == GetNextWorkRequired(&indexLast, &block, params);
    }
}

static bool CheckProofGeneric(const CBlockHeader& block, const uint32_t max_block_signature_size, const CScript& challenge, const CScript& scriptSig, const CScriptWitness& witness)
{
    // Legacy blocks have empty witness, dynafed blocks have empty scriptSig
    bool is_dyna = !witness.stack.empty();

    // Check signature limits for blocks
    if (scriptSig.size() > max_block_signature_size) {
        assert(!is_dyna);
        return false;
    } else if (witness.GetSerializedSize() > max_block_signature_size) {
        assert(is_dyna);
        return false;
    }

    // Some anti-DoS flags, though max_block_signature_size caps the possible
    // danger in malleation of the block witness data.
    unsigned int proof_flags = SCRIPT_VERIFY_P2SH // For cleanstack evaluation under segwit flag
        | SCRIPT_VERIFY_STRICTENC // Minimally-sized DER sigs
        | SCRIPT_VERIFY_NULLDUMMY // No extra data stuffed into OP_CMS witness
        | SCRIPT_VERIFY_CLEANSTACK // No extra pushes leftover in witness
        | SCRIPT_VERIFY_MINIMALDATA // Pushes are minimally-sized
        | SCRIPT_VERIFY_SIGPUSHONLY // Witness is push-only
        | SCRIPT_VERIFY_LOW_S // Stop easiest signature fiddling
        | SCRIPT_VERIFY_WITNESS // Witness and to enforce cleanstack
        | (is_dyna ? 0 : SCRIPT_NO_SIGHASH_BYTE); // Non-dynafed blocks do not have sighash byte
    return GenericVerifyScript(scriptSig, witness, challenge, proof_flags, block);
}

bool CheckProof(const CBlockHeader& block, const Consensus::Params& params)
{
    if (g_signed_blocks) {
        const DynaFedParams& dynafed_params = block.m_dynafed_params;
        if (dynafed_params.IsNull()) {
            return CheckProofGeneric(block, params.max_block_signature_size, params.signblockscript, block.proof.solution, CScriptWitness());
        } else {
            return CheckProofGeneric(block, dynafed_params.m_current.m_signblock_witness_limit, dynafed_params.m_current.m_signblockscript, CScript(), block.m_signblock_witness);
        }
    } else {
        return CheckProofOfWork(block.GetHash(), block.nBits, params);
    }
}

bool CheckProofSignedParent(const CBlockHeader& block, const Consensus::Params& params)
{
    const DynaFedParams& dynafed_params = block.m_dynafed_params;
    if (dynafed_params.IsNull()) {
        return CheckProofGeneric(block, params.max_block_signature_size, params.parent_chain_signblockscript, block.proof.solution, CScriptWitness());
    } else {
        // Dynamic federations means we cannot validate the signer set
        // at least without tracking the parent chain more directly.
        // Note that we do not even serialize dynamic federation block witness data
        // currently for merkle proofs which is the only context in which
        // this function is currently used.
        return true;
    }
}
