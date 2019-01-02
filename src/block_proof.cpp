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

void ResetChallenge(CBlockHeader& block, const CBlockIndex& indexLast, const Consensus::Params& params)
{
    block.proof.challenge = indexLast.proof.challenge;
}

static bool CheckProofGeneric(const CBlockHeader& block, const Consensus::Params& params, const CScript& challenge)
{
    if (block.GetHash() == params.hashGenesisBlock)
       return true;

    if (block.proof.solution.size() > params.max_block_signature_size) {
        return false;
    }

    // Some anti-DoS flags, though consensus.max_block_signature_size caps the possible
    // danger in malleation of the block witness data.
    unsigned int proof_flags = SCRIPT_VERIFY_P2SH // For cleanstack evalution under segwit flag
        | SCRIPT_VERIFY_STRICTENC // Minimally-sized DER sigs
        | SCRIPT_VERIFY_NULLDUMMY // No extra data stuffed into OP_CMS witness
        | SCRIPT_VERIFY_CLEANSTACK // No extra pushes leftover in witness
        | SCRIPT_VERIFY_MINIMALDATA // Pushes are minimally-sized
        | SCRIPT_VERIFY_SIGPUSHONLY // Witness is push-only
        | SCRIPT_VERIFY_LOW_S // Stop easiest signature fiddling
        | SCRIPT_VERIFY_WITNESS // Required for cleanstack eval in VerifyScript
        | SCRIPT_NO_SIGHASH_BYTE; // non-Check(Multi)Sig signatures will not have sighash byte
    return GenericVerifyScript(block.proof.solution, challenge, proof_flags, block);
}

bool CheckProof(const CBlockHeader& block, const Consensus::Params& params)
{
    if (g_signed_blocks) {
        return CheckProofGeneric(block, params, params.signblockscript);
    } else {
        return CheckProofOfWork(block.GetHash(), block.nBits, params);
    }
}

bool CheckProofSignedParent(const CBlockHeader& block, const Consensus::Params& params)
{
    return CheckProofGeneric(block, params, params.parent_chain_signblockscript);
}

void ResetProof(CBlockHeader& block)
{
    block.proof.solution.clear();
}
