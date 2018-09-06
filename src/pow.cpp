// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "pow.h"

#include "arith_uint256.h"
#include "chain.h"
#include "chainparams.h"
#include "core_io.h"
#include "hash.h"
#include "keystore.h"
#include "primitives/block.h"
#include "primitives/bitcoin/block.h"
#include "script/generic.hpp"
#include "script/standard.h"
#include "uint256.h"

#ifdef ENABLE_WALLET
#include "wallet/wallet.h"
#endif

CScript CombineBlockSignatures(const Consensus::Params& params, const CBlockHeader& header, const CScript& scriptSig1, const CScript& scriptSig2)
{
    SignatureData sig1(scriptSig1);
    SignatureData sig2(scriptSig2);
    return GenericCombineSignatures(params.signblockscript, header, sig1, sig2).scriptSig;
}

bool CheckChallenge(const CBlockHeader& block, const CBlockIndex& indexLast, const Consensus::Params& params)
{
    return block.proof.challenge == indexLast.proof.challenge;
}

void ResetChallenge(CBlockHeader& block, const CBlockIndex& indexLast, const Consensus::Params& params)
{
    block.proof.challenge = indexLast.proof.challenge;
}

bool CheckBitcoinProof(uint256 hash, unsigned int nBits)
{
    bool fNegative;
    bool fOverflow;
    arith_uint256 bnTarget;

    bnTarget.SetCompact(nBits, &fNegative, &fOverflow);

    // Check range
    if (fNegative || bnTarget == 0 || fOverflow || bnTarget > UintToArith256(Params().GetConsensus().parentChainPowLimit))
        return false;

    // Check proof of work matches claimed amount
    if (UintToArith256(hash) > bnTarget)
        return false;

    return true;
}

static bool CheckProofGeneric(const CBlockHeader& block, const Consensus::Params& params, const CScript& challenge)
{
    if (block.GetHash() == params.hashGenesisBlock)
       return true;

    // Some important anti-DoS flags.
    // Note: Blockhashes do not commit to the proof.
    // Therefore we may have a signature be mealleated
    // to stay valid, but cause the block to fail
    // validation, in this case, block weight.
    // In that case, the block will be marked as permanently
    // invalid and not processed.
    // NOTE: These have only been deemed sufficient for OP_CMS
    // ANY OTHER SCRIPT TYPE MAY REQUIRE DIFFERENT FLAGS/CONSIDERATIONS
    // TODO: Better design to not have to worry about script specifics
    // i.e. exempt block header solution from weight limit
    unsigned int proof_flags = SCRIPT_VERIFY_P2SH // Just allows P2SH evaluation
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

bool CheckProofSignedParent(const CBlockHeader& block, const Consensus::Params& params)
{
    return CheckProofGeneric(block, params, params.parent_chain_signblockscript);
}

bool CheckProof(const CBlockHeader& block, const Consensus::Params& params)
{
    return CheckProofGeneric(block, params, params.signblockscript);
}

bool MaybeGenerateProof(const Consensus::Params& params, CBlockHeader *pblock, CWallet *pwallet)
{
#ifdef ENABLE_WALLET
    SignatureData solution(pblock->proof.solution);
    bool res = GenericSignScript(*pwallet, *pblock, params.signblockscript, solution);
    pblock->proof.solution = solution.scriptSig;
    return res;
#endif
    return false;
}

void ResetProof(CBlockHeader& block)
{
    block.proof.solution.clear();
}
