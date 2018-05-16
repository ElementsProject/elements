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

CScript CombineBlockSignatures(const CBlockHeader& header, const CScript& scriptSig1, const CScript& scriptSig2)
{
    SignatureData sig1(scriptSig1);
    SignatureData sig2(scriptSig2);
    return GenericCombineSignatures(header.proof.challenge, header, sig1, sig2).scriptSig;
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

bool CheckProof(const CBlockHeader& block, const Consensus::Params& params)
{
    if (block.GetHash() == params.hashGenesisBlock)
       return true;
    return GenericVerifyScript(block.proof.solution, block.proof.challenge, SCRIPT_VERIFY_P2SH, block);
}

bool MaybeGenerateProof(CBlockHeader *pblock, CWallet *pwallet)
{
#ifdef ENABLE_WALLET
    SignatureData solution(pblock->proof.solution);
    bool res = GenericSignScript(*pwallet, *pblock, pblock->proof.challenge, solution);
    pblock->proof.solution = solution.scriptSig;
    return res;
#endif
    return false;
}

void ResetProof(CBlockHeader& block)
{
    block.proof.solution.clear();
}
