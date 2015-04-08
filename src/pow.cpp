// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2014 The Bitcoin developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "pow.h"

#include "chain.h"
#include "chainparams.h"
#include "hash.h"
#include "keystore.h"
#include "primitives/block.h"
#include "script/generic.hpp"
#include "script/standard.h"
#include "uint256.h"
#include "util.h"
#include "wallet.h"

extern CWallet* pwalletMain;

CScript CombineBlockSignatures(const CBlockHeader& header, const CScript& scriptSig1, const CScript& scriptSig2)
{
    return GenericCombineSignatures(header.proof.challenge, header, scriptSig1, scriptSig2);
}

bool CheckChallenge(const CBlockHeader& block, const CBlockIndex& indexLast)
{
    return block.proof.challenge == indexLast.proof.challenge;
}

void ResetChallenge(CBlockHeader& block, const CBlockIndex& indexLast)
{
    block.proof.challenge = indexLast.proof.challenge;
}


bool CheckBitcoinProof(const CBlockHeader& block)
{
    bool fNegative;
    bool fOverflow;
    uint256 bnTarget;

    bnTarget.SetCompact(block.bitcoinproof.challenge, &fNegative, &fOverflow);

    // Check range
    if (fNegative || bnTarget == 0 || fOverflow || bnTarget > Params().ProofOfWorkLimit())
        return error("%s : nBits below minimum work", __func__);

    // Check proof of work matches claimed amount
    if (block.GetHash() > bnTarget)
        return error("%s : hash doesn't match nBits", __func__);

    return true;
}

bool CheckProof(const CBlockHeader& block)
{
    if (block.GetHash() == Params().HashGenesisBlock())
       return true;
    return GenericVerifyScript(block.proof.solution, block.proof.challenge, SCRIPT_VERIFY_P2SH, block);
}

bool GenerateProof(CBlockHeader *pblock, CWallet *pwallet)
{
    return GenericSignScript(*pwallet, *pblock, pblock->proof.challenge, pblock->proof.solution);
}

void ResetProof(CBlockHeader& block)
{
    block.proof.solution.clear();
}

uint256 GetBlockProof(const CBlockIndex& block)
{
    return 1;
}

double GetChallengeDifficulty(const CBlockIndex* blockindex)
{
    return 1;
}

std::string GetChallengeStr(const CBlockIndex& block)
{
    return block.proof.challenge.ToString();
}

std::string GetChallengeStrHex(const CBlockIndex& block)
{
    return block.proof.challenge.ToString();
}

uint32_t GetNonce(const CBlockHeader& block)
{
    return 1;
}

void SetNonce(CBlockHeader& block, uint32_t nNonce)
{
}
