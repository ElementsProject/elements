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

CScript CombineBlockSignatures(CScript scriptPubKey, const CBlockHeader& header, const CScript& scriptSig1, const CScript& scriptSig2)
{
    return GenericCombineSignatures(scriptPubKey, header, scriptSig1, scriptSig2);
}

bool CheckChallenge(const CBlockHeader& block, const CBlockIndex& indexLast)
{
    return block.proof.challenge == indexLast.proof.challenge;
}

void ResetChallenge(CBlockHeader& block, const CBlockIndex& indexLast)
{
    CPubKey pubkey = pwalletMain->GenerateNewKey();
    block.proof.challenge = GetScriptForDestination(pubkey.GetID());
}

bool CheckProof(const CBlockHeader& block)
{
    return GenericVerifyScript(block.proof.solution, block.proof.challenge, SCRIPT_VERIFY_P2SH, block);
}

bool GenerateProof(CBlockHeader *pblock)
{
    return GenericSignScript(*pwalletMain, *pblock, pblock->proof.challenge, pblock->proof.solution);
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
