// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2014 The Bitcoin developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "pow.h"

#include "chain.h"
#include "chainparams.h"
#include "hash.h"
#include "primitives/block.h"
#include "serialize.h"
#include "streams.h"
#include "uint256.h"
#include "util.h"

bool CheckChallenge(const CBlockHeader& block, const CBlockIndex& indexLast)
{
    return true;
}

void ResetChallenge(CBlockHeader& block, const CBlockIndex& indexLast)
{
}

bool CheckProof(const CBlockHeader& block)
{
    return true;
}

bool GenerateProof(CBlockHeader *pblock)
{
    return true;
}

void ResetProof(CBlockHeader& block)
{
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
    return strprintf("%08x", 1);
}

std::string GetChallengeStrHex(const CBlockIndex& block)
{
    return "concept challenge";
}

uint32_t GetNonce(const CBlockHeader& block)
{
    return 1;
}

void SetNonce(CBlockHeader& block, uint32_t nNonce)
{
}
