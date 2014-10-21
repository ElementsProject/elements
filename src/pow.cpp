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

unsigned int GetNextWorkRequired(const CBlockIndex* pindexLast, int64_t nTime)
{
    unsigned int nProofOfWorkLimit = Params().ProofOfWorkLimit().GetCompact();

    // Genesis block
    if (pindexLast == NULL)
        return nProofOfWorkLimit;

    // Only change once per interval
    if ((pindexLast->nHeight+1) % Params().Interval() != 0)
    {
        if (Params().AllowMinDifficultyBlocks())
        {
            // Special difficulty rule for testnet:
            // If the new block's timestamp is more than 2* 10 minutes
            // then allow mining of a min-difficulty block.
            if (nTime > pindexLast->GetBlockTime() + Params().TargetSpacing()*2)
                return nProofOfWorkLimit;
            else
            {
                // Return the last non-special-min-difficulty-rules-block
                const CBlockIndex* pindex = pindexLast;
                while (pindex->pprev && pindex->nHeight % Params().Interval() != 0 && pindex->proof.nBits == nProofOfWorkLimit)
                    pindex = pindex->pprev;
                return pindex->proof.nBits;
            }
        }
        return pindexLast->proof.nBits;
    }

    // Go back by what we want to be 14 days worth of blocks
    const CBlockIndex* pindexFirst = pindexLast;
    for (int i = 0; pindexFirst && i < Params().Interval()-1; i++)
        pindexFirst = pindexFirst->pprev;
    assert(pindexFirst);

    // Limit adjustment step
    int64_t nActualTimespan = pindexLast->GetBlockTime() - pindexFirst->GetBlockTime();
    LogPrintf("  nActualTimespan = %d  before bounds\n", nActualTimespan);
    if (nActualTimespan < Params().TargetTimespan()/4)
        nActualTimespan = Params().TargetTimespan()/4;
    if (nActualTimespan > Params().TargetTimespan()*4)
        nActualTimespan = Params().TargetTimespan()*4;

    // Retarget
    uint256 bnNew;
    uint256 bnOld;
    bnNew.SetCompact(pindexLast->proof.nBits);
    bnOld = bnNew;
    bnNew *= nActualTimespan;
    bnNew /= Params().TargetTimespan();

    if (bnNew > Params().ProofOfWorkLimit())
        bnNew = Params().ProofOfWorkLimit();

    /// debug print
    LogPrintf("GetNextWorkRequired RETARGET\n");
    LogPrintf("Params().TargetTimespan() = %d    nActualTimespan = %d\n", Params().TargetTimespan(), nActualTimespan);
    LogPrintf("Before: %08x  %s\n", pindexLast->proof.nBits, bnOld.ToString());
    LogPrintf("After:  %08x  %s\n", bnNew.GetCompact(), bnNew.ToString());

    return bnNew.GetCompact();
}

bool CheckChallenge(const CBlockHeader& block, const CBlockIndex& indexLast)
{
    return block.proof.nBits == GetNextWorkRequired(&indexLast, block.GetBlockTime());
}

void ResetChallenge(CBlockHeader& block, const CBlockIndex& indexLast)
{
    block.proof.nBits = GetNextWorkRequired(&indexLast, block.GetBlockTime());
}

bool CheckProof(const CBlockHeader& block)
{
    bool fNegative;
    bool fOverflow;
    uint256 bnTarget;

    if (Params().SkipProofOfWorkCheck())
       return true;

    bnTarget.SetCompact(block.proof.nBits, &fNegative, &fOverflow);

    // Check range
    if (fNegative || bnTarget == 0 || fOverflow || bnTarget > Params().ProofOfWorkLimit())
        return error("%s : nBits below minimum work", __func__);

    // Check proof of work matches claimed amount
    if (block.GetHash() > bnTarget)
        return error("%s : hash doesn't match nBits", __func__);

    return true;
}

bool GenerateProof(CBlockHeader *pblock)
{
    // Write the first 76 bytes of the block header to a double-SHA256 state.
    uint256 hash;
    CHash256 hasher;
    CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
    ss << *pblock;
    assert(ss.size() == 80);
    hasher.Write((unsigned char*)&ss[0], 76);

    while (true) {
        pblock->proof.nNonce++;

        // Write the last 4 bytes of the block header (the nonce) to a copy of
        // the double-SHA256 state, and compute the result.
        CHash256(hasher).Write((unsigned char*)&pblock->proof.nNonce, 4).Finalize((unsigned char*)&hash);

        // Check if the hash has at least some zero bits,
        if (((uint16_t*)&hash)[15] == 0) {
            // then check if it has enough to reach the target
            uint256 hashTarget = uint256().SetCompact(pblock->proof.nBits);
            if (hash <= hashTarget) {
                assert(hash == pblock->GetHash());
                LogPrintf("hash: %s  \ntarget: %s\n", hash.GetHex(), hashTarget.GetHex());
                return true;
            }
        }

        // If nothing found after trying for a while, return -1
        if ((pblock->proof.nNonce & 0xfff) == 0)
            return false;
    }
}

void ResetProof(CBlockHeader& block)
{
    block.proof.nNonce = 0;
}

uint256 GetBlockProof(const CBlockIndex& block)
{
    uint256 bnTarget;
    bool fNegative;
    bool fOverflow;
    bnTarget.SetCompact(block.proof.nBits, &fNegative, &fOverflow);
    if (fNegative || fOverflow || bnTarget == 0)
        return 0;
    // We need to compute 2**256 / (bnTarget+1), but we can't represent 2**256
    // as it's too large for a uint256. However, as 2**256 is at least as large
    // as bnTarget+1, it is equal to ((2**256 - bnTarget - 1) / (bnTarget+1)) + 1,
    // or ~bnTarget / (nTarget+1) + 1.
    return (~bnTarget / (bnTarget + 1)) + 1;
}

double GetChallengeDifficulty(const CBlockIndex* blockindex)
{
    int nShift = (blockindex->proof.nBits >> 24) & 0xff;

    double dDiff =
        (double)0x0000ffff / (double)(blockindex->proof.nBits & 0x00ffffff);

    while (nShift < 29)
    {
        dDiff *= 256.0;
        nShift++;
    }
    while (nShift > 29)
    {
        dDiff /= 256.0;
        nShift--;
    }
    return dDiff;
}

std::string GetChallengeStr(const CBlockIndex& block)
{
    return strprintf("%08x", block.proof.nBits);
}

std::string GetChallengeStrHex(const CBlockIndex& block)
{
    return uint256().SetCompact(block.proof.nBits).GetHex();
}

uint32_t GetNonce(const CBlockHeader& block)
{
    return block.proof.nNonce;
}

void SetNonce(CBlockHeader& block, uint32_t nNonce)
{
    block.proof.nNonce = nNonce;
}
