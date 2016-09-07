// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2015 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_POW_H
#define BITCOIN_POW_H

#include "consensus/params.h"

#include <stdint.h>
#include <string>

class CBlockHeader;
class CBlockIndex;
class CProof;
class CScript;
class CWallet;
class uint256;


/** Check whether a block hash satisfies the proof-of-work requirement specified by nBits */
bool CheckProof(const CBlockHeader& block, const Consensus::Params&);
/** Scans nonces looking for a hash with at least some zero bits */
bool MaybeGenerateProof(CBlockHeader* pblock, CWallet* pwallet);
void ResetProof(CBlockHeader& block);
bool CheckChallenge(const CBlockHeader& block, const CBlockIndex& indexLast, const Consensus::Params&);
void ResetChallenge(CBlockHeader& block, const CBlockIndex& indexLast, const Consensus::Params&);

CScript CombineBlockSignatures(const CBlockHeader& header, const CScript& scriptSig1, const CScript& scriptSig2);

/** Avoid using these functions when possible */
double GetChallengeDifficulty(const CBlockIndex* blockindex);
std::string GetChallengeStr(const CBlockIndex& block);
std::string GetChallengeStrHex(const CBlockIndex& block);
uint32_t GetNonce(const CBlockHeader& block);
void SetNonce(CBlockHeader& block, uint32_t nNonce);

#endif // BITCOIN_POW_H
