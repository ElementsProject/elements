// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_BLOCK_PROOF_H
#define BITCOIN_BLOCK_PROOF_H

#include <consensus/params.h>

#include <stdint.h>

class CBlockHeader;
class CBlockIndex;
class CProof;
class CScript;

// Elements signed chain functionality

/** Check on header proof, depending on chain type, PoW or signed **/
bool CheckProof(const CBlockHeader& block, const Consensus::Params&);
bool CheckProofSignedParent(const CBlockHeader& block, const Consensus::Params&);
void ResetProof(CBlockHeader& block);
bool CheckChallenge(const CBlockHeader& block, const CBlockIndex& indexLast, const Consensus::Params&);
void ResetChallenge(CBlockHeader& block, const CBlockIndex& indexLast, const Consensus::Params&);

#endif // BITCOIN_BLOCK_PROOF_H
