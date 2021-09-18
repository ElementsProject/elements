// Copyright (c) 2017-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_PEGINS_H
#define BITCOIN_PEGINS_H

#include <amount.h>
#include <consensus/params.h>
#include <merkleblock.h>
#include <primitives/bitcoin/transaction.h>
#include <primitives/bitcoin/merkleblock.h>
#include <primitives/transaction.h>
#include <script/script.h>
#include <chain.h>

#include <variant>

/** Calculates script necessary for p2ch peg-in transactions */
CScript calculate_contract(const CScript& federationRedeemScript, const CScript& witnessProgram);
bool GetAmountFromParentChainPegin(CAmount& amount, const Sidechain::Bitcoin::CTransaction& txBTC, unsigned int nOut);
bool GetAmountFromParentChainPegin(CAmount& amount, const CTransaction& txBTC, unsigned int nOut);
/** Check whether a parent chain block hash satisfies the proof-of-work requirement specified by nBits */
bool CheckParentProofOfWork(uint256 hash, unsigned int nBits, const Consensus::Params&);
/** Checks pegin witness for validity */
bool IsValidPeginWitness(const CScriptWitness& pegin_witness, const std::vector<std::pair<CScript, CScript>>& fedpegscripts, const COutPoint& prevout, std::string& err_msg, bool check_depth, bool* depth_failed = nullptr);

/* Consensus-critical. Matching against telescoped multisig used on Liquid v1:
 * Pseudo-structure:
 * Check number of elements on stack
 * If enough for federation multisig, push all multisig args onto stack except OP_CMS
 * If not, check CSV timeout, then if successful, push emergency key multisig args on
 * stack except OP_CMS. End if, then push OP_CMS.
 */
bool MatchLiquidWatchman(const CScript& script);

/** Get full fedpegscripts from two previous epoch starts based on given index
 * nextblock_validation is false when doing block validation, true for mempool
 * or "lookahead" purposes. Newest epochs first. The first returned element is the
 * scriptPubKey for the script, the second is the witnessScript. */
std::vector<std::pair<CScript, CScript>> GetValidFedpegScripts(const CBlockIndex* pblockindex, const Consensus::Params& params, bool nextblock_validation);

/** Create the peg-in witness stack */
CScriptWitness CreatePeginWitness(const CAmount& value, const CAsset& asset, const uint256& genesis_hash, const CScript& claim_script, const CTransactionRef& tx_ref, const CMerkleBlock& merkle_block);
CScriptWitness CreatePeginWitness(const CAmount& value, const CAsset& asset, const uint256& genesis_hash, const CScript& claim_script, const Sidechain::Bitcoin::CTransactionRef& tx_ref, const Sidechain::Bitcoin::CMerkleBlock& merkle_block);

/** Break out the individual parts of the peg-in witness stack */
bool DecomposePeginWitness(const CScriptWitness& witness, CAmount& value, CAsset& asset, uint256& genesis_hash, CScript& claim_script, std::variant<std::monostate, Sidechain::Bitcoin::CTransactionRef, CTransactionRef>& tx, std::variant<std::monostate, Sidechain::Bitcoin::CMerkleBlock, CMerkleBlock>& merkle_block);

#endif // BITCOIN_PEGINS_H
