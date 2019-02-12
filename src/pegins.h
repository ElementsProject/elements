// Copyright (c) 2017-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_PEGINS_H
#define BITCOIN_PEGINS_H

#include <amount.h>
#include <consensus/params.h>
#include <primitives/bitcoin/transaction.h>
#include <primitives/transaction.h>
#include <script/script.h>

/** Calculates script necessary for p2ch peg-in transactions */
CScript calculate_contract(const CScript& federationRedeemScript, const CScript& witnessProgram);
bool GetAmountFromParentChainPegin(CAmount& amount, const Sidechain::Bitcoin::CTransaction& txBTC, unsigned int nOut);
bool GetAmountFromParentChainPegin(CAmount& amount, const CTransaction& txBTC, unsigned int nOut);
/** Check whether a parent chain block hash satisfies the proof-of-work requirement specified by nBits */
bool CheckParentProofOfWork(uint256 hash, unsigned int nBits, const Consensus::Params&);
/** Checks pegin witness for validity */
bool IsValidPeginWitness(const CScriptWitness& pegin_witness, const COutPoint& prevout, std::string& err_msg, bool check_depth);
// Constructs unblinded output to be used in amount and scriptpubkey checks during pegin
CTxOut GetPeginOutputFromWitness(const CScriptWitness& pegin_witness);

/* Belt-and-suspenders-only matching against telescoped multisig used on Liquid v1:
 * Pseudo-structure:
 * Check number of elements on stack
 * If enough for federation multisig, push all multisig args onto stack except OP_CMS
 * If not, check CSV timeout, then if successful, push emergency key multisig args on
 * stack except OP_CMS. End if, then push OP_CMS.
 */
bool MatchLiquidWatchman(const CScript& script);

#endif // BITCOIN_PEGINS_H
