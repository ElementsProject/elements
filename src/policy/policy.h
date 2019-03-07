// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_POLICY_POLICY_H
#define BITCOIN_POLICY_POLICY_H

#include "consensus/consensus.h"
#include "script/interpreter.h"
#include "script/standard.h"

#include <string>
#include <vector>
#include <boost/thread/thread.hpp> // boost::thread::interrupt

class CCoinsViewCache;
class CCoinsView;

/** The sha256 of Bitcoin genesis block, for easy reference **/
extern CAsset policyAsset;

/** the asset for freezelist policy **/
extern CAsset freezelistAsset;
/** the asset for burnlist policy **/
extern CAsset burnlistAsset;
/** the asset for burnlist policy **/
extern CAsset whitelistAsset;

/** Default for -blockmaxsize, which controls the maximum size of block the mining code will create **/
static const unsigned int DEFAULT_BLOCK_MAX_SIZE = 1000000;
/** Default for -blockprioritysize, maximum space for zero/low-fee transactions **/
static const unsigned int DEFAULT_BLOCK_PRIORITY_SIZE = DEFAULT_BLOCK_MAX_SIZE/5;
/** Default for -blockmaxweight, which controls the range of block weights the mining code will create **/
static const unsigned int DEFAULT_BLOCK_MAX_WEIGHT = 4000000;
/** Default for -blockmintxfee, which sets the minimum feerate for a transaction in blocks created by mining code **/
static const unsigned int DEFAULT_BLOCK_MIN_TX_FEE = 1000;
/** The maximum weight for transactions we're willing to relay/mine */
static const unsigned int MAX_STANDARD_TX_WEIGHT = 400000;
/** Maximum number of signature check operations in an IsStandard() P2SH script */
static const unsigned int MAX_P2SH_SIGOPS = 15;
/** The maximum number of sigops we're willing to relay/mine in a single tx */
static const unsigned int MAX_STANDARD_TX_SIGOPS_COST = MAX_BLOCK_SIGOPS_COST/5;
/** Default for -maxmempool, maximum megabytes of mempool memory usage */
static const unsigned int DEFAULT_MAX_MEMPOOL_SIZE = 300;
/** Default for -incrementalrelayfee, which sets the minimum feerate increase for mempool limiting or BIP 125 replacement **/
static const unsigned int DEFAULT_INCREMENTAL_RELAY_FEE = 1000;
/** Default for -bytespersigop */
static const unsigned int DEFAULT_BYTES_PER_SIGOP = 20;
/** The maximum number of witness stack items in a standard P2WSH script */
static const unsigned int MAX_STANDARD_P2WSH_STACK_ITEMS = 100;
/** The maximum size of each witness stack item in a standard P2WSH script */
static const unsigned int MAX_STANDARD_P2WSH_STACK_ITEM_SIZE = 80;
/** The maximum size of a standard witnessScript */
static const unsigned int MAX_STANDARD_P2WSH_SCRIPT_SIZE = 3600;
/** Min feerate for defining dust. Historically this has been the same as the
 * minRelayTxFee, however changing the dust limit changes which transactions are
 * standard and should be done with care and ideally rarely. It makes sense to
 * only increase the dust limit after prior releases were already not creating
 * outputs below the new threshold */
static const unsigned int DUST_RELAY_TX_FEE = 1000;
/**
 * Standard script verification flags that standard transactions will comply
 * with. However scripts violating these flags may still be present in valid
 * blocks and we must accept those blocks.
 */
static const unsigned int STANDARD_SCRIPT_VERIFY_FLAGS = MANDATORY_SCRIPT_VERIFY_FLAGS |
                                                         SCRIPT_VERIFY_DERSIG |
                                                         SCRIPT_VERIFY_STRICTENC |
                                                         SCRIPT_VERIFY_MINIMALDATA |
                                                         SCRIPT_VERIFY_NULLDUMMY |
                                                         SCRIPT_VERIFY_DISCOURAGE_UPGRADABLE_NOPS |
                                                         SCRIPT_VERIFY_CLEANSTACK |
                                                         SCRIPT_VERIFY_MINIMALIF |
                                                         SCRIPT_VERIFY_NULLFAIL |
                                                         SCRIPT_VERIFY_CHECKLOCKTIMEVERIFY |
                                                         SCRIPT_VERIFY_CHECKSEQUENCEVERIFY |
                                                         SCRIPT_VERIFY_LOW_S |
                                                         SCRIPT_VERIFY_WITNESS |
                                                         SCRIPT_VERIFY_DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM |
                                                         SCRIPT_VERIFY_WITNESS_PUBKEYTYPE;

/** For convenience, standard but not mandatory verify flags. */
static const unsigned int STANDARD_NOT_MANDATORY_VERIFY_FLAGS = STANDARD_SCRIPT_VERIFY_FLAGS & ~MANDATORY_SCRIPT_VERIFY_FLAGS;

/** Used as the flags parameter to sequence and nLocktime checks in non-consensus code. */
static const unsigned int STANDARD_LOCKTIME_VERIFY_FLAGS = LOCKTIME_VERIFY_SEQUENCE |
                                                           LOCKTIME_MEDIAN_TIME_PAST;

bool IsStandard(const CScript& scriptPubKey, txnouttype& whichType);
    /**
     * Check for standard transaction types
     * @return True if all outputs (scriptPubKeys) use only standard transaction forms
     */
bool IsStandardTx(const CTransaction& tx, std::string& reason);
    /**
     * Check if all a transactions outputs are OP_RETURN
     */
bool IsBurn(const CTransaction& tx);
    /**
     * Check if a transaction has outputs what are of a policy asset type
     */
bool IsPolicy(const CTransaction& tx);
    /**
     * Check if an asset is of a policy asset type
     */
bool IsPolicy(const CAsset& asset);

    /**
     * Check if a transaction has outputs what are of a policy asset type
     */
bool IsPolicy(const CTransaction& tx);

    /**
     * Check all type and whitelist status of outputs of tx
     * Return true if all outputs of tx are type TX_PUBKEYHASH and all PUBKEYHASHes are present in the whitelist database
     */
bool IsWhitelisted(const CTransaction& tx);
    /**
     *
     */
bool IsRedemption(CTransaction const &tx);
    /**
     *
     */
bool IsValidBurn(CTransaction const &tx, CCoinsViewCache const &mapInputs);
    /**
     * Check all inputs and determine if public keys are on the burnlist and all non-fee outputs are OP_RETURN
     * Return true if all inputs of tx are type TX_PUBKEYHASH and all PUBKEYs are on the burn list
     */
bool IsBurnlisted(const CTransaction& tx, const CCoinsViewCache& mapInputs);
    /**
    * Check all inputs and determine if public keys are on the freezelist
    * Return true if all inputs of tx are type TX_PUBKEYHASH and all PUBKEYs are present in the freezelist
    */
bool IsFreezelisted(const CTransaction& tx, const CCoinsViewCache& mapInputs);

    /**                                                                
    * Update the freezelist with the input tx encoding
    * if the tx has an encoded address in its outputs, these are added to the freezelist
    * if the tx has encoded addresses in its inputs, these are removed from the freezelist
    */
bool UpdateFreezeList(const CTransaction& tx, const CCoinsViewCache& mapInputs);

    /**                                                                
    * Update the burnlist with the input tx encoding
    * if the tx has an encoded address in its outputs, these are added to the burnlist
    * if the tx has encoded addresses in its inputs, these are removed from the burnlist
    */
bool UpdateBurnList(const CTransaction& tx, const CCoinsViewCache& mapInputs);

    //function to scan the UTXO set for freezelist addresses
bool LoadFreezeList(CCoinsView *view);

    //function to scane the UTXO set for burnlist addresses
bool LoadBurnList(CCoinsView *view);

    /**
    */

    //function to scan the UTXO set for freezelist addresses
bool LoadFreezeList(CCoinsView *view);

    //function to scane the UTXO set for burnlist addresses
bool LoadBurnList(CCoinsView *view);
bool AreInputsStandard(const CTransaction& tx, const CCoinsViewCache& mapInputs);
    /**
     * Check if the transaction is over standard P2WSH resources limit:
     * 3600bytes witnessScript size, 80bytes per witness stack element, 100 witness stack ocean
     * These limits are adequate for multi-signature up to n-of-100 using OP_CHECKSIG, OP_ADD, and OP_EQUAL,
     */
bool IsWitnessStandard(const CTransaction& tx, const CCoinsViewCache& mapInputs);

void AddToWhitelist(const std::vector<std::string> address_key);
/**
 *Take a vector containing [tweakedAddress, untweakedPublicKey].
 *Throw an exception if:
 *a) The address of key are not valid.
 *b) The tweaked address cannot be derived from the public key and the contract hash.
 *
 **/


extern CFeeRate incrementalRelayFee;
extern CFeeRate dustRelayFee;
extern unsigned int nBytesPerSigOp;

/** Compute the virtual transaction size (weight reinterpreted as bytes). */
int64_t GetVirtualTransactionSize(int64_t nWeight, int64_t nSigOpCost);
int64_t GetVirtualTransactionSize(const CTransaction& tx, int64_t nSigOpCost = 0);

#endif // BITCOIN_POLICY_POLICY_H
