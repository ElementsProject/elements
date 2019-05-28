// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "base58.h"
#include "amount.h"
#include "chain.h"
#include "chainparams.h"
#include "checkpoints.h"
#include "coins.h"
#include "consensus/validation.h"
#include "validation.h"
#include "policy/policy.h"
#include "primitives/transaction.h"
#include "rpc/server.h"
#include "pow.h"
#include "streams.h"
#include "sync.h"
#include "txmempool.h"
#include "util.h"
#include "utilstrencodings.h"
#include "hash.h"
#include "request.h"

#include <fstream>

#include <stdint.h>

#include <univalue.h>

#include <boost/algorithm/string.hpp>
#include <boost/thread/thread.hpp> // boost::thread::interrupt
#include <boost/algorithm/string.hpp>


#include <mutex>
#include <condition_variable>
using namespace std;

struct CUpdatedBlock
{
    uint256 hash;
    int height;
};

static std::mutex cs_blockchange;
static std::condition_variable cond_blockchange;
static CUpdatedBlock latestblock;

extern void TxToJSON(const CTransaction& tx, const uint256 hashBlock, UniValue& entry);
extern UniValue requestToJSON(const CRequest &request);
extern UniValue bidToJSON(const CBid &bid);
void ScriptPubKeyToJSON(const CScript& scriptPubKey, UniValue& out, bool fIncludeHex);

double GetDifficulty(const CBlockIndex* blockindex)
{
    // Floating point number that is a multiple of the minimum difficulty,
    // minimum difficulty = 1.0.
    if (blockindex == NULL)
    {
        if (chainActive.Tip() == NULL)
            return 1.0;
        else
            blockindex = chainActive.Tip();
    }
    return GetChallengeDifficulty(blockindex);
}

UniValue blockheaderToJSON(const CBlockIndex* blockindex)
{
    UniValue result(UniValue::VOBJ);
    result.push_back(Pair("hash", blockindex->GetBlockHash().GetHex()));
    int confirmations = -1;
    // Only report confirmations if the block is on the main chain
    if (chainActive.Contains(blockindex))
        confirmations = chainActive.Height() - blockindex->nHeight + 1;
    result.push_back(Pair("confirmations", confirmations));
    result.push_back(Pair("height", blockindex->nHeight));
    result.push_back(Pair("version", blockindex->nVersion));
    result.push_back(Pair("versionHex", strprintf("%08x", blockindex->nVersion)));
    result.push_back(Pair("merkleroot", blockindex->hashMerkleRoot.GetHex()));
    result.push_back(Pair("time", (int64_t)blockindex->nTime));
    result.push_back(Pair("mediantime", (int64_t)blockindex->GetMedianTimePast()));
    result.push_back(Pair("nonce", (uint64_t)GetNonce(blockindex->GetBlockHeader())));
    result.push_back(Pair("bits", GetChallengeStr(blockindex->GetBlockHeader())));
    result.push_back(Pair("difficulty", GetDifficulty(blockindex)));
    result.push_back(Pair("chainwork", blockindex->nChainWork.GetHex()));
    result.push_back(Pair("contracthash", blockindex->hashContract.GetHex()));
    result.push_back(Pair("attestationhash", blockindex->hashAttestation.GetHex()));
    result.push_back(Pair("mappinghash", blockindex->hashMapping.GetHex()));
    if (blockindex->pprev)
        result.push_back(Pair("previousblockhash", blockindex->pprev->GetBlockHash().GetHex()));
    CBlockIndex *pnext = chainActive.Next(blockindex);
    if (pnext)
        result.push_back(Pair("nextblockhash", pnext->GetBlockHash().GetHex()));
    return result;
}

UniValue blockToJSON(const CBlock& block, const CBlockIndex* blockindex, bool txDetails = false)
{
    UniValue result(UniValue::VOBJ);
    result.push_back(Pair("hash", blockindex->GetBlockHash().GetHex()));
    int confirmations = -1;
    // Only report confirmations if the block is on the main chain
    if (chainActive.Contains(blockindex))
        confirmations = chainActive.Height() - blockindex->nHeight + 1;
    result.push_back(Pair("confirmations", confirmations));
    result.push_back(Pair("strippedsize", (int)::GetSerializeSize(block, SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS)));
    result.push_back(Pair("size", (int)::GetSerializeSize(block, SER_NETWORK, PROTOCOL_VERSION)));
    result.push_back(Pair("weight", (int)::GetBlockWeight(block)));
    result.push_back(Pair("height", blockindex->nHeight));
    result.push_back(Pair("version", block.nVersion));
    result.push_back(Pair("versionHex", strprintf("%08x", block.nVersion)));
    result.push_back(Pair("merkleroot", block.hashMerkleRoot.GetHex()));
    UniValue txs(UniValue::VARR);
    for(const auto& tx : block.vtx)
    {
        if(txDetails)
        {
            UniValue objTx(UniValue::VOBJ);
            TxToJSON(*tx, uint256(), objTx);
            txs.push_back(objTx);
        }
        else
            txs.push_back(tx->GetHash().GetHex());
    }
    result.push_back(Pair("tx", txs));
    result.push_back(Pair("time", block.GetBlockTime()));
    result.push_back(Pair("mediantime", (int64_t)blockindex->GetMedianTimePast()));
    result.push_back(Pair("nonce", (uint64_t)GetNonce(block)));
    result.push_back(Pair("bits", GetChallengeStr(block)));
    result.push_back(Pair("difficulty", GetDifficulty(blockindex)));
    result.push_back(Pair("chainwork", blockindex->nChainWork.GetHex()));
    result.push_back(Pair("contracthash", blockindex->hashContract.GetHex()));
    result.push_back(Pair("attestationhash", blockindex->hashAttestation.GetHex()));
    result.push_back(Pair("mappinghash", blockindex->hashMapping.GetHex()));
    if (blockindex->pprev)
        result.push_back(Pair("previousblockhash", blockindex->pprev->GetBlockHash().GetHex()));
    CBlockIndex *pnext = chainActive.Next(blockindex);
    if (pnext)
        result.push_back(Pair("nextblockhash", pnext->GetBlockHash().GetHex()));
    return result;
}

UniValue getblockcount(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 0)
        throw runtime_error(
            "getblockcount\n"
            "\nReturns the number of blocks in the longest blockchain.\n"
            "\nResult:\n"
            "n    (numeric) The current block count\n"
            "\nExamples:\n"
            + HelpExampleCli("getblockcount", "")
            + HelpExampleRpc("getblockcount", "")
        );

    LOCK(cs_main);
    return chainActive.Height();
}

UniValue getbestblockhash(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 0)
        throw runtime_error(
            "getbestblockhash\n"
            "\nReturns the hash of the best (tip) block in the longest blockchain.\n"
            "\nResult:\n"
            "\"hex\"      (string) the block hash hex encoded\n"
            "\nExamples:\n"
            + HelpExampleCli("getbestblockhash", "")
            + HelpExampleRpc("getbestblockhash", "")
        );

    LOCK(cs_main);
    return chainActive.Tip()->GetBlockHash().GetHex();
}

void RPCNotifyBlockChange(bool ibd, const CBlockIndex * pindex)
{
    if(pindex) {
        std::lock_guard<std::mutex> lock(cs_blockchange);
        latestblock.hash = pindex->GetBlockHash();
        latestblock.height = pindex->nHeight;
    }
	cond_blockchange.notify_all();
}

UniValue waitfornewblock(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() > 1)
        throw runtime_error(
            "waitfornewblock (timeout)\n"
            "\nWaits for a specific new block and returns useful info about it.\n"
            "\nReturns the current block on timeout or exit.\n"
            "\nArguments:\n"
            "1. timeout (int, optional, default=0) Time in milliseconds to wait for a response. 0 indicates no timeout.\n"
            "\nResult:\n"
            "{                           (json object)\n"
            "  \"hash\" : {       (string) The blockhash\n"
            "  \"height\" : {     (int) Block height\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("waitfornewblock", "1000")
            + HelpExampleRpc("waitfornewblock", "1000")
        );
    int timeout = 0;
    if (request.params.size() > 0)
        timeout = request.params[0].get_int();

    CUpdatedBlock block;
    {
        std::unique_lock<std::mutex> lock(cs_blockchange);
        block = latestblock;
        if(timeout)
            cond_blockchange.wait_for(lock, std::chrono::milliseconds(timeout), [&block]{return latestblock.height != block.height || latestblock.hash != block.hash || !IsRPCRunning(); });
        else
            cond_blockchange.wait(lock, [&block]{return latestblock.height != block.height || latestblock.hash != block.hash || !IsRPCRunning(); });
        block = latestblock;
    }
    UniValue ret(UniValue::VOBJ);
    ret.push_back(Pair("hash", block.hash.GetHex()));
    ret.push_back(Pair("height", block.height));
    return ret;
}

UniValue waitforblock(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() < 1 || request.params.size() > 2)
        throw runtime_error(
            "waitforblock <blockhash> (timeout)\n"
            "\nWaits for a specific new block and returns useful info about it.\n"
            "\nReturns the current block on timeout or exit.\n"
            "\nArguments:\n"
            "1. \"blockhash\" (required, string) Block hash to wait for.\n"
            "2. timeout       (int, optional, default=0) Time in milliseconds to wait for a response. 0 indicates no timeout.\n"
            "\nResult:\n"
            "{                           (json object)\n"
            "  \"hash\" : {       (string) The blockhash\n"
            "  \"height\" : {     (int) Block height\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("waitforblock", "\"0000000000079f8ef3d2c688c244eb7a4570b24c9ed7b4a8c619eb02596f8862\", 1000")
            + HelpExampleRpc("waitforblock", "\"0000000000079f8ef3d2c688c244eb7a4570b24c9ed7b4a8c619eb02596f8862\", 1000")
        );
    int timeout = 0;

    uint256 hash = uint256S(request.params[0].get_str());

    if (request.params.size() > 1)
        timeout = request.params[1].get_int();

    CUpdatedBlock block;
    {
        std::unique_lock<std::mutex> lock(cs_blockchange);
        if(timeout)
            cond_blockchange.wait_for(lock, std::chrono::milliseconds(timeout), [&hash]{return latestblock.hash == hash || !IsRPCRunning();});
        else
            cond_blockchange.wait(lock, [&hash]{return latestblock.hash == hash || !IsRPCRunning(); });
        block = latestblock;
    }

    UniValue ret(UniValue::VOBJ);
    ret.push_back(Pair("hash", block.hash.GetHex()));
    ret.push_back(Pair("height", block.height));
    return ret;
}

UniValue waitforblockheight(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() < 1 || request.params.size() > 2)
        throw runtime_error(
            "waitforblockheight <height> (timeout)\n"
            "\nWaits for (at least) block height and returns the height and hash\n"
            "of the current tip.\n"
            "\nReturns the current block on timeout or exit.\n"
            "\nArguments:\n"
            "1. height  (required, int) Block height to wait for (int)\n"
            "2. timeout (int, optional, default=0) Time in milliseconds to wait for a response. 0 indicates no timeout.\n"
            "\nResult:\n"
            "{                           (json object)\n"
            "  \"hash\" : {       (string) The blockhash\n"
            "  \"height\" : {     (int) Block height\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("waitforblockheight", "\"100\", 1000")
            + HelpExampleRpc("waitforblockheight", "\"100\", 1000")
        );
    int timeout = 0;

    int height = request.params[0].get_int();

    if (request.params.size() > 1)
        timeout = request.params[1].get_int();

    CUpdatedBlock block;
    {
        std::unique_lock<std::mutex> lock(cs_blockchange);
        if(timeout)
            cond_blockchange.wait_for(lock, std::chrono::milliseconds(timeout), [&height]{return latestblock.height >= height || !IsRPCRunning();});
        else
            cond_blockchange.wait(lock, [&height]{return latestblock.height >= height || !IsRPCRunning(); });
        block = latestblock;
    }
    UniValue ret(UniValue::VOBJ);
    ret.push_back(Pair("hash", block.hash.GetHex()));
    ret.push_back(Pair("height", block.height));
    return ret;
}

UniValue getdifficulty(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 0)
        throw runtime_error(
            "getdifficulty\n"
            "\nReturns the proof-of-work difficulty as a multiple of the minimum difficulty.\n"
            "\nResult:\n"
            "n.nnn       (numeric) the proof-of-work difficulty as a multiple of the minimum difficulty.\n"
            "\nExamples:\n"
            + HelpExampleCli("getdifficulty", "")
            + HelpExampleRpc("getdifficulty", "")
        );

    LOCK(cs_main);
    return GetDifficulty();
}

std::string EntryDescriptionString()
{
    return "    \"size\" : n,             (numeric) virtual transaction size as defined in BIP 141. This is different from actual serialized size for witness transactions as witness data is discounted.\n"
           "    \"fee\" : n,              (numeric) transaction fee in " + CURRENCY_UNIT + "\n"
           "    \"modifiedfee\" : n,      (numeric) transaction fee with fee deltas used for mining priority\n"
           "    \"time\" : n,             (numeric) local time transaction entered pool in seconds since 1 Jan 1970 GMT\n"
           "    \"height\" : n,           (numeric) block height when transaction entered pool\n"
           "    \"startingpriority\" : n, (numeric) DEPRECATED. Priority when transaction entered pool\n"
           "    \"currentpriority\" : n,  (numeric) DEPRECATED. Transaction priority now\n"
           "    \"descendantcount\" : n,  (numeric) number of in-mempool descendant transactions (including this one)\n"
           "    \"descendantsize\" : n,   (numeric) virtual transaction size of in-mempool descendants (including this one)\n"
           "    \"descendantfees\" : n,   (numeric) modified fees (see above) of in-mempool descendants (including this one)\n"
           "    \"ancestorcount\" : n,    (numeric) number of in-mempool ancestor transactions (including this one)\n"
           "    \"ancestorsize\" : n,     (numeric) virtual transaction size of in-mempool ancestors (including this one)\n"
           "    \"ancestorfees\" : n,     (numeric) modified fees (see above) of in-mempool ancestors (including this one)\n"
           "    \"depends\" : [           (array) unconfirmed transactions used as inputs for this transaction\n"
           "        \"transactionid\",    (string) parent transaction id\n"
           "       ... ]\n";
}

void entryToJSON(UniValue &info, const CTxMemPoolEntry &e)
{
    AssertLockHeld(mempool.cs);

    info.push_back(Pair("size", (int)e.GetTxSize()));
    info.push_back(Pair("fee", ValueFromAmount(e.GetFee())));
    info.push_back(Pair("modifiedfee", ValueFromAmount(e.GetModifiedFee())));
    info.push_back(Pair("time", e.GetTime()));
    info.push_back(Pair("height", (int)e.GetHeight()));
    info.push_back(Pair("startingpriority", e.GetPriority(e.GetHeight())));
    info.push_back(Pair("currentpriority", e.GetPriority(chainActive.Height())));
    info.push_back(Pair("descendantcount", e.GetCountWithDescendants()));
    info.push_back(Pair("descendantsize", e.GetSizeWithDescendants()));
    info.push_back(Pair("descendantfees", e.GetModFeesWithDescendants()));
    info.push_back(Pair("ancestorcount", e.GetCountWithAncestors()));
    info.push_back(Pair("ancestorsize", e.GetSizeWithAncestors()));
    info.push_back(Pair("ancestorfees", e.GetModFeesWithAncestors()));
    const CTransaction& tx = e.GetTx();
    set<string> setDepends;
    BOOST_FOREACH(const CTxIn& txin, tx.vin)
    {
        if (mempool.exists(txin.prevout.hash))
            setDepends.insert(txin.prevout.hash.ToString());
    }

    UniValue depends(UniValue::VARR);
    BOOST_FOREACH(const string& dep, setDepends)
    {
        depends.push_back(dep);
    }

    info.push_back(Pair("depends", depends));
}

UniValue mempoolToJSON(bool fVerbose = false)
{
    if (fVerbose)
    {
        LOCK(mempool.cs);
        UniValue o(UniValue::VOBJ);
        BOOST_FOREACH(const CTxMemPoolEntry& e, mempool.mapTx)
        {
            const uint256& hash = e.GetTx().GetHash();
            UniValue info(UniValue::VOBJ);
            entryToJSON(info, e);
            o.push_back(Pair(hash.ToString(), info));
        }
        return o;
    }
    else
    {
        vector<uint256> vtxid;
        mempool.queryHashes(vtxid);

        UniValue a(UniValue::VARR);
        BOOST_FOREACH(const uint256& hash, vtxid)
            a.push_back(hash.ToString());

        return a;
    }
}

UniValue getrawmempool(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() > 1)
        throw runtime_error(
            "getrawmempool ( verbose )\n"
            "\nReturns all transaction ids in memory pool as a json array of string transaction ids.\n"
            "\nArguments:\n"
            "1. verbose (boolean, optional, default=false) True for a json object, false for array of transaction ids\n"
            "\nResult: (for verbose = false):\n"
            "[                     (json array of string)\n"
            "  \"transactionid\"     (string) The transaction id\n"
            "  ,...\n"
            "]\n"
            "\nResult: (for verbose = true):\n"
            "{                           (json object)\n"
            "  \"transactionid\" : {       (json object)\n"
            + EntryDescriptionString()
            + "  }, ...\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("getrawmempool", "true")
            + HelpExampleRpc("getrawmempool", "true")
        );

    bool fVerbose = false;
    if (request.params.size() > 0)
        fVerbose = request.params[0].get_bool();

    return mempoolToJSON(fVerbose);
}

UniValue getmempoolancestors(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() < 1 || request.params.size() > 2) {
        throw runtime_error(
            "getmempoolancestors txid (verbose)\n"
            "\nIf txid is in the mempool, returns all in-mempool ancestors.\n"
            "\nArguments:\n"
            "1. \"txid\"                 (string, required) The transaction id (must be in mempool)\n"
            "2. verbose                  (boolean, optional, default=false) True for a json object, false for array of transaction ids\n"
            "\nResult (for verbose=false):\n"
            "[                       (json array of strings)\n"
            "  \"transactionid\"           (string) The transaction id of an in-mempool ancestor transaction\n"
            "  ,...\n"
            "]\n"
            "\nResult (for verbose=true):\n"
            "{                           (json object)\n"
            "  \"transactionid\" : {       (json object)\n"
            + EntryDescriptionString()
            + "  }, ...\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("getmempoolancestors", "\"mytxid\"")
            + HelpExampleRpc("getmempoolancestors", "\"mytxid\"")
            );
    }

    bool fVerbose = false;
    if (request.params.size() > 1)
        fVerbose = request.params[1].get_bool();

    uint256 hash = ParseHashV(request.params[0], "parameter 1");

    LOCK(mempool.cs);

    CTxMemPool::txiter it = mempool.mapTx.find(hash);
    if (it == mempool.mapTx.end()) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Transaction not in mempool");
    }

    CTxMemPool::setEntries setAncestors;
    uint64_t noLimit = std::numeric_limits<uint64_t>::max();
    std::string dummy;
    mempool.CalculateMemPoolAncestors(*it, setAncestors, noLimit, noLimit, noLimit, noLimit, dummy, false);

    if (!fVerbose) {
        UniValue o(UniValue::VARR);
        BOOST_FOREACH(CTxMemPool::txiter ancestorIt, setAncestors) {
            o.push_back(ancestorIt->GetTx().GetHash().ToString());
        }

        return o;
    } else {
        UniValue o(UniValue::VOBJ);
        BOOST_FOREACH(CTxMemPool::txiter ancestorIt, setAncestors) {
            const CTxMemPoolEntry &e = *ancestorIt;
            const uint256& _hash = e.GetTx().GetHash();
            UniValue info(UniValue::VOBJ);
            entryToJSON(info, e);
            o.push_back(Pair(_hash.ToString(), info));
        }
        return o;
    }
}

UniValue getmempooldescendants(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() < 1 || request.params.size() > 2) {
        throw runtime_error(
            "getmempooldescendants txid (verbose)\n"
            "\nIf txid is in the mempool, returns all in-mempool descendants.\n"
            "\nArguments:\n"
            "1. \"txid\"                 (string, required) The transaction id (must be in mempool)\n"
            "2. verbose                  (boolean, optional, default=false) True for a json object, false for array of transaction ids\n"
            "\nResult (for verbose=false):\n"
            "[                       (json array of strings)\n"
            "  \"transactionid\"           (string) The transaction id of an in-mempool descendant transaction\n"
            "  ,...\n"
            "]\n"
            "\nResult (for verbose=true):\n"
            "{                           (json object)\n"
            "  \"transactionid\" : {       (json object)\n"
            + EntryDescriptionString()
            + "  }, ...\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("getmempooldescendants", "\"mytxid\"")
            + HelpExampleRpc("getmempooldescendants", "\"mytxid\"")
            );
    }

    bool fVerbose = false;
    if (request.params.size() > 1)
        fVerbose = request.params[1].get_bool();

    uint256 hash = ParseHashV(request.params[0], "parameter 1");

    LOCK(mempool.cs);

    CTxMemPool::txiter it = mempool.mapTx.find(hash);
    if (it == mempool.mapTx.end()) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Transaction not in mempool");
    }

    CTxMemPool::setEntries setDescendants;
    mempool.CalculateDescendants(it, setDescendants);
    // CTxMemPool::CalculateDescendants will include the given tx
    setDescendants.erase(it);

    if (!fVerbose) {
        UniValue o(UniValue::VARR);
        BOOST_FOREACH(CTxMemPool::txiter descendantIt, setDescendants) {
            o.push_back(descendantIt->GetTx().GetHash().ToString());
        }

        return o;
    } else {
        UniValue o(UniValue::VOBJ);
        BOOST_FOREACH(CTxMemPool::txiter descendantIt, setDescendants) {
            const CTxMemPoolEntry &e = *descendantIt;
            const uint256& _hash = e.GetTx().GetHash();
            UniValue info(UniValue::VOBJ);
            entryToJSON(info, e);
            o.push_back(Pair(_hash.ToString(), info));
        }
        return o;
    }
}

UniValue getmempoolentry(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 1) {
        throw runtime_error(
            "getmempoolentry txid\n"
            "\nReturns mempool data for given transaction\n"
            "\nArguments:\n"
            "1. \"txid\"                   (string, required) The transaction id (must be in mempool)\n"
            "\nResult:\n"
            "{                           (json object)\n"
            + EntryDescriptionString()
            + "}\n"
            "\nExamples:\n"
            + HelpExampleCli("getmempoolentry", "\"mytxid\"")
            + HelpExampleRpc("getmempoolentry", "\"mytxid\"")
        );
    }

    uint256 hash = ParseHashV(request.params[0], "parameter 1");

    LOCK(mempool.cs);

    CTxMemPool::txiter it = mempool.mapTx.find(hash);
    if (it == mempool.mapTx.end()) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Transaction not in mempool");
    }

    const CTxMemPoolEntry &e = *it;
    UniValue info(UniValue::VOBJ);
    entryToJSON(info, e);
    return info;
}

UniValue getblockhash(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "getblockhash height\n"
            "\nReturns hash of block in best-block-chain at height provided.\n"
            "\nArguments:\n"
            "1. height         (numeric, required) The height index\n"
            "\nResult:\n"
            "\"hash\"         (string) The block hash\n"
            "\nExamples:\n"
            + HelpExampleCli("getblockhash", "1000")
            + HelpExampleRpc("getblockhash", "1000")
        );

    LOCK(cs_main);

    int nHeight = request.params[0].get_int();
    if (nHeight < 0 || nHeight > chainActive.Height())
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Block height out of range");

    CBlockIndex* pblockindex = chainActive[nHeight];
    return pblockindex->GetBlockHash().GetHex();
}

UniValue getblockheader(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() < 1 || request.params.size() > 2)
        throw runtime_error(
            "getblockheader \"hash\" ( verbose )\n"
            "\nIf verbose is false, returns a string that is serialized, hex-encoded data for blockheader 'hash'.\n"
            "If verbose is true, returns an Object with information about blockheader <hash>.\n"
            "\nArguments:\n"
            "1. \"hash\"          (string, required) The block hash\n"
            "2. verbose           (boolean, optional, default=true) true for a json object, false for the hex encoded data\n"
            "\nResult (for verbose = true):\n"
            "{\n"
            "  \"hash\" : \"hash\",     (string) the block hash (same as provided)\n"
            "  \"confirmations\" : n,   (numeric) The number of confirmations, or -1 if the block is not on the main chain\n"
            "  \"height\" : n,          (numeric) The block height or index\n"
            "  \"version\" : n,         (numeric) The block version\n"
            "  \"versionHex\" : \"00000000\", (string) The block version formatted in hexadecimal\n"
            "  \"merkleroot\" : \"xxxx\", (string) The merkle root\n"
            "  \"time\" : ttt,          (numeric) The block time in seconds since epoch (Jan 1 1970 GMT)\n"
            "  \"mediantime\" : ttt,    (numeric) The median block time in seconds since epoch (Jan 1 1970 GMT)\n"
            "  \"nonce\" : n,           (numeric) The nonce\n"
            "  \"bits\" : \"1d00ffff\", (string) The bits\n"
            "  \"difficulty\" : x.xxx,  (numeric) The difficulty\n"
            "  \"chainwork\" : \"0000...1f3\"     (string) Expected number of hashes required to produce the current chain (in hex)\n"
            "  \"previousblockhash\" : \"hash\",  (string) The hash of the previous block\n"
            "  \"nextblockhash\" : \"hash\",      (string) The hash of the next block\n"
            "}\n"
            "\nResult (for verbose=false):\n"
            "\"data\"             (string) A string that is serialized, hex-encoded data for block 'hash'.\n"
            "\nExamples:\n"
            + HelpExampleCli("getblockheader", "\"00000000c937983704a73af28acdec37b049d214adbda81d7e2a3dd146f6ed09\"")
            + HelpExampleRpc("getblockheader", "\"00000000c937983704a73af28acdec37b049d214adbda81d7e2a3dd146f6ed09\"")
        );

    LOCK(cs_main);

    std::string strHash = request.params[0].get_str();
    uint256 hash(uint256S(strHash));

    bool fVerbose = true;
    if (request.params.size() > 1)
        fVerbose = request.params[1].get_bool();

    if (mapBlockIndex.count(hash) == 0)
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Block not found");

    CBlockIndex* pblockindex = mapBlockIndex[hash];

    if (!fVerbose)
    {
        CDataStream ssBlock(SER_NETWORK, PROTOCOL_VERSION);
        ssBlock << pblockindex->GetBlockHeader();
        std::string strHex = HexStr(ssBlock.begin(), ssBlock.end());
        return strHex;
    }

    return blockheaderToJSON(pblockindex);
}

static CBlock GetBlockChecked(const CBlockIndex* pblockindex)
{
    CBlock block;
    if (fHavePruned && !(pblockindex->nStatus & BLOCK_HAVE_DATA) && pblockindex->nTx > 0) {
        throw JSONRPCError(RPC_MISC_ERROR, "Block not available (pruned data)");
    }

    if (!ReadBlockFromDisk(block, pblockindex, Params().GetConsensus())) {
        // Block not found on disk. This could be because we have the block
        // header in our index but don't have the block (for example if a
        // non-whitelisted node sends us an unrequested long chain of valid
        // blocks, we add the headers to our index, but don't accept the
        // block).
        throw JSONRPCError(RPC_MISC_ERROR, "Block not found on disk");
    }

    return block;
}

static UniValue getblock(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() < 1 || request.params.size() > 2)
        throw std::runtime_error(
            "getblock \"blockhash\" ( verbosity ) \n"
            "\nIf verbosity is 0, returns a string that is serialized, hex-encoded data for block 'hash'.\n"
            "If verbosity is 1, returns an Object with information about block <hash>.\n"
            "If verbosity is 2, returns an Object with information about block <hash> and information about each transaction. \n"
            "\nArguments:\n"
            "1. \"blockhash\"          (string, required) The block hash\n"
            "2. verbosity              (numeric, optional, default=1) 0 for hex encoded data, 1 for a json object, and 2 for json object with transaction data\n"
            "\nResult (for verbosity = 0):\n"
            "\"data\"             (string) A string that is serialized, hex-encoded data for block 'hash'.\n"
            "\nResult (for verbosity = 1):\n"
            "{\n"
            "  \"hash\" : \"hash\",     (string) the block hash (same as provided)\n"
            "  \"confirmations\" : n,   (numeric) The number of confirmations, or -1 if the block is not on the main chain\n"
            "  \"size\" : n,            (numeric) The block size\n"
            "  \"strippedsize\" : n,    (numeric) The block size excluding witness data\n"
            "  \"weight\" : n           (numeric) The block weight as defined in BIP 141\n"
            "  \"height\" : n,          (numeric) The block height or index\n"
            "  \"version\" : n,         (numeric) The block version\n"
            "  \"versionHex\" : \"00000000\", (string) The block version formatted in hexadecimal\n"
            "  \"merkleroot\" : \"xxxx\", (string) The merkle root\n"
            "  \"tx\" : [               (array of string) The transaction ids\n"
            "     \"transactionid\"     (string) The transaction id\n"
            "     ,...\n"
            "  ],\n"
            "  \"time\" : ttt,          (numeric) The block time in seconds since epoch (Jan 1 1970 GMT)\n"
            "  \"mediantime\" : ttt,    (numeric) The median block time in seconds since epoch (Jan 1 1970 GMT)\n"
            "  \"nonce\" : n,           (numeric) The nonce\n"
            "  \"bits\" : \"1d00ffff\", (string) The bits\n"
            "  \"difficulty\" : x.xxx,  (numeric) The difficulty\n"
            "  \"chainwork\" : \"xxxx\",  (string) Expected number of hashes required to produce the chain up to this block (in hex)\n"
            "  \"previousblockhash\" : \"hash\",  (string) The hash of the previous block\n"
            "  \"nextblockhash\" : \"hash\"       (string) The hash of the next block\n"
            "}\n"
            "\nResult (for verbosity = 2):\n"
            "{\n"
            "  ...,                     Same output as verbosity = 1.\n"
            "  \"tx\" : [               (array of Objects) The transactions in the format of the getrawtransaction RPC. Different from verbosity = 1 \"tx\" result.\n"
            "         ,...\n"
            "  ],\n"
            "  ,...                     Same output as verbosity = 1.\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("getblock", "\"00000000c937983704a73af28acdec37b049d214adbda81d7e2a3dd146f6ed09\"")
            + HelpExampleRpc("getblock", "\"00000000c937983704a73af28acdec37b049d214adbda81d7e2a3dd146f6ed09\"")
        );

    LOCK(cs_main);

    std::string strHash = request.params[0].get_str();
    uint256 hash(uint256S(strHash));

    int verbosity = 1;
    if (!request.params[1].isNull()) {
        if(request.params[1].isNum())
            verbosity = request.params[1].get_int();
        else
            verbosity = request.params[1].get_bool() ? 1 : 0;
    }

    if (mapBlockIndex.count(hash) == 0) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Block not found");
    }

    CBlockIndex* pblockindex = mapBlockIndex[hash];
    const CBlock block = GetBlockChecked(pblockindex);

    if (verbosity <= 0)
    {
        CDataStream ssBlock(SER_NETWORK, PROTOCOL_VERSION | RPCSerializationFlags());
        ssBlock << block;
        std::string strHex = HexStr(ssBlock.begin(), ssBlock.end());
        return strHex;
    }

    return blockToJSON(block, pblockindex, verbosity >= 2);
}

struct CCoinsStats
{
    int nHeight;
    uint256 hashBlock;
    uint64_t nTransactions;
    uint64_t nTransactionOutputs;
    uint64_t nSerializedSize;
    uint256 hashSerialized;
    CAmount nTotalAmount;

    CCoinsStats() : nHeight(0), nTransactions(0), nTransactionOutputs(0), nSerializedSize(0), nTotalAmount(0) {}
};

struct CAssetStats
{
    uint64_t nSpendableOutputs;
    uint64_t nFrozenOutputs;
    CAmount nSpendableAmount;
    CAmount nFrozenAmount;

    CAssetStats() : nSpendableOutputs(0), nFrozenOutputs(0), nSpendableAmount(0), nFrozenAmount(0) {}
};

//! Calculate statistics about the unspent transaction output set
static bool GetUTXOStats(CCoinsView *view, CCoinsStats &stats)
{
    std::unique_ptr<CCoinsViewCursor> pcursor(view->Cursor());

    CHashWriter ss(SER_GETHASH, PROTOCOL_VERSION);
    stats.hashBlock = pcursor->GetBestBlock();
    {
        LOCK(cs_main);
        stats.nHeight = mapBlockIndex.find(stats.hashBlock)->second->nHeight;
    }
    ss << stats.hashBlock;
    CAmount nTotalAmount = 0;
    while (pcursor->Valid()) {
        boost::this_thread::interruption_point();
        uint256 key;
        CCoins coins;
        if (pcursor->GetKey(key) && pcursor->GetValue(coins)) {
            stats.nTransactions++;
            ss << key;
            for (unsigned int i=0; i<coins.vout.size(); i++) {
                const CTxOut &out = coins.vout[i];
                if (!out.IsNull()) {
                    stats.nTransactionOutputs++;
                    ss << VARINT(i+1);
                    ss << out;
                    if (out.nValue.IsExplicit())
                        nTotalAmount += out.nValue.GetAmount();
                }
            }
            stats.nSerializedSize += 32 + pcursor->GetValueSize();
            ss << VARINT(0);
        } else {
            return error("%s: unable to read value", __func__);
        }
        pcursor->Next();
    }
    stats.hashSerialized = ss.GetHash();
    stats.nTotalAmount = nTotalAmount;
    return true;
}

static bool GetAssetStats(CCoinsView *view, std::map<CAsset,CAssetStats> &stats)
{
    std::unique_ptr<CCoinsViewCursor> pcursor(view->Cursor());

    CHashWriter ss(SER_GETHASH, PROTOCOL_VERSION);
    uint256 hashBlock = pcursor->GetBestBlock();
    {
        LOCK(cs_main);
    }
    ss << hashBlock;

    //set freeze-flag key
    uint160 frzInt;
    frzInt.SetHex("0x0000000000000000000000000000000000000000");
    CKeyID frzId;
    frzId = CKeyID(frzInt);

  //main loop over coins (transactions with > 0 unspent outputs
    while (pcursor->Valid()) {
        boost::this_thread::interruption_point();
        uint256 key;
        CCoins coins;
        if (pcursor->GetKey(key) && pcursor->GetValue(coins)) {
            ss << key;
            bool frozenTx = false;

            //loop over vouts within a single transaction
	    for (unsigned int i=0; i<coins.vout.size(); i++) {
	        const CTxOut &out = coins.vout[i];

                //check if the tx is flagged frozen (i.e. one output is a zero address)
		txnouttype whichType;
		std::vector<std::vector<unsigned char> > vSolutions;
		Solver(out.scriptPubKey, whichType, vSolutions);
		if(whichType == TX_PUBKEYHASH) {
		  CKeyID keyId;
		  keyId = CKeyID(uint160(vSolutions[0]));
		  if(keyId == frzId) frozenTx = true;
		}
	    }
            //loop over all vouts within a single transaction
            for (unsigned int i=0; i<coins.vout.size(); i++) {
	        const CTxOut &out = coins.vout[i];

                //null vouts are spent
		if (!out.IsNull()) {
		    ss << VARINT(i+1);
		    ss << out;
		    if(frozenTx) {
		        stats[out.nAsset.GetAsset()].nFrozenOutputs++;
			if (out.nValue.IsExplicit())
			    stats[out.nAsset.GetAsset()].nFrozenAmount += out.nValue.GetAmount();
		    } else {
		        stats[out.nAsset.GetAsset()].nSpendableOutputs++;
			if (out.nValue.IsExplicit())
			    stats[out.nAsset.GetAsset()].nSpendableAmount += out.nValue.GetAmount();
		    }
		}
	    }
	    ss << VARINT(0);
	} else {
	  return error("%s: unable to read value", __func__);
	}
	pcursor->Next();
    }
    return true;
}

UniValue pruneblockchain(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "pruneblockchain\n"
            "\nArguments:\n"
            "1. \"height\"       (numeric, required) The block height to prune up to. May be set to a discrete height, or a unix timestamp\n"
            "                  to prune blocks whose block time is at least 2 hours older than the provided timestamp.\n"
            "\nResult:\n"
            "n    (numeric) Height of the last block pruned.\n"
            "\nExamples:\n"
            + HelpExampleCli("pruneblockchain", "1000")
            + HelpExampleRpc("pruneblockchain", "1000"));

    if (!fPruneMode)
        throw JSONRPCError(RPC_METHOD_NOT_FOUND, "Cannot prune blocks because node is not in prune mode.");

    LOCK(cs_main);

    int heightParam = request.params[0].get_int();
    if (heightParam < 0)
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Negative block height.");

    // Height value more than a billion is too high to be a block height, and
    // too low to be a block time (corresponds to timestamp from Sep 2001).
    if (heightParam > 1000000000) {
        // Add a 2 hour buffer to include blocks which might have had old timestamps
        CBlockIndex* pindex = chainActive.FindEarliestAtLeast(heightParam - 7200);
        if (!pindex) {
            throw JSONRPCError(RPC_INTERNAL_ERROR, "Could not find block with at least the specified timestamp.");
        }
        heightParam = pindex->nHeight;
    }

    unsigned int height = (unsigned int) heightParam;
    unsigned int chainHeight = (unsigned int) chainActive.Height();
    if (chainHeight < Params().PruneAfterHeight())
        throw JSONRPCError(RPC_INTERNAL_ERROR, "Blockchain is too short for pruning.");
    else if (height > chainHeight)
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Blockchain is shorter than the attempted prune height.");
    else if (height > chainHeight - MIN_BLOCKS_TO_KEEP) {
        LogPrint("rpc", "Attempt to prune blocks close to the tip.  Retaining the minimum number of blocks.");
        height = chainHeight - MIN_BLOCKS_TO_KEEP;
    }

    PruneBlockFilesManual(height);
    return uint64_t(height);
}

UniValue gettxoutsetinfo(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 0)
        throw runtime_error(
            "gettxoutsetinfo\n"
            "\nReturns statistics about the unspent transaction output set.\n"
            "Note this call may take some time.\n"
            "\nResult:\n"
            "{\n"
            "  \"height\":n,     (numeric) The current block height (index)\n"
            "  \"bestblock\": \"hex\",   (string) the best block hash hex\n"
            "  \"transactions\": n,      (numeric) The number of transactions\n"
            "  \"txouts\": n,            (numeric) The number of output transactions\n"
            "  \"bytes_serialized\": n,  (numeric) The serialized size\n"
            "  \"hash_serialized\": \"hash\",   (string) The serialized hash\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("gettxoutsetinfo", "")
            + HelpExampleRpc("gettxoutsetinfo", "")
        );

    UniValue ret(UniValue::VOBJ);

    CCoinsStats stats;
    FlushStateToDisk();
    if (GetUTXOStats(pcoinsTip, stats)) {
        ret.push_back(Pair("height", (int64_t)stats.nHeight));
        ret.push_back(Pair("bestblock", stats.hashBlock.GetHex()));
        ret.push_back(Pair("transactions", (int64_t)stats.nTransactions));
        ret.push_back(Pair("txouts", (int64_t)stats.nTransactionOutputs));
        ret.push_back(Pair("bytes_serialized", (int64_t)stats.nSerializedSize));
        ret.push_back(Pair("hash_serialized", stats.hashSerialized.GetHex()));
    } else {
        throw JSONRPCError(RPC_INTERNAL_ERROR, "Unable to read UTXO set");
    }
    return ret;
}

UniValue getrequestbids(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "getrequestbids ( \"requesthash\" ) \n"
            "Returns an object containing the bids for the specified request.\n"
            "\nArguments:\n"
            "1. \"requesthash\"   (string, optional) The request transaction hash\n"
            "\nResult:\n"
            "[\n"
            " {\n"
            "   \"genesisBlock\": \"hash\",     (string) Client genesis for request\n"
            "   \"startBlockHeight\": n,   (numeric) Request start height\n"
            "   \"numTickets\": n,      (numeric) The number of guardnodes required\n"
            "   \"decayConst\": n,            (numeric) Decay constant for auction\n"
            "   \"feePercentage\": n,  (numeric) Fee percentage\n"
            "   \"startPrice\": n,  (numeric) Auction starting price\n"
            "   \"auctionPrice\": n,  (numeric) Auction current price\n"
            "   \"endBlockHeight\": n,   (numeric) Request end height\n"
            "   \"txid\": \"hash\",   (string) The request transaction hash\n"
            "   \"bids\": [         (array of objects) List of bid transactions\n"
            "       {\n"
            "           \"hash\",\n"
            "           \"feePubKey\",\n"
            "       },\n"
            "   ]\n"
            " },\n"
            "]\n"
            "\nExamples:\n"
            + HelpExampleCli("getrequestbids", "123450e138b1014173844ee0e4d557ff8a2463b14fcaeab18f6a63aa7c7e1d05")
            + HelpExampleRpc("getrequestbids", "123450e138b1014173844ee0e4d557ff8a2463b14fcaeab18f6a63aa7c7e1d05")
    );

    uint256 hash(uint256S(request.params[0].get_str()));
    UniValue ret(UniValue::VOBJ);
    UniValue retBids(UniValue::VARR);

    if (fRequestList) {
        for (auto it = requestList.begin(); it != requestList.end(); ++it) {
            if (it->first == hash) {
                ret = requestToJSON(it->second);
                ret.push_back(Pair("txid", it->first.ToString()));
                for (const auto &bid : it->second.sBids) {
                    retBids.push_back(bidToJSON(bid));
                }
            }
        }
    } else {
        FlushStateToDisk();
        std::unique_ptr<CCoinsViewCursor> pcursor(static_cast<CCoinsView*>(pcoinsTip)->Cursor());
        CRequest req;
        auto nHeight = (uint32_t)chainActive.Height();
        while (pcursor->Valid()) {
            boost::this_thread::interruption_point();
            uint256 key;
            CCoins coins;
            if (pcursor->GetKey(key) && pcursor->GetValue(coins)) {
                 if (key == hash) { // request unspent
                    if (GetRequest(coins.vout[0], key, coins.nHeight, req)) {
                        if (IsValidRequest(req, nHeight)) {
                            ret = requestToJSON(req);
                            ret.push_back(Pair("txid", key.ToString()));
                        }
                    }
                }
            } else {
                throw JSONRPCError(RPC_INTERNAL_ERROR, "Unable to read UTXO set");
            }
            pcursor->Next();
        }
        std::unique_ptr<CCoinsViewCursor> pcursor2(static_cast<CCoinsView*>(pcoinsTip)->Cursor());
        while (pcursor2->Valid()) {
            boost::this_thread::interruption_point();
            uint256 key;
            CCoins coins;
            if (pcursor2->GetKey(key) && pcursor2->GetValue(coins)) {
                if (coins.vout.size() > 1) { // bid transactions
                    CBid bid;
                    if (GetRequestBid(coins.vout, key, coins.nHeight, bid)) {
                        if (IsValidRequestBid(req, bid)) {
                            req.AddBid(bid);
                        }
                    }
                }
            } else {
                throw JSONRPCError(RPC_INTERNAL_ERROR, "Unable to read UTXO set");
            }
            pcursor2->Next();
        }
        for (const auto &bid : req.sBids) {
            retBids.push_back(bidToJSON(bid));
        }
    }

    if (ret.size() > 0) {
        ret.push_back(Pair("bids", retBids));
        return ret;
    }
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "No such request transaction");
}

UniValue getrequests(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() > 1)
        throw runtime_error(
            "getrequests ( \"genesishash\" ) \n"
            "Returns an object containing all active requests in the system.\n"
            "\nArguments:\n"
            "1. \"genesishash\"   (string, optional) The client genesis hash for the request\n"
            "\nResult:\n"
            "[\n"
            " {\n"
            "   \"genesisBlock\": \"hash\",     (string) Client genesis for request\n"
            "   \"startBlockHeight\": n,   (numeric) Request start height\n"
            "   \"numTickets\": n,      (numeric) The number of guardnodes required\n"
            "   \"decayConst\": n,            (numeric) Decay constant for auction\n"
            "   \"feePercentage\": n,  (numeric) Fee percentage\n"
            "   \"startPrice\": n,  (numeric) Auction starting price\n"
            "   \"auctionPrice\": n,  (numeric) Auction current price\n"
            "   \"endBlockHeight\": n,   (numeric) Request end height\n"
            "   \"confirmedBlockHeight\": n,   (numeric) Block height Request was confirmed\n"
            "   \"txid\": \"hash\",   (string) The request transaction hash\n"
            " },\n"
            "]\n"
            "\nExamples:\n"
            + HelpExampleCli("getrequests", "")
            + HelpExampleCli("getrequests", "123450e138b1014173844ee0e4d557ff8a2463b14fcaeab18f6a63aa7c7e1d05")
            + HelpExampleRpc("getrequests", "")
            + HelpExampleRpc("getrequests", "123450e138b1014173844ee0e4d557ff8a2463b14fcaeab18f6a63aa7c7e1d05")
    );

    bool fGenesisCheck = false;
    uint256 hash;
    if (request.params.size() == 1 && !request.params[0].isNull()) {
        fGenesisCheck = true;
        hash.SetHex(request.params[0].get_str());
    }

    UniValue ret(UniValue::VARR);

    if (fRequestList) {
        for (auto it = requestList.begin(); it != requestList.end(); ++it) {
            if (!fGenesisCheck || (it->second.hashGenesis == hash)) {
                auto item = requestToJSON(it->second);
                item.push_back(Pair("txid", it->first.ToString()));
                ret.push_back(item);
            }
        }
    } else {
        FlushStateToDisk();
        std::unique_ptr<CCoinsViewCursor> pcursor(static_cast<CCoinsView*>(pcoinsTip)->Cursor());
        while (pcursor->Valid()) {
            boost::this_thread::interruption_point();
            uint256 key;
            CCoins coins;
            if (pcursor->GetKey(key) && pcursor->GetValue(coins)) {
                if (coins.vout.size() == 1 && !coins.IsCoinBase()
                && coins.vout[0].nAsset.IsExplicit() && coins.vout[0].nAsset.GetAsset() == permissionAsset) {
                    CRequest req;
                    if (GetRequest(coins.vout[0], key, coins.nHeight, req)) {
                        if (IsValidRequest(req, (uint32_t)chainActive.Height())) {
                            if (!fGenesisCheck || (req.hashGenesis == hash)) {
                                auto item = requestToJSON(req);
                                item.push_back(Pair("txid", key.ToString()));
                                ret.push_back(item);
                            }
                        }
                    }
                }
            } else {
                throw JSONRPCError(RPC_INTERNAL_ERROR, "Unable to read UTXO set");
            }
            pcursor->Next();
        }
    }
    return ret;
}

UniValue getutxoassetinfo(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 0)
        throw runtime_error(
            "getassetstats\n"
            "\nReturns a summary of the total amounts of unspent assets in the UTXO set\n"
            "Note this call may take some time.\n"
            "\nResult:\n"
            "[                     (json array of objects)\n"
            "  {\n"
            "    \"asset\":\"<asset>\",   (string) Asset type ID \n"
	    "    \"amountspendable\":\"X.XX\",     (numeric) The total amount of spendable asset.\n"
            "    \"spendabletxouts\":\"n\",         (numeric) The number of spendable outputs of the asset.\n"
	    "    \"amountfrozen\":\"X.XX\",       (numeric) The total amount of frozen asset.\n"
            "    \"frozentxouts\":\"n\",          (numeric) The number of frozen outputs of the asset.\n"
            "  }\n"
            "  ,...\n"
            "]\n"
            "\nExamples:\n"
            + HelpExampleCli("getassetstats", "")
            + HelpExampleRpc("getassetstats", "")
			);

    UniValue ret(UniValue::VARR);
    FlushStateToDisk();

    std::map<CAsset,CAssetStats> stats;
    if (GetAssetStats(pcoinsTip, stats)) {
        for(auto const& asset : stats){
    	    UniValue item(UniValue::VOBJ);
    	    item.push_back(Pair("asset",asset.first.GetHex()));
    	    item.push_back(Pair("spendabletxouts",asset.second.nSpendableOutputs));
    	    item.push_back(Pair("amountspendable",ValueFromAmount(asset.second.nSpendableAmount)));
    	    item.push_back(Pair("frozentxouts",asset.second.nFrozenOutputs));
    	    item.push_back(Pair("amountfrozen",ValueFromAmount(asset.second.nFrozenAmount)));
            //add entropy and token mappings
            if(fRecordInflation) {
                bool fd = false;
                for(uint32_t itr = 0; itr < assetEntropyMap.size(); ++itr) {
                    if(assetEntropyMap[itr].asset == asset.first) {
                        item.push_back(Pair("entropy",assetEntropyMap[itr].entropy.GetHex()));
                        item.push_back(Pair("token",assetEntropyMap[itr].token.GetHex()));
                        fd = true;
                        break;
                    }
                }
                if(!fd) {
                    item.push_back(Pair("entropy","null"));
                    item.push_back(Pair("token","null"));
                }
            }
    	    ret.push_back(item);
    	}
    } else {
        throw JSONRPCError(RPC_INTERNAL_ERROR, "Unable to read UTXO set");
    }
    return ret;
}

UniValue getfreezehistory(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 0)
        throw runtime_error(
            "getfreezehistory height\n"
            "Returns an array conatining the history of frozen (redemption) transactions\n"
            "It returns all outputs that have been unfrozen in the last height blocks\n"
            "If height is zero it returns all frozen outputs\n"
            "\nResult:\n"
            "[\n"
            "   {\n"
            "       \"txid\": \"xxxx\",        (string) transaction ID of the redemption transaction\n"
            "       \"blocks\": xxxxxx,         (numeric) the current number of blocks processed in the server\n"
            "   }\n"
            "]\n"
            "\nExamples:\n"
            + HelpExampleCli("getblockchaininfo", "0")
            + HelpExampleRpc("getblockchaininfo", "0")
        );

//    uint32_t nHeight = request.params[0].get_int();

    uint32_t nHeight = 0;

    UniValue ar(UniValue::VARR);
    uint32_t bh = chainActive.Height();
    for (uint32_t itr = 0; itr < freezeHistList.size(); ++itr) {
        if(freezeHistList[itr].spendheight > bh - nHeight || nHeight == 0) {
            UniValue obj(UniValue::VOBJ);
            obj.push_back(Pair("txid",freezeHistList[itr].txid.GetHex()));
            obj.push_back(Pair("vout",(int)freezeHistList[itr].vout));
            obj.push_back(Pair("asset",freezeHistList[itr].asset.GetHex()));
            obj.push_back(Pair("value",ValueFromAmount(freezeHistList[itr].value)));
            obj.push_back(Pair("start",(int)freezeHistList[itr].freezeheight));
            obj.push_back(Pair("end",(int)freezeHistList[itr].spendheight));
            ar.push_back(obj);
        }
    }
    return ar;
}

UniValue gettxout(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() < 2 || request.params.size() > 3)
        throw runtime_error(
            "gettxout \"txid\" n ( include_mempool )\n"
            "\nReturns details about an unspent transaction output.\n"
            "\nArguments:\n"
            "1. \"txid\"       (string, required) The transaction id\n"
            "2. n              (numeric, required) vout number\n"
            "3. include_mempool  (boolean, optional) Whether to include the mempool\n"
            "\nResult:\n"
            "{\n"
            "  \"bestblock\" : \"hash\",    (string) the block hash\n"
            "  \"confirmations\" : n,       (numeric) The number of confirmations\n"
            "  \"value\" : x.xxx,           (numeric) The transaction value in " + CURRENCY_UNIT + "\n"
            "  \"amountcommitment\": \"hex\", (string) the output's value commitment, if blinded\n"
            "  \"asset\": \"hex\",          (string) the output's asset type, if unblinded\n"
            "  \"assetcommitment\": \"hex\", (string) the output's asset commitment, if blinded\n"
            "  \"scriptPubKey\" : {         (json object)\n"
            "     \"asm\" : \"code\",       (string) \n"
            "     \"hex\" : \"hex\",        (string) \n"
            "     \"reqSigs\" : n,          (numeric) Number of required signatures\n"
            "     \"type\" : \"pubkeyhash\", (string) The type, eg pubkeyhash\n"
            "     \"addresses\" : [          (array of string) array of bitcoin addresses\n"
            "        \"address\"     (string) bitcoin address\n"
            "        ,...\n"
            "     ]\n"
            "  },\n"
            "  \"version\" : n,            (numeric) The version\n"
            "  \"coinbase\" : true|false   (boolean) Coinbase or not\n"
            "}\n"

            "\nExamples:\n"
            "\nGet unspent transactions\n"
            + HelpExampleCli("listunspent", "") +
            "\nView the details\n"
            + HelpExampleCli("gettxout", "\"txid\" 1") +
            "\nAs a json rpc call\n"
            + HelpExampleRpc("gettxout", "\"txid\", 1")
        );

    LOCK(cs_main);

    UniValue ret(UniValue::VOBJ);

    std::string strHash = request.params[0].get_str();
    uint256 hash(uint256S(strHash));
    int n = request.params[1].get_int();
    bool fMempool = true;
    if (request.params.size() > 2)
        fMempool = request.params[2].get_bool();

    CCoins coins;
    if (fMempool) {
        LOCK(mempool.cs);
        CCoinsViewMemPool view(pcoinsTip, mempool);
        if (!view.GetCoins(hash, coins))
            return NullUniValue;
        mempool.pruneSpent(hash, coins); // TODO: this should be done by the CCoinsViewMemPool
    } else {
        if (!pcoinsTip->GetCoins(hash, coins))
            return NullUniValue;
    }
    if (n<0 || (unsigned int)n>=coins.vout.size() || coins.vout[n].IsNull())
        return NullUniValue;

    BlockMap::iterator it = mapBlockIndex.find(pcoinsTip->GetBestBlock());
    CBlockIndex *pindex = it->second;
    ret.push_back(Pair("bestblock", pindex->GetBlockHash().GetHex()));
    if ((unsigned int)coins.nHeight == MEMPOOL_HEIGHT)
        ret.push_back(Pair("confirmations", 0));
    else
        ret.push_back(Pair("confirmations", pindex->nHeight - coins.nHeight + 1));
    if (coins.vout[n].nValue.IsExplicit()) {
        ret.push_back(Pair("value", ValueFromAmount(coins.vout[n].nValue.GetAmount())));
    } else {
        ret.push_back(Pair("amountcommitment", HexStr(coins.vout[n].nValue.vchCommitment)));
    }
    if (coins.vout[n].nAsset.IsExplicit()) {
        ret.push_back(Pair("asset", coins.vout[n].nAsset.GetAsset().GetHex()));
    } else {
        ret.push_back(Pair("assetcommitment", HexStr(coins.vout[n].nAsset.vchCommitment)));
    }

    UniValue o(UniValue::VOBJ);
    ScriptPubKeyToJSON(coins.vout[n].scriptPubKey, o, true);
    ret.push_back(Pair("scriptPubKey", o));
    ret.push_back(Pair("version", coins.nVersion));
    ret.push_back(Pair("coinbase", coins.fCoinBase));

    return ret;
}

UniValue verifychain(const JSONRPCRequest& request)
{
    int nCheckLevel = GetArg("-checklevel", DEFAULT_CHECKLEVEL);
    int nCheckDepth = GetArg("-checkblocks", DEFAULT_CHECKBLOCKS);
    if (request.fHelp || request.params.size() > 2)
        throw runtime_error(
            "verifychain ( checklevel nblocks )\n"
            "\nVerifies blockchain database.\n"
            "\nArguments:\n"
            "1. checklevel   (numeric, optional, 0-4, default=" + strprintf("%d", nCheckLevel) + ") How thorough the block verification is.\n"
            "2. nblocks      (numeric, optional, default=" + strprintf("%d", nCheckDepth) + ", 0=all) The number of blocks to check.\n"
            "\nResult:\n"
            "true|false       (boolean) Verified or not\n"
            "\nExamples:\n"
            + HelpExampleCli("verifychain", "")
            + HelpExampleRpc("verifychain", "")
        );

    LOCK(cs_main);

    if (request.params.size() > 0)
        nCheckLevel = request.params[0].get_int();
    if (request.params.size() > 1)
        nCheckDepth = request.params[1].get_int();

    return CVerifyDB().VerifyDB(Params(), pcoinsTip, nCheckLevel, nCheckDepth);
}

static UniValue BIP9SoftForkDesc(const Consensus::Params& consensusParams, Consensus::DeploymentPos id)
{
    UniValue rv(UniValue::VOBJ);
    const ThresholdState thresholdState = VersionBitsTipState(consensusParams, id);
    switch (thresholdState) {
    case THRESHOLD_DEFINED: rv.push_back(Pair("status", "defined")); break;
    case THRESHOLD_STARTED: rv.push_back(Pair("status", "started")); break;
    case THRESHOLD_LOCKED_IN: rv.push_back(Pair("status", "locked_in")); break;
    case THRESHOLD_ACTIVE: rv.push_back(Pair("status", "active")); break;
    case THRESHOLD_FAILED: rv.push_back(Pair("status", "failed")); break;
    }
    if (THRESHOLD_STARTED == thresholdState)
    {
        rv.push_back(Pair("bit", consensusParams.vDeployments[id].bit));
    }
    rv.push_back(Pair("startTime", consensusParams.vDeployments[id].nStartTime));
    rv.push_back(Pair("timeout", consensusParams.vDeployments[id].nTimeout));
    rv.push_back(Pair("since", VersionBitsTipStateSinceHeight(consensusParams, id)));
    return rv;
}

void BIP9SoftForkDescPushBack(UniValue& bip9_softforks, const std::string &name, const Consensus::Params& consensusParams, Consensus::DeploymentPos id)
{
    // Deployments with timeout value of 0 are hidden.
    // A timeout value of 0 guarantees a softfork will never be activated.
    // This is used when softfork codes are merged without specifying the deployment schedule.
    if (consensusParams.vDeployments[id].nTimeout > 0)
        bip9_softforks.push_back(Pair(name, BIP9SoftForkDesc(consensusParams, id)));
}

UniValue getblockchaininfo(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 0)
        throw runtime_error(
            "getblockchaininfo\n"
            "Returns an object containing various state info regarding blockchain processing.\n"
            "\nResult:\n"
            "{\n"
            "  \"chain\": \"xxxx\",        (string) current network name as defined in BIP70 (main, test, regtest)\n"
            "  \"blocks\": xxxxxx,         (numeric) the current number of blocks processed in the server\n"
            "  \"headers\": xxxxxx,        (numeric) the current number of headers we have validated\n"
            "  \"bestblockhash\": \"...\", (string) the hash of the currently best block\n"
            "  \"difficulty\": xxxxxx,     (numeric) the current difficulty\n"
            "  \"mediantime\": xxxxxx,     (numeric) median time for the current best block\n"
            "  \"verificationprogress\": xxxx, (numeric) estimate of verification progress [0..1]\n"
            "  \"chainwork\": \"xxxx\"     (string) total amount of work in active chain, in hexadecimal\n"
            "  \"pruned\": xx,             (boolean) if the blocks are subject to pruning\n"
            "  \"pruneheight\": xxxxxx,    (numeric) lowest-height complete block stored\n"
            "  \"softforks\": [            (array) status of softforks in progress\n"
            "     {\n"
            "        \"id\": \"xxxx\",        (string) name of softfork\n"
            "        \"version\": xx,         (numeric) block version\n"
            "        \"reject\": {            (object) progress toward rejecting pre-softfork blocks\n"
            "           \"status\": xx,       (boolean) true if threshold reached\n"
            "        },\n"
            "     }, ...\n"
            "  ],\n"
            "  \"bip9_softforks\": {          (object) status of BIP9 softforks in progress\n"
            "     \"xxxx\" : {                (string) name of the softfork\n"
            "        \"status\": \"xxxx\",    (string) one of \"defined\", \"started\", \"locked_in\", \"active\", \"failed\"\n"
            "        \"bit\": xx,             (numeric) the bit (0-28) in the block version field used to signal this softfork (only for \"started\" status)\n"
            "        \"startTime\": xx,       (numeric) the minimum median time past of a block at which the bit gains its meaning\n"
            "        \"timeout\": xx,         (numeric) the median time past of a block at which the deployment is considered failed if not yet locked in\n"
            "        \"since\": xx            (numeric) height of the first block to which the status applies\n"
            "     }\n"
            "  }\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("getblockchaininfo", "")
            + HelpExampleRpc("getblockchaininfo", "")
        );

    LOCK(cs_main);

    UniValue obj(UniValue::VOBJ);
    obj.push_back(Pair("chain",                 Params().NetworkIDString()));
    obj.push_back(Pair("blocks",                (int)chainActive.Height()));
    obj.push_back(Pair("headers",               pindexBestHeader ? pindexBestHeader->nHeight : -1));
    obj.push_back(Pair("bestblockhash",         chainActive.Tip()->GetBlockHash().GetHex()));
    obj.push_back(Pair("difficulty",            (double)GetDifficulty()));
    obj.push_back(Pair("mediantime",            (int64_t)chainActive.Tip()->GetMedianTimePast()));
    obj.push_back(Pair("verificationprogress",  GuessVerificationProgress(Params().TxData(), chainActive.Tip())));
    obj.push_back(Pair("chainwork",             chainActive.Tip()->nChainWork.GetHex()));
    obj.push_back(Pair("pruned",                fPruneMode));

    const Consensus::Params& consensusParams = Params().GetConsensus();
    UniValue bip9_softforks(UniValue::VOBJ);
    BIP9SoftForkDescPushBack(bip9_softforks, "csv", consensusParams, Consensus::DEPLOYMENT_CSV);
    BIP9SoftForkDescPushBack(bip9_softforks, "segwit", consensusParams, Consensus::DEPLOYMENT_SEGWIT);
    obj.push_back(Pair("bip9_softforks", bip9_softforks));

    if (fPruneMode)
    {
        CBlockIndex *block = chainActive.Tip();
        while (block && block->pprev && (block->pprev->nStatus & BLOCK_HAVE_DATA))
            block = block->pprev;

        obj.push_back(Pair("pruneheight",        block->nHeight));
    }
    return obj;
}

UniValue getsidechaininfo(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 0)
        throw runtime_error(
            "getsidechaininfo\n"
            "Returns an object containing various state info regarding sidechain functionality.\n"
            "\nResult:\n"
            "{\n"
            "  \"fedpegscript\": \"xxxx\",        (string) The fedpegscript in hex\n"
            "  \"pegged_asset\" : \"xxxx\",        (string) Pegged asset type in hex\n"
            "  \"min_peg_diff\" : \"xxxx\",        (string) The minimum difficulty parent chain header target. Peg-in headers that have less work will be rejected as an anti-Dos measure.\n"
            "  \"parent_blockhash\" : \"xxxx\",    (string) The parent genesis blockhash as source of pegged-in funds.\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("getsidechaininfo", "")
            + HelpExampleRpc("getsidechaininfo", "")
        );

    LOCK(cs_main);

    const Consensus::Params& consensus = Params().GetConsensus();
    const uint256& parent_blockhash = Params().ParentGenesisBlockHash();

    UniValue obj(UniValue::VOBJ);
    obj.push_back(Pair("fedpegscript", HexStr(consensus.fedpegScript.begin(), consensus.fedpegScript.end())));
    obj.push_back(Pair("pegged_asset", consensus.pegged_asset.GetHex()));
    obj.push_back(Pair("min_peg_diff", consensus.parentChainPowLimit.GetHex()));
    obj.push_back(Pair("parent_blockhash", parent_blockhash.GetHex()));
    return obj;
}


/** Comparison function for sorting the getchaintips heads.  */
struct CompareBlocksByHeight
{
    bool operator()(const CBlockIndex* a, const CBlockIndex* b) const
    {
        /* Make sure that unequal blocks with the same height do not compare
           equal. Use the pointers themselves to make a distinction. */

        if (a->nHeight != b->nHeight)
          return (a->nHeight > b->nHeight);

        return a < b;
    }
};

UniValue getchaintips(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 0)
        throw runtime_error(
            "getchaintips\n"
            "Return information about all known tips in the block tree,"
            " including the main chain as well as orphaned branches.\n"
            "\nResult:\n"
            "[\n"
            "  {\n"
            "    \"height\": xxxx,         (numeric) height of the chain tip\n"
            "    \"hash\": \"xxxx\",         (string) block hash of the tip\n"
            "    \"branchlen\": 0          (numeric) zero for main chain\n"
            "    \"status\": \"active\"      (string) \"active\" for the main chain\n"
            "  },\n"
            "  {\n"
            "    \"height\": xxxx,\n"
            "    \"hash\": \"xxxx\",\n"
            "    \"branchlen\": 1          (numeric) length of branch connecting the tip to the main chain\n"
            "    \"status\": \"xxxx\"        (string) status of the chain (active, valid-fork, valid-headers, headers-only, invalid)\n"
            "  }\n"
            "]\n"
            "Possible values for status:\n"
            "1.  \"invalid\"               This branch contains at least one invalid block\n"
            "2.  \"headers-only\"          Not all blocks for this branch are available, but the headers are valid\n"
            "3.  \"valid-headers\"         All blocks are available for this branch, but they were never fully validated\n"
            "4.  \"valid-fork\"            This branch is not part of the active chain, but is fully validated\n"
            "5.  \"active\"                This is the tip of the active main chain, which is certainly valid\n"
            "\nExamples:\n"
            + HelpExampleCli("getchaintips", "")
            + HelpExampleRpc("getchaintips", "")
        );

    LOCK(cs_main);

    /*
     * Idea:  the set of chain tips is chainActive.tip, plus orphan blocks which do not have another orphan building off of them.
     * Algorithm:
     *  - Make one pass through mapBlockIndex, picking out the orphan blocks, and also storing a set of the orphan block's pprev pointers.
     *  - Iterate through the orphan blocks. If the block isn't pointed to by another orphan, it is a chain tip.
     *  - add chainActive.Tip()
     */
    std::set<const CBlockIndex*, CompareBlocksByHeight> setTips;
    std::set<const CBlockIndex*> setOrphans;
    std::set<const CBlockIndex*> setPrevs;

    BOOST_FOREACH(const PAIRTYPE(const uint256, CBlockIndex*)& item, mapBlockIndex)
    {
        if (!chainActive.Contains(item.second)) {
            setOrphans.insert(item.second);
            setPrevs.insert(item.second->pprev);
        }
    }

    for (std::set<const CBlockIndex*>::iterator it = setOrphans.begin(); it != setOrphans.end(); ++it)
    {
        if (setPrevs.erase(*it) == 0) {
            setTips.insert(*it);
        }
    }

    // Always report the currently active tip.
    setTips.insert(chainActive.Tip());

    /* Construct the output array.  */
    UniValue res(UniValue::VARR);
    BOOST_FOREACH(const CBlockIndex* block, setTips)
    {
        UniValue obj(UniValue::VOBJ);
        obj.push_back(Pair("height", block->nHeight));
        obj.push_back(Pair("hash", block->phashBlock->GetHex()));

        const int branchLen = block->nHeight - chainActive.FindFork(block)->nHeight;
        obj.push_back(Pair("branchlen", branchLen));

        string status;
        if (chainActive.Contains(block)) {
            // This block is part of the currently active chain.
            status = "active";
        } else if (block->nStatus & BLOCK_FAILED_MASK) {
            // This block or one of its ancestors is invalid.
            status = "invalid";
        } else if (block->nChainTx == 0) {
            // This block cannot be connected because full block data for it or one of its parents is missing.
            status = "headers-only";
        } else if (block->IsValid(BLOCK_VALID_SCRIPTS)) {
            // This block is fully validated, but no longer part of the active chain. It was probably the active block once, but was reorganized.
            status = "valid-fork";
        } else if (block->IsValid(BLOCK_VALID_TREE)) {
            // The headers for this block are valid, but it has not been validated. It was probably never part of the most-work chain.
            status = "valid-headers";
        } else {
            // No clue.
            status = "unknown";
        }
        obj.push_back(Pair("status", status));

        res.push_back(obj);
    }

    return res;
}

UniValue mempoolInfoToJSON()
{
    UniValue ret(UniValue::VOBJ);
    ret.push_back(Pair("size", (int64_t) mempool.size()));
    ret.push_back(Pair("bytes", (int64_t) mempool.GetTotalTxSize()));
    ret.push_back(Pair("usage", (int64_t) mempool.DynamicMemoryUsage()));
    size_t maxmempool = GetArg("-maxmempool", DEFAULT_MAX_MEMPOOL_SIZE) * 1000000;
    ret.push_back(Pair("maxmempool", (int64_t) maxmempool));
    ret.push_back(Pair("mempoolminfee", ValueFromAmount(mempool.GetMinFee(maxmempool).GetFeePerK())));

    return ret;
}

UniValue getmempoolinfo(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 0)
        throw runtime_error(
            "getmempoolinfo\n"
            "\nReturns details on the active state of the TX memory pool.\n"
            "\nResult:\n"
            "{\n"
            "  \"size\": xxxxx,               (numeric) Current tx count\n"
            "  \"bytes\": xxxxx,              (numeric) Sum of all virtual transaction sizes as defined in BIP 141. Differs from actual serialized size because witness data is discounted\n"
            "  \"usage\": xxxxx,              (numeric) Total memory usage for the mempool\n"
            "  \"maxmempool\": xxxxx,         (numeric) Maximum memory usage for the mempool\n"
            "  \"mempoolminfee\": xxxxx       (numeric) Minimum fee for tx to be accepted\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("getmempoolinfo", "")
            + HelpExampleRpc("getmempoolinfo", "")
        );

    return mempoolInfoToJSON();
}

UniValue preciousblock(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "preciousblock \"blockhash\"\n"
            "\nTreats a block as if it were received before others with the same work.\n"
            "\nA later preciousblock call can override the effect of an earlier one.\n"
            "\nThe effects of preciousblock are not retained across restarts.\n"
            "\nArguments:\n"
            "1. \"blockhash\"   (string, required) the hash of the block to mark as precious\n"
            "\nResult:\n"
            "\nExamples:\n"
            + HelpExampleCli("preciousblock", "\"blockhash\"")
            + HelpExampleRpc("preciousblock", "\"blockhash\"")
        );

    std::string strHash = request.params[0].get_str();
    uint256 hash(uint256S(strHash));
    CBlockIndex* pblockindex;

    {
        LOCK(cs_main);
        if (mapBlockIndex.count(hash) == 0)
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Block not found");

        pblockindex = mapBlockIndex[hash];
    }

    CValidationState state;
    PreciousBlock(state, Params(), pblockindex);

    if (!state.IsValid()) {
        throw JSONRPCError(RPC_DATABASE_ERROR, state.GetRejectReason());
    }

    return NullUniValue;
}

UniValue addtowhitelist(const JSONRPCRequest& request)
{
    unsigned int nparams=request.params.size();
  if (request.fHelp || nparams < 2 || nparams > 3)
    throw runtime_error(
            "addtowhitelist \"tweakedaddress\" \"basepubkey\" \"kycpubkey\"\n"
            "\nAttempts to add an address (tweakedaddress) to the node mempool whitelist.\n"
            "The address is checked that it has been tweaked with the contract hash.\n"
            "\nArguments:\n"
            "1. \"tweakedaddress\"  (string, required) Base58 tweaked address\n"
            "2. \"basepubkey\"     (string, required) Hex encoded of the compressed base (un-tweaked) public key\n"
            "3. \"kycaddress\"     (string, optional) Base58 KYC address\n"
            "\nExamples:\n"
            + HelpExampleCli("addtowhitelist", "\"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB \" \"02e2367f74add814a482ab341cd514516f6c56dd951ceb1d51d9ddeb335968355e\",\"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
            + HelpExampleRpc("addtowhitelist", "\"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB \" \"02e2367f74add814a482ab341cd514516f6c56dd951ceb1d51d9ddeb335968355e\", \"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
                        );
try{
    if(nparams == 2){
        addressWhitelist.add_derived(request.params[0].get_str(), request.params[1].get_str());
    } else {
        addressWhitelist.add_derived(request.params[0].get_str(), request.params[1].get_str(),
        request.params[2].get_str());
    }
} catch(std::invalid_argument e){
    throw JSONRPCError(RPC_INVALID_PARAMETER, e.what());
}

  return NullUniValue;
}

UniValue readwhitelist(const JSONRPCRequest& request)
{
  if (request.fHelp || request.params.size() < 1 || request.params.size() > 2)
    throw runtime_error(
            "readwhitelist \"filename\"\n"
            "Read in derived keys and tweaked addresses from key dump file (see dumpderivedkeys) into the address whitelist.\n"
            "\nArguments:\n"
            "1. \"filename\"    (string, required) The key file\n"
            "2. \"kycaddress\"  (string, optional) The KYC address of the key file owner\n"
            "\nExamples:\n"
            "\nDump the keys\n"
            + HelpExampleCli("readwhitelist", "\"test\", \"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
            + HelpExampleRpc("readwhitelist", "\"test\", \"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
			);

    std::string sKYCAddress="";
    if(request.params.size()==2){
        sKYCAddress=request.params[1].get_str();
        CBitcoinAddress addr;
        if(addr.SetString(sKYCAddress)){
            CKeyID id;
            addr.GetKeyID(id);
            addressWhitelist.whitelist_kyc(id);
        }
    }

    std::ifstream file;
    file.open(request.params[0].get_str().c_str(), std::ios::in | std::ios::ate);
    if (!file.is_open())
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Cannot open key dump file");
    file.seekg(0, file.beg);

    // parse file to extract bitcoin address - untweaked pubkey pairs and validate derivation
    while (file.good())
    {
        std::string line;
        std::getline(file, line);
        if (line.empty() || line[0] == '#')
            continue;

        std::vector<std::string> vstr;
        boost::split(vstr, line, boost::is_any_of(" "));
        if (vstr.size() < 2)
            continue;

	   addressWhitelist.add_derived(vstr[0], vstr[1], sKYCAddress);
    }

    file.close();

    return NullUniValue;
}

UniValue querywhitelist(const JSONRPCRequest& request)
{

  if (request.fHelp || request.params.size() != 1)
    throw runtime_error(
            "querywhitelist \"address\" \n"
            "\nChecks if an address is present in the node mempool whitelist.\n"
            "\nArguments:\n"
            "1. \"address\"  (string, required) Base58 encoded address\n"
            "\nExamples:\n"
            + HelpExampleCli("querywhitelist", "\"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
            + HelpExampleRpc("querywhitelist", "\"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
			);

  CBitcoinAddress address;
  if (!address.SetString(request.params[0].get_str()))
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid  address");

  CKeyID keyId;
  if (!address.GetKeyID(keyId))
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid key id");

  return addressWhitelist.is_whitelisted(keyId);
}

UniValue removefromwhitelist(const JSONRPCRequest& request)
{

  if (request.fHelp || request.params.size() != 1)
    throw runtime_error(
            "removefromwhitelist \"address\" \n"
            "\nRemoves an address from the node mempool whitelist.\n"
            "\nArguments:\n"
            "1. \"address\"  (string, required) Base58 encoded address\n"
            "\nExamples:\n"
            + HelpExampleCli("removefromwhitelist", "\"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
            + HelpExampleRpc("removefromwhitelist", "\"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
                        );

  CBitcoinAddress address;
  if (!address.SetString(request.params[0].get_str()))
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid  address");

  CKeyID keyId;
  if (!address.GetKeyID(keyId))
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid key id");

  addressWhitelist.remove(&keyId);
  return NullUniValue;
}

UniValue dumpwhitelist(const JSONRPCRequest& request)
{

  if (request.fHelp || request.params.size() != 1)
    throw runtime_error(
            "dumpwhitelist \"filename\"\n"
            "\nDumps all addresses in the tx mempool to a text file.\n"
	        "\nArguments:\n"
            "1. \"filename\"    (string, required) The filename\n"
            "\nExamples:\n"
            + HelpExampleCli("dumpwhitelist", "\"test\"")
            + HelpExampleRpc("dumpwhitelist", "\"test\"")
			);

  std::ofstream file;
  file.open(request.params[0].get_str().c_str());
  if (!file.is_open())
    throw JSONRPCError(RPC_INVALID_PARAMETER, "Cannot open key dump file");

  // produce output
  file << strprintf("# Whitelisted address dump - format: [address] [kyckey]");
  file << "\n";

  for(auto it=addressWhitelist.begin(); it!=addressWhitelist.end(); ++it){
    //Check KYC status (owner may be in blacklist)
    if(!addressWhitelist.is_whitelisted(*it)) continue;
     std::string strAddr = CBitcoinAddress(*it).ToString();
     CKeyID kycKey;
     addressWhitelist.LookupKYCKey(CKeyID(*it), kycKey);
     std::string strKYCKey = CBitcoinAddress(kycKey).ToString();
     file << strprintf("%s %s\n",
              strAddr, strKYCKey);
  }

  file << "\n";
  file << "# End of dump\n";
  file.close();

  return NullUniValue;
}


UniValue clearwhitelist(const JSONRPCRequest& request)
{

  if (request.fHelp || request.params.size() != 0)
    throw runtime_error(
            "clearwhitelist \n"
            "\nClears the node mempool transaction whitelist (no arguments).\n"
            + HelpExampleCli("clearwhitelist", "\"true\"")
            + HelpExampleRpc("clearwhitelist", "\"true\"")
			);

  addressWhitelist.clear();

  return NullUniValue;
}

UniValue addtofreezelist(const JSONRPCRequest& request)
{
  if (request.fHelp || request.params.size() != 1)
    throw runtime_error(
			    "addtofreezelist \"address\"\n"
            "\nAdd an address to the node mempool freezelist.\n"
            "\nArguments:\n"
            "1. \"address\"  (string, required) Base58 address\n"
            "\nExamples:\n"
			    + HelpExampleCli("addtofreezelist", "\"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
			    + HelpExampleRpc("addtofreezelist", "\"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
			);

  CBitcoinAddress address;
  if (!address.SetString(request.params[0].get_str()))
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid  address");

  CKeyID keyId;
  if (!address.GetKeyID(keyId))
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid key id");

  //insert address into sorted freezelist vector (if it doesn't already exist in the list)
  addressFreezelist.add_sorted(&keyId);

  return NullUniValue;
}

UniValue queryfreezelist(const JSONRPCRequest& request)
{

  if (request.fHelp || request.params.size() != 1)
    throw runtime_error(
            "queryfreezelist \"address\" \n"
            "\nChecks if an address is present in the node mempool freezelist.\n"
            "\nArguments:\n"
            "1. \"address\"  (string, required) Base58 encoded address\n"
            "\nExamples:\n"
            + HelpExampleCli("queryfreezelist", "\"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
            + HelpExampleRpc("queryfreezelist", "\"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
                        );

  CBitcoinAddress address;
  if (!address.SetString(request.params[0].get_str()))
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid  address");

  CKeyID keyId;
  if (!address.GetKeyID(keyId))
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid key id");

  return addressFreezelist.find(&keyId);
}

UniValue removefromfreezelist(const JSONRPCRequest& request)
{

  if (request.fHelp || request.params.size() != 1)
    throw runtime_error(
            "removefromfreezelist \"address\" \n"
            "\nRemoves an address from the node mempool freezelist.\n"
            "\nArguments:\n"
            "1. \"address\"  (string, required) Base58 encoded address\n"
            "\nExamples:\n"
            + HelpExampleCli("removefromfreezelist", "\"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
            + HelpExampleRpc("removefromfreezelist", "\"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
                        );

  CBitcoinAddress address;
  if (!address.SetString(request.params[0].get_str()))
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid  address");

  CKeyID keyId;
  if (!address.GetKeyID(keyId))
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid key id");

  addressFreezelist.remove(&keyId);

  return NullUniValue;
}

UniValue clearfreezelist(const JSONRPCRequest& request)
{

  if (request.fHelp || request.params.size() != 0)
    throw runtime_error(
            "clearfreezelist \n"
            "\nClears the node mempool transaction freezelist (no arguments).\n"
            + HelpExampleCli("clearfreezelist", "\"true\"")
            + HelpExampleRpc("clearfreezelist", "\"true\"")
                        );

  addressFreezelist.clear();

  return NullUniValue;
}

UniValue addtoburnlist(const JSONRPCRequest& request)
{
  if (request.fHelp || request.params.size() != 1)
    throw runtime_error(
                            "addtoburnlist \"address\"\n"
            "\nAdd an address to the node mempool burnlist.\n"
            "\nArguments:\n"
            "1. \"address\"  (string, required) Base58 address\n"
            "\nExamples:\n"
                            + HelpExampleCli("addtoburnlist", "\"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
                            + HelpExampleRpc("addtoburnlist", "\"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
                        );

  CBitcoinAddress address;
  if (!address.SetString(request.params[0].get_str()))
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid  address");

  CKeyID keyId;
  if (!address.GetKeyID(keyId))
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid key id");

  //insert address into sorted freezelist vector (if it doesn't already exist in the list)
  addressBurnlist.add_sorted(&keyId);

return NullUniValue;
}

UniValue queryburnlist(const JSONRPCRequest& request)
{

  if (request.fHelp || request.params.size() != 1)
    throw runtime_error(
            "queryburnlist \"address\" \n"
            "\nChecks if an address is present in the node mempool burnlist.\n"
            "\nArguments:\n"
            "1. \"address\"  (string, required) Base58 encoded address\n"
            "\nExamples:\n"
            + HelpExampleCli("queryburnlist", "\"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
            + HelpExampleRpc("queryburnlist", "\"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
                        );

  CBitcoinAddress address;
  if (!address.SetString(request.params[0].get_str()))
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid  address");

  CKeyID keyId;
  if (!address.GetKeyID(keyId))
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid key id");

  return addressBurnlist.find(&keyId);
}

UniValue removefromburnlist(const JSONRPCRequest& request)
{

  if (request.fHelp || request.params.size() != 1)
    throw runtime_error(
            "removefromburnlist \"address\" \n"
            "\nRemoves an address from the node mempool burnlist.\n"
            "\nArguments:\n"
            "1. \"address\"  (string, required) Base58 encoded address\n"
            "\nExamples:\n"
            + HelpExampleCli("removefromburnlist", "\"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
            + HelpExampleRpc("removefromburnlist", "\"2dncVuBznaXPDNv8YXCKmpfvoDPNZ288MhB\"")
                        );

  CBitcoinAddress address;
  if (!address.SetString(request.params[0].get_str()))
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid  address");

  CKeyID keyId;
  if (!address.GetKeyID(keyId))
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid key id");

  addressBurnlist.remove(&keyId);

  return NullUniValue;
}

UniValue clearburnlist(const JSONRPCRequest& request)
{

  if (request.fHelp || request.params.size() != 0)
    throw runtime_error(
            "clearburnlist \n"
            "\nClears the node mempool transaction burnlist (no arguments).\n"
            + HelpExampleCli("clearburnlist", "\"true\"")
            + HelpExampleRpc("clearburnlist", "\"true\"")
                        );

  addressBurnlist.clear();
  return NullUniValue;
}

UniValue invalidateblock(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "invalidateblock \"blockhash\"\n"
            "\nPermanently marks a block as invalid, as if it violated a consensus rule.\n"
            "\nArguments:\n"
            "1. \"blockhash\"   (string, required) the hash of the block to mark as invalid\n"
            "\nResult:\n"
            "\nExamples:\n"
            + HelpExampleCli("invalidateblock", "\"blockhash\"")
            + HelpExampleRpc("invalidateblock", "\"blockhash\"")
        );

    std::string strHash = request.params[0].get_str();
    uint256 hash(uint256S(strHash));
    CValidationState state;

    {
        LOCK(cs_main);
        if (mapBlockIndex.count(hash) == 0)
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Block not found");

        CBlockIndex* pblockindex = mapBlockIndex[hash];
        InvalidateBlock(state, Params(), pblockindex);
    }

    if (state.IsValid()) {
        ActivateBestChain(state, Params());
    }

    if (!state.IsValid()) {
        throw JSONRPCError(RPC_DATABASE_ERROR, state.GetRejectReason());
    }

    return NullUniValue;
}

UniValue reconsiderblock(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "reconsiderblock \"blockhash\"\n"
            "\nRemoves invalidity status of a block and its descendants, reconsider them for activation.\n"
            "This can be used to undo the effects of invalidateblock.\n"
            "\nArguments:\n"
            "1. \"blockhash\"   (string, required) the hash of the block to reconsider\n"
            "\nResult:\n"
            "\nExamples:\n"
            + HelpExampleCli("reconsiderblock", "\"blockhash\"")
            + HelpExampleRpc("reconsiderblock", "\"blockhash\"")
        );

    std::string strHash = request.params[0].get_str();
    uint256 hash(uint256S(strHash));

    {
        LOCK(cs_main);
        if (mapBlockIndex.count(hash) == 0)
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Block not found");

        CBlockIndex* pblockindex = mapBlockIndex[hash];
        ResetBlockFailureFlags(pblockindex);
    }

    CValidationState state;
    ActivateBestChain(state, Params());

    if (!state.IsValid()) {
        throw JSONRPCError(RPC_DATABASE_ERROR, state.GetRejectReason());
    }

    return NullUniValue;
}

UniValue getmappinghash(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() > 1)
        throw runtime_error(
                "getmappinghash blockheight\n"
                "\nReturns the mapping hash for the specified block height.\n"
                "\nArguments:\n"
                "1. blockheight         (numeric, required) The height index\n"
                "\nResult:\n"
                "\"mapping\"         (string) The mapping hash\n"
                "\nExamples:\n"
                + HelpExampleCli("getmappinghash", "1000")
                + HelpExampleRpc("getmappinghash", "1000")
                );

    LOCK(cs_main);

    int nHeight = chainActive.Height();
    if (request.params.size() > 0)
    {
        nHeight = request.params[0].get_int();
        if (nHeight < 0 || nHeight > chainActive.Height())
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Block height out of range");
    }

    CBlockIndex* pblockindex = chainActive[nHeight];
    return pblockindex->hashMapping.ToString();
}

UniValue getcontracthash(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() > 1)
        throw runtime_error(
                "getcontracthash blockheight\n"
                "\nReturns the contract hash for the specified block height.\n"
                "\nArguments:\n"
                "1. blockheight         (numeric, required) The height index\n"
                "\nResult:\n"
                "\"contracthash\"         (string) The contract hash\n"
                "\nExamples:\n"
                + HelpExampleCli("getcontracthash", "1000")
                + HelpExampleRpc("getcontracthash", "1000")
                );

    LOCK(cs_main);

    int nHeight = chainActive.Height();
    if (request.params.size() > 0)
    {
        nHeight = request.params[0].get_int();
        if (nHeight < 0 || nHeight > chainActive.Height())
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Block height out of range");
    }

    CBlockIndex* pblockindex = chainActive[nHeight];
    return pblockindex->hashContract.ToString();
}

UniValue getcontract(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 0)
        throw runtime_error(
                "getcontract \n"
                "\nReturns the latest contract from the node\n"
                "\nUp to date contract details are only maintained in signing nodes (no arguments).\n"
                "\nResult:\n"
                "{\n"
                "   \"contract\" : \"contract\""
                "}\n"
                + HelpExampleCli("getcontract", "\"true\"")
                + HelpExampleRpc("getcontract", "\"true\"")
                );

    UniValue ret(UniValue::VOBJ);
    ret.push_back(Pair("contract", GetContract()));
    return ret;
}

template<typename T>
static T CalculateTruncatedMedian(std::vector<T>& scores)
{
    size_t size = scores.size();
    if (size == 0) {
        return 0;
    }

    std::sort(scores.begin(), scores.end());
    if (size % 2 == 0) {
        return (scores[size / 2 - 1] + scores[size / 2]) / 2;
    } else {
        return scores[size / 2];
    }
}

template<typename T>
static inline bool SetHasKeys(const std::set<T>& set) {return false;}
template<typename T, typename Tk, typename... Args>
static inline bool SetHasKeys(const std::set<T>& set, const Tk& key, const Args&... args)
{
    return (set.count(key) != 0) || SetHasKeys(set, args...);
}

// outpoint (needed for the utxo index) + nHeight + fCoinBase
static constexpr size_t PER_UTXO_OVERHEAD = sizeof(COutPoint) + sizeof(uint32_t) + sizeof(bool);

static UniValue getblockstats(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() < 1 || request.params.size() > 4)
        throw std::runtime_error(
            "getblockstats ( hash_or_height stats )\n"
            "\nCompute per block statistics for a given window. All amounts are in satoshis.\n"
            "\nIt won't work for some heights with pruning.\n"
            // "\nIt won't work without -txindex for utxo_size_inc, *fee or *feerate stats.\n"
            "\nArguments:\n"
            "1. \"hash_or_height\"     (string or numeric, required) The block hash or height of the target block. If height, negative values count back from the current tip\n"
            "2. \"stats\"      (array,  optional) Values to plot, by default all values, see result below)"
            "    ["
            "      \"height\",   (string, optional) Selected statistic\n"
            "      \"time\",     (string, optional) Selected statistic\n"
            "      ,...\n"
            "    ]\n"
            "\nResult: (all values are in reverse order height-wise)\n"
            "{                             (json object)\n"
            "  \"avgfee\": xxxxx,          (numeric) Average fee in the block\n"
            "  \"avgfeerate\": xxxxx,      (numeric) Average feerate (in satoshis per virtual byte)\n"
            "  \"avgtxsize\": xxxxx,       (numeric) Average transaction size\n"
            "  \"blockhash\": xxxxx,       (string) The block hash (to check for potential reorgs)\n"
            "  \"height\": xxxxx,          (numeric) The height of the block\n"
            "  \"ins\": xxxxx,             (numeric) The number of inputs (excluding coinbase)\n"
            "  \"maxfee\": xxxxx,          (numeric) Maximum fee in the block\n"
            "  \"maxfeerate\": xxxxx,      (numeric) Maximum feerate (in satoshis per virtual byte)\n"
            "  \"maxtxsize\": xxxxx,       (numeric) Maximum transaction size\n"
            "  \"medianfee\": xxxxx,       (numeric) Truncated median fee in the block\n"
            "  \"medianfeerate\": xxxxx,   (numeric) Truncated median feerate (in satoshis per virtual byte)\n"
            "  \"mediantime\": xxxxx,      (numeric) The block median time past\n"
            "  \"mediantxsize\": xxxxx,    (numeric) Truncated median transaction size\n"
            "  \"minfee\": xxxxx,          (numeric) Minimum fee in the block\n"
            "  \"minfeerate\": xxxxx,      (numeric) Minimum feerate (in satoshis per virtual byte)\n"
            "  \"mintxsize\": xxxxx,       (numeric) Minimum transaction size\n"
            "  \"outs\": xxxxx,            (numeric) The number of outputs\n"
            "  \"subsidy\": xxxxx,         (numeric) The block subsidy\n"
            "  \"swtotal_size\": xxxxx,    (numeric) Total size of all segwit transactions\n"
            "  \"swtotal_weight\": xxxxx,  (numeric) Total weight of all segwit transactions divided by segwit scale factor (4)\n"
            "  \"swtxs\": xxxxx,           (numeric) The number of segwit transactions\n"
            "  \"time\": xxxxx,            (numeric) The block time\n"
            "  \"total_out\": xxxxx,       (numeric) Total amount in all outputs (excluding coinbase and thus reward [ie subsidy + totalfee])\n"
            "  \"total_size\": xxxxx,      (numeric) Total size of all non-coinbase transactions\n"
            "  \"total_weight\": xxxxx,    (numeric) Total weight of all non-coinbase transactions divided by segwit scale factor (4)\n"
            "  \"totalfee\": xxxxx,        (numeric) The fee total\n"
            "  \"txs\": xxxxx,             (numeric) The number of transactions (excluding coinbase)\n"
            "  \"utxo_increase\": xxxxx,   (numeric) The increase/decrease in the number of unspent outputs\n"
            "  \"utxo_size_inc\": xxxxx,   (numeric) The increase/decrease in size for the utxo index (not discounting op_return and similar)\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("getblockstats", "1000 '[\"minfeerate\",\"avgfeerate\"]'")
            + HelpExampleRpc("getblockstats", "1000 '[\"minfeerate\",\"avgfeerate\"]'")
        );

    LOCK(cs_main);

    CBlockIndex* pindex;
    if (request.params[0].isNum()) {
        const int height = request.params[0].get_int();
        const int current_tip = chainActive.Height();
        if (height < 0) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Target block height %d is negative", height));
        }
        if (height > current_tip) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Target block height %d after current tip %d", height, current_tip));
        }

        pindex = chainActive[height];
    } else {
        const std::string strHash = request.params[0].get_str();
        const uint256 hash(uint256S(strHash));
        pindex = mapBlockIndex[hash];
    }
    if (!pindex) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Block not found");
    }
    if (!chainActive.Contains(pindex)) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Block is not in chain %s", Params().NetworkIDString()));
    }

    assert(pindex != nullptr);

    std::set<std::string> stats;
    if (!request.params[1].isNull()) {
        const UniValue stats_univalue = request.params[1].get_array();
        for (unsigned int i = 0; i < stats_univalue.size(); i++) {
            const std::string stat = stats_univalue[i].get_str();
            stats.insert(stat);
        }
    }

    const CBlock block = GetBlockChecked(pindex);

    const bool do_all = stats.size() == 0; // Calculate everything if nothing selected (default)
    const bool do_mediantxsize = do_all || stats.count("mediantxsize") != 0;
    const bool do_medianfee = do_all || stats.count("medianfee") != 0;
    const bool do_medianfeerate = do_all || stats.count("medianfeerate") != 0;
    const bool loop_inputs = do_all || stats.count("utxo_size_inc");
    const bool loop_outputs = do_all || do_medianfee || do_medianfeerate || loop_inputs ||
        SetHasKeys(stats, "totalfee", "avgfee", "avgfeerate", "minfee", "maxfee", "minfeerate", "maxfeerate", "total_out");
    const bool do_calculate_size = do_mediantxsize ||
        SetHasKeys(stats, "total_size", "avgtxsize", "mintxsize", "maxtxsize", "swtotal_size");
    const bool do_calculate_weight = do_all || SetHasKeys(stats, "total_weight", "avgfeerate", "swtotal_weight", "avgfeerate", "medianfeerate", "minfeerate", "maxfeerate");
    const bool do_calculate_sw = do_all || SetHasKeys(stats, "swtxs", "swtotal_size", "swtotal_weight");

    CAmount maxfee = 0;
    CAmount maxfeerate = 0;
    CAmount minfee = MAX_MONEY;
    CAmount minfeerate = MAX_MONEY;
    CAmount total_out = 0;
    CAmount totalfee = 0;
    int64_t inputs = 0;
    int64_t maxtxsize = 0;
    int64_t mintxsize = MAX_BLOCK_SERIALIZED_SIZE;
    int64_t outputs = 0;
    int64_t swtotal_size = 0;
    int64_t swtotal_weight = 0;
    int64_t swtxs = 0;
    int64_t total_size = 0;
    int64_t total_weight = 0;
    int64_t utxo_size_inc = 0;
    std::vector<CAmount> fee_array;
    std::vector<CAmount> feerate_array;
    std::vector<int64_t> txsize_array;

    for (const auto& tx : block.vtx) {
        outputs += tx->vout.size();

        CAmount txfee = 0;
        CAmount tx_total_out = 0;
        if (loop_outputs) {
            for (const CTxOut& out : tx->vout) {
                utxo_size_inc += GetSerializeSize(out, SER_NETWORK, PROTOCOL_VERSION) + PER_UTXO_OVERHEAD;
            }
        }

        if (tx->IsCoinBase()) {
            continue;
        }

        if (loop_outputs) {
            for (const CTxOut& out : tx->vout) {
                if (out.IsFee()) {
                    txfee += out.nValue.GetAmount();
                }
                if (out.nValue.IsExplicit() && out.nAsset.IsExplicit()) {
                    tx_total_out += out.nValue.GetAmount();
                }
            }
        }

        inputs += tx->vin.size(); // Don't count coinbase's fake input
        total_out += tx_total_out; // Don't count coinbase reward

        int64_t tx_size = 0;
        if (do_calculate_size) {

            tx_size = tx->GetTotalSize();
            if (do_mediantxsize) {
                txsize_array.push_back(tx_size);
            }
            maxtxsize = std::max(maxtxsize, tx_size);
            mintxsize = std::min(mintxsize, tx_size);
            total_size += tx_size;
        }

        int64_t weight = 0;
        if (do_calculate_weight) {
            weight = GetTransactionWeight(*tx);
            total_weight += weight;
        }

        if (do_calculate_sw && tx->HasWitness()) {
            ++swtxs;
            swtotal_size += tx_size;
            swtotal_weight += weight;
        }

        if (loop_inputs) {

            if (!fTxIndex) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "One or more of the selected stats requires -txindex enabled");
            }
            for (const CTxIn& in : tx->vin) {
                if (in.m_is_pegin) {
                    continue;
                }
                CTransactionRef tx_in;
                uint256 hashBlock;
                if (!GetTransaction(in.prevout.hash, tx_in, Params().GetConsensus(), hashBlock, false)) {
                    throw JSONRPCError(RPC_INTERNAL_ERROR, std::string("Unexpected internal error (tx index seems corrupt)"));
                }

                CTxOut prevoutput = tx_in->vout[in.prevout.n];
                utxo_size_inc -= GetSerializeSize(prevoutput, SER_NETWORK, PROTOCOL_VERSION) + PER_UTXO_OVERHEAD;
            }
        }

        if (loop_outputs) {
            assert(MoneyRange(txfee));
            if (do_medianfee) {
              fee_array.push_back(txfee);
            }
            maxfee = std::max(maxfee, txfee);
            minfee = std::min(minfee, txfee);
            totalfee += txfee;

            // New feerate uses satoshis per virtual byte instead of per serialized byte
            CAmount feerate = weight ? (txfee * WITNESS_SCALE_FACTOR) / weight : 0;
            if (do_medianfeerate) {
              feerate_array.push_back(feerate);
            }
            maxfeerate = std::max(maxfeerate, feerate);
            minfeerate = std::min(minfeerate, feerate);
        }
    }

    UniValue ret_all(UniValue::VOBJ);
    ret_all.pushKV("avgfee", (block.vtx.size() > 1) ? totalfee / (block.vtx.size() - 1) : 0);
    ret_all.pushKV("avgfeerate", total_weight ? (totalfee * WITNESS_SCALE_FACTOR) / total_weight : 0); // Unit: sat/vbyte
    ret_all.pushKV("avgtxsize", (block.vtx.size() > 1) ? total_size / (block.vtx.size() - 1) : 0);
    ret_all.pushKV("blockhash", pindex->GetBlockHash().GetHex());
    ret_all.pushKV("height", (int64_t)pindex->nHeight);
    ret_all.pushKV("ins", inputs);
    ret_all.pushKV("maxfee", maxfee);
    ret_all.pushKV("maxfeerate", maxfeerate);
    ret_all.pushKV("maxtxsize", maxtxsize);
    ret_all.pushKV("medianfee", CalculateTruncatedMedian(fee_array));
    ret_all.pushKV("medianfeerate", CalculateTruncatedMedian(feerate_array));
    ret_all.pushKV("mediantime", pindex->GetMedianTimePast());
    ret_all.pushKV("mediantxsize", CalculateTruncatedMedian(txsize_array));
    ret_all.pushKV("minfee", (minfee == MAX_MONEY) ? 0 : minfee);
    ret_all.pushKV("minfeerate", (minfeerate == MAX_MONEY) ? 0 : minfeerate);
    ret_all.pushKV("mintxsize", mintxsize == MAX_BLOCK_SERIALIZED_SIZE ? 0 : mintxsize);
    ret_all.pushKV("outs", outputs);
    ret_all.pushKV("subsidy", GetBlockSubsidy(pindex->nHeight, Params().GetConsensus()));
    ret_all.pushKV("swtotal_size", swtotal_size);
    ret_all.pushKV("swtotal_weight", swtotal_weight);
    ret_all.pushKV("swtxs", swtxs);
    ret_all.pushKV("time", pindex->GetBlockTime());
    ret_all.pushKV("total_out", total_out);
    ret_all.pushKV("total_size", total_size);
    ret_all.pushKV("total_weight", total_weight);
    ret_all.pushKV("totalfee", totalfee);
    ret_all.pushKV("txs", (int64_t)block.vtx.size());
    ret_all.pushKV("utxo_increase", outputs - inputs);
    ret_all.pushKV("utxo_size_inc", utxo_size_inc);

    if (do_all) {
        return ret_all;
    }

    UniValue ret(UniValue::VOBJ);
    for (const std::string& stat : stats) {
        const UniValue& value = ret_all[stat];
        if (value.isNull()) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Invalid selected statistic %s", stat));
        }
        ret.pushKV(stat, value);
    }
    return ret;
}

static const CRPCCommand commands[] =
    {
        //  category              name                      actor (function)         okSafe argNames
        //  --------------------- ------------------------  -----------------------  ------ ----------
        {"blockchain", "getblockchaininfo", &getblockchaininfo, true, {}},
        {"blockchain", "getblockstats", &getblockstats, true, {"hash_or_height", "stats"}},
        {"blockchain", "getbestblockhash", &getbestblockhash, true, {}},
        {"blockchain", "getblockcount", &getblockcount, true, {}},
        {"blockchain", "getblock", &getblock, true, {"blockhash", "verbosity"}},
        {"blockchain", "getblockhash", &getblockhash, true, {"height"}},
        {"blockchain", "getblockheader", &getblockheader, true, {"blockhash", "verbose"}},
        {"blockchain", "getchaintips", &getchaintips, true, {}},
        {"blockchain", "getdifficulty", &getdifficulty, true, {}},
        {"blockchain", "getmempoolancestors", &getmempoolancestors, true, {"txid", "verbose"}},
        {"blockchain", "getmempooldescendants", &getmempooldescendants, true, {"txid", "verbose"}},
        {"blockchain", "getmempoolentry", &getmempoolentry, true, {"txid"}},
        {"blockchain", "getmempoolinfo", &getmempoolinfo, true, {}},
        {"blockchain", "getrawmempool", &getrawmempool, true, {"verbose"}},
        {"blockchain", "getsidechaininfo", &getsidechaininfo, true, {}},
        {"blockchain", "gettxout", &gettxout, true, {"txid", "n", "include_mempool"}},
        {"blockchain", "gettxoutsetinfo", &gettxoutsetinfo, true, {}},
        {"blockchain", "getutxoassetinfo", &getutxoassetinfo, true, {}},
        {"blockchain", "getrequests", &getrequests, true, {"genesis_hash"}},
        {"blockchain", "getrequestbids", &getrequestbids, true, {"request_hash"}},
        {"blockchain", "getfreezehistory", &getfreezehistory, true, {"height"}},
        {"blockchain", "pruneblockchain", &pruneblockchain, true, {"height"}},
        {"blockchain", "verifychain", &verifychain, true, {"checklevel", "nblocks"}},

        {"blockchain", "preciousblock", &preciousblock, true, {"blockhash"}},

        {"blockchain", "addtowhitelist", &addtowhitelist, true, {"address", "basepubkey", "kycpubkey"}},
        {"blockchain", "readwhitelist", &readwhitelist, true, {"filename", "kycaddress"}},
        {"blockchain", "querywhitelist", &querywhitelist, true, {"address"}},
        {"blockchain", "removefromwhitelist", &removefromwhitelist, true, {"address"}},
        {"blockchain", "dumpwhitelist", &dumpwhitelist, true, {}},
        {"blockchain", "clearwhitelist", &clearwhitelist, true, {}},


        {"blockchain", "addtofreezelist", &addtofreezelist, true, {"address"}},
        {"blockchain", "removefromfreezelist", &removefromfreezelist, true, {"address"}},
        {"blockchain", "queryfreezelist", &queryfreezelist, true, {"address"}},
        {"blockchain", "clearfreezelist", &clearfreezelist, true, {}},

        {"blockchain", "addtoburnlist", &addtoburnlist, true, {"address"}},
        {"blockchain", "removefromburnlist", &removefromburnlist, true, {"address"}},
        {"blockchain", "queryburnlist", &queryburnlist, true, {"address"}},
        {"blockchain", "clearburnlist", &clearburnlist, true, {}},

        {"blockchain", "getcontract", &getcontract, true, {}},
        {"blockchain", "getcontracthash", &getcontracthash, true, {"blockheight"}},
        {"blockchain", "getmappinghash", &getmappinghash, true, {"blockheight"}},

        /* Not shown in help */
        {"hidden", "invalidateblock", &invalidateblock, true, {"blockhash"}},
        {"hidden", "reconsiderblock", &reconsiderblock, true, {"blockhash"}},
        {"hidden", "waitfornewblock", &waitfornewblock, true, {"timeout"}},
        {"hidden", "waitforblock", &waitforblock, true, {"blockhash", "timeout"}},
        {"hidden", "waitforblockheight", &waitforblockheight, true, {"height", "timeout"}},
};

void RegisterBlockchainRPCCommands(CRPCTable &t)
{
    for (unsigned int vcidx = 0; vcidx < ARRAYLEN(commands); vcidx++)
        t.appendCommand(commands[vcidx].name, &commands[vcidx]);
}
