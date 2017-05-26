// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2015 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "base58.h"
#include "blind.h"
#include "chain.h"
#include "coins.h"
#include "consensus/validation.h"
#include "core_io.h"
#include "init.h"
#include "issuance.h"
#include "keystore.h"
#include "main.h"
#include "merkleblock.h"
#include "net.h"
#include "policy/policy.h"
#include "primitives/transaction.h"
#include "rpc/server.h"
#include "script/script.h"
#include "script/script_error.h"
#include "script/sign.h"
#include "script/standard.h"
#include "txmempool.h"
#include "uint256.h"
#include "utilstrencodings.h"
#include "util.h"
#ifdef ENABLE_WALLET
#include "wallet/wallet.h"
#endif

#include <stdint.h>

#include <boost/assign/list_of.hpp>
#include <secp256k1_rangeproof.h>

#include <univalue.h>

using namespace std;

static secp256k1_context* secp256k1_blind_context = NULL;

class RPCRawTransaction_ECC_Init {
public:
    RPCRawTransaction_ECC_Init() {
        assert(secp256k1_blind_context == NULL);

        secp256k1_context *ctx = secp256k1_context_create(SECP256K1_CONTEXT_NONE);
        assert(ctx != NULL);

        secp256k1_blind_context = ctx;
    }

    ~RPCRawTransaction_ECC_Init() {
        secp256k1_context *ctx = secp256k1_blind_context;
        secp256k1_blind_context = NULL;

        if (ctx) {
            secp256k1_context_destroy(ctx);
        }
    }
};
static RPCRawTransaction_ECC_Init ecc_init_on_load;

void ScriptPubKeyToJSON(const CScript& scriptPubKey, UniValue& out, bool fIncludeHex)
{
    txnouttype type;
    vector<CTxDestination> addresses;
    int nRequired;

    out.push_back(Pair("asm", ScriptToAsmStr(scriptPubKey)));
    if (fIncludeHex)
        out.push_back(Pair("hex", HexStr(scriptPubKey.begin(), scriptPubKey.end())));

    if (!ExtractDestinations(scriptPubKey, type, addresses, nRequired)) {
        out.push_back(Pair("type", GetTxnOutputType(type)));
        return;
    }

    out.push_back(Pair("reqSigs", nRequired));
    out.push_back(Pair("type", GetTxnOutputType(type)));

    UniValue a(UniValue::VARR);
    BOOST_FOREACH(const CTxDestination& addr, addresses)
        a.push_back(CBitcoinAddress(addr).ToString());
    out.push_back(Pair("addresses", a));
}

void TxToJSON(const CTransaction& tx, const uint256 hashBlock, UniValue& entry)
{
    entry.push_back(Pair("txid", tx.GetHash().GetHex()));
    entry.push_back(Pair("hash", tx.GetHashWithWitness().GetHex()));
    entry.push_back(Pair("withash", tx.ComputeWitnessHash().GetHex()));
    entry.push_back(Pair("size", (int)::GetSerializeSize(tx, SER_NETWORK, PROTOCOL_VERSION)));
    entry.push_back(Pair("vsize", (int)::GetVirtualTransactionSize(tx)));
    entry.push_back(Pair("version", tx.nVersion));
    entry.push_back(Pair("locktime", (int64_t)tx.nLockTime));
    
    UniValue vin(UniValue::VARR);
    for (unsigned int i = 0; i < tx.vin.size(); i++) {
        const CTxIn& txin = tx.vin[i];
        UniValue in(UniValue::VOBJ);
        if (tx.IsCoinBase())
            in.push_back(Pair("coinbase", HexStr(txin.scriptSig.begin(), txin.scriptSig.end())));
        else {
            in.push_back(Pair("txid", txin.prevout.hash.GetHex()));
            in.push_back(Pair("vout", (int64_t)txin.prevout.n));
            UniValue o(UniValue::VOBJ);
            o.push_back(Pair("asm", ScriptToAsmStr(txin.scriptSig, true)));
            o.push_back(Pair("hex", HexStr(txin.scriptSig.begin(), txin.scriptSig.end())));
            in.push_back(Pair("scriptSig", o));
        }
        if (!tx.wit.IsNull()) {
            if (!tx.wit.vtxinwit[i].IsNull()) {
                UniValue scriptWitness(UniValue::VARR);
                for (unsigned int j = 0; j < tx.wit.vtxinwit[i].scriptWitness.stack.size(); j++) {
                    std::vector<unsigned char> item = tx.wit.vtxinwit[i].scriptWitness.stack[j];
                    scriptWitness.push_back(HexStr(item.begin(), item.end()));
                }
                in.push_back(Pair("scriptWitness", scriptWitness));
            }
        }
        const CAssetIssuance& issuance = txin.assetIssuance;
        if (!issuance.IsNull()) {
            UniValue issue(UniValue::VOBJ);
            issue.push_back(Pair("assetBlindingNonce", issuance.assetBlindingNonce.GetHex()));
            issue.push_back(Pair("assetEntropy", issuance.assetEntropy.GetHex()));
            CAsset asset;
            CAsset token;
            uint256 entropy;
            if (issuance.assetBlindingNonce.IsNull()) {
                GenerateAssetEntropy(entropy, txin.prevout, issuance.assetEntropy);
                CalculateAsset(asset, entropy);
                CalculateReissuanceToken(token, entropy, issuance.nAmount.IsCommitment());
                issue.push_back(Pair("isreissuance", false));
                issue.push_back(Pair("token", token.GetHex()));
            }
            else {
                issue.push_back(Pair("isreissuance", true));
                CalculateAsset(asset, issuance.assetEntropy);
            }
            issue.push_back(Pair("asset", asset.GetHex()));

            if (issuance.nAmount.IsExplicit()) {
                issue.push_back(Pair("assetamount", ValueFromAmount(issuance.nAmount.GetAmount())));
            } else if (issuance.nAmount.IsCommitment()) {
                issue.push_back(Pair("assetvaluecommitment", HexStr(issuance.nAmount.vchCommitment)));
            }
            if (issuance.nInflationKeys.IsExplicit()) {
                issue.push_back(Pair("tokenamount", ValueFromAmount(issuance.nInflationKeys.GetAmount())));
            } else if (issuance.nInflationKeys.IsCommitment()) {
                issue.push_back(Pair("tokenvaluecommitment", HexStr(issuance.nInflationKeys.vchCommitment)));
            }
            in.push_back(Pair("issuance", issue));
        }
        in.push_back(Pair("sequence", (int64_t)txin.nSequence));
        vin.push_back(in);
    }
    entry.push_back(Pair("vin", vin));
    UniValue vout(UniValue::VARR);
    for (unsigned int i = 0; i < tx.vout.size(); i++) {
        const CTxOut& txout = tx.vout[i];
        UniValue out(UniValue::VOBJ);
        if (txout.nValue.IsExplicit())
            out.push_back(Pair("value", ValueFromAmount(txout.nValue.GetAmount())));
        else {
            int exp;
            int mantissa;
            uint64_t minv;
            uint64_t maxv;
            const CTxOutWitness* ptxoutwit = tx.wit.vtxoutwit.size() <= i? NULL: &tx.wit.vtxoutwit[i];
            if (ptxoutwit && secp256k1_rangeproof_info(secp256k1_blind_context, &exp, &mantissa, &minv, &maxv, &ptxoutwit->vchRangeproof[0], ptxoutwit->vchRangeproof.size())) {
                if (exp == -1) {
                    out.push_back(Pair("value", ValueFromAmount((CAmount)minv)));
                } else {
                    out.push_back(Pair("value-minimum", ValueFromAmount((CAmount)minv)));
                    out.push_back(Pair("value-maximum", ValueFromAmount((CAmount)maxv)));
                }
                out.push_back(Pair("ct-exponent", exp));
                out.push_back(Pair("ct-bits", mantissa));
            }
        }
        const CConfidentialAsset& asset = txout.nAsset;
        if (asset.IsExplicit()) {
            out.push_back(Pair("asset", asset.GetAsset().GetHex()));
        }
        else if (asset.IsCommitment()) {
            out.push_back(Pair("assetcommitment", HexStr(asset.vchCommitment)));
        }

        {
            CDataStream ssValue(SER_NETWORK, PROTOCOL_VERSION);
            ssValue << txout.nValue;
            out.push_back(Pair("serValue", HexStr(ssValue.begin(), ssValue.end())));
        }
        out.push_back(Pair("n", (int64_t)i));
        UniValue o(UniValue::VOBJ);
        ScriptPubKeyToJSON(txout.scriptPubKey, o, true);
        out.push_back(Pair("scriptPubKey", o));
        vout.push_back(out);
    }
    entry.push_back(Pair("vout", vout));

    if (!hashBlock.IsNull()) {
        entry.push_back(Pair("blockhash", hashBlock.GetHex()));
        BlockMap::iterator mi = mapBlockIndex.find(hashBlock);
        if (mi != mapBlockIndex.end() && (*mi).second) {
            CBlockIndex* pindex = (*mi).second;
            if (chainActive.Contains(pindex)) {
                entry.push_back(Pair("confirmations", 1 + chainActive.Height() - pindex->nHeight));
                entry.push_back(Pair("time", pindex->GetBlockTime()));
                entry.push_back(Pair("blocktime", pindex->GetBlockTime()));
            }
            else
                entry.push_back(Pair("confirmations", 0));
        }
    }
}

UniValue getrawtransaction(const UniValue& params, bool fHelp)
{
    if (fHelp || params.size() < 1 || params.size() > 2)
        throw runtime_error(
            "getrawtransaction \"txid\" ( verbose )\n"
            "\nNOTE: By default this function only works sometimes. This is when the tx is in the mempool\n"
            "or there is an unspent output in the utxo for this transaction. To make it always work,\n"
            "you need to maintain a transaction index, using the -txindex command line option.\n"
            "\nReturn the raw transaction data.\n"
            "\nIf verbose=0, returns a string that is serialized, hex-encoded data for 'txid'.\n"
            "If verbose is non-zero, returns an Object with information about 'txid'.\n"

            "\nArguments:\n"
            "1. \"txid\"      (string, required) The transaction id\n"
            "2. verbose       (numeric, optional, default=0) If 0, return a string, other return a json object\n"

            "\nResult (if verbose is not set or set to 0):\n"
            "\"data\"      (string) The serialized, hex-encoded data for 'txid'\n"

            "\nResult (if verbose > 0):\n"
            "{\n"
            "  \"hex\" : \"data\",       (string) The serialized, hex-encoded data for 'txid'\n"
            "  \"txid\" : \"id\",        (string) The transaction id (same as provided)\n"
            "  \"hash\" : \"id\",        (string) The transaction hash (differs from txid for witness transactions)\n"
            "  \"size\" : n,             (numeric) The serialized transaction size\n"
            "  \"vsize\" : n,            (numeric) The virtual transaction size (differs from size for witness transactions)\n"
            "  \"version\" : n,          (numeric) The version\n"
            "  \"locktime\" : ttt,       (numeric) The lock time\n"
            "  \"vin\" : [               (array of json objects)\n"
            "     {\n"
            "       \"txid\": \"id\",    (string) The transaction id\n"
            "       \"vout\": n,         (numeric) \n"
            "       \"scriptSig\": {     (json object) The script\n"
            "         \"asm\": \"asm\",  (string) asm\n"
            "         \"hex\": \"hex\"   (string) hex\n"
            "       },\n"
            "       \"sequence\": n      (numeric) The script sequence number\n"
            "       \"txinwitness\": [\"hex\", ...] (array of string) hex-encoded witness data (if any)\n"
            "     }\n"
            "     ,...\n"
            "  ],\n"
            "  \"vout\" : [              (array of json objects)\n"
            "     {\n"
            "       \"value\" : x.xxx,            (numeric) The value in " + CURRENCY_UNIT + "\n"
            "       \"fee_value\" : x.xxx,        (numeric) The fee value in " + CURRENCY_UNIT + "\n"
            "       \"n\" : n,                    (numeric) index\n"
            "       \"asset\" : \"hex\"           (string) the asset id, if unblinded\n"
            "       \"assetcommitment\" : \"hex\" (string) the asset tag, if blinded\n"
            "       \"scriptPubKey\" : {          (json object)\n"
            "         \"asm\" : \"asm\",          (string) the asm\n"
            "         \"hex\" : \"hex\",          (string) the hex\n"
            "         \"reqSigs\" : n,            (numeric) The required sigs\n"
            "         \"type\" : \"pubkeyhash\",  (string) The type, eg 'pubkeyhash'\n"
            "         \"addresses\" : [           (json array of string)\n"
            "           \"bitcoinaddress\"        (string) bitcoin address\n"
            "           ,...\n"
            "         ]\n"
            "       }\n"
            "     }\n"
            "     ,...\n"
            "  ],\n"
            "  \"blockhash\" : \"hash\",   (string) the block hash\n"
            "  \"confirmations\" : n,      (numeric) The confirmations\n"
            "  \"time\" : ttt,             (numeric) The transaction time in seconds since epoch (Jan 1 1970 GMT)\n"
            "  \"blocktime\" : ttt         (numeric) The block time in seconds since epoch (Jan 1 1970 GMT)\n"
            "}\n"

            "\nExamples:\n"
            + HelpExampleCli("getrawtransaction", "\"mytxid\"")
            + HelpExampleCli("getrawtransaction", "\"mytxid\" 1")
            + HelpExampleRpc("getrawtransaction", "\"mytxid\", 1")
        );

    LOCK(cs_main);

    uint256 hash = ParseHashV(params[0], "parameter 1");

    bool fVerbose = false;
    if (params.size() > 1)
        fVerbose = (params[1].get_int() != 0);

    CTransaction tx;
    uint256 hashBlock;
    if (!GetTransaction(hash, tx, Params().GetConsensus(), hashBlock, true))
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "No information available about transaction");

    string strHex = EncodeHexTx(tx);

    if (!fVerbose)
        return strHex;

    UniValue result(UniValue::VOBJ);
    result.push_back(Pair("hex", strHex));
    TxToJSON(tx, hashBlock, result);
    return result;
}

UniValue gettxoutproof(const UniValue& params, bool fHelp)
{
    if (fHelp || (params.size() != 1 && params.size() != 2))
        throw runtime_error(
            "gettxoutproof [\"txid\",...] ( blockhash )\n"
            "\nReturns a hex-encoded proof that \"txid\" was included in a block.\n"
            "\nNOTE: By default this function only works sometimes. This is when there is an\n"
            "unspent output in the utxo for this transaction. To make it always work,\n"
            "you need to maintain a transaction index, using the -txindex command line option or\n"
            "specify the block in which the transaction is included manually (by blockhash).\n"
            "\nReturn the raw transaction data.\n"
            "\nArguments:\n"
            "1. \"txids\"       (string) A json array of txids to filter\n"
            "    [\n"
            "      \"txid\"     (string) A transaction hash\n"
            "      ,...\n"
            "    ]\n"
            "2. \"block hash\"  (string, optional) If specified, looks for txid in the block with this hash\n"
            "\nResult:\n"
            "\"data\"           (string) A string that is a serialized, hex-encoded data for the proof.\n"
        );

    set<uint256> setTxids;
    uint256 oneTxid;
    UniValue txids = params[0].get_array();
    for (unsigned int idx = 0; idx < txids.size(); idx++) {
        const UniValue& txid = txids[idx];
        if (txid.get_str().length() != 64 || !IsHex(txid.get_str()))
            throw JSONRPCError(RPC_INVALID_PARAMETER, string("Invalid txid ")+txid.get_str());
        uint256 hash(uint256S(txid.get_str()));
        if (setTxids.count(hash))
            throw JSONRPCError(RPC_INVALID_PARAMETER, string("Invalid parameter, duplicated txid: ")+txid.get_str());
       setTxids.insert(hash);
       oneTxid = hash;
    }

    LOCK(cs_main);

    CBlockIndex* pblockindex = NULL;

    uint256 hashBlock;
    if (params.size() > 1)
    {
        hashBlock = uint256S(params[1].get_str());
        if (!mapBlockIndex.count(hashBlock))
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Block not found");
        pblockindex = mapBlockIndex[hashBlock];
    } else {
        CCoins coins;
        if (pcoinsTip->GetCoins(oneTxid, coins) && coins.nHeight > 0 && coins.nHeight <= chainActive.Height())
            pblockindex = chainActive[coins.nHeight];
    }

    if (pblockindex == NULL)
    {
        CTransaction tx;
        if (!GetTransaction(oneTxid, tx, Params().GetConsensus(), hashBlock, false) || hashBlock.IsNull())
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Transaction not yet in block");
        if (!mapBlockIndex.count(hashBlock))
            throw JSONRPCError(RPC_INTERNAL_ERROR, "Transaction index corrupt");
        pblockindex = mapBlockIndex[hashBlock];
    }

    CBlock block;
    if(!ReadBlockFromDisk(block, pblockindex, Params().GetConsensus()))
        throw JSONRPCError(RPC_INTERNAL_ERROR, "Can't read block from disk");

    unsigned int ntxFound = 0;
    BOOST_FOREACH(const CTransaction&tx, block.vtx)
        if (setTxids.count(tx.GetHash()))
            ntxFound++;
    if (ntxFound != setTxids.size())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "(Not all) transactions not found in specified block");

    CDataStream ssMB(SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS);
    CMerkleBlock mb(block, setTxids);
    ssMB << mb;
    std::string strHex = HexStr(ssMB.begin(), ssMB.end());
    return strHex;
}

UniValue verifytxoutproof(const UniValue& params, bool fHelp)
{
    if (fHelp || params.size() != 1)
        throw runtime_error(
            "verifytxoutproof \"proof\"\n"
            "\nVerifies that a proof points to a transaction in a block, returning the transaction it commits to\n"
            "and throwing an RPC error if the block is not in our best chain\n"
            "\nArguments:\n"
            "1. \"proof\"    (string, required) The hex-encoded proof generated by gettxoutproof\n"
            "\nResult:\n"
            "[\"txid\"]      (array, strings) The txid(s) which the proof commits to, or empty array if the proof is invalid\n"
        );

    CDataStream ssMB(ParseHexV(params[0], "proof"), SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS);
    CMerkleBlock merkleBlock;
    ssMB >> merkleBlock;

    UniValue res(UniValue::VARR);

    vector<uint256> vMatch;
    vector<unsigned int> vIndex;
    if (merkleBlock.txn.ExtractMatches(vMatch, vIndex) != merkleBlock.header.hashMerkleRoot)
        return res;

    LOCK(cs_main);

    if (!mapBlockIndex.count(merkleBlock.header.GetHash()) || !chainActive.Contains(mapBlockIndex[merkleBlock.header.GetHash()]))
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Block not found in chain");

    BOOST_FOREACH(const uint256& hash, vMatch)
        res.push_back(hash.GetHex());
    return res;
}

UniValue createrawtransaction(const UniValue& params, bool fHelp)
{
    if (fHelp || params.size() < 2 || params.size() > 4)
        throw runtime_error(
            "createrawtransaction [{\"txid\":\"id\",\"vout\":n,\"amount\":n},...] {\"address\":amount,\"data\":\"hex\",...} ( locktime {\"address\":asset} )\n"
            "\nCreate a transaction spending the given inputs and creating new outputs.\n"
            "Outputs can be addresses or data.\n"
            "Returns hex-encoded raw transaction.\n"
            "Note that the transaction's inputs are not signed, and\n"
            "it is not stored in the wallet or transmitted to the network.\n"

            "\nArguments:\n"
            "1. \"transactions\"            (required) A json array of json objects\n"
            "     [\n"
            "       {\n"
            "         \"txid\": \"id\",       (string, required) The transaction id\n"
            "         \"vout\": n           (numeric, required) The output number\n"
            "         \"amount\": x.xxx,    (numeric, required) The amount being spent\n"
            "         \"asset\": \"string\"   (string, optional, default=bitcoin) The asset of the input, as a tag string or a hex value\n"
            "         \"sequence\": n       (numeric, optional) The sequence number\n"
            "       }\n"
            "       ,...\n"
            "     ]\n"
            "2. \"outputs\"                 (required) A json object with outputs\n"
            "    {\n"
            "      \"address\": x.xxx       (numeric or string, required) The key is the address, the numeric value (can be string) is the given amount of the specified asset type\n"
            "      \"data\": \"hex\",         (string, required) The key is \"data\", the value is hex encoded data\n"
            "      \"fee\": x.xxx           (numeric or string, required) The key is \"fee\", the value the fee output you want to add.\n"
            "      ...\n"
            "    }\n"
            "3. locktime                  (numeric, optional, default=0) Raw locktime. Non-0 value also locktime-activates inputs\n"
            "4. \"output_assets\"           (strings, optional, default=bitcoin) A json object of assets to addresses\n"
            "   {\n"
            "       \"address\": \"hex\" \n"
            "        \"fee\": \"hex\" \n"
            "       ...\n"
            "   }\n"
            "\nResult:\n"
            "\"transaction\"            (string) Hex string of the transaction\n"

            "\nExamples\n"
            + HelpExampleCli("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0,\\\"amount\\\":2.5}]\" \"{\\\"address\\\":2.41}\"")
            + HelpExampleCli("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0,\\\"amount\\\":2.5,\\\"asset\\\":\\\"myasset\\\"}]\" \"{\\\"address\\\":2.41}\" 0 \"{\\\"address\\\":\\\"myasset\\\"}\"")
            + HelpExampleCli("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0,\\\"amount\\\":2.5}]\" \"{\\\"data\\\":\\\"00010203\\\"}\"")
            + HelpExampleRpc("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0,\\\"amount\\\":2.5}]\", \"{\\\"address\\\":2.41}\"")
            + HelpExampleRpc("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0,\\\"amount\\\":2.5,\\\"asset\\\":\\\"myasset\\\"}]\", \"{\\\"address\\\":2.41}\", 0, \"{\\\"address\\\":\\\"myasset\\\"}\"")
            + HelpExampleRpc("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0,\\\"amount\\\":2.5}]\", \"{\\\"data\\\":\\\"00010203\\\"}\"")
        );

    RPCTypeCheck(params, boost::assign::list_of(UniValue::VARR)(UniValue::VOBJ)(UniValue::VNUM)(UniValue::VOBJ), true);
    if (params[0].isNull() || params[1].isNull())
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, arguments 1 and 2 must be non-null");

    UniValue inputs = params[0].get_array();
    UniValue sendTo = params[1].get_obj();

    CMutableTransaction rawTx;

    if (params.size() > 2 && !params[2].isNull()) {
        int64_t nLockTime = params[2].get_int64();
        if (nLockTime < 0 || nLockTime > std::numeric_limits<uint32_t>::max())
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, locktime out of range");
        rawTx.nLockTime = nLockTime;
    }

    UniValue assets;
    if (params.size() > 3 && !params[3].isNull()) {
        assets = params[3].get_obj();
    }

    CAmountMap inputValue;

    for (unsigned int idx = 0; idx < inputs.size(); idx++) {
        const UniValue& input = inputs[idx];
        const UniValue& o = input.get_obj();

        uint256 txid = ParseHashO(o, "txid");
        const UniValue& vout_v = find_value(o, "vout");
        if (!vout_v.isNum())
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, missing vout key");
        int nOutput = vout_v.get_int();
        if (nOutput < 0)
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, vout must be positive");

        uint32_t nSequence = (rawTx.nLockTime ? std::numeric_limits<uint32_t>::max() - 1 : std::numeric_limits<uint32_t>::max());

        // set the sequence number if passed in the parameters object
        const UniValue& sequenceObj = find_value(o, "sequence");
        if (sequenceObj.isNum()) {
            int64_t seqNr64 = sequenceObj.get_int64();
            if (seqNr64 < 0 || seqNr64 > std::numeric_limits<uint32_t>::max())
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, sequence number is out of range");
            else
                nSequence = (uint32_t)seqNr64;
        }

        CTxIn in(COutPoint(txid, nOutput), CScript(), nSequence);

        CAsset asset(policyAsset);
        const UniValue& asset_val = find_value(o, "asset");
        if (asset_val.isStr()) {
            asset = CAsset(ParseHashO(o, "asset"));
        }

        UniValue vout_value = find_value(o, "amount");
        if (vout_value.isNull()) {
            LogPrintf("deprecated use of `nValue' in call to createrawtransaction --- use `amount' instead\n");
            vout_value = find_value(o, "nValue");
        }
        inputValue[asset] += AmountFromValue(vout_value);

        rawTx.vin.push_back(in);
    }

    set<CBitcoinAddress> setAddress;
    vector<string> addrList = sendTo.getKeys();
    BOOST_FOREACH(const string& name_, addrList) {
        // Defaults to policyAsset
        CAsset asset(policyAsset);
        if (!assets.isNull()) {
            if (find_value(assets, name_).isNull())
                throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, string("Given output_asset address is not a valid given output address: ")+name_);
            asset = CAsset(ParseHashO(assets, name_));
        }

        if (name_ == "data") {
            std::vector<unsigned char> data = ParseHexV(sendTo[name_].getValStr(),"Data");

            CTxOut out(asset, 0, CScript() << OP_RETURN << data);
            rawTx.vout.push_back(out);
        } else if (name_ == "fee") {
            CAmount nAmount = AmountFromValue(sendTo[name_]);
            CTxOut out(asset, nAmount, CScript());
            rawTx.vout.push_back(out);
        } else {
            CBitcoinAddress address(name_);
            if (!address.IsValid())
                throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, string("Invalid Bitcoin address: ")+name_);

            if (setAddress.count(address))
                throw JSONRPCError(RPC_INVALID_PARAMETER, string("Invalid parameter, duplicated address: ")+name_);
            setAddress.insert(address);

            CScript scriptPubKey = GetScriptForDestination(address.Get());
            CAmount nAmount = AmountFromValue(sendTo[name_]);

            CTxOut out(asset, nAmount, scriptPubKey);
            if (address.IsBlinded()) {
                CPubKey confidentiality_pubkey = address.GetBlindingKey();
                if (!confidentiality_pubkey.IsValid())
                     throw JSONRPCError(RPC_INVALID_PARAMETER, string("Invalid parameter: invalid confidentiality public key given"));
                out.nNonce.vchCommitment = std::vector<unsigned char>(confidentiality_pubkey.begin(), confidentiality_pubkey.end());
            }
            rawTx.vout.push_back(out);
        }
    }

    return EncodeHexTx(rawTx);
}

// Rewind the outputs to unblinded, and push placeholders for blinding info
void FillBlinds(CMutableTransaction& tx, bool fUseWallet, std::vector<uint256>& output_value_blinds, std::vector<uint256>& output_asset_blinds, std::vector<CPubKey>& output_pubkeys, std::vector<CKey>& asset_keys, std::vector<CKey>& token_keys) {
    for (size_t nOut = 0; nOut < tx.vout.size(); nOut++) {
        if (!tx.vout[nOut].nValue.IsExplicit()) {
            CTxOutWitness* ptxoutwit = tx.wit.vtxoutwit.size() <= nOut? NULL: &tx.wit.vtxoutwit[nOut];
            uint256 blinding_factor;
            uint256 asset_blinding_factor;
            CAsset asset;
            CAmount amount;
#ifdef ENABLE_WALLET
            // This can only be used to recover things like change addresses and self-sends.
            if (fUseWallet && ptxoutwit && UnblindConfidentialPair(pwalletMain->GetBlindingKey(&tx.vout[nOut].scriptPubKey), tx.vout[nOut].nValue, tx.vout[nOut].nAsset, tx.vout[nOut].nNonce, tx.vout[nOut].scriptPubKey, ptxoutwit->vchRangeproof, amount, blinding_factor, asset, asset_blinding_factor) != 0) {
                // Wipe out confidential info from output and output witness
                CScript scriptPubKey = tx.vout[nOut].scriptPubKey;
                CTxOut newOut(asset, amount, scriptPubKey);
                tx.vout[nOut] = newOut;
                ptxoutwit->SetNull();

                // Mark for re-blinding with same key that deblinded it
                CPubKey pubkey(pwalletMain->GetBlindingKey(&tx.vout[nOut].scriptPubKey).GetPubKey());
                output_pubkeys.push_back(pubkey);
                output_value_blinds.push_back(uint256());
                output_asset_blinds.push_back(uint256());
                continue;
            }
#endif
            // If no wallet, or unable to unblind, leave it alone in next blinding step
            output_pubkeys.push_back(CPubKey());
            output_value_blinds.push_back(uint256());
            output_asset_blinds.push_back(uint256());
        } else if (tx.vout[nOut].nNonce.IsNull()) {
            output_pubkeys.push_back(CPubKey());
            output_value_blinds.push_back(uint256());
            output_asset_blinds.push_back(uint256());
        } else {
            CPubKey pubkey(tx.vout[nOut].nNonce.vchCommitment);
            if (!pubkey.IsValid()) {
                 throw JSONRPCError(RPC_INVALID_PARAMETER, string("Invalid parameter: invalid confidentiality public key given"));
            }
            output_pubkeys.push_back(pubkey);
            output_value_blinds.push_back(uint256());
            output_asset_blinds.push_back(uint256());
        }
    }

    // Fill out issuance blinding keys to be used directly as nonce for rangeproof
    for (size_t nIn = 0; nIn < tx.vin.size(); nIn++) {
        CAssetIssuance& issuance = tx.vin[nIn].assetIssuance;
        if (issuance.IsNull()) {
            asset_keys.push_back(CKey());
            token_keys.push_back(CKey());
            continue;
        }

        // Calculate underlying asset for use as blinding key script
        CAsset asset;
        // New issuance, compute the asset ids
        if (issuance.assetBlindingNonce.IsNull()) {
            uint256 entropy;
            GenerateAssetEntropy(entropy, tx.vin[nIn].prevout, issuance.assetEntropy);
            CalculateAsset(asset, entropy);
        }
        // Re-issuance
        else {
            // TODO Give option to skip blinding when the reissuance token was derived without blinding ability. For now we assume blinded
            // hashAssetIdentifier doubles as the entropy on reissuance
            CalculateAsset(asset, issuance.assetEntropy);
        }

        // Special format for issuance blinding keys, unique for each transaction
        CScript blindingScript = CScript() << OP_RETURN << std::vector<unsigned char>(tx.vin[nIn].prevout.hash.begin(), tx.vin[nIn].prevout.hash.end()) << tx.vin[nIn].prevout.n;

        for (size_t nPseudo = 0; nPseudo < 2; nPseudo++) {
            CConfidentialValue& confValue = (nPseudo == 0) ? issuance.nAmount : issuance.nInflationKeys;
            if (confValue.IsCommitment()) {
                // Rangeproof must exist
                if (tx.wit.vtxinwit.size() <= nIn) {
                    throw JSONRPCError(RPC_INVALID_PARAMETER, string("Transaction issuance is already blinded but has no attached rangeproof."));
                }
                CTxInWitness& txinwit = tx.wit.vtxinwit[nIn];
                std::vector<unsigned char>& vchRangeproof = (nPseudo == 0) ? txinwit.vchIssuanceAmountRangeproof : txinwit.vchInflationKeysRangeproof;
                uint256 blinding_factor;
                uint256 asset_blinding_factor;
                CAmount amount;
#ifdef ENABLE_WALLET
                if (fUseWallet && UnblindConfidentialPair(pwalletMain->GetBlindingKey(&blindingScript), confValue, CConfidentialAsset(asset), CConfidentialNonce(), CScript(), vchRangeproof, amount, blinding_factor, asset, asset_blinding_factor) != 0) {
                    // Wipe out confidential info from issuance
                    vchRangeproof.clear();
                    confValue = CConfidentialValue(amount);
                    // One key both blinded values, single key needed for issuance reveal
                    asset_keys.push_back(pwalletMain->GetBlindingKey(&blindingScript));
                    token_keys.push_back(pwalletMain->GetBlindingKey(&blindingScript));
                    continue;
                }
#endif
                // If no wallet, or unable to unblind, leave it alone in next blinding step
                asset_keys.push_back(CKey());
                token_keys.push_back(CKey());
            } else {
                // Without wallet, nothing to be done.
                asset_keys.push_back(CKey());
                token_keys.push_back(CKey());
#ifdef ENABLE_WALLET
                // Use wallet to generate blindingkey used directly as nonce
                // as user is not "sending" to anyone.
                // Always assumed we want to blind here.
                // TODO Signal intent for all blinding via API including replacing nonce commitment
                if (fUseWallet) {
                    asset_keys[asset_keys.size()-1] = pwalletMain->GetBlindingKey(&blindingScript);
                    token_keys[token_keys.size()-1] = pwalletMain->GetBlindingKey(&blindingScript);
                }
#endif
            }
        }
    }
}

UniValue rawblindrawtransaction(const UniValue& params, bool fHelp)
{
    if (fHelp || (params.size() < 5 || params.size() > 7))
        throw runtime_error(
            "rawblindrawtransaction \"hexstring\" [\"inputblinder\",...] [\"inputamount\",...] [\"inputasset\",...] [\"inputassetblinder\",...] ( totalblinder, ignoreblindfail )\n"
            "\nConvert one or more outputs of a raw transaction into confidential ones.\n"
            "Returns the hex-encoded raw transaction.\n"
            "The input raw transaction cannot have already-blinded outputs.\n"
            "The output keys used can be specified by using a confidential address in createrawtransaction.\n"
            "If an additional blinded output is required to make a balanced blinding, a 0-value unspendable output will be added. Since there is no access to the wallet the blinding pubkey from the last output with blinding key will be repeated.\n"

            "\nArguments:\n"
            "1. \"hexstring\",          (string, required) A hex-encoded raw transaction.\n"
            "2. [                     (array, required) An array with one entry per transaction input.\n"
            "    \"inputblinder\"       (string, required) A hex-encoded blinding factor, one for each input.\n"
            "                         Blinding factors can be found in the \"blinder\" output of listunspent.\n"
            "   ],\n"
            "3. [                     (array, required) An array with one entry per transaction input.\n"
            "   \"inputamount\"       (numeric, required) An amount for each input.\n"
            "   ],\n"
            "4. [                     (array, required) An array with one entry per transaction input.\n"
            "   \"inputasset\"        (string, required) A hex-encoded asset id, one for each input.\n"
            "   ],\n"
            "5. [                     (array, required) An array with one entry per transaction input.\n"
            "   \"inputassetblinder\" (string, required) A hex-encoded asset blinding factor, one for each input.\n"
            "   ],\n"
            "6. \"totalblinder\"        (string, optional) Ignored for now.\n"
            "7. \"ignoreblindfail\"\"   (bool, optional, default=true) Return a transaction even when a blinding attempt fails due to number of blinded inputs/outputs.\n"

            "\nResult:\n"
            "\"transaction\"              (string) hex string of the transaction\n"
        );

    if (params.size() == 5) {
        RPCTypeCheck(params, boost::assign::list_of(UniValue::VSTR)(UniValue::VARR)(UniValue::VARR)(UniValue::VARR)(UniValue::VARR));
    } else if (params.size() == 6) {
        RPCTypeCheck(params, boost::assign::list_of(UniValue::VSTR)(UniValue::VARR)(UniValue::VARR)(UniValue::VARR)(UniValue::VARR)(UniValue::VSTR));
    } else {
        RPCTypeCheck(params, boost::assign::list_of(UniValue::VSTR)(UniValue::VARR)(UniValue::VARR)(UniValue::VARR)(UniValue::VARR)(UniValue::VSTR)(UniValue::VBOOL));
    }

    vector<unsigned char> txData(ParseHexV(params[0], "argument 1"));
    CDataStream ssData(txData, SER_NETWORK, PROTOCOL_VERSION);
    CMutableTransaction tx;
    try {
        ssData >> tx;
    } catch (const std::exception &) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    }

    UniValue inputBlinds = params[1].get_array();
    UniValue inputAmounts = params[2].get_array();
    UniValue inputAssets = params[3].get_array();
    UniValue inputAssetBlinds = params[4].get_array();

    bool fIgnoreBlindFail = true;
    if (params.size() > 6) {
        fIgnoreBlindFail = params[6].get_bool();
    }

    int n_blinded_ins = 0;

    if (inputBlinds.size() != tx.vin.size()) throw JSONRPCError(RPC_INVALID_PARAMETER, string("Invalid parameter: one (potentially empty) input blind for each input must be provided"));
    if (inputAmounts.size() != tx.vin.size()) throw JSONRPCError(RPC_INVALID_PARAMETER, string("Invalid parameter: one (potentially empty) input blind for each input must be provided"));
    if (inputAssets.size() != tx.vin.size()) throw JSONRPCError(RPC_INVALID_PARAMETER, string("Invalid parameter: one (potentially empty) input asset id for each input must be provided"));
    if (inputAssetBlinds.size() != tx.vin.size()) throw JSONRPCError(RPC_INVALID_PARAMETER, string("Invalid parameter: one (potentially empty) input asset blind for each input must be provided"));

    std::vector<CAmount> input_amounts;
    std::vector<uint256> input_blinds;
    std::vector<uint256> input_asset_blinds;
    std::vector<CAsset> input_assets;
    std::vector<uint256> output_value_blinds;
    std::vector<uint256> output_asset_blinds;
    std::vector<CAsset> output_assets;
    std::vector<CPubKey> output_pubkeys;
    for (size_t nIn = 0; nIn < tx.vin.size(); nIn++) {
        if (!inputBlinds[nIn].isStr())
            throw JSONRPCError(RPC_INVALID_PARAMETER, "input blinds must be an array of hex strings");
        if (!inputAssetBlinds[nIn].isStr())
            throw JSONRPCError(RPC_INVALID_PARAMETER, "input asset blinds must be an array of hex strings");
        if (!inputAssets[nIn].isStr())
            throw JSONRPCError(RPC_INVALID_PARAMETER, "input asset ids must be an array of hex strings");
        if (!inputAmounts[nIn].isNum())
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Amounts must be numeric.");

        std::string blind(inputBlinds[nIn].get_str());
        std::string assetblind(inputAssetBlinds[nIn].get_str());
        std::string asset(inputAssets[nIn].get_str());
        if (!IsHex(blind) || blind.length() != 32*2)
            throw JSONRPCError(RPC_INVALID_PARAMETER, "input blinds must be an array of 32-byte hex-encoded strings");
        if (!IsHex(assetblind) || assetblind.length() != 32*2)
            throw JSONRPCError(RPC_INVALID_PARAMETER, "input asset blinds must be an array of 32-byte hex-encoded strings");
        if (!IsHex(asset) || asset.length() != 32*2)
            throw JSONRPCError(RPC_INVALID_PARAMETER, "input asset blinds must be an array of 32-byte hex-encoded strings");

        input_blinds.push_back(uint256S(blind));
        input_asset_blinds.push_back(uint256S(assetblind));
        input_assets.push_back(CAsset(uint256S(asset)));
        input_amounts.push_back(inputAmounts[nIn].get_int64());

        if (!input_blinds.back().IsNull()) {
            n_blinded_ins++;
        }
    }

    std::vector<CKey> asset_keys;
    std::vector<CKey> token_keys;
    FillBlinds(tx, false, output_value_blinds, output_asset_blinds, output_pubkeys, asset_keys, token_keys);

    // How many are we trying to blind?
    int numPubKeys = 0;
    unsigned int keyIndex = 0;
    for (unsigned int i = 0; i < output_pubkeys.size(); i++) {
        const CPubKey& key = output_pubkeys[i];
        if (key.IsValid()) {
            numPubKeys++;
            keyIndex = i;
        }
    }

    if (numPubKeys == 0 && n_blinded_ins == 0) {
        // Vacuous, just return the transaction
        return EncodeHexTx(tx);
    } else if (n_blinded_ins > 0 && numPubKeys == 0) {
        // Blinded inputs need to balanced with something to be valid, make a dummy.
        // No privacy lost because all outputs are explicit anyways.
        CTxOut newTxOut(tx.vout.back().nAsset.GetAsset(), 0, CScript() << OP_RETURN);
        tx.vout.push_back(newTxOut);
        numPubKeys++;
        // Just copy some non-zero key
        output_pubkeys.push_back(output_pubkeys[keyIndex]);
    } else if (n_blinded_ins == 0 && numPubKeys == 1) {
        if (fIgnoreBlindFail) {
            // Just get rid of the ECDH key in the nonce field and return
            tx.vout[keyIndex].nNonce.SetNull();
            return EncodeHexTx(tx);
        } else {
            throw JSONRPCError(RPC_INVALID_PARAMETER, string("Unable to blind transaction: Add another output to blind in order to complete the blinding."));
        }
    }

    if (BlindTransaction(input_blinds, input_asset_blinds, input_assets, input_amounts, output_value_blinds, output_asset_blinds, output_pubkeys, std::vector<CKey>(), std::vector<CKey>(), tx) != numPubKeys) {
        // TODO Have more rich return values, communicating to user what has been blinded
        // User may be ok not blinding something that for instance has no corresponding type on input
        throw JSONRPCError(RPC_INVALID_PARAMETER, string("Unable to blind transaction: Are you sure each asset type to blind is represented in the inputs?"));
    }

    return EncodeHexTx(tx);
}

#ifdef ENABLE_WALLET
UniValue blindrawtransaction(const UniValue& params, bool fHelp)
{
    if (fHelp || (params.size() < 1 || params.size() > 4))
        throw runtime_error(
            "blindrawtransaction \"hexstring\" ( ignoreblindfail [\"assetcommitment,...\"] totalblinder )\n"
            "\nConvert one or more outputs of a raw transaction into confidential ones using only wallet inputs.\n"
            "Returns the hex-encoded raw transaction.\n"
            "The output keys used can be specified by using a confidential address in createrawtransaction.\n"
            "This call may add an additional 0-value unspendable output in order to balance the blinders.\n"

            "\nArguments:\n"
            "1. \"hexstring\",          (string, required) A hex-encoded raw transaction.\n"
            "2. \"ignoreblindfail\"\"   (bool, optional, default=true) Return a transaction even when a blinding attempt fails due to number of blinded inputs/outputs.\n"
            "3. [                       (array, optional) An array of input asset generators. If provided, this list must be empty, or match the final input commitment list, including ordering, to make a valid surjection proof. This list does not include generators for issuances, as these assets are inherently unblinded.\n"
            "    \"assetcommitment\"   (string, optional) A hex-encoded asset commitment, one for each input.\n"
            "                        Null commitments must be \"\".\n"
            "   ],\n"
            "4. \"totalblinder\"        (string, optional) Ignored for now.\n"

            "\nResult:\n"
            "\"transaction\"              (string) hex string of the transaction\n"
        );

    if (params.size() == 1) {
        RPCTypeCheck(params, boost::assign::list_of(UniValue::VSTR));
    } else if (params.size() == 2){
        RPCTypeCheck(params, boost::assign::list_of(UniValue::VSTR)(UniValue::VBOOL));
    } else if (params.size() == 3){
        RPCTypeCheck(params, boost::assign::list_of(UniValue::VSTR)(UniValue::VBOOL)(UniValue::VARR));
    } else {
        RPCTypeCheck(params, boost::assign::list_of(UniValue::VSTR)(UniValue::VBOOL)(UniValue::VARR)(UniValue::VSTR));
    }

    vector<unsigned char> txData(ParseHexV(params[0], "argument 1"));
    CDataStream ssData(txData, SER_NETWORK, PROTOCOL_VERSION);
    CMutableTransaction tx;
    try {
        ssData >> tx;
    } catch (const std::exception &) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    }

    bool fIgnoreBlindFail = true;
    if (params.size() > 1) {
        fIgnoreBlindFail = params[1].get_bool();
    }

    std::vector<std::vector<unsigned char> > auxiliary_generators;
    if (params.size() > 2) {
        UniValue assetCommitments = params[2].get_array();
        if (assetCommitments.size() != 0 && assetCommitments.size() < tx.vin.size()) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Asset commitment array must have at least as many entries as transaction inputs.");
        }
        for (size_t nIn = 0; nIn < assetCommitments.size(); nIn++) {
            if (assetCommitments[nIn].isStr()) {
                std::string assetcommitment = assetCommitments[nIn].get_str();
                if (IsHex(assetcommitment) && assetcommitment.size() == 66) {
                    auxiliary_generators.push_back(ParseHex(assetcommitment));
                    continue;
                }
            }
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Asset commitments must be a hex encoded string of length 66.");
        }
    }

    LOCK(pwalletMain->cs_wallet);

    std::vector<uint256> input_blinds;
    std::vector<uint256> input_asset_blinds;
    std::vector<CAsset> input_assets;
    std::vector<CAmount> input_amounts;
    std::vector<uint256> output_blinds;
    std::vector<uint256> output_asset_blinds;
    std::vector<CAsset> output_assets;
    std::vector<CPubKey> output_pubkeys;
    int n_blinded_ins = 0;
    for (size_t nIn = 0; nIn < tx.vin.size(); nIn++) {

        std::map<uint256, CWalletTx>::iterator it = pwalletMain->mapWallet.find(tx.vin[nIn].prevout.hash);
        if (it == pwalletMain->mapWallet.end()) {
            // For inputs we don't own input assetcommitments for the surjection must be supplied
            if (auxiliary_generators.size() > 0) {
                input_blinds.push_back(uint256());
                input_asset_blinds.push_back(uint256());
                input_assets.push_back(CAsset());
                input_amounts.push_back(-1);
                continue;
            }
            throw JSONRPCError(RPC_INVALID_PARAMETER, string("Invalid parameter: transaction spends from non-wallet output and no assetcommitment list was given."));
        }
        if (tx.vin[nIn].prevout.n >= it->second.vout.size()) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, string("Invalid parameter: transaction spends non-existing output"));
        }
        input_blinds.push_back(it->second.GetOutputBlindingFactor(tx.vin[nIn].prevout.n));
        input_asset_blinds.push_back(it->second.GetOutputAssetBlindingFactor(tx.vin[nIn].prevout.n));
        // These cases unneeded? If value is explicit we can still get via GetOutputX calls.
        if (it->second.vout[tx.vin[nIn].prevout.n].nAsset.IsExplicit()) {
            input_assets.push_back(it->second.vout[tx.vin[nIn].prevout.n].nAsset.GetAsset());
        }
        else {
            input_assets.push_back(it->second.GetOutputAsset(tx.vin[nIn].prevout.n));
        }
        if (it->second.vout[tx.vin[nIn].prevout.n].nValue.IsExplicit()) {
            input_amounts.push_back(it->second.vout[tx.vin[nIn].prevout.n].nValue.GetAmount());
        }
        else {
            input_amounts.push_back(it->second.GetOutputValueOut(tx.vin[nIn].prevout.n));
            n_blinded_ins += 1;
        }
    }

    std::vector<CKey> asset_keys;
    std::vector<CKey> token_keys;
    FillBlinds(tx, true, output_blinds, output_asset_blinds, output_pubkeys, asset_keys, token_keys);

    // How many are we trying to blind?
    int numPubKeys = 0;
    unsigned int keyIndex = 0;
    for (unsigned int i = 0; i < output_pubkeys.size(); i++) {
        const CPubKey& key = output_pubkeys[i];
        if (key.IsValid()) {
            numPubKeys++;
            keyIndex = i;
        }
    }

    if (numPubKeys == 0 && n_blinded_ins == 0) {
        // Vacuous, just return the transaction
        return EncodeHexTx(tx);
    } else if (n_blinded_ins > 0 && numPubKeys == 0) {
        // Blinded inputs need to balanced with something to be valid, make a dummy.
        // No privacy lost because all outputs are explicit anyways.
        CTxOut newTxOut(tx.vout.back().nAsset.GetAsset(), 0, CScript() << OP_RETURN);
        tx.vout.push_back(newTxOut);
        numPubKeys++;
        output_pubkeys.push_back(pwalletMain->GetBlindingPubKey(newTxOut.scriptPubKey));
    } else if (n_blinded_ins == 0 && numPubKeys == 1) {
        if (fIgnoreBlindFail) {
            // Just get rid of the ECDH key in the nonce field and return
            tx.vout[keyIndex].nNonce.SetNull();
            return EncodeHexTx(tx);
        } else {
            throw JSONRPCError(RPC_INVALID_PARAMETER, string("Unable to blind transaction: Add another output to blind in order to complete the blinding."));
        }
    }

    if (BlindTransaction(input_blinds, input_asset_blinds, input_assets, input_amounts, output_blinds, output_asset_blinds, output_pubkeys, std::vector<CKey>(), std::vector<CKey>(), tx, (auxiliary_generators.size() ? &auxiliary_generators : NULL)) != numPubKeys) {
        // TODO Have more rich return values, communicating to user what has been blinded
        // User may be ok not blinding something that for instance has no corresponding type on input
        throw JSONRPCError(RPC_INVALID_PARAMETER, string("Unable to blind transaction: Are you sure each asset type to blind is represented in the inputs?"));
    }

    return EncodeHexTx(tx);
}
#endif

UniValue decoderawtransaction(const UniValue& params, bool fHelp)
{
    if (fHelp || params.size() != 1)
        throw runtime_error(
            "decoderawtransaction \"hexstring\"\n"
            "\nReturn a JSON object representing the serialized, hex-encoded transaction.\n"

            "\nArguments:\n"
            "1. \"hex\"      (string, required) The transaction hex string\n"

            "\nResult:\n"
            "{\n"
            "  \"txid\" : \"id\",        (string) The transaction id\n"
            "  \"hash\" : \"id\",        (string) The transaction hash (differs from txid for witness transactions)\n"
            "  \"size\" : n,             (numeric) The transaction size\n"
            "  \"vsize\" : n,            (numeric) The virtual transaction size (differs from size for witness transactions)\n"
            "  \"version\" : n,          (numeric) The version\n"
            "  \"locktime\" : ttt,       (numeric) The lock time\n"
            "  \"fee\" : x.xxx,          (numeric) The transaction fee in " + CURRENCY_UNIT + "\n"
            "  \"vin\" : [               (array of json objects)\n"
            "     {\n"
            "       \"txid\": \"id\",    (string) The transaction id\n"
            "       \"vout\": n,         (numeric) The output number\n"
            "       \"scriptSig\": {     (json object) The script\n"
            "         \"asm\": \"asm\",  (string) asm\n"
            "         \"hex\": \"hex\"   (string) hex\n"
            "       },\n"
            "       \"txinwitness\": [\"hex\", ...] (array of string) hex-encoded witness data (if any)\n"
            "       \"sequence\": n     (numeric) The script sequence number\n"
            "     }\n"
            "     ,...\n"
            "  ],\n"
            "  \"vout\" : [             (array of json objects)\n"
            "     {\n"
            "       \"value\" : x.xxx,            (numeric) The value in " + CURRENCY_UNIT + "\n"
            "       \"n\" : n,                    (numeric) index\n"
            "       \"asset\" : \"hex\"           (string) the asset id, if unblinded\n"
            "       \"assetcommitment\" : \"hex\" (string) the asset tag, if blinded\n"
            "       \"scriptPubKey\" : {          (json object)\n"
            "         \"asm\" : \"asm\",          (string) the asm\n"
            "         \"hex\" : \"hex\",          (string) the hex\n"
            "         \"reqSigs\" : n,            (numeric) The required sigs\n"
            "         \"type\" : \"pubkeyhash\",  (string) The type, eg 'pubkeyhash'\n"
            "         \"addresses\" : [           (json array of string)\n"
            "           \"12tvKAXCxZjSmdNbao16dKXC8tRWfcF5oc\"   (string) bitcoin address\n"
            "           ,...\n"
            "         ]\n"
            "       }\n"
            "     }\n"
            "     ,...\n"
            "  ],\n"
            "}\n"

            "\nExamples:\n"
            + HelpExampleCli("decoderawtransaction", "\"hexstring\"")
            + HelpExampleRpc("decoderawtransaction", "\"hexstring\"")
        );

    LOCK(cs_main);
    RPCTypeCheck(params, boost::assign::list_of(UniValue::VSTR));

    CTransaction tx;

    if (!DecodeHexTx(tx, params[0].get_str(), true))
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");

    UniValue result(UniValue::VOBJ);
    TxToJSON(tx, uint256(), result);

    return result;
}

UniValue decodescript(const UniValue& params, bool fHelp)
{
    if (fHelp || params.size() != 1)
        throw runtime_error(
            "decodescript \"hex\"\n"
            "\nDecode a hex-encoded script.\n"
            "\nArguments:\n"
            "1. \"hex\"     (string) the hex encoded script\n"
            "\nResult:\n"
            "{\n"
            "  \"asm\":\"asm\",   (string) Script public key\n"
            "  \"hex\":\"hex\",   (string) hex encoded public key\n"
            "  \"type\":\"type\", (string) The output type\n"
            "  \"reqSigs\": n,    (numeric) The required signatures\n"
            "  \"addresses\": [   (json array of string)\n"
            "     \"address\"     (string) bitcoin address\n"
            "     ,...\n"
            "  ],\n"
            "  \"p2sh\",\"address\" (string) script address\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("decodescript", "\"hexstring\"")
            + HelpExampleRpc("decodescript", "\"hexstring\"")
        );

    RPCTypeCheck(params, boost::assign::list_of(UniValue::VSTR));

    UniValue r(UniValue::VOBJ);
    CScript script;
    if (params[0].get_str().size() > 0){
        vector<unsigned char> scriptData(ParseHexV(params[0], "argument"));
        script = CScript(scriptData.begin(), scriptData.end());
    } else {
        // Empty scripts are valid
    }
    ScriptPubKeyToJSON(script, r, false);

    r.push_back(Pair("p2sh", CBitcoinAddress(CScriptID(script)).ToString()));
    return r;
}

/** Pushes a JSON object for script verification or signing errors to vErrorsRet. */
static void TxInErrorToJSON(const CTxIn& txin, UniValue& vErrorsRet, const std::string& strMessage)
{
    UniValue entry(UniValue::VOBJ);
    entry.push_back(Pair("txid", txin.prevout.hash.ToString()));
    entry.push_back(Pair("vout", (uint64_t)txin.prevout.n));
    entry.push_back(Pair("scriptSig", HexStr(txin.scriptSig.begin(), txin.scriptSig.end())));
    entry.push_back(Pair("sequence", (uint64_t)txin.nSequence));
    entry.push_back(Pair("error", strMessage));
    vErrorsRet.push_back(entry);
}

UniValue signrawtransaction(const UniValue& params, bool fHelp)
{
    if (fHelp || params.size() < 1 || params.size() > 4)
        throw runtime_error(
            "signrawtransaction \"hexstring\" ( [{\"txid\":\"id\",\"vout\":n,\"scriptPubKey\":\"hex\",\"redeemScript\":\"hex\"},...] [\"privatekey1\",...] sighashtype )\n"
            "\nSign inputs for raw transaction (serialized, hex-encoded).\n"
            "The second optional argument (may be null) is an array of previous transaction outputs that\n"
            "this transaction depends on but may not yet be in the block chain.\n"
            "The third optional argument (may be null) is an array of base58-encoded private\n"
            "keys that, if given, will be the only keys used to sign the transaction.\n"
#ifdef ENABLE_WALLET
            + HelpRequiringPassphrase() + "\n"
#endif

            "\nArguments:\n"
            "1. \"hexstring\"     (string, required) The transaction hex string\n"
            "2. \"prevtxs\"       (string, optional) An json array of previous dependent transaction outputs\n"
            "     [               (json array of json objects, or 'null' if none provided)\n"
            "       {\n"
            "         \"txid\":\"id\",             (string, required) The transaction id\n"
            "         \"vout\":n,                  (numeric, required) The output number\n"
            "         \"scriptPubKey\": \"hex\",   (string, required) script key\n"
            "         \"redeemScript\": \"hex\",   (string, required for P2SH or P2WSH) redeem script\n"
            "         \"amount\": value            (numeric, required) The amount spent\n"
            "       }\n"
            "       ,...\n"
            "    ]\n"
            "3. \"privatekeys\"     (string, optional) A json array of base58-encoded private keys for signing\n"
            "    [                  (json array of strings, or 'null' if none provided)\n"
            "      \"privatekey\"   (string) private key in base58-encoding\n"
            "      ,...\n"
            "    ]\n"
            "4. \"sighashtype\"     (string, optional, default=ALL) The signature hash type. Must be one of\n"
            "       \"ALL\"\n"
            "       \"NONE\"\n"
            "       \"SINGLE\"\n"
            "       \"ALL|ANYONECANPAY\"\n"
            "       \"NONE|ANYONECANPAY\"\n"
            "       \"SINGLE|ANYONECANPAY\"\n"

            "\nResult:\n"
            "{\n"
            "  \"hex\" : \"value\",           (string) The hex-encoded raw transaction with signature(s)\n"
            "  \"complete\" : true|false,   (boolean) If the transaction has a complete set of signatures\n"
            "  \"errors\" : [                 (json array of objects) Script verification errors (if there are any)\n"
            "    {\n"
            "      \"txid\" : \"hash\",           (string) The hash of the referenced, previous transaction\n"
            "      \"vout\" : n,                (numeric) The index of the output to spent and used as input\n"
            "      \"scriptSig\" : \"hex\",       (string) The hex-encoded signature script\n"
            "      \"sequence\" : n,            (numeric) Script sequence number\n"
            "      \"error\" : \"text\"           (string) Verification or signing error related to the input\n"
            "    }\n"
            "    ,...\n"
            "  ]\n"
            "}\n"

            "\nExamples:\n"
            + HelpExampleCli("signrawtransaction", "\"myhex\"")
            + HelpExampleRpc("signrawtransaction", "\"myhex\"")
        );

#ifdef ENABLE_WALLET
    LOCK2(cs_main, pwalletMain ? &pwalletMain->cs_wallet : NULL);
#else
    LOCK(cs_main);
#endif
    RPCTypeCheck(params, boost::assign::list_of(UniValue::VSTR)(UniValue::VARR)(UniValue::VARR)(UniValue::VSTR), true);

    vector<unsigned char> txData(ParseHexV(params[0], "argument 1"));
    CDataStream ssData(txData, SER_NETWORK, PROTOCOL_VERSION);
    vector<CMutableTransaction> txVariants;
    while (!ssData.empty()) {
        try {
            CMutableTransaction tx;
            ssData >> tx;
            txVariants.push_back(tx);
        }
        catch (const std::exception&) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
        }
    }

    if (txVariants.empty())
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Missing transaction");

    // mergedTx will end up with all the signatures; it
    // starts as a clone of the rawtx:
    CMutableTransaction mergedTx(txVariants[0]);

    // Fetch previous transactions (inputs):
    CCoinsView viewDummy;
    CCoinsViewCache view(&viewDummy);
    {
        LOCK(mempool.cs);
        CCoinsViewCache &viewChain = *pcoinsTip;
        CCoinsViewMemPool viewMempool(&viewChain, mempool);
        view.SetBackend(viewMempool); // temporarily switch cache backend to db+mempool view

        BOOST_FOREACH(const CTxIn& txin, mergedTx.vin) {
            const uint256& prevHash = txin.prevout.hash;
            CCoins coins;
            view.AccessCoins(prevHash); // this is certainly allowed to fail
        }

        view.SetBackend(viewDummy); // switch back to avoid locking mempool for too long
    }

    bool fGivenKeys = false;
    CBasicKeyStore tempKeystore;
    if (params.size() > 2 && !params[2].isNull()) {
        fGivenKeys = true;
        UniValue keys = params[2].get_array();
        for (unsigned int idx = 0; idx < keys.size(); idx++) {
            UniValue k = keys[idx];
            CBitcoinSecret vchSecret;
            bool fGood = vchSecret.SetString(k.get_str());
            if (!fGood)
                throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid private key");
            CKey key = vchSecret.GetKey();
            if (!key.IsValid())
                throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Private key outside allowed range");
            tempKeystore.AddKey(key);
        }
    }
#ifdef ENABLE_WALLET
    else if (pwalletMain)
        EnsureWalletIsUnlocked();
#endif

    // Add previous txouts given in the RPC call:
    if (params.size() > 1 && !params[1].isNull()) {
        UniValue prevTxs = params[1].get_array();
        for (unsigned int idx = 0; idx < prevTxs.size(); idx++) {
            const UniValue& p = prevTxs[idx];
            if (!p.isObject())
                throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "expected object with {\"txid'\",\"vout\",\"scriptPubKey\"}");

            UniValue prevOut = p.get_obj();

            RPCTypeCheckObj(prevOut,
                {
                    {"txid", UniValueType(UniValue::VSTR)},
                    {"vout", UniValueType(UniValue::VNUM)},
                    {"scriptPubKey", UniValueType(UniValue::VSTR)},
                });

            uint256 txid = ParseHashO(prevOut, "txid");

            int nOut = find_value(prevOut, "vout").get_int();
            if (nOut < 0)
                throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "vout must be positive");

            vector<unsigned char> pkData(ParseHexO(prevOut, "scriptPubKey"));
            CScript scriptPubKey(pkData.begin(), pkData.end());

            {
                CCoinsModifier coins = view.ModifyCoins(txid);
                if (coins->IsAvailable(nOut) && coins->vout[nOut].scriptPubKey != scriptPubKey) {
                    string err("Previous output scriptPubKey mismatch:\n");
                    err = err + ScriptToAsmStr(coins->vout[nOut].scriptPubKey) + "\nvs:\n"+
                        ScriptToAsmStr(scriptPubKey);
                    throw JSONRPCError(RPC_DESERIALIZATION_ERROR, err);
                }
                if ((unsigned int)nOut >= coins->vout.size())
                    coins->vout.resize(nOut+1);
                coins->vout[nOut].scriptPubKey = scriptPubKey;
                coins->vout[nOut].nValue = 0;
                if (prevOut.exists("amount")) {
                    coins->vout[nOut].nValue = AmountFromValue(find_value(prevOut, "amount"));
                }
            }

            // if redeemScript given and not using the local wallet (private keys
            // given), add redeemScript to the tempKeystore so it can be signed:
            if (fGivenKeys && (scriptPubKey.IsPayToScriptHash() || scriptPubKey.IsPayToWitnessScriptHash())) {
                RPCTypeCheckObj(prevOut,
                    {
                        {"txid", UniValueType(UniValue::VSTR)},
                        {"vout", UniValueType(UniValue::VNUM)},
                        {"scriptPubKey", UniValueType(UniValue::VSTR)},
                        {"redeemScript", UniValueType(UniValue::VSTR)},
                    });
                UniValue v = find_value(prevOut, "redeemScript");
                if (!v.isNull()) {
                    vector<unsigned char> rsData(ParseHexV(v, "redeemScript"));
                    CScript redeemScript(rsData.begin(), rsData.end());
                    tempKeystore.AddCScript(redeemScript);
                }
            }
        }
    }

#ifdef ENABLE_WALLET
    const CKeyStore& keystore = ((fGivenKeys || !pwalletMain) ? tempKeystore : *pwalletMain);
#else
    const CKeyStore& keystore = tempKeystore;
#endif

    int nHashType = SIGHASH_ALL;
    if (params.size() > 3 && !params[3].isNull()) {
        static map<string, int> mapSigHashValues =
            boost::assign::map_list_of
            (string("ALL"), int(SIGHASH_ALL))
            (string("ALL|ANYONECANPAY"), int(SIGHASH_ALL|SIGHASH_ANYONECANPAY))
            (string("NONE"), int(SIGHASH_NONE))
            (string("NONE|ANYONECANPAY"), int(SIGHASH_NONE|SIGHASH_ANYONECANPAY))
            (string("SINGLE"), int(SIGHASH_SINGLE))
            (string("SINGLE|ANYONECANPAY"), int(SIGHASH_SINGLE|SIGHASH_ANYONECANPAY))
            ;
        string strHashType = params[3].get_str();
        if (mapSigHashValues.count(strHashType))
            nHashType = mapSigHashValues[strHashType];
        else
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid sighash param");
    }

    bool fHashSingle = ((nHashType & ~SIGHASH_ANYONECANPAY) == SIGHASH_SINGLE);

    // Script verification errors
    UniValue vErrors(UniValue::VARR);

    // Use CTransaction for the constant parts of the
    // transaction to avoid rehashing.
    const CTransaction txConst(mergedTx);
    // Sign what we can:
    for (unsigned int i = 0; i < mergedTx.vin.size(); i++) {
        CTxIn& txin = mergedTx.vin[i];
        const CCoins* coins = view.AccessCoins(txin.prevout.hash);
        if (coins == NULL || !coins->IsAvailable(txin.prevout.n)) {
            TxInErrorToJSON(txin, vErrors, "Input not found or already spent");
            continue;
        }
        const CScript& prevPubKey = coins->vout[txin.prevout.n].scriptPubKey;
        const CConfidentialValue& amount = coins->vout[txin.prevout.n].nValue;

        SignatureData sigdata;
        // Only sign SIGHASH_SINGLE if there's a corresponding output:
        if (!fHashSingle || (i < mergedTx.vout.size()))
            ProduceSignature(MutableTransactionSignatureCreator(&keystore, &mergedTx, i, amount, nHashType), prevPubKey, sigdata);

        // ... and merge in other signatures:
        BOOST_FOREACH(const CMutableTransaction& txv, txVariants) {
            sigdata = CombineSignatures(prevPubKey, MutableTransactionNoWithdrawsSignatureChecker(&mergedTx, i, amount), sigdata, DataFromTransaction(txv, i));
        }

        UpdateTransaction(mergedTx, i, sigdata);

        ScriptError serror = SCRIPT_ERR_OK;
        if (!VerifyScript(txin.scriptSig, prevPubKey, mergedTx.wit.vtxinwit.size() > i ? &mergedTx.wit.vtxinwit[i].scriptWitness : NULL, STANDARD_SCRIPT_VERIFY_FLAGS, MutableTransactionNoWithdrawsSignatureChecker(&mergedTx, i, amount), &serror)) {
            TxInErrorToJSON(txin, vErrors, ScriptErrorString(serror));
        }
    }
    bool fComplete = vErrors.empty();

    UniValue result(UniValue::VOBJ);
    result.push_back(Pair("hex", EncodeHexTx(mergedTx)));
    result.push_back(Pair("complete", fComplete));
    if (!vErrors.empty()) {
        result.push_back(Pair("errors", vErrors));
    }

    AuditLogPrintf("%s : signrawtransaction %s\n", getUser(), EncodeHexTx(mergedTx));

    return result;
}

UniValue sendrawtransaction(const UniValue& params, bool fHelp)
{
    if (fHelp || params.size() < 1 || params.size() > 3)
        throw runtime_error(
            "sendrawtransaction \"hexstring\" ( allowhighfees ) ( allowunblindfails )\n"
            "\nSubmits raw transaction (serialized, hex-encoded) to local node and network.\n"
            "\nAlso see createrawtransaction and signrawtransaction calls.\n"
            "\nArguments:\n"
            "1. \"hexstring\"    (string, required) The hex string of the raw transaction)\n"
            "2. allowhighfees    (boolean, optional, default=false) Allow high fees\n"
            "3. allowblindfails  (boolean, optional, default=false) Allow outputs which have a pubkey attached (ie are blindable), which are unblinded\n"
            "\nResult:\n"
            "\"hex\"             (string) The transaction hash in hex\n"
            "\nExamples:\n"
            "\nCreate a transaction\n"
            + HelpExampleCli("createrawtransaction", "\"[{\\\"txid\\\" : \\\"mytxid\\\",\\\"vout\\\":0}]\" \"{\\\"myaddress\\\":0.01}\"") +
            "Sign the transaction, and get back the hex\n"
            + HelpExampleCli("signrawtransaction", "\"myhex\"") +
            "\nSend the transaction (signed hex)\n"
            + HelpExampleCli("sendrawtransaction", "\"signedhex\"") +
            "\nAs a json rpc call\n"
            + HelpExampleRpc("sendrawtransaction", "\"signedhex\"")
        );

    LOCK(cs_main);
    RPCTypeCheck(params, boost::assign::list_of(UniValue::VSTR)(UniValue::VBOOL)(UniValue::VBOOL));

    // parse hex string from parameter
    CTransaction tx;
    if (!DecodeHexTx(tx, params[0].get_str()))
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    uint256 hashTx = tx.GetHash();

    CAmount nMaxRawTxFee = maxTxFee;
    if (params.size() > 1 && params[1].get_bool())
        nMaxRawTxFee = 0;

    bool fOverrideBlindable = false;
    if (params.size() > 2)
        fOverrideBlindable = params[2].get_bool();

    if (!fOverrideBlindable) {
        for (unsigned i = 0; i < tx.vout.size(); i++) {
            const CTxOut& txout = tx.vout[i];
            if (txout.nValue.IsExplicit() && txout.nNonce.vchCommitment.size() != 0)
                throw JSONRPCError(RPC_TRANSACTION_ERROR, strprintf("Output %u is unblinded, but has blinding pubkey attached, please use [raw]blindrawtransaction", i));
        }
    }

    CCoinsViewCache &view = *pcoinsTip;
    const CCoins* existingCoins = view.AccessCoins(hashTx);
    bool fHaveMempool = mempool.exists(hashTx);
    bool fHaveChain = existingCoins && existingCoins->nHeight < 1000000000;
    if (!fHaveMempool && !fHaveChain) {
        // push to local node and sync with wallets
        CValidationState state;
        bool fMissingInputs;
        if (!AcceptToMemoryPool(mempool, state, tx, false, &fMissingInputs, false, nMaxRawTxFee)) {
            if (state.IsInvalid()) {
                throw JSONRPCError(RPC_TRANSACTION_REJECTED, strprintf("%i: %s", state.GetRejectCode(), state.GetRejectReason()));
            } else {
                if (fMissingInputs) {
                    throw JSONRPCError(RPC_TRANSACTION_ERROR, "Missing inputs");
                }
                throw JSONRPCError(RPC_TRANSACTION_ERROR, state.GetRejectReason());
            }
        }
    } else if (fHaveChain) {
        throw JSONRPCError(RPC_TRANSACTION_ALREADY_IN_CHAIN, "transaction already in block chain");
    }
    RelayTransaction(tx);

    AuditLogPrintf("%s : sendrawtransaction %s\n", getUser(), tx.ToString());

    return hashTx.GetHex();
}

static const CRPCCommand commands[] =
{ //  category              name                      actor (function)         okSafeMode
  //  --------------------- ------------------------  -----------------------  ----------
    { "rawtransactions",    "getrawtransaction",      &getrawtransaction,      true  },
    { "rawtransactions",    "createrawtransaction",   &createrawtransaction,   true  },
    { "rawtransactions",    "decoderawtransaction",   &decoderawtransaction,   true  },
    { "rawtransactions",    "decodescript",           &decodescript,           true  },
    { "rawtransactions",    "sendrawtransaction",     &sendrawtransaction,     false },
    { "rawtransactions",    "signrawtransaction",     &signrawtransaction,     false }, /* uses wallet if enabled */
    { "rawtransactions",    "rawblindrawtransaction", &rawblindrawtransaction, false },
#ifdef ENABLE_WALLET
    { "rawtransactions",    "blindrawtransaction",    &blindrawtransaction,    true  },
#endif
    { "blockchain",         "gettxoutproof",          &gettxoutproof,          true  },
    { "blockchain",         "verifytxoutproof",       &verifytxoutproof,       true  },
};

void RegisterRawTransactionRPCCommands(CRPCTable &tableRPC)
{
    for (unsigned int vcidx = 0; vcidx < ARRAYLEN(commands); vcidx++)
        tableRPC.appendCommand(commands[vcidx].name, &commands[vcidx]);
}
