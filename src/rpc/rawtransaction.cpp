// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
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
#include "validation.h"
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
#include "global/common.h"
#include "assetsdir.h"
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

static void SidehainScriptPubKeyToJSON(const CScript& scriptPubKey, UniValue& out, bool fIncludeHex, bool is_parent_chain)
{
    const std::string prefix = is_parent_chain ? "pegout_" : "";
    txnouttype type;
    vector<CTxDestination> addresses;
    int nRequired;
    out.push_back(Pair(prefix + "asm", ScriptToAsmStr(scriptPubKey)));
    if (fIncludeHex)
        out.push_back(Pair(prefix + "hex", HexStr(scriptPubKey.begin(), scriptPubKey.end())));
    if (!ExtractDestinations(scriptPubKey, type, addresses, nRequired)) {
        out.push_back(Pair(prefix + "type", GetTxnOutputType(type)));
        return;
    }
    out.push_back(Pair(prefix + "reqSigs", nRequired));
    out.push_back(Pair(prefix + "type", GetTxnOutputType(type)));
    UniValue a(UniValue::VARR);
    if (is_parent_chain) {
        for (CTxDestination const &addr : addresses)
            a.push_back(CParentBitcoinAddress(addr).ToString());
    } else {
        for(CTxDestination const &addr : addresses)
            a.push_back(CBitcoinAddress(addr).ToString());
    }
    out.push_back(Pair(prefix + "addresses", a));
}

void ScriptPubKeyToJSON(const CScript& scriptPubKey, UniValue& out, bool fIncludeHex)
{
    SidehainScriptPubKeyToJSON(scriptPubKey, out, fIncludeHex, false);
    uint256 pegout_chain;
    CScript pegout_scriptpubkey;
    if (scriptPubKey.IsPegoutScript(pegout_chain, pegout_scriptpubkey)) {
        out.push_back(Pair("pegout_chain", pegout_chain.GetHex()));
        SidehainScriptPubKeyToJSON(pegout_scriptpubkey, out, fIncludeHex, true);
    }
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
            in.push_back(Pair("is_pegin", txin.m_is_pegin));
        }
        if (tx.HasWitness()) {
            UniValue scriptWitness(UniValue::VARR);
            UniValue pegin_witness(UniValue::VARR);
            if (tx.wit.vtxinwit.size() > i) {
                for (unsigned int j = 0; j < tx.wit.vtxinwit[i].scriptWitness.stack.size(); j++) {
                    std::vector<unsigned char> item = tx.wit.vtxinwit[i].scriptWitness.stack[j];
                    scriptWitness.push_back(HexStr(item.begin(), item.end()));
                }
                for (unsigned int j = 0; j < tx.wit.vtxinwit[i].m_pegin_witness.stack.size(); j++) {
                    std::vector<unsigned char> item = tx.wit.vtxinwit[i].m_pegin_witness.stack[j];
                    pegin_witness.push_back(HexStr(item.begin(), item.end()));
                }
            }
            in.push_back(Pair("scriptWitness", scriptWitness));
            in.push_back(Pair("pegin_witness", pegin_witness));
        }
        const CAssetIssuance& issuance = txin.assetIssuance;
        if (!issuance.IsNull()) {
            UniValue issue(UniValue::VOBJ);
            issue.push_back(Pair("assetBlindingNonce", issuance.assetBlindingNonce.GetHex()));
            CAsset asset;
            CAsset token;
            uint256 entropy;
            if (!issuance.IsReissuance()) {
                GenerateAssetEntropy(entropy, txin.prevout, issuance.assetEntropy);
                issue.push_back(Pair("assetEntropy", entropy.GetHex()));
                CalculateAsset(asset, entropy);
                CalculateReissuanceToken(token, entropy, issuance.nAmount.IsCommitment());
                issue.push_back(Pair("isreissuance", false));
                issue.push_back(Pair("token", token.GetHex()));
            }
            else {
                issue.push_back(Pair("assetEntropy", issuance.assetEntropy.GetHex()));
                issue.push_back(Pair("isreissuance", true));
                CalculateAsset(asset, issuance.assetEntropy);
            }
            issue.push_back(Pair("asset", asset.GetHex()));
            if (issuance.nAmount.IsExplicit()) {
                issue.push_back(Pair("assetamount", ValueFromAmount(issuance.nAmount.GetAmount())));
            } else if (issuance.nAmount.IsCommitment()) {
                issue.push_back(Pair("assetamountcommitment", HexStr(issuance.nAmount.vchCommitment)));
            }
            if (issuance.nInflationKeys.IsExplicit()) {
                issue.push_back(Pair("tokenamount", ValueFromAmount(issuance.nInflationKeys.GetAmount())));
            } else if (issuance.nInflationKeys.IsCommitment()) {
                issue.push_back(Pair("tokenamountcommitment", HexStr(issuance.nInflationKeys.vchCommitment)));
            }
            const std::string policyLabel = gAssetsDir.GetLabel(asset);
            if (policyLabel != "") 
            {
                issue.push_back(Pair("assetlabel", policyLabel));
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
        if (txout.nValue.IsExplicit()) {
            out.push_back(Pair("value", ValueFromAmount(txout.nValue.GetAmount())));
        } else {
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
            out.push_back(Pair("amountcommitment", HexStr(txout.nValue.vchCommitment)));
        }
        const CConfidentialAsset& asset = txout.nAsset;
        if (asset.IsExplicit()) {
            out.push_back(Pair("asset", asset.GetAsset().GetHex()));
        } else if (asset.IsCommitment()) {
            out.push_back(Pair("assetcommitment", HexStr(asset.vchCommitment)));
        }
        if (asset.IsExplicit()) {
            std::string policyLabel = gAssetsDir.GetLabel(asset.GetAsset());
            if (policyLabel != "") 
            {
                out.push_back(Pair("assetlabel", policyLabel));
            }
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

UniValue getrawtransaction(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() < 1 || request.params.size() > 2)
        throw runtime_error(
            "getrawtransaction \"txid\" ( verbose )\n"
            "\nNOTE: By default this function only works for mempool transactions. If the -txindex option is\n"
            "enabled, it also works for blockchain transactions.\n"
            "DEPRECATED: for now, it also works for transactions with unspent outputs.\n"
            "\nReturn the raw transaction data.\n"
            "\nIf verbose is 'true', returns an Object with information about 'txid'.\n"
            "If verbose is 'false' or omitted, returns a string that is serialized, hex-encoded data for 'txid'.\n"
            "\nArguments:\n"
            "1. \"txid\"      (string, required) The transaction id\n"
            "2. verbose       (bool, optional, default=false) If false, return a string, otherwise return a json object\n"
            "\nResult (if verbose is not set or set to false):\n"
            "\"data\"      (string) The serialized, hex-encoded data for 'txid'\n"
            "\nResult (if verbose is set to true):\n"
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
            "       \"issuance\"         (object) Info on issuance\n"
            "     }\n"
            "     ,...\n"
            "  ],\n"
            "  \"vout\" : [              (array of json objects)\n"
            "     {\n"
            "       \"value\" : x.xxx,            (numeric) The value in " + CURRENCY_UNIT + "\n"
            "       \"amountcommitment\": \"hex\",     (string) the output's value commitment, if blinded\n"
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
            "           \"address\"        (string) ocean address\n"
            "           ,...\n"
            "         ]\n"
            "         \"pegout_chain\" : \"hex\", (string) (only pegout) Hash of genesis block of parent chain'\n"
            "         \"pegout_asm\":\"asm\",     (string) (only pegout) pegout scriptpubkey (asm)'\n"
            "         \"pegout_hex\":\"hex\",     (string) (only pegout) pegout scriptpubkey (hex)'\n"
            "         \"pegout_reqSigs\" : n,     (numeric) (only pegout) pegout required sigs\n"
            "         \"pegout_type\" : \"pubkeyhash\", (string) (only pegout) The pegout type, eg 'pubkeyhash'\n"
            "         \"pegout_addresses\" : [    (json array of string) (only pegout)\n"
            "           \"address\"        (string) bitcoin address\n"
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
            + HelpExampleCli("getrawtransaction", "\"mytxid\" true")
            + HelpExampleRpc("getrawtransaction", "\"mytxid\", true")
        );
    LOCK(cs_main);
    uint256 hash = ParseHashV(request.params[0], "parameter 1");
    // Accept either a bool (true) or a num (>=1) to indicate verbose output.
    bool fVerbose = false;
    if (request.params.size() > 1) {
        if (request.params[1].isNum()) {
            if (request.params[1].get_int() != 0) {
                fVerbose = true;
            }
        }
        else if(request.params[1].isBool()) {
            if(request.params[1].isTrue()) {
                fVerbose = true;
            }
        }
        else {
            throw JSONRPCError(RPC_TYPE_ERROR, "Invalid type provided. Verbose parameter must be a boolean.");
        }
    }
    CTransactionRef tx;
    uint256 hashBlock;
    if (!GetTransaction(hash, tx, Params().GetConsensus(), hashBlock, true))
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, std::string(fTxIndex ? "No such mempool or blockchain transaction"
            : "No such mempool transaction. Use -txindex to enable blockchain transaction queries") +
            ". Use gettransaction for wallet transactions.");
    string strHex = EncodeHexTx(*tx, RPCSerializationFlags());
    if (!fVerbose)
        return strHex;
    UniValue result(UniValue::VOBJ);
    result.push_back(Pair("hex", strHex));
    TxToJSON(*tx, hashBlock, result);
    return result;
}

UniValue gettxoutproof(const JSONRPCRequest& request)
{
    if (request.fHelp || (request.params.size() != 1 && request.params.size() != 2))
        throw runtime_error(
            "gettxoutproof [\"txid\",...] ( blockhash )\n"
            "\nReturns a hex-encoded proof that \"txid\" was included in a block.\n"
            "\nNOTE: By default this function only works sometimes. This is when there is an\n"
            "unspent output in the utxo for this transaction. To make it always work,\n"
            "you need to maintain a transaction index, using the -txindex command line option or\n"
            "specify the block in which the transaction is included manually (by blockhash).\n"
            "\nArguments:\n"
            "1. \"txids\"       (string) A json array of txids to filter\n"
            "    [\n"
            "      \"txid\"     (string) A transaction hash\n"
            "      ,...\n"
            "    ]\n"
            "2. \"blockhash\"   (string, optional) If specified, looks for txid in the block with this hash\n"
            "\nResult:\n"
            "\"data\"           (string) A string that is a serialized, hex-encoded data for the proof.\n"
        );
    set<uint256> setTxids;
    uint256 oneTxid;
    UniValue txids = request.params[0].get_array();
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
    if (request.params.size() > 1)
    {
        hashBlock = uint256S(request.params[1].get_str());
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
        CTransactionRef tx;
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
    for (const auto& tx : block.vtx)
        if (setTxids.count(tx->GetHash()))
            ntxFound++;
    if (ntxFound != setTxids.size())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "(Not all) transactions not found in specified block");
    CDataStream ssMB(SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS);
    CMerkleBlock mb(block, setTxids);
    ssMB << mb;
    std::string strHex = HexStr(ssMB.begin(), ssMB.end());
    return strHex;
}

UniValue verifytxoutproof(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "verifytxoutproof \"proof\"\n"
            "\nVerifies that a proof points to a transaction in a block, returning the transaction it commits to\n"
            "and throwing an RPC error if the block is not in our best chain\n"
            "\nArguments:\n"
            "1. \"proof\"    (string, required) The hex-encoded proof generated by gettxoutproof\n"
            "\nResult:\n"
            "[\"txid\"]      (array, strings) The txid(s) which the proof commits to, or empty array if the proof is invalid\n"
        );
    CDataStream ssMB(ParseHexV(request.params[0], "proof"), SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS);
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
    for (uint256 const &hash : vMatch)
        res.push_back(hash.GetHex());
    return res;
}
// @brief Define for String Error.
#define ERROR_BLOCK_HEIGHT "Invalid parameter, missing blockheight key"
#define ERROR_DECAY_CONST "Invalid parameter, missing decayConst key"
#define ERROR_DUPLICATED_ADDRESS "Invalid parameter, duplicated address: "
#define ERROR_END_BLOCK_HEIGHT "Invalid parameter, missing endBlockHeight key"
#define ERROR_END_BLOCK_HEIGHT_VALUE "Invalid parameter, endBlockHeight must be positive"
#define ERROR_FEE "Invalid parameter, missing fee key"
#define ERROR_FEE_VALUE "Invalid parameter, endBlockHeight must be positive"
#define ERROR_GENESIS "Invalid parameter, genesis must be string"
#define ERROR_INVALID_ADDRESS "Invalid Bitcoin address: "
#define ERROR_N_OUTPUT "Invalid parameter, vout must be positive"
#define ERROR_SEQUENCE "Invalid parameter, sequence number is out of range"
#define ERROR_START_BLOCK_HEIGHT "Invalid parameter, missing startBlockHeight key"
#define ERROR_START_BLOCK_HEIGHT_VALUE "Invalid parameter, startBlockHeight must be positive"
#define ERROR_TICKETS "Invalid parameter, missing tickets key"
#define ERROR_TICKETS_VALUE "Invalid parameter, tickets must be positive"
#define ERROR_VOUT "Invalid parameter, missing vout key"
#define ERROR_VOUT_VALUE "Invalid parameter, vout must be positive"
// @brief Set in MACRO to simplify readability.
#define VALUE_OBJ UniValue::VOBJ
// @fn createrawrequesttx_runtime_error
// @brief
// @return string
static string createrawrequesttx_runtime_error(void) {
  return R"(createrawrequesttx
Arguments:

1. "inputs"                 (object, required) A json array of json objects.
{
  "txid": xxxx,             (string, required) The transaction id.
  "vout": n,                (numeric, required) The output number.
}

2. "outputs"                (object, required) a json object with outputs.
{
  "pubkey": xxxx,           (string, required)
  "decayConst": n,          (numeric, required)
  "endBlockHeight": n,      (numeric, required)
  "fee": n,                 (numeric, required)
  "genesisBlockHash": xxxx, (string, required)
  "startBlockHeight": n,    (numeric, required)
  "startPrice": n,          (numeric, required)
  "tickets": n,             (numeric, required)
  "value": n.               (numeric, required)
}

Result:
transaction                 (string) hex string of the transaction

Examples:
  ...
)";
}

static inline void createrawrequesttx_input(CMutableTransaction &rawTx,
                                            UniValue const &input) {
    uint32_t nOutput;
    uint256 txid = ParseHashO(input, "txid");
    UniValue const& vout = find_value(input, "vout");
    if (!vout.isNum())
        throw JSONRPCError(RPC_INVALID_PARAMETER, ERROR_VOUT);
    if ((nOutput = vout.get_int()) < 0)
        throw JSONRPCError(RPC_INVALID_PARAMETER, ERROR_VOUT_VALUE);
    rawTx.vin.push_back(CTxIn(COutPoint(txid, nOutput), CScript(), UINT_MAX - 1));
}

static inline void createrawrequesttx_output(CMutableTransaction& rawTx,
                                            CAsset const& asset,
                                            CAmount const& amount,
                                            UniValue const& output)
{
    // get target public key first
    const UniValue& pkey = output["pubkey"];
    if (!IsHex(pkey.getValStr()))
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Pubkey must be a hex string");
    std::vector<unsigned char> datapubkey(ParseHex(pkey.getValStr()));
    CPubKey targetPubKey(datapubkey.begin(), datapubkey.end());
    //we check that this pubkey is a real curve point
    if (!targetPubKey.IsFullyValid())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Pubkey is not a valid public key");

    // get genesis for request
    uint256 genesisBlockHash = ParseHashO(output, "genesisBlockHash");
    CDataStream datapubkey2(SER_NETWORK, PROTOCOL_VERSION);
    datapubkey2 << (char)2; // pubkey prefix
    datapubkey2 << genesisBlockHash;

    // get the rest request info
    UniValue const& decayConst = output["decayConst"];
    UniValue const& fee = output["fee"];
    UniValue const& startBlockHeight = output["startBlockHeight"];
    UniValue const& ticket = output["tickets"];
    UniValue const& startPrice = output["startPrice"];
    if (!decayConst.isNum())
        throw JSONRPCError(RPC_INVALID_PARAMETER, ERROR_DECAY_CONST);
    if (!fee.isNum())
        throw JSONRPCError(RPC_INVALID_PARAMETER, ERROR_FEE);
    if (fee.get_int() < 0)
        throw JSONRPCError(RPC_INVALID_PARAMETER, ERROR_FEE_VALUE);
    if (!startBlockHeight.isNum())
        throw JSONRPCError(RPC_INVALID_PARAMETER, ERROR_START_BLOCK_HEIGHT);
    if (startBlockHeight.get_int() < 0)
        throw JSONRPCError(RPC_INVALID_PARAMETER, ERROR_START_BLOCK_HEIGHT_VALUE);
    if (!ticket.isNum())
        throw JSONRPCError(RPC_INVALID_PARAMETER, ERROR_TICKETS);
    if (ticket.get_int() < 0)
        throw JSONRPCError(RPC_INVALID_PARAMETER, ERROR_TICKETS_VALUE);

    CDataStream datapubkey3(SER_NETWORK, PROTOCOL_VERSION);
    datapubkey3 << (char)3; // pubkey prefix
    datapubkey3 << startBlockHeight.get_int();
    datapubkey3 << ticket.get_int();
    datapubkey3 << decayConst.get_int();
    datapubkey3 << fee.get_int();
    datapubkey3 << AmountFromValue(startPrice);
    datapubkey3.resize(33);

    // get lock time block height
    UniValue const& endBlockHeight = find_value(output, "endBlockHeight");
    if (!endBlockHeight.isNum())
        throw JSONRPCError(RPC_INVALID_PARAMETER, ERROR_END_BLOCK_HEIGHT);
    if (endBlockHeight.get_int() < 0)
        throw JSONRPCError(RPC_INVALID_PARAMETER, ERROR_END_BLOCK_HEIGHT_VALUE);

    rawTx.vout.push_back(
        CTxOut(asset, amount,
            CScript() << CScriptNum(endBlockHeight.get_int()) << OP_CHECKLOCKTIMEVERIFY << OP_DROP
                      << CScript::EncodeOP_N(1)
                      << ToByteVector(targetPubKey)
                      << ToByteVector(datapubkey2)
                      << ToByteVector(datapubkey3)
                      << CScript::EncodeOP_N(3) << OP_CHECKMULTISIG));
};

UniValue createrawrequesttx(JSONRPCRequest const &request) {
    if (request.fHelp || request.params.size() != 2)
        throw runtime_error(createrawrequesttx_runtime_error());

    RPCTypeCheck(request.params, {VALUE_OBJ, VALUE_OBJ}, true);

    UniValue input = request.params[0].get_obj();
    CMutableTransaction rawTx;
    rawTx.nLockTime = chainActive.Height();
    createrawrequesttx_input(rawTx, input);

    CAsset asset = CAsset(permissionAsset);
    UniValue output = request.params[1].get_obj();
    CAmount nAmount = AmountFromValue(find_value(output, "value"));
    createrawrequesttx_output(rawTx, asset, nAmount, output);

    return EncodeHexTx(rawTx);
}

// @fn createrawbidtx_runtime_error
// @brief
// @return string
static string createrawbidtx_runtime_error(void) {
  return R"(createrawbidtx
Arguments:

1. "inputs"                 (object, required) A json array of json objects.
[
  {
    "txid": xxxx,             (string, required) The transaction id.
    "vout": n,                (numeric, required) The output number.
    "asset": "string"         (string, required) The asset of the input, as a tag string or a hex value"
  },
]

2. "outputs"                (object, required) a json object with outputs.
{
  "pubkey": xxxx,           (string, required)  Target stake pubkey
  "value": n,               (numeric, required) Staked value locked in target pubkey
  "change": n,              (numeric, optional) Change value of transaction
  "changeAddress": "string" (string, optional) Change address of transaction
  "fee": n,                 (numeric, required) Fee value of transaction
  "endBlockHeight": n,      (numeric, required) Service end height
  "requestTxid": xxxx,      (string, required) Request txid for providing services
  "feePubkey": xxxx,        (string, required) Pubkey to pay fees in the client service chain
}

Result:
transaction                 (string) hex string of the transaction

Examples:
  ...
)";
}

static inline void createrawbidtx_input(CMutableTransaction &rawTx,
                                            UniValue const &inputs) {
    for (size_t i = 0; i < inputs.size(); ++i) {
        const auto &inputObj = inputs[i].get_obj();
        uint32_t nOutput;
        uint256 txid = ParseHashO(inputObj, "txid");
        UniValue const& vout = find_value(inputObj, "vout");
        if (!vout.isNum())
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, missing vout key");
        if ((nOutput = vout.get_int()) < 0)
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, vout must be positive");
        rawTx.vin.push_back(CTxIn(COutPoint(txid, nOutput), CScript(), UINT_MAX - 1));
    }
}

static inline void createrawbidtx_output(CMutableTransaction& rawTx,
                                            CAsset const& asset,
                                            UniValue const& output)
{
    // get target public key first
    const UniValue& pkey = output["pubkey"];
    if (!IsHex(pkey.getValStr()))
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Pubkey must be a hex string");
    std::vector<unsigned char> datapubkey(ParseHex(pkey.getValStr()));
    CPubKey targetPubKey(datapubkey.begin(), datapubkey.end());
    if (!targetPubKey.IsFullyValid())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Pubkey is not a valid public key");

    // get request txid
    uint256 requestTxid = ParseHashO(output, "requestTxid");
    CDataStream datapubkey2(SER_NETWORK, PROTOCOL_VERSION);
    datapubkey2 << (char)2; // pubkey prefix
    datapubkey2 << requestTxid;

    // get the fee pubkey
    const UniValue& feePkey = output["feePubkey"];
    if (!IsHex(feePkey.getValStr()))
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Fee Pubkey must be a hex string");
    std::vector<unsigned char> datapubkey3(ParseHex(feePkey.getValStr()));
    CPubKey feePubKey(datapubkey3.begin(), datapubkey3.end());
    if (!feePubKey.IsFullyValid())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Fee Pubkey is not a valid public key");

    // get lock time block height
    UniValue const& endBlockHeight = find_value(output, "endBlockHeight");
    if (!endBlockHeight.isNum())
        throw JSONRPCError(RPC_INVALID_PARAMETER, ERROR_END_BLOCK_HEIGHT);
    if (endBlockHeight.get_int() < 0)
        throw JSONRPCError(RPC_INVALID_PARAMETER, ERROR_END_BLOCK_HEIGHT_VALUE);

    CAmount amount = AmountFromValue(find_value(output, "value"));
    rawTx.vout.push_back(
        CTxOut(asset, amount,
            CScript() << CScriptNum(endBlockHeight.get_int()) << OP_CHECKLOCKTIMEVERIFY << OP_DROP
                      << CScript::EncodeOP_N(1)
                      << ToByteVector(targetPubKey)
                      << ToByteVector(datapubkey2)
                      << ToByteVector(feePubKey)
                      << CScript::EncodeOP_N(3) << OP_CHECKMULTISIG));
};

UniValue createrawbidtx(JSONRPCRequest const &request) {
    if (request.fHelp || request.params.size() != 2)
        throw runtime_error(createrawbidtx_runtime_error());

    RPCTypeCheck(request.params, {UniValue::VARR, UniValue::VOBJ}, true);

    UniValue inputs = request.params[0].get_array();
    CMutableTransaction rawTx;
    rawTx.nLockTime = chainActive.Height();
    createrawbidtx_input(rawTx, inputs);

    CAsset asset = CAsset(ParseHashO(inputs[0].get_obj(), "asset"));
    UniValue output = request.params[1].get_obj();
    createrawbidtx_output(rawTx, asset, output);

    const UniValue &change = find_value(output, "change");
    const UniValue &changeAddr = find_value(output, "changeAddress");
    if (!change.isNull() && !changeAddr.isNull()) {
        const auto &nChange = AmountFromValue(change);
        CBitcoinAddress address(changeAddr.get_str());
        if (!address.IsValid())
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, string("Invalid Bitcoin address: ")+changeAddr.get_str());
        CScript scriptPubKey = GetScriptForDestination(address.Get());
        CTxOut out(asset, nChange, scriptPubKey);
        rawTx.vout.push_back(out);
    }

    CAmount nFee = AmountFromValue(find_value(output, "fee"));
    CTxOut out(asset, nFee, CScript());
    rawTx.vout.push_back(out);

    return EncodeHexTx(rawTx);
}

UniValue createrawtransaction(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() < 2 || request.params.size() > 4)
        throw runtime_error(
            "createrawtransaction [{\"txid\":\"id\",\"vout\":n},...] {\"address\":amount,\"data\":\"hex\",...} ( locktime {\"address\":asset} )\n"
            "\nCreate a transaction spending the given inputs and creating new outputs.\n"
            "Outputs can be addresses or data.\n"
            "Returns hex-encoded raw transaction.\n"
            "Note that the transaction's inputs are not signed, and\n"
            "it is not stored in the wallet or transmitted to the network.\n"

            "\nArguments:\n"
            "1. \"inputs\"                (array, required) A json array of json objects\n"
            "     [\n"
            "       {\n"
            "         \"txid\":\"id\",    (string, required) The transaction id\n"
            "         \"vout\":n,         (numeric, required) The output number\n"
            "         \"asset\": \"string\"   (string, optional, default=bitcoin) The asset of the input, as a tag string or a hex value\n"
            "         \"sequence\":n      (numeric, optional) The sequence number\n"
            "       } \n"
            "       ,...\n"
            "     ]\n"
            "2. \"outputs\"               (object, required) a json object with outputs\n"
            "    {\n"
            "      \"address\": x.xxx,    (numeric or string, optional) The key is the bitcoin address, the numeric value (can be string) is the " + CURRENCY_UNIT + " amount\n"
            "      \"data\": \"hex\"      (string, optional) The key is \"data\", the value is hex encoded data\n"
            "      \"vdata\": \"hex\"     (string, optional) The key is \"vdata\", the value is an array of hex encoded data\n"
            "      \"fee\": x.xxx         (numeric or string, optional) The key is \"fee\", the value the fee output you want to add.\n"
            "      ,...\n"
            "    }\n"
            "3. locktime                  (numeric, optional, default=0) Raw locktime. Non-0 value also locktime-activates inputs\n"
            "4. \"output_assets\"           (strings, optional, default=bitcoin) A json object of assets to addresses\n"
            "   {\n"
            "       \"address\": \"hex\" \n"
            "        \"fee\": \"hex\" \n"
            "       ...\n"
            "   }\n"
            "\nResult:\n"
            "\"transaction\"              (string) hex string of the transaction\n"

            "\nExamples:\n"
            + HelpExampleCli("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\" \"{\\\"address\\\":2.41}\"")
            + HelpExampleCli("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0\\\"asset\\\":\\\"myasset\\\"}]\" \"{\\\"address\\\":2.41}\" 0 \"{\\\"address\\\":\\\"myasset\\\"}\"")
            + HelpExampleCli("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\" \"{\\\"data\\\":\\\"00010203\\\"}\"")
            + HelpExampleRpc("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\", \"{\\\"address\\\":2.41}\"")
            + HelpExampleRpc("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0\\\"asset\\\":\\\"myasset\\\"}]\", \"{\\\"address\\\":2.41}\", 0, \"{\\\"address\\\":\\\"myasset\\\"}\"")
            + HelpExampleRpc("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\", \"{\\\"data\\\":\\\"00010203\\\"}\"")
        );
    RPCTypeCheck(request.params, boost::assign::list_of(UniValue::VARR)(UniValue::VOBJ)(UniValue::VNUM)(UniValue::VOBJ), true);
    if (request.params[0].isNull() || request.params[1].isNull())
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, arguments 1 and 2 must be non-null");
    UniValue inputs = request.params[0].get_array();
    UniValue sendTo = request.params[1].get_obj();
    CMutableTransaction rawTx;
    if (request.params.size() > 2 && !request.params[2].isNull()) {
        int64_t nLockTime = request.params[2].get_int64();
        if (nLockTime < 0 || nLockTime > std::numeric_limits<uint32_t>::max())
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, locktime out of range");
        rawTx.nLockTime = nLockTime;
    }
    UniValue assets;
    if (request.params.size() > 3 && !request.params[3].isNull())
        assets = request.params[3].get_obj();
    for (unsigned int idx = 0; idx < inputs.size(); idx++) {
        UniValue const &input = inputs[idx];
        UniValue const &o = input.get_obj();
        uint256 txid = ParseHashO(o, "txid");
        UniValue const &vout_v = find_value(o, "vout");
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
        UniValue const &asset_val = find_value(o, "asset");
        if (asset_val.isStr())
            asset = CAsset(ParseHashO(o, "asset"));
        rawTx.vin.push_back(in);
    }
    set<CBitcoinAddress> setAddress;
    vector<string> addrList = sendTo.getKeys();
    for (string const &name_ : addrList) {
        // Defaults to policyAsset
        CAsset asset(policyAsset);
        if (!assets.isNull())
            if (!find_value(assets, name_).isNull())
                asset = CAsset(ParseHashO(assets, name_));
        if (name_ == "data") {
            std::vector<unsigned char> data = ParseHexV(sendTo[name_].getValStr(),"Data");
            CTxOut out(asset, 0, CScript() << OP_RETURN << data);
            rawTx.vout.push_back(out);
        } else if (name_ == "vdata") {
            UniValue vdata = sendTo[name_].get_array();
            CScript datascript = CScript() << OP_RETURN;
            for (size_t i = 0; i < vdata.size(); i++) {
                std::vector<unsigned char> data = ParseHexV(vdata[i].get_str(), "Data");
                datascript << data;
            }
            CTxOut out(asset, 0, datascript);
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

UniValue createrawpolicytx(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 4)
        throw runtime_error(
            "createrawpolicytx [{\"txid\":\"id\",\"vout\":n},...] [{\"pubkey\":amount,\"data\":\"address\"},...] locktime asset\n"
            "\nCreate a transaction spending the given inputs and creating 1-of-2 policy list update outputs.\n"
            "Returns hex-encoded raw transaction.\n"
            "Note that the transaction's inputs are not signed, and\n"
            "it is not stored in the wallet or transmitted to the network.\n"

            "\nArguments:\n"
            "1. \"inputs\"                (array, required) A json array of json objects\n"
            "     [\n"
            "       {\n"
            "         \"txid\":\"id\",    (string, required) The transaction id\n"
            "         \"vout\":n,         (numeric, required) The output number\n"
            "         \"asset\": \"string\"   (string, optional, default=bitcoin) The asset of the input, as a tag string or a hex value\n"
            "         \"sequence\":n      (numeric, optional) The sequence number\n"
            "       } \n"
            "       ,...\n"
            "     ]\n"
            "2. \"outputs\"               (array, required) a json array of json objects\n"
            "     [\n"
            "    {\n"
            "      \"pubkey\": \"pubKey\",    (string, required) The key is \"pubkey\" and the value is the admin public key\n"
            "      \"value\": \"value\"      (numeric or string, required) The key is \"value\", the value is the permission token amount\n"
            "      \"address\": \"address\"      (string, optional) The key is \"address\", the value is hex encoded 20 byte address to be added to the policy list\n"
            "      \"userkey\": \"userkey\"      (string, optional) The key is \"userkey\", the value is hex encoded 32 byte key to be added to the policy list\n"
            "    }\n"
            "       ,...\n"
            "     ]\n"
            "3. locktime                  (numeric, required, default=0) Raw locktime. Non-0 value also locktime-activates inputs\n"
            "4. \"output_asset\"           (string, required) The policy list asset type (hex)\n"
            "\nResult:\n"
            "\"transaction\"              (string) hex string of the transaction\n"

            "\nExamples:\n"
            + HelpExampleCli("createrawpolicytx", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\" \"{\\\"pubkey\\\":2.41}\"")
            + HelpExampleCli("createrawpolicytx", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0\\\"asset\\\":\\\"myasset\\\"}]\" \"{\\\"pubkey\\\":2.41}\" 0 \"{\\\"address\\\":\\\"myasset\\\"}\"")
            + HelpExampleCli("createrawpolicytx", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\" \"{\\\"data\\\":\\\"47ef9c62a982cb8d91ba7291bae\\\"}\"")
            + HelpExampleRpc("createrawpolicytx", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\", \"{\\\"address\\\":2.41}\"")
            + HelpExampleRpc("createrawpolicytx", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0\\\"asset\\\":\\\"myasset\\\"}]\", \"{\\\"pubkey\\\":2.41}\", 0, \"{\\\"address\\\":\\\"myasset\\\"}\"")
            + HelpExampleRpc("createrawpolicytx", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\", \"{\\\"data\\\":\\\"47ef9c62a982cb8d91ba7291bae\\\"}\"")
        );

    RPCTypeCheck(request.params, boost::assign::list_of(UniValue::VARR)(UniValue::VARR)(UniValue::VNUM)(UniValue::VSTR), true);
    if (request.params[0].isNull() || request.params[1].isNull())
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, arguments 1 and 2 must be non-null");

    UniValue inputs = request.params[0].get_array();
    UniValue outputs = request.params[1].get_array();

    CMutableTransaction rawTx;

    int64_t nLockTime = request.params[2].get_int64();
    if (nLockTime < 0 || nLockTime > std::numeric_limits<uint32_t>::max())
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, locktime out of range");
    rawTx.nLockTime = nLockTime;

    std::string assetstr = request.params[3].get_str();
    CAsset asset;
    asset.SetHex(assetstr);

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

        rawTx.vin.push_back(in);
    }

    //loop over all outputs
    for (unsigned int idx = 0; idx < outputs.size(); idx++) {
        const UniValue& output = outputs[idx];
        const UniValue& o = output.get_obj();

        //get the admin pubkey from the RPC
        const UniValue& pkey = find_value(o, "pubkey");

        if (!IsHex(pkey.getValStr()))
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Pubkey must be a hex string");
        std::vector<unsigned char> datapubkey(ParseHex(pkey.getValStr()));
        CPubKey adminPubKey(datapubkey.begin(), datapubkey.end());
        //we check that this pubkey is a real curve point
        if (!adminPubKey.IsFullyValid())
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Pubkey is not a valid public key");


        std::string data;
        //get the address from the RPC
        const UniValue& address = find_value(o, "address");

        if(address.isStr()){
            CBitcoinAddress bcaddress;
            if (!bcaddress.SetString(address.getValStr()))
                throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid  address");

            CKeyID keyId;
            if (!bcaddress.GetKeyID(keyId))
                throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid key id");

            std::string hexaddress = HexStr(keyId.begin(), keyId.end());
            //concatenate with padding bytes
            data = "02000000000000000000000000" + hexaddress;
            //we do not check that this pubkey is a real curve point
        }

        const UniValue& userkey = find_value(o, "userkey");

        if (userkey.isStr()) {
            if(data.length() > 0)
                throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Cannot have both address and userkey");
            if (!IsHex(userkey.getValStr()))
                throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Userkey must be a hex string");
            if(userkey.getValStr().length() != 66)
                throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Userkey must be 33 bytes in length");

            data = userkey.getValStr();
            //we do not check that this pubkey is a real curve point
        }

       std::vector<unsigned char> datavec(ParseHex(data));
       datavec.resize(33, 0);

        if (userkey.isStr()) {
            //for userkey: reverse the last 30 bytes so that this key cannot be used to spend the tx
            std::reverse(datavec.begin()+3, datavec.end());
        }

        CPubKey listData(datavec.begin(), datavec.end());

        //get the address from the RPC

        std::vector<CPubKey> pubkeys;
        pubkeys.resize(2);
        int nRequired = 1;
        pubkeys[0] = adminPubKey;
        pubkeys[1] = listData;

        CScript result = GetScriptForMultisig(nRequired, pubkeys);

        const UniValue& outval = find_value(o, "value");
        CAmount nAmount = AmountFromValue(outval);
        CTxOut out(asset, nAmount, result);
        rawTx.vout.push_back(out);
    }

    return EncodeHexTx(rawTx);
}

// Rewind the outputs to unblinded, and push placeholders for blinding info
void FillBlinds(CMutableTransaction& tx, bool fUseWallet, std::vector<uint256>& output_value_blinds, std::vector<uint256>& output_asset_blinds, std::vector<CPubKey>& output_pubkeys, std::vector<CKey>& asset_keys, std::vector<CKey>& token_keys) {
    for (size_t nOut = 0; nOut < tx.vout.size(); nOut++) {
        if (!tx.vout[nOut].nValue.IsExplicit()) {
#ifdef ENABLE_WALLET
            CTxOutWitness* ptxoutwit = tx.wit.vtxoutwit.size() <= nOut? NULL: &tx.wit.vtxoutwit[nOut];
            uint256 blinding_factor;
            uint256 asset_blinding_factor;
            CAsset asset;
            CAmount amount;
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
        if (!issuance.IsReissuance()) {
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

UniValue rawblindrawtransaction(const JSONRPCRequest& request)
{
    if (request.fHelp || (request.params.size() < 5 || request.params.size() > 7))
        throw std::runtime_error(
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
    if (request.params.size() == 5) {
        RPCTypeCheck(request.params, boost::assign::list_of(UniValue::VSTR)(UniValue::VARR)(UniValue::VARR)(UniValue::VARR)(UniValue::VARR));
    } else if (request.params.size() == 6) {
        RPCTypeCheck(request.params, boost::assign::list_of(UniValue::VSTR)(UniValue::VARR)(UniValue::VARR)(UniValue::VARR)(UniValue::VARR)(UniValue::VSTR));
    } else {
        RPCTypeCheck(request.params, boost::assign::list_of(UniValue::VSTR)(UniValue::VARR)(UniValue::VARR)(UniValue::VARR)(UniValue::VARR)(UniValue::VSTR)(UniValue::VBOOL));
    }
    vector<unsigned char> txData(ParseHexV(request.params[0], "argument 1"));
    CDataStream ssData(txData, SER_NETWORK, PROTOCOL_VERSION);
    CMutableTransaction tx;
    try {
        ssData >> tx;
    } catch (const std::exception &) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    }
    UniValue inputBlinds = request.params[1].get_array();
    UniValue inputAmounts = request.params[2].get_array();
    UniValue inputAssets = request.params[3].get_array();
    UniValue inputAssetBlinds = request.params[4].get_array();
    bool fIgnoreBlindFail = true;
    if (request.params.size() > 6) {
        fIgnoreBlindFail = request.params[6].get_bool();
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
        input_amounts.push_back(AmountFromValue(inputAmounts[nIn]));
        if (!input_blinds.back().IsNull()) {
            n_blinded_ins++;
        }
    }
    std::vector<CKey> asset_keys;
    std::vector<CKey> token_keys;
    FillBlinds(tx, false, output_value_blinds, output_asset_blinds, output_pubkeys, asset_keys, token_keys);
    // How many are we trying to blind?
    int numPubKeys = 0;
    unsigned int keyIndex = -1;
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
        // No notion of wallet, cannot complete this blinding without passed-in pubkey
        throw JSONRPCError(RPC_INVALID_PARAMETER, string("Unable to blind transaction: Add another output to blind in order to complete the blinding."));
    } else if (n_blinded_ins == 0 && numPubKeys == 1) {
        if (fIgnoreBlindFail) {
            // Just get rid of the ECDH key in the nonce field and return
            tx.vout[keyIndex].nNonce.SetNull();
            return EncodeHexTx(tx);
        } else {
            throw JSONRPCError(RPC_INVALID_PARAMETER, string("Unable to blind transaction: Add another output to blind in order to complete the blinding."));
        }
    }
    int ret = BlindTransaction(input_blinds, input_asset_blinds, input_assets, input_amounts, output_value_blinds, output_asset_blinds, output_pubkeys, std::vector<CKey>(), std::vector<CKey>(), tx);
    if (ret != numPubKeys) {
        // TODO Have more rich return values, communicating to user what has been blinded
        // User may be ok not blinding something that for instance has no corresponding type on input
        throw JSONRPCError(RPC_INVALID_PARAMETER, string("Unable to blind transaction: Are you sure each asset type to blind is represented in the inputs?"));
    }
    return EncodeHexTx(tx);
}

#ifdef ENABLE_WALLET
UniValue blindrawtransaction(const JSONRPCRequest& request)
{
    if (request.fHelp || (request.params.size() < 1 || request.params.size() > 4))
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
    if (request.params.size() == 1) {
        RPCTypeCheck(request.params, boost::assign::list_of(UniValue::VSTR));
    } else if (request.params.size() == 2){
        RPCTypeCheck(request.params, boost::assign::list_of(UniValue::VSTR)(UniValue::VBOOL));
    } else if (request.params.size() == 3){
        RPCTypeCheck(request.params, boost::assign::list_of(UniValue::VSTR)(UniValue::VBOOL)(UniValue::VARR));
    } else {
        RPCTypeCheck(request.params, boost::assign::list_of(UniValue::VSTR)(UniValue::VBOOL)(UniValue::VARR)(UniValue::VSTR));
    }
    vector<unsigned char> txData(ParseHexV(request.params[0], "argument 1"));
    CDataStream ssData(txData, SER_NETWORK, PROTOCOL_VERSION);
    CMutableTransaction tx;
    try {
        ssData >> tx;
    } catch (const std::exception &) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    }
    bool fIgnoreBlindFail = true;
    if (request.params.size() > 1) {
        fIgnoreBlindFail = request.params[1].get_bool();
    }
    std::vector<std::vector<unsigned char> > auxiliary_generators;
    if (request.params.size() > 2) {
        UniValue assetCommitments = request.params[2].get_array();
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
        if (tx.vin[nIn].prevout.n >= it->second.tx->vout.size()) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, string("Invalid parameter: transaction spends non-existing output"));
        }
        input_blinds.push_back(it->second.GetOutputBlindingFactor(tx.vin[nIn].prevout.n));
        input_asset_blinds.push_back(it->second.GetOutputAssetBlindingFactor(tx.vin[nIn].prevout.n));
        // These cases unneeded? If value is explicit we can still get via GetOutputX calls.
        if (it->second.tx->vout[tx.vin[nIn].prevout.n].nAsset.IsExplicit()) {
            input_assets.push_back(it->second.tx->vout[tx.vin[nIn].prevout.n].nAsset.GetAsset());
        }
        else {
            input_assets.push_back(it->second.GetOutputAsset(tx.vin[nIn].prevout.n));
        }
        if (it->second.tx->vout[tx.vin[nIn].prevout.n].nValue.IsExplicit()) {
            input_amounts.push_back(it->second.tx->vout[tx.vin[nIn].prevout.n].nValue.GetAmount());
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

UniValue decoderawtransaction(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "decoderawtransaction \"hexstring\"\n"
            "\nReturn a JSON object representing the serialized, hex-encoded transaction.\n"
            "\nArguments:\n"
            "1. \"hexstring\"      (string, required) The transaction hex string\n"
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
            "       \"issuance\"         (object) Info on issuance\n"
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
    RPCTypeCheck(request.params, boost::assign::list_of(UniValue::VSTR));
    CMutableTransaction mtx;
    if (!DecodeHexTx(mtx, request.params[0].get_str()))
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    UniValue result(UniValue::VOBJ);
    TxToJSON(CTransaction(std::move(mtx)), uint256(), result);
    return result;
}

UniValue decodescript(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "decodescript \"hexstring\"\n"
            "\nDecode a hex-encoded script.\n"
            "\nArguments:\n"
            "1. \"hexstring\"     (string) the hex encoded script\n"
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
            "  \"p2sh\",\"address\" (string) address of P2SH script wrapping this redeem script (not returned if the script is already a P2SH).\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("decodescript", "\"hexstring\"")
            + HelpExampleRpc("decodescript", "\"hexstring\"")
        );
    RPCTypeCheck(request.params, boost::assign::list_of(UniValue::VSTR));
    UniValue r(UniValue::VOBJ);
    CScript script;
    if (request.params[0].get_str().size() > 0){
        vector<unsigned char> scriptData(ParseHexV(request.params[0], "argument"));
        script = CScript(scriptData.begin(), scriptData.end());
    } else {
        // Empty scripts are valid
    }
    ScriptPubKeyToJSON(script, r, false);
    UniValue type;
    type = find_value(r, "type");
    if (type.isStr() && type.get_str() != "scripthash") {
        // P2SH cannot be wrapped in a P2SH. If this script is already a P2SH,
        // don't return the address for a P2SH of the P2SH.
        r.push_back(Pair("p2sh", CBitcoinAddress(CScriptID(script)).ToString()));
    }
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

UniValue signrawtransaction(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() < 1 || request.params.size() > 4)
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
            "3. \"privkeys\"     (string, optional) A json array of base58-encoded private keys for signing\n"
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
    RPCTypeCheck(request.params, boost::assign::list_of(UniValue::VSTR)(UniValue::VARR)(UniValue::VARR)(UniValue::VSTR), true);
    vector<unsigned char> txData(ParseHexV(request.params[0], "argument 1"));
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
        for (CTxIn const &txin : mergedTx.vin) {
            const uint256& prevHash = txin.prevout.hash;
            CCoins coins;
            view.AccessCoins(prevHash); // this is certainly allowed to fail
        }
        view.SetBackend(viewDummy); // switch back to avoid locking mempool for too long
    }
    bool fGivenKeys = false;
    CBasicKeyStore tempKeystore;
    if (request.params.size() > 2 && !request.params[2].isNull()) {
        fGivenKeys = true;
        UniValue keys = request.params[2].get_array();
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
    if (request.params.size() > 1 && !request.params[1].isNull()) {
        UniValue prevTxs = request.params[1].get_array();
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
    if (request.params.size() > 3 && !request.params[3].isNull()) {
        static map<string, int> mapSigHashValues =
            boost::assign::map_list_of
            (string("ALL"), int(SIGHASH_ALL))
            (string("ALL|ANYONECANPAY"), int(SIGHASH_ALL|SIGHASH_ANYONECANPAY))
            (string("NONE"), int(SIGHASH_NONE))
            (string("NONE|ANYONECANPAY"), int(SIGHASH_NONE|SIGHASH_ANYONECANPAY))
            (string("SINGLE"), int(SIGHASH_SINGLE))
            (string("SINGLE|ANYONECANPAY"), int(SIGHASH_SINGLE|SIGHASH_ANYONECANPAY))
            ;
        string strHashType = request.params[3].get_str();
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
    // Sign what we can, including peg-in inputs:
    for (unsigned int i = 0; i < mergedTx.vin.size(); i++) {
        CTxIn& txin = mergedTx.vin[i];
        const CCoins* coins = view.AccessCoins(txin.prevout.hash);
        if (!txin.m_is_pegin && (coins == NULL || !coins->IsAvailable(txin.prevout.n))) {
            TxInErrorToJSON(txin, vErrors, "Input not found or already spent");
            continue;
        } else if (txin.m_is_pegin && (txConst.wit.vtxinwit.size() <= i || !IsValidPeginWitness(txConst.wit.vtxinwit[i].m_pegin_witness, txin.prevout))) {
            TxInErrorToJSON(txin, vErrors, "Peg-in input has invalid proof.");
            continue;
        }
        const CScript& prevPubKey = txin.m_is_pegin ? GetPeginOutputFromWitness(txConst.wit.vtxinwit[i].m_pegin_witness).scriptPubKey : coins->vout[txin.prevout.n].scriptPubKey;
        const CConfidentialValue& amount = txin.m_is_pegin ? GetPeginOutputFromWitness(txConst.wit.vtxinwit[i].m_pegin_witness).nValue : coins->vout[txin.prevout.n].nValue;
        SignatureData sigdata;
        // Only sign SIGHASH_SINGLE if there's a corresponding output:
        if (!fHashSingle || (i < mergedTx.vout.size()))
            ProduceSignature(MutableTransactionSignatureCreator(&keystore, &mergedTx, i, amount, nHashType), prevPubKey, sigdata);
        // ... and merge in other signatures:
        for (CMutableTransaction const &txv : txVariants) {
            if (txv.vin.size() > i) {
                sigdata = CombineSignatures(prevPubKey, TransactionSignatureChecker(&txConst, i, amount), sigdata, DataFromTransaction(txv, i));
            }
        }
        UpdateTransaction(mergedTx, i, sigdata);
        ScriptError serror = SCRIPT_ERR_OK;
        if (!VerifyScript(txin.scriptSig, prevPubKey, (mergedTx.wit.vtxinwit.size() > i) ? &mergedTx.wit.vtxinwit[i].scriptWitness : NULL, STANDARD_SCRIPT_VERIFY_FLAGS, TransactionSignatureChecker(&txConst, i, amount), &serror)) {
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

UniValue testmempoolaccept(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() < 1 || request.params.size() > 2) {
        throw std::runtime_error(
            // clang-format off
            "testmempoolaccept [\"rawtxs\"] ( allowhighfees )\n"
            "\nReturns if raw transaction (serialized, hex-encoded) would be accepted by mempool.\n"
            "\nThis checks if the transaction violates the consensus or policy rules.\n"
            "\nSee sendrawtransaction call.\n"
            "\nArguments:\n"
            "1. rawtxs           (string, required) Hex strings of raw transactions.\n"
            "2. allowhighfees    (boolean, optional, default=false) Allow high fees\n"
            "\nResult:\n"
            "[                   (array) The result of the mempool acceptance test for each raw transaction in the input array.\n"
            "                            Length is exactly one for now.\n"
            " {\n"
            "  \"txid\"           (string) The transaction hash in hex\n"
            "  \"allowed\"        (boolean) If the mempool allows this tx to be inserted\n"
            "  \"reject-reason\"  (string) Rejection string (only present when 'allowed' is false)\n"
            " }\n"
            "]\n"
            "\nExamples:\n"
            "\nTest acceptance of the transaction (signed hex)\n"
            + HelpExampleCli("testmempoolaccept", "signedhex") +
            "\nAs a json rpc call\n"
            + HelpExampleRpc("testmempoolaccept", "signedhex")
            // clang-format on
            );
    }
    CMutableTransaction mtx;
    if (!DecodeHexTx(mtx, request.params[0].get_str())) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    }
    CTransactionRef tx(MakeTransactionRef(std::move(mtx)));
    const uint256& tx_hash = tx->GetHash();
    CAmount max_raw_tx_fee = ::maxTxFee;
    if (!request.params[1].isNull() && request.params[1].get_bool()) {
        max_raw_tx_fee = 0;
    }
    UniValue result_0(UniValue::VOBJ);
    result_0.pushKV("txid", tx_hash.GetHex());
    CValidationState state;
    bool missing_inputs;
    bool test_accept_res;
    bool fLimitFree = false;
    {
        LOCK(cs_main);
        test_accept_res = AcceptToMemoryPool(mempool, state, std::move(tx), fLimitFree, &missing_inputs,
            nullptr /* plTxnReplaced */, false /* bypass_limits */, max_raw_tx_fee, /* test_accpet */ true);
    }
    result_0.pushKV("allowed", test_accept_res);
    if (!test_accept_res) {
        if (state.IsInvalid()) {
            result_0.pushKV("reject-reason", strprintf("%i: %s", state.GetRejectCode(), state.GetRejectReason()));
        } else if (missing_inputs) {
            result_0.pushKV("reject-reason", "missing-inputs");
        } else {
            result_0.pushKV("reject-reason", state.GetRejectReason());
        }
    }
    return result_0;
}

UniValue sendrawtransaction(const JSONRPCRequest& request) {
  if (request.fHelp || request.params.size() < 1 || request.params.size() > 3) {
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
  }
  LOCK(cs_main);
  RPCTypeCheck(request.params, boost::assign::list_of(UniValue::VSTR)(UniValue::VBOOL)(UniValue::VBOOL));
  // parse hex string from parameter
  CMutableTransaction mtx;
  if (!DecodeHexTx(mtx, request.params[0].get_str()))
    throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
  CTransactionRef tx(MakeTransactionRef(std::move(mtx)));
  uint256 const &hashTx = tx->GetHash();
  bool fLimitFree = false;
  CAmount nMaxRawTxFee = maxTxFee;
  if (request.params.size() > 1 && request.params[1].get_bool())
    nMaxRawTxFee = 0;
  bool fOverrideBlindable = false;
  if (request.params.size() > 2)
    fOverrideBlindable = request.params[2].get_bool();
  if (!fOverrideBlindable) {
    for (uint32_t i = 0; i < tx->vout.size(); ++i) {
      CTxOut const &txout = tx->vout[i];
      if (txout.nValue.IsExplicit() && txout.nNonce.vchCommitment.size() != 0)
        throw JSONRPCError(RPC_TRANSACTION_ERROR, strprintf("Output %u is unblinded, but has blinding pubkey attached, please use [raw]blindrawtransaction", i));
    }
  }
  CCoinsViewCache &view = *pcoinsTip;
  CCoins const *existingCoins = view.AccessCoins(hashTx);
  bool fHaveMempool = mempool.exists(hashTx);
  bool fHaveChain = existingCoins && existingCoins->nHeight < 1000000000;
  if (!fHaveMempool && !fHaveChain) {
    // push to local node and sync with wallets
    CValidationState state;
    bool fMissingInputs;
    if (!AcceptToMemoryPool(mempool, state, std::move(tx), fLimitFree, &fMissingInputs, NULL, false, nMaxRawTxFee)) {
      if (state.IsInvalid()) {
        throw JSONRPCError(RPC_TRANSACTION_REJECTED, strprintf("%i: %s", state.GetRejectCode(), state.GetRejectReason()));
      } else {
        if (fMissingInputs)
          throw JSONRPCError(RPC_TRANSACTION_ERROR, "Missing inputs");
        throw JSONRPCError(RPC_TRANSACTION_ERROR, state.GetRejectReason());
      }
    }
  } else if (fHaveChain)
    throw JSONRPCError(RPC_TRANSACTION_ALREADY_IN_CHAIN, "transaction already in block chain");
  if (!g_connman)
    throw JSONRPCError(RPC_CLIENT_P2P_DISABLED, "Error: Peer-to-peer functionality missing or disabled");
  AuditLogPrintf("%s : sendrawtransaction %s\n", getUser(), hashTx.GetHex());
  CInv inv(MSG_TX, hashTx);
  g_connman->ForEachNode([&inv](CNode* pnode) { pnode->PushInventory(inv); });
  return hashTx.GetHex();
}

static const CRPCCommand commands[] =
{ //  category              name                      actor (function)         okSafeMode
  //  --------------------- ------------------------  -----------------------  ----------
    { "rawtransactions",    "getrawtransaction",      &getrawtransaction,      true,  {"txid","verbose"} },
    { "rawtransactions",    "createrawtransaction",   &createrawtransaction,   true,  {"inputs","outputs","locktime","output_assets"} },
    { "rawtransactions",    "createrawpolicytx",      &createrawpolicytx,      true,  {"inputs","outputs","locktime","asset"} },
    { "rawtransactions",    "createrawrequesttx",     &createrawrequesttx,     true,  {"inputs","outputs"} },
    { "rawtransactions",    "createrawbidtx",         &createrawbidtx,         true,  {"inputs","outputs"} },
    { "rawtransactions",    "decoderawtransaction",   &decoderawtransaction,   true,  {"hexstring"} },
    { "rawtransactions",    "decodescript",           &decodescript,           true,  {"hexstring"} },
    { "rawtransactions",    "sendrawtransaction",     &sendrawtransaction,     false, {"hexstring","allowhighfees"} },
    { "rawtransactions",    "signrawtransaction",     &signrawtransaction,     false, {"hexstring","prevtxs","privkeys","sighashtype"} }, /* uses wallet if enabled */
    { "rawtransactions",    "testmempoolaccept",      &testmempoolaccept,      false, {"hexstring","allowhighfees"} },
    { "rawtransactions",    "rawblindrawtransaction", &rawblindrawtransaction, false, {}},
#ifdef ENABLE_WALLET
    { "rawtransactions",    "blindrawtransaction",    &blindrawtransaction,    true, {}},
#endif
    { "blockchain",         "gettxoutproof",          &gettxoutproof,          true,  {"txids", "blockhash"} },
    { "blockchain",         "verifytxoutproof",       &verifytxoutproof,       true,  {"proof"} },
};

void RegisterRawTransactionRPCCommands(CRPCTable &t) {
  for (uint32_t vcidx = 0; vcidx < ARRAYLEN(commands); ++vcidx)
    t.appendCommand(commands[vcidx].name, &commands[vcidx]);
}
