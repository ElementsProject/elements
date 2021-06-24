// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <asset.h>
#include <block_proof.h>
#include <chain.h>
#include <coins.h>
#include <consensus/validation.h>
#include <core_io.h>
#include <index/txindex.h>
#include <key_io.h>
#include <merkleblock.h>
#include <net.h>
#include <node/coin.h>
#include <node/context.h>
#include <node/psbt.h>
#include <node/transaction.h>
#include <pegins.h>
#include <policy/policy.h>
#include <policy/rbf.h>
#include <primitives/transaction.h>
#include <primitives/bitcoin/merkleblock.h>
#include <primitives/bitcoin/transaction.h>
#include <psbt.h>
#include <random.h>
#include <rpc/blockchain.h>
#include <rpc/rawtransaction_util.h>
#include <rpc/server.h>
#include <rpc/util.h>
#include <script/pegins.h>
#include <script/script.h>
#include <script/sign.h>
#include <script/signingprovider.h>
#include <script/standard.h>
#include <uint256.h>
#include <util/bip32.h>
#include <util/moneystr.h>
#include <util/rbf.h>
#include <util/strencodings.h>
#include <util/string.h>
#include <validation.h>
#include <validationinterface.h>
#include <confidential_validation.h>
#include <blind.h>
#include <issuance.h>


#include <numeric>
#include <stdint.h>

#include <univalue.h>

static void TxToJSON(const CTransaction& tx, const uint256 hashBlock, UniValue& entry)
{
    // Call into TxToUniv() in bitcoin-common to decode the transaction hex.
    //
    // Blockchain contextual information (confirmations and blocktime) is not
    // available to code in bitcoin-common, so we query them here and push the
    // data into the returned UniValue.
    TxToUniv(tx, uint256(), entry, true, RPCSerializationFlags());

    if (!hashBlock.IsNull()) {
        LOCK(cs_main);

        entry.pushKV("blockhash", hashBlock.GetHex());
        CBlockIndex* pindex = g_chainman.m_blockman.LookupBlockIndex(hashBlock);
        if (pindex) {
            if (::ChainActive().Contains(pindex)) {
                entry.pushKV("confirmations", 1 + ::ChainActive().Height() - pindex->nHeight);
                entry.pushKV("time", pindex->GetBlockTime());
                entry.pushKV("blocktime", pindex->GetBlockTime());
            }
            else
                entry.pushKV("confirmations", 0);
        }
    }
}

static RPCHelpMan getrawtransaction()
{
    return RPCHelpMan{
                "getrawtransaction",
                "\nReturn the raw transaction data.\n"

                "\nBy default this function only works for mempool transactions. When called with a blockhash\n"
                "argument, getrawtransaction will return the transaction if the specified block is available and\n"
                "the transaction is found in that block. When called without a blockhash argument, getrawtransaction\n"
                "will return the transaction if it is in the mempool, or if -txindex is enabled and the transaction\n"
                "is in a block in the blockchain.\n"

                "\nHint: Use gettransaction for wallet transactions.\n"

                "\nIf verbose is 'true', returns an Object with information about 'txid'.\n"
                "If verbose is 'false' or omitted, returns a string that is serialized, hex-encoded data for 'txid'.\n",
                {
                    {"txid", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The transaction id"},
                    {"verbose", RPCArg::Type::BOOL, /* default */ "false", "If false, return a string, otherwise return a json object"},
                    {"blockhash", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED_NAMED_ARG, "The block in which to look for the transaction"},
                },
                {
                    RPCResult{"if verbose is not set or set to false",
                         RPCResult::Type::STR, "data", "The serialized, hex-encoded data for 'txid'"
                     },
                     RPCResult{"if verbose is set to true",
                         RPCResult::Type::OBJ, "", "",
                         {
                             {RPCResult::Type::BOOL, "in_active_chain", "Whether specified block is in the active chain or not (only present with explicit \"blockhash\" argument)"},
                             {RPCResult::Type::STR_HEX, "hex", "The serialized, hex-encoded data for 'txid'"},
                             {RPCResult::Type::STR_HEX, "txid", "The transaction id (same as provided)"},
                             {RPCResult::Type::STR_HEX, "hash", "The transaction hash (differs from txid for witness transactions)"},
                             {RPCResult::Type::NUM, "size", "The serialized transaction size"},
                             {RPCResult::Type::NUM, "vsize", "The virtual transaction size (differs from size for witness transactions)"},
                             {RPCResult::Type::NUM, "weight", "The transaction's weight (between vsize*4-3 and vsize*4)"},
                             {RPCResult::Type::NUM, "version", "The version"},
                             {RPCResult::Type::NUM_TIME, "locktime", "The lock time"},
                             {RPCResult::Type::ARR, "vin", "",
                             {
                                 {RPCResult::Type::OBJ, "", "",
                                 {
                                     {RPCResult::Type::STR_HEX, "txid", "The transaction id"},
                                     {RPCResult::Type::NUM, "vout", "The output number"},
                                     {RPCResult::Type::OBJ, "scriptSig", "The script",
                                     {
                                         {RPCResult::Type::STR, "asm", "asm"},
                                         {RPCResult::Type::STR_HEX, "hex", "hex"},
                                     }},
                                     {RPCResult::Type::NUM, "sequence", "The script sequence number"},
                                     {RPCResult::Type::ARR, "txinwitness", "",
                                     {
                                         {RPCResult::Type::STR_HEX, "hex", "hex-encoded witness data (if any)"},
                                     }},
                                 }},
                             }},
                             {RPCResult::Type::ARR, "vout", "",
                             {
                                 {RPCResult::Type::OBJ, "", "",
                                 {
                                     {RPCResult::Type::NUM, "value", "The value in " + CURRENCY_UNIT},
                                     {RPCResult::Type::NUM, "n", "index"},
                                     {RPCResult::Type::OBJ, "scriptPubKey", "",
                                     {
                                         {RPCResult::Type::STR, "asm", "the asm"},
                                         {RPCResult::Type::STR, "hex", "the hex"},
                                         {RPCResult::Type::NUM, "reqSigs", "The required sigs"},
                                         {RPCResult::Type::STR, "type", "The type, eg 'pubkeyhash'"},
                                         {RPCResult::Type::ARR, "addresses", "",
                                         {
                                             {RPCResult::Type::STR, "address", ""},
                                         }},
                                         {RPCResult::Type::STR_HEX, "pegout_chain", "(only pegout) Hash of genesis block of parent chain"},
                                         {RPCResult::Type::STR, "pegout_asm", "(only pegout) pegout scriptpubkey (asm)"},
                                         {RPCResult::Type::STR_HEX, "pegout_hex", "(only pegout) pegout scriptpubkey (hex)"},
                                         {RPCResult::Type::STR, "pegout_type", "(only pegout) The pegout type, eg 'pubkeyhash'"},
                                         {RPCResult::Type::ARR, "pegout_addresses", "(only pegout)",
                                         {
                                             {RPCResult::Type::STR, "address", ""},
                                         }},
                                     }},
                                 }},
                             }},
                             {RPCResult::Type::STR_HEX, "blockhash", "the block hash"},
                             {RPCResult::Type::NUM, "confirmations", "The confirmations"},
                             {RPCResult::Type::NUM_TIME, "blocktime", "The block time expressed in " + UNIX_EPOCH_TIME},
                             {RPCResult::Type::NUM, "time", "Same as \"blocktime\""},
                        }
                    },
                },
                RPCExamples{
                    HelpExampleCli("getrawtransaction", "\"mytxid\"")
            + HelpExampleCli("getrawtransaction", "\"mytxid\" true")
            + HelpExampleRpc("getrawtransaction", "\"mytxid\", true")
            + HelpExampleCli("getrawtransaction", "\"mytxid\" false \"myblockhash\"")
            + HelpExampleCli("getrawtransaction", "\"mytxid\" true \"myblockhash\"")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    const NodeContext& node = EnsureNodeContext(request.context);

    bool in_active_chain = true;
    uint256 hash = ParseHashV(request.params[0], "parameter 1");
    CBlockIndex* blockindex = nullptr;

    if (!Params().GetConsensus().connect_genesis_outputs &&
            hash == Params().GenesisBlock().hashMerkleRoot) {
        // Special exception for the genesis block coinbase transaction
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "The genesis block coinbase is not considered an ordinary transaction and cannot be retrieved");
    }

    // Accept either a bool (true) or a num (>=1) to indicate verbose output.
    bool fVerbose = false;
    if (!request.params[1].isNull()) {
        fVerbose = request.params[1].isNum() ? (request.params[1].get_int() != 0) : request.params[1].get_bool();
    }

    if (!request.params[2].isNull()) {
        LOCK(cs_main);

        uint256 blockhash = ParseHashV(request.params[2], "parameter 3");
        blockindex = g_chainman.m_blockman.LookupBlockIndex(blockhash);
        if (!blockindex) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Block hash not found");
        }
        in_active_chain = ::ChainActive().Contains(blockindex);
    }

    bool f_txindex_ready = false;
    if (g_txindex && !blockindex) {
        f_txindex_ready = g_txindex->BlockUntilSyncedToCurrentChain();
    }

    uint256 hash_block;
    const CTransactionRef tx = GetTransaction(blockindex, node.mempool.get(), hash, Params().GetConsensus(), hash_block);
    if (!tx) {
        std::string errmsg;
        if (blockindex) {
            if (!(blockindex->nStatus & BLOCK_HAVE_DATA)) {
                throw JSONRPCError(RPC_MISC_ERROR, "Block not available");
            }
            errmsg = "No such transaction found in the provided block";
        } else if (!g_txindex) {
            errmsg = "No such mempool transaction. Use -txindex or provide a block hash to enable blockchain transaction queries";
        } else if (!f_txindex_ready) {
            errmsg = "No such mempool transaction. Blockchain transactions are still in the process of being indexed";
        } else {
            errmsg = "No such mempool or blockchain transaction";
        }
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, errmsg + ". Use gettransaction for wallet transactions.");
    }

    if (!fVerbose) {
        return EncodeHexTx(CTransaction(*tx), RPCSerializationFlags());
    }

    UniValue result(UniValue::VOBJ);
    if (blockindex) result.pushKV("in_active_chain", in_active_chain);
    TxToJSON(*tx, hash_block, result);
    return result;
},
    };
}

static RPCHelpMan gettxoutproof()
{
    return RPCHelpMan{"gettxoutproof",
                "\nReturns a hex-encoded proof that \"txid\" was included in a block.\n"
                "\nNOTE: By default this function only works sometimes. This is when there is an\n"
                "unspent output in the utxo for this transaction. To make it always work,\n"
                "you need to maintain a transaction index, using the -txindex command line option or\n"
                "specify the block in which the transaction is included manually (by blockhash).\n",
                {
                    {"txids", RPCArg::Type::ARR, RPCArg::Optional::NO, "The txids to filter",
                        {
                            {"txid", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "A transaction hash"},
                        },
                        },
                    {"blockhash", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED_NAMED_ARG, "If specified, looks for txid in the block with this hash"},
                },
                RPCResult{
                    RPCResult::Type::STR, "data", "A string that is a serialized, hex-encoded data for the proof."
                },
                RPCExamples{""},
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    std::set<uint256> setTxids;
    UniValue txids = request.params[0].get_array();
    if (txids.empty()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Parameter 'txids' cannot be empty");
    }
    for (unsigned int idx = 0; idx < txids.size(); idx++) {
        auto ret = setTxids.insert(ParseHashV(txids[idx], "txid"));
        if (!ret.second) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, std::string("Invalid parameter, duplicated txid: ") + txids[idx].get_str());
        }
    }

    CBlockIndex* pblockindex = nullptr;
    uint256 hashBlock;
    if (!request.params[1].isNull()) {
        LOCK(cs_main);
        hashBlock = ParseHashV(request.params[1], "blockhash");
        pblockindex = g_chainman.m_blockman.LookupBlockIndex(hashBlock);
        if (!pblockindex) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Block not found");
        }
    } else {
        LOCK(cs_main);

        // Loop through txids and try to find which block they're in. Exit loop once a block is found.
        for (const auto& tx : setTxids) {
            const Coin& coin = AccessByTxid(::ChainstateActive().CoinsTip(), tx);
            if (!coin.IsSpent()) {
                pblockindex = ::ChainActive()[coin.nHeight];
                break;
            }
        }
    }


    // Allow txindex to catch up if we need to query it and before we acquire cs_main.
    if (g_txindex && !pblockindex) {
        g_txindex->BlockUntilSyncedToCurrentChain();
    }

    LOCK(cs_main);

    if (pblockindex == nullptr) {
        const CTransactionRef tx = GetTransaction(/* block_index */ nullptr, /* mempool */ nullptr, *setTxids.begin(), Params().GetConsensus(), hashBlock);
        if (!tx || hashBlock.IsNull()) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Transaction not yet in block");
        }
        pblockindex = g_chainman.m_blockman.LookupBlockIndex(hashBlock);
        if (!pblockindex) {
            throw JSONRPCError(RPC_INTERNAL_ERROR, "Transaction index corrupt");
        }
    }

    CBlock block;
    if (!ReadBlockFromDisk(block, pblockindex, Params().GetConsensus())) {
        throw JSONRPCError(RPC_INTERNAL_ERROR, "Can't read block from disk");
    }

    unsigned int ntxFound = 0;
    for (const auto& tx : block.vtx) {
        if (setTxids.count(tx->GetHash())) {
            ntxFound++;
        }
    }
    if (ntxFound != setTxids.size()) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Not all transactions found in specified or retrieved block");
    }

    CDataStream ssMB(SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS);
    CMerkleBlock mb(block, setTxids);
    ssMB << mb;
    std::string strHex = HexStr(ssMB);
    return strHex;
},
    };
}

static RPCHelpMan verifytxoutproof()
{
    return RPCHelpMan{"verifytxoutproof",
                "\nVerifies that a proof points to a transaction in a block, returning the transaction it commits to\n"
                "and throwing an RPC error if the block is not in our best chain\n",
                {
                    {"proof", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The hex-encoded proof generated by gettxoutproof"},
                },
                RPCResult{
                    RPCResult::Type::ARR, "", "",
                    {
                        {RPCResult::Type::STR_HEX, "txid", "The txid(s) which the proof commits to, or empty array if the proof can not be validated."},
                    }
                },
                RPCExamples{""},
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    CDataStream ssMB(ParseHexV(request.params[0], "proof"), SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS);
    CMerkleBlock merkleBlock;
    ssMB >> merkleBlock;

    UniValue res(UniValue::VARR);

    std::vector<uint256> vMatch;
    std::vector<unsigned int> vIndex;
    if (merkleBlock.txn.ExtractMatches(vMatch, vIndex) != merkleBlock.header.hashMerkleRoot)
        return res;

    LOCK(cs_main);

    const CBlockIndex* pindex = g_chainman.m_blockman.LookupBlockIndex(merkleBlock.header.GetHash());
    if (!pindex || !::ChainActive().Contains(pindex) || pindex->nTx == 0) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Block not found in chain");
    }

    // Check if proof is valid, only add results if so
    if (pindex->nTx == merkleBlock.txn.GetNumTransactions()) {
        for (const uint256& hash : vMatch) {
            res.push_back(hash.GetHex());
        }
    }

    return res;
},
    };
}

static RPCHelpMan createrawtransaction()
{
    return RPCHelpMan{"createrawtransaction",
                "\nCreate a transaction spending the given inputs and creating new outputs.\n"
                "Outputs can be addresses or data.\n"
                "Returns hex-encoded raw transaction.\n"
                "Note that the transaction's inputs are not signed, and\n"
                "it is not stored in the wallet or transmitted to the network.\n",
                {
                    {"inputs", RPCArg::Type::ARR, RPCArg::Optional::NO, "The inputs",
                        {
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                                {
                                    {"txid", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The transaction id"},
                                    {"vout", RPCArg::Type::NUM, RPCArg::Optional::NO, "The output number"},
                                    {"sequence", RPCArg::Type::NUM, /* default */ "depends on the value of the 'replaceable' and 'locktime' arguments", "The sequence number"},
                                    {"pegin_bitcoin_tx", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The raw bitcoin transaction (in hex) depositing bitcoin to the mainchain_address generated by getpeginaddress"},
                                    {"pegin_txout_proof", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "A rawtxoutproof (in hex) generated by the mainchain daemon's `gettxoutproof` containing a proof of only bitcoin_tx"},
                                    {"pegin_claim_script", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The claim script generated by getpeginaddress."},
                                },
                                },
                        },
                        },
                    {"outputs", RPCArg::Type::ARR, RPCArg::Optional::NO, "The outputs (key-value pairs), where none of the keys are duplicated.\n"
                            "That is, each address can only appear once and there can only be one 'data' object.\n"
                            "For compatibility reasons, a dictionary, which holds the key-value pairs directly, is also\n"
                            "                             accepted as second parameter.",
                        {
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                                {
                                    {"address", RPCArg::Type::AMOUNT, RPCArg::Optional::NO, "A key-value pair. The key (string) is the bitcoin address, the value (float or string) is the amount in " + CURRENCY_UNIT},
                                },
                                },
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                                {
                                    {"data", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "A key-value pair. The key must be \"data\", the value is hex-encoded data"},
                                },
                                },
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                                {
                                    {"vdata", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The key is \"vdata\", the value is an array of hex encoded data"},
                                },
                                },
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                                {
                                    {"burn", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "A key-value pair. The key must be \"burn\", the value is the amount that will be burned."},
                                },
                                },
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                                {
                                    {"fee", RPCArg::Type::AMOUNT, RPCArg::Optional::NO, "The key is \"fee\", the value the fee output you want to add."},
                                },
                                },
                        },
                        },
                    {"locktime", RPCArg::Type::NUM, /* default */ "0", "Raw locktime. Non-0 value also locktime-activates inputs"},
                    {"replaceable", RPCArg::Type::BOOL, /* default */ "false", "Marks this transaction as BIP125-replaceable.\n"
            "                             Allows this transaction to be replaced by a transaction with higher fees. If provided, it is an error if explicit sequence numbers are incompatible."},
                    {"output_assets", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "A json object of addresses to the assets (label or hex ID) used to pay them. (default: bitcoin)",
                        {
                            {"address", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "A key-value pair. The key (string) is the bitcoin address, the value is the asset label or asset ID."},
                            {"fee", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "A key-value pair. The key (string) is the bitcoin address, the value is the asset label or asset ID."},
                        },
                        },
                },
                RPCResult{
                    RPCResult::Type::STR_HEX, "transaction", "hex string of the transaction"
                },
                RPCExamples{
                    HelpExampleCli("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\" \"[{\\\"address\\\":0.01}]\"")
            + HelpExampleCli("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\" \"[{\\\"data\\\":\\\"00010203\\\"}]\"")
            + HelpExampleRpc("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\", \"[{\\\"address\\\":0.01}]\"")
            + HelpExampleRpc("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\", \"[{\\\"data\\\":\\\"00010203\\\"}]\"")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    RPCTypeCheck(request.params, {
        UniValue::VARR,
        UniValueType(), // ARR or OBJ, checked later
        UniValue::VNUM,
        UniValue::VBOOL,
        UniValue::VOBJ
        }, true
    );

    bool rbf = false;
    if (!request.params[3].isNull()) {
        rbf = request.params[3].isTrue();
    }
    CMutableTransaction rawTx = ConstructTransaction(request.params[0], request.params[1], request.params[2], rbf, request.params[4]);

    return EncodeHexTx(CTransaction(rawTx));
},
    };
}

static RPCHelpMan decoderawtransaction()
{
    return RPCHelpMan{"decoderawtransaction",
                "\nReturn a JSON object representing the serialized, hex-encoded transaction.\n",
                {
                    {"hexstring", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The transaction hex string"},
                    {"iswitness", RPCArg::Type::BOOL, /* default */ "depends on heuristic tests", "Whether the transaction hex is a serialized witness transaction.\n"
                        "If iswitness is not present, heuristic tests will be used in decoding.\n"
                        "If true, only witness deserialization will be tried.\n"
                        "If false, only non-witness deserialization will be tried.\n"
                        "This boolean should reflect whether the transaction has inputs\n"
                        "(e.g. fully valid, or on-chain transactions), if known by the caller."
                    },
                },
                RPCResult{
                    RPCResult::Type::OBJ, "", "",
                    {
                        {RPCResult::Type::STR_HEX, "txid", "The transaction id"},
                        {RPCResult::Type::STR_HEX, "hash", "The transaction hash (differs from txid for witness transactions)"},
                        {RPCResult::Type::NUM, "size", "The transaction size"},
                        {RPCResult::Type::NUM, "vsize", "The virtual transaction size (differs from size for witness transactions)"},
                        {RPCResult::Type::NUM, "weight", "The transaction's weight (between vsize*4 - 3 and vsize*4)"},
                        {RPCResult::Type::NUM, "version", "The version"},
                        {RPCResult::Type::NUM_TIME, "locktime", "The lock time"},
                        {RPCResult::Type::ARR, "vin", "",
                        {
                            {RPCResult::Type::OBJ, "", "",
                            {
                                {RPCResult::Type::STR_HEX, "txid", "The transaction id"},
                                {RPCResult::Type::NUM, "vout", "The output number"},
                                {RPCResult::Type::OBJ, "scriptSig", "The script",
                                {
                                    {RPCResult::Type::STR, "asm", "asm"},
                                    {RPCResult::Type::STR_HEX, "hex", "hex"},
                                }},
                                {RPCResult::Type::ARR, "txinwitness", "",
                                {
                                    {RPCResult::Type::STR_HEX, "hex", "hex-encoded witness data (if any)"},
                                }},
                                {RPCResult::Type::NUM, "sequence", "The script sequence number"},
                            }},
                        }},
                        {RPCResult::Type::ARR, "vout", "",
                        {
                            {RPCResult::Type::OBJ, "", "",
                            {
                                {RPCResult::Type::NUM, "value", "The value in " + CURRENCY_UNIT},
                                {RPCResult::Type::NUM, "n", "index"},
                                {RPCResult::Type::OBJ, "scriptPubKey", "",
                                {
                                    {RPCResult::Type::STR, "asm", "the asm"},
                                    {RPCResult::Type::STR_HEX, "hex", "the hex"},
                                    {RPCResult::Type::NUM, "reqSigs", "The required sigs"},
                                    {RPCResult::Type::STR, "type", "The type, eg 'pubkeyhash'"},
                                    {RPCResult::Type::ARR, "addresses", "",
                                    {
                                        {RPCResult::Type::STR, "address", "bitcoin address"},
                                    }},
                                }},
                            }},
                        }},
                    }
                },
                RPCExamples{
                    HelpExampleCli("decoderawtransaction", "\"hexstring\"")
            + HelpExampleRpc("decoderawtransaction", "\"hexstring\"")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    RPCTypeCheck(request.params, {UniValue::VSTR, UniValue::VBOOL});

    CMutableTransaction mtx;

    bool try_witness = request.params[1].isNull() ? true : request.params[1].get_bool();
    bool try_no_witness = request.params[1].isNull() ? true : !request.params[1].get_bool();

    if (!DecodeHexTx(mtx, request.params[0].get_str(), try_no_witness, try_witness)) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    }

    UniValue result(UniValue::VOBJ);
    TxToUniv(CTransaction(std::move(mtx)), uint256(), result, false);

    return result;
},
    };
}

static std::string GetAllOutputTypes()
{
    std::vector<std::string> ret;
    using U = std::underlying_type<TxoutType>::type;
    for (U i = (U)TxoutType::NONSTANDARD; i <= (U)TxoutType::WITNESS_UNKNOWN; ++i) {
        ret.emplace_back(GetTxnOutputType(static_cast<TxoutType>(i)));
    }
    return Join(ret, ", ");
}

static RPCHelpMan decodescript()
{
    return RPCHelpMan{"decodescript",
                "\nDecode a hex-encoded script.\n",
                {
                    {"hexstring", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "the hex-encoded script"},
                },
                RPCResult{
                    RPCResult::Type::OBJ, "", "",
                    {
                        {RPCResult::Type::STR, "asm", "Script public key"},
                        {RPCResult::Type::STR, "type", "The output type (e.g. "+GetAllOutputTypes()+")"},
                        {RPCResult::Type::NUM, "reqSigs", "The required signatures"},
                        {RPCResult::Type::ARR, "addresses", "",
                        {
                            {RPCResult::Type::STR, "address", "bitcoin address"},
                        }},
                        {RPCResult::Type::STR, "p2sh", "address of P2SH script wrapping this redeem script (not returned if the script is already a P2SH)"},
                        {RPCResult::Type::OBJ, "segwit", "Result of a witness script public key wrapping this redeem script (not returned if the script is a P2SH or witness)",
                        {
                            {RPCResult::Type::STR, "asm", "String representation of the script public key"},
                            {RPCResult::Type::STR_HEX, "hex", "Hex string of the script public key"},
                            {RPCResult::Type::STR, "type", "The type of the script public key (e.g. witness_v0_keyhash or witness_v0_scripthash)"},
                            {RPCResult::Type::NUM, "reqSigs", "The required signatures (always 1)"},
                            {RPCResult::Type::ARR, "addresses", "(always length 1)",
                            {
                                {RPCResult::Type::STR, "address", "segwit address"},
                            }},
                            {RPCResult::Type::STR, "p2sh-segwit", "address of the P2SH script wrapping this witness redeem script"},
                        }},
                    }
                },
                RPCExamples{
                    HelpExampleCli("decodescript", "\"hexstring\"")
            + HelpExampleRpc("decodescript", "\"hexstring\"")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    RPCTypeCheck(request.params, {UniValue::VSTR});

    UniValue r(UniValue::VOBJ);
    CScript script;
    if (request.params[0].get_str().size() > 0){
        std::vector<unsigned char> scriptData(ParseHexV(request.params[0], "argument"));
        script = CScript(scriptData.begin(), scriptData.end());
    } else {
        // Empty scripts are valid
    }
    ScriptPubKeyToUniv(script, r, /* fIncludeHex */ false);

    UniValue type;
    type = find_value(r, "type");

    if (type.isStr() && type.get_str() != "scripthash") {
        // P2SH cannot be wrapped in a P2SH. If this script is already a P2SH,
        // don't return the address for a P2SH of the P2SH.
        r.pushKV("p2sh", EncodeDestination(ScriptHash(script)));
        // P2SH and witness programs cannot be wrapped in P2WSH, if this script
        // is a witness program, don't return addresses for a segwit programs.
        if (type.get_str() == "pubkey" || type.get_str() == "pubkeyhash" || type.get_str() == "multisig" || type.get_str() == "nonstandard" || type.get_str() == "true") {
            std::vector<std::vector<unsigned char>> solutions_data;
            TxoutType which_type = Solver(script, solutions_data);
            // Uncompressed pubkeys cannot be used with segwit checksigs.
            // If the script contains an uncompressed pubkey, skip encoding of a segwit program.
            if ((which_type == TxoutType::PUBKEY) || (which_type == TxoutType::MULTISIG)) {
                for (const auto& solution : solutions_data) {
                    if ((solution.size() != 1) && !CPubKey(solution).IsCompressed()) {
                        return r;
                    }
                }
            }
            UniValue sr(UniValue::VOBJ);
            CScript segwitScr;
            if (which_type == TxoutType::PUBKEY) {
                segwitScr = GetScriptForDestination(WitnessV0KeyHash(Hash160(solutions_data[0])));
            } else if (which_type == TxoutType::PUBKEYHASH) {
                segwitScr = GetScriptForDestination(WitnessV0KeyHash(uint160{solutions_data[0]}));
            } else {
                // Scripts that are not fit for P2WPKH are encoded as P2WSH.
                // Newer segwit program versions should be considered when then become available.
                segwitScr = GetScriptForDestination(WitnessV0ScriptHash(script));
            }
            ScriptPubKeyToUniv(segwitScr, sr, /* fIncludeHex */ true);
            sr.pushKV("p2sh-segwit", EncodeDestination(ScriptHash(segwitScr)));
            r.pushKV("segwit", sr);
        }
    }

    return r;
},
    };
}

static RPCHelpMan combinerawtransaction()
{
    return RPCHelpMan{"combinerawtransaction",
                "\nCombine multiple partially signed transactions into one transaction.\n"
                "The combined transaction may be another partially signed transaction or a \n"
                "fully signed transaction.",
                {
                    {"txs", RPCArg::Type::ARR, RPCArg::Optional::NO, "The hex strings of partially signed transactions",
                        {
                            {"hexstring", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "A hex-encoded raw transaction"},
                        },
                        },
                },
                RPCResult{
                    RPCResult::Type::STR, "", "The hex-encoded raw transaction with signature(s)"
                },
                RPCExamples{
                    HelpExampleCli("combinerawtransaction", R"('["myhex1", "myhex2", "myhex3"]')")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{

    UniValue txs = request.params[0].get_array();
    std::vector<CMutableTransaction> txVariants(txs.size());

    for (unsigned int idx = 0; idx < txs.size(); idx++) {
        if (!DecodeHexTx(txVariants[idx], txs[idx].get_str())) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR, strprintf("TX decode failed for tx %d. Make sure the tx has at least one input.", idx));
        }
    }

    if (txVariants.empty()) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Missing transactions");
    }

    // mergedTx will end up with all the signatures; it
    // starts as a clone of the rawtx:
    CMutableTransaction mergedTx(txVariants[0]);

    // Fetch previous transactions (inputs):
    CCoinsView viewDummy;
    CCoinsViewCache view(&viewDummy);
    {
        const CTxMemPool& mempool = EnsureMemPool(request.context);
        LOCK(cs_main);
        LOCK(mempool.cs);
        CCoinsViewCache &viewChain = ::ChainstateActive().CoinsTip();
        CCoinsViewMemPool viewMempool(&viewChain, mempool);
        view.SetBackend(viewMempool); // temporarily switch cache backend to db+mempool view

        for (const CTxIn& txin : mergedTx.vin) {
            view.AccessCoin(txin.prevout); // Load entries from viewChain into view; can fail.
        }

        view.SetBackend(viewDummy); // switch back to avoid locking mempool for too long
    }

    // Sign what we can:
    for (unsigned int i = 0; i < mergedTx.vin.size(); i++) {
        CTxIn& txin = mergedTx.vin[i];
        const Coin& coin = view.AccessCoin(txin.prevout);
        if (coin.IsSpent()) {
            throw JSONRPCError(RPC_VERIFY_ERROR, "Input not found or already spent");
        }
        SignatureData sigdata;

        // ... and merge in other signatures:
        for (const CMutableTransaction& txv : txVariants) {
            if (txv.vin.size() > i) {
                sigdata.MergeSignatureData(DataFromTransaction(txv, i, coin.out));
            }
        }
        ProduceSignature(DUMMY_SIGNING_PROVIDER, MutableTransactionSignatureCreator(&mergedTx, i, coin.out.nValue, 1), coin.out.scriptPubKey, sigdata);

        UpdateTransaction(mergedTx, i, sigdata);
    }

    return EncodeHexTx(CTransaction(mergedTx));
},
    };
}

static RPCHelpMan signrawtransactionwithkey()
{
    return RPCHelpMan{"signrawtransactionwithkey",
                "\nSign inputs for raw transaction (serialized, hex-encoded).\n"
                "The second argument is an array of base58-encoded private\n"
                "keys that will be the only keys used to sign the transaction.\n"
                "The third optional argument (may be null) is an array of previous transaction outputs that\n"
                "this transaction depends on but may not yet be in the block chain.\n",
                {
                    {"hexstring", RPCArg::Type::STR, RPCArg::Optional::NO, "The transaction hex string"},
                    {"privkeys", RPCArg::Type::ARR, RPCArg::Optional::NO, "The base58-encoded private keys for signing",
                        {
                            {"privatekey", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "private key in base58-encoding"},
                        },
                        },
                    {"prevtxs", RPCArg::Type::ARR, RPCArg::Optional::OMITTED_NAMED_ARG, "The previous dependent transaction outputs",
                        {
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                                {
                                    {"txid", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The transaction id"},
                                    {"vout", RPCArg::Type::NUM, RPCArg::Optional::NO, "The output number"},
                                    {"scriptPubKey", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "script key"},
                                    {"redeemScript", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "(required for P2SH) redeem script"},
                                    {"witnessScript", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "(required for P2WSH or P2SH-P2WSH) witness script"},
                                    {"amount", RPCArg::Type::AMOUNT, RPCArg::Optional::OMITTED, "The amount spent (required if non-confidential segwit output)"},
                                    {"amountcommitment", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "The amount commitment spent (required if confidential segwit output)"},
                                },
                                },
                        },
                        },
                    {"sighashtype", RPCArg::Type::STR, /* default */ "ALL", "The signature hash type. Must be one of:\n"
            "       \"ALL\"\n"
            "       \"NONE\"\n"
            "       \"SINGLE\"\n"
            "       \"ALL|ANYONECANPAY\"\n"
            "       \"NONE|ANYONECANPAY\"\n"
            "       \"SINGLE|ANYONECANPAY\"\n"
                    },
                },
                RPCResult{
                    RPCResult::Type::OBJ, "", "",
                    {
                        {RPCResult::Type::STR_HEX, "hex", "The hex-encoded raw transaction with signature(s)"},
                        {RPCResult::Type::BOOL, "complete", "If the transaction has a complete set of signatures"},
                        {RPCResult::Type::ARR, "errors", /* optional */ true, "Script verification errors (if there are any)",
                        {
                            {RPCResult::Type::OBJ, "", "",
                            {
                                {RPCResult::Type::STR_HEX, "txid", "The hash of the referenced, previous transaction"},
                                {RPCResult::Type::NUM, "vout", "The index of the output to spent and used as input"},
                                {RPCResult::Type::STR_HEX, "scriptSig", "The hex-encoded signature script"},
                                {RPCResult::Type::NUM, "sequence", "Script sequence number"},
                                {RPCResult::Type::STR, "error", "Verification or signing error related to the input"},
                            }},
                        }},
                        {RPCResult::Type::STR, "warning", "Warning that a peg-in input signed may be immature. This could mean lack of connectivity to or misconfiguration of the daemon"},
                    }
                },
                RPCExamples{
                    HelpExampleCli("signrawtransactionwithkey", "\"myhex\" \"[\\\"key1\\\",\\\"key2\\\"]\"")
            + HelpExampleRpc("signrawtransactionwithkey", "\"myhex\", \"[\\\"key1\\\",\\\"key2\\\"]\"")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    RPCTypeCheck(request.params, {UniValue::VSTR, UniValue::VARR, UniValue::VARR, UniValue::VSTR}, true);

    CMutableTransaction mtx;
    if (!DecodeHexTx(mtx, request.params[0].get_str())) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed. Make sure the tx has at least one input.");
    }

    FillableSigningProvider keystore;
    const UniValue& keys = request.params[1].get_array();
    for (unsigned int idx = 0; idx < keys.size(); ++idx) {
        UniValue k = keys[idx];
        CKey key = DecodeSecret(k.get_str());
        if (!key.IsValid()) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid private key");
        }
        keystore.AddKey(key);
    }

    // Fetch previous transactions (inputs):
    std::map<COutPoint, Coin> coins;
    for (const CTxIn& txin : mtx.vin) {
        coins[txin.prevout]; // Create empty map entry keyed by prevout.
    }
    NodeContext& node = EnsureNodeContext(request.context);
    FindCoins(node, coins);

    // Parse the prevtxs array
    ParsePrevouts(request.params[2], &keystore, coins);

    UniValue result(UniValue::VOBJ);
    SignTransaction(mtx, &keystore, coins, request.params[3], result);
    return result;
},
    };
}

static RPCHelpMan sendrawtransaction()
{
    return RPCHelpMan{"sendrawtransaction",
                "\nSubmit a raw transaction (serialized, hex-encoded) to local node and network.\n"
                "\nThe transaction will be sent unconditionally to all peers, so using sendrawtransaction\n"
                "for manual rebroadcast may degrade privacy by leaking the transaction's origin, as\n"
                "nodes will normally not rebroadcast non-wallet transactions already in their mempool.\n"
                "\nA specific exception, RPC_TRANSACTION_ALREADY_IN_CHAIN, may throw if the transaction cannot be added to the mempool.\n"
                "\nRelated RPCs: createrawtransaction, signrawtransactionwithkey\n",
                {
                    {"hexstring", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The hex string of the raw transaction"},
                    {"maxfeerate", RPCArg::Type::AMOUNT, /* default */ FormatMoney(DEFAULT_MAX_RAW_TX_FEE_RATE.GetFeePerK()),
                        "Reject transactions whose fee rate is higher than the specified value, expressed in " + CURRENCY_UNIT +
                            "/kB.\nSet to 0 to accept any fee rate.\n"},
                },
                RPCResult{
                    RPCResult::Type::STR_HEX, "", "The transaction hash in hex"
                },
                RPCExamples{
            "\nCreate a transaction\n"
            + HelpExampleCli("createrawtransaction", "\"[{\\\"txid\\\" : \\\"mytxid\\\",\\\"vout\\\":0}]\" \"{\\\"myaddress\\\":0.01}\"") +
            "Sign the transaction, and get back the hex\n"
            + HelpExampleCli("signrawtransactionwithwallet", "\"myhex\"") +
            "\nSend the transaction (signed hex)\n"
            + HelpExampleCli("sendrawtransaction", "\"signedhex\"") +
            "\nAs a JSON-RPC call\n"
            + HelpExampleRpc("sendrawtransaction", "\"signedhex\"")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    RPCTypeCheck(request.params, {
        UniValue::VSTR,
        UniValueType(), // VNUM or VSTR, checked inside AmountFromValue()
    });

    CMutableTransaction mtx;
    if (!DecodeHexTx(mtx, request.params[0].get_str())) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed. Make sure the tx has at least one input.");
    }
    CTransactionRef tx(MakeTransactionRef(std::move(mtx)));

    const CFeeRate max_raw_tx_fee_rate = request.params[1].isNull() ?
                                             DEFAULT_MAX_RAW_TX_FEE_RATE :
                                             CFeeRate(AmountFromValue(request.params[1]));

    for (const auto& out : tx->vout) {
        // If we have a nonce, it could be a smuggled pubkey, or it could be a
        //   proper nonce produced by blinding. In the latter case, the value
        //   will always be blinded and not explicit. In the former case, we
        //   error out because the transaction is not blinded properly.
        if (!out.nNonce.IsNull() && out.nValue.IsExplicit()) {
            throw JSONRPCError(RPC_TRANSACTION_ERROR, "Transaction output has nonce, but is not blinded. Did you forget to call blindpsbt, blindrawtranssaction, or rawblindrawtransaction?");
        }
    }

    int64_t virtual_size = GetVirtualTransactionSize(*tx);
    CAmount max_raw_tx_fee = max_raw_tx_fee_rate.GetFee(virtual_size);

    std::string err_string;
    AssertLockNotHeld(cs_main);
    NodeContext& node = EnsureNodeContext(request.context);
    const TransactionError err = BroadcastTransaction(node, tx, err_string, max_raw_tx_fee, /*relay*/ true, /*wait_callback*/ true);
    if (TransactionError::OK != err) {
        throw JSONRPCTransactionError(err, err_string);
    }

    return tx->GetHash().GetHex();
},
    };
}

static RPCHelpMan testmempoolaccept()
{
    return RPCHelpMan{"testmempoolaccept",
                "\nReturns result of mempool acceptance tests indicating if raw transaction (serialized, hex-encoded) would be accepted by mempool.\n"
                "\nThis checks if the transaction violates the consensus or policy rules.\n"
                "\nSee sendrawtransaction call.\n",
                {
                    {"rawtxs", RPCArg::Type::ARR, RPCArg::Optional::NO, "An array of hex strings of raw transactions.\n"
            "                                        Length must be one for now.",
                        {
                            {"rawtx", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, ""},
                        },
                        },
                    {"maxfeerate", RPCArg::Type::AMOUNT, /* default */ FormatMoney(DEFAULT_MAX_RAW_TX_FEE_RATE.GetFeePerK()), "Reject transactions whose fee rate is higher than the specified value, expressed in " + CURRENCY_UNIT + "/kB\n"},
                },
                RPCResult{
                    RPCResult::Type::ARR, "", "The result of the mempool acceptance test for each raw transaction in the input array.\n"
                        "Length is exactly one for now.",
                    {
                        {RPCResult::Type::OBJ, "", "",
                        {
                            {RPCResult::Type::STR_HEX, "txid", "The transaction hash in hex"},
                            {RPCResult::Type::STR_HEX, "wtxid", "The transaction witness hash in hex"},
                            {RPCResult::Type::BOOL, "allowed", "If the mempool allows this tx to be inserted"},
                            {RPCResult::Type::NUM, "vsize", "Virtual transaction size as defined in BIP 141. This is different from actual serialized size for witness transactions as witness data is discounted (only present when 'allowed' is true)"},
                            {RPCResult::Type::OBJ, "fees", "Transaction fees (only present if 'allowed' is true)",
                            {
                                {RPCResult::Type::STR_AMOUNT, "base", "transaction fee in " + CURRENCY_UNIT},
                            }},
                            {RPCResult::Type::STR, "reject-reason", "Rejection string (only present when 'allowed' is false)"},
                        }},
                    }
                },
                RPCExamples{
            "\nCreate a transaction\n"
            + HelpExampleCli("createrawtransaction", "\"[{\\\"txid\\\" : \\\"mytxid\\\",\\\"vout\\\":0}]\" \"{\\\"myaddress\\\":0.01}\"") +
            "Sign the transaction, and get back the hex\n"
            + HelpExampleCli("signrawtransactionwithwallet", "\"myhex\"") +
            "\nTest acceptance of the transaction (signed hex)\n"
            + HelpExampleCli("testmempoolaccept", R"('["signedhex"]')") +
            "\nAs a JSON-RPC call\n"
            + HelpExampleRpc("testmempoolaccept", "[\"signedhex\"]")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    RPCTypeCheck(request.params, {
        UniValue::VARR,
        UniValueType(), // VNUM or VSTR, checked inside AmountFromValue()
    });

    if (request.params[0].get_array().size() != 1) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Array must contain exactly one raw transaction for now");
    }

    CMutableTransaction mtx;
    if (!DecodeHexTx(mtx, request.params[0].get_array()[0].get_str())) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed. Make sure the tx has at least one input.");
    }
    CTransactionRef tx(MakeTransactionRef(std::move(mtx)));

    const CFeeRate max_raw_tx_fee_rate = request.params[1].isNull() ?
                                             DEFAULT_MAX_RAW_TX_FEE_RATE :
                                             CFeeRate(AmountFromValue(request.params[1]));

    CTxMemPool& mempool = EnsureMemPool(request.context);
    int64_t virtual_size = GetVirtualTransactionSize(*tx);
    CAmount max_raw_tx_fee = max_raw_tx_fee_rate.GetFee(virtual_size);

    UniValue result(UniValue::VARR);
    UniValue result_0(UniValue::VOBJ);
    result_0.pushKV("txid", tx->GetHash().GetHex());
    result_0.pushKV("wtxid", tx->GetWitnessHash().GetHex());

    const MempoolAcceptResult accept_result = WITH_LOCK(cs_main, return AcceptToMemoryPool(::ChainstateActive(), mempool, std::move(tx),
                                                  false /* bypass_limits */, /* test_accept */ true));

    // Only return the fee and vsize if the transaction would pass ATMP.
    // These can be used to calculate the feerate.
    if (accept_result.m_result_type == MempoolAcceptResult::ResultType::VALID) {
        const CAmount fee = accept_result.m_base_fees.value();
        // Check that fee does not exceed maximum fee
        if (max_raw_tx_fee && fee > max_raw_tx_fee) {
            result_0.pushKV("allowed", false);
            result_0.pushKV("reject-reason", "max-fee-exceeded");
        } else {
            result_0.pushKV("allowed", true);
            result_0.pushKV("vsize", virtual_size);
            UniValue fees(UniValue::VOBJ);
            fees.pushKV("base", ValueFromAmount(fee));
            result_0.pushKV("fees", fees);
        }
        result.push_back(std::move(result_0));
    } else {
        result_0.pushKV("allowed", false);
        const TxValidationState state = accept_result.m_state;
        if (state.GetResult() == TxValidationResult::TX_MISSING_INPUTS) {
            result_0.pushKV("reject-reason", "missing-inputs");
        } else {
            result_0.pushKV("reject-reason", state.GetRejectReason());
        }
        result.push_back(std::move(result_0));
    }
    return result;
},
    };
}

static RPCHelpMan blindpsbt()
{
    return RPCHelpMan{"blindpsbt",
                "\nUses the blinding data from the PSBT inputs to generate the blinding data for the PSBT outputs.\n",
                {
                    {"psbt", RPCArg::Type::STR, RPCArg::Optional::NO, "The PSBT base64 string"},
                    {"ignoreblindfail", RPCArg::Type::BOOL, /* default*/ "true", "Return a transaction even when a blinding attempt fails due to number of blinded inputs/outputs."},
                },
                RPCResult{
                    RPCResult::Type::STR, "psbt", "base64-encoded partially signed transaction",
                },
                RPCExamples{
                    HelpExampleCli("blindpsbt", "\"psbt\"")
                    + HelpExampleRpc("blindpsbt", "\"psbt\"")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    if (!g_con_elementsmode)
        throw std::runtime_error("PSBT operations are disabled when not in elementsmode.\n");

    RPCTypeCheck(request.params, {UniValue::VSTR, UniValue::VBOOL}, true);

    // Unserialize the transactions
    PartiallySignedTransaction psbtx;
    std::string error;
    if (!DecodeBase64PSBT(psbtx, request.params[0].get_str(), error)) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, strprintf("TX decode failed %s", error));
    }

    bool fIgnoreBlindFail = true;
    if (!request.params[1].isNull()) {
        fIgnoreBlindFail = request.params[1].get_bool();
    }

    // TODO(gwillen): Refactor out significant duplicated code between here and rawblindrawtransaction.

    std::vector<CAmount> input_amounts;
    std::vector<uint256> input_blinds;
    std::vector<uint256> input_asset_blinds;
    std::vector<CAsset> input_assets;
    std::vector<uint256> output_value_blinds;
    std::vector<uint256> output_asset_blinds;
    std::vector<CAsset> output_assets;
    std::vector<CPubKey> output_pubkeys;

    int n_blinded_ins = 0;

    // TODO(gwillen): If blinding is not possible due to missing input data, we should bail here with a useful error message.
    for (const auto& input : psbtx.inputs) {
        input_blinds.push_back(input.value_blinding_factor);
        input_asset_blinds.push_back(input.asset_blinding_factor);
        input_assets.push_back(input.asset);
        input_amounts.push_back(input.value ? *input.value : CAmount(-1));

        if (!input_blinds.back().IsNull()) {
            n_blinded_ins++;
        }
    }

    for (auto& output : psbtx.outputs) {
        output_pubkeys.push_back(output.blinding_pubkey);
    }

    // How many are we trying to blind?
    int num_pubkeys = 0;
    unsigned int keyIndex = (unsigned) -1;
    for (unsigned int i = 0; i < output_pubkeys.size(); i++) {
        const CPubKey& key = output_pubkeys[i];
        if (key.IsValid()) {
            num_pubkeys++;
            keyIndex = i;
        }
    }

    CMutableTransaction& tx = *psbtx.tx;

    // TODO(gwillen): Replace all this with the 'bonus output' scheme to use an OP_RETURN to balance blinders, with a rangeproof exponent of -1 (public).
    if (num_pubkeys == 0 && n_blinded_ins == 0) {
        // Vacuous, just return the transaction
        return EncodePSBT(psbtx);
    } else if (n_blinded_ins > 0 && num_pubkeys == 0) {
        // No notion of wallet, cannot complete this blinding without passed-in pubkey
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Unable to blind transaction: Add another output to blind in order to complete the blinding.");
    } else if (n_blinded_ins == 0 && num_pubkeys == 1) {
        if (fIgnoreBlindFail) {
            // Remove the pubkey to signal that blinding is complete
            psbtx.outputs[keyIndex].blinding_pubkey = CPubKey();
            return EncodePSBT(psbtx);
        } else {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Unable to blind transaction: Add another output to blind in order to complete the blinding.");
        }
    }

    CMutableTransaction tx_tmp = tx;  // We don't want to mutate the transaction in the PSBT yet, just extract blinding data

    // TODO(gwillen): Make this do something better than fail silently if there are any issuances, reissuances, pegins, etc.
    int ret = BlindTransaction(input_blinds, input_asset_blinds, input_assets, input_amounts, output_value_blinds, output_asset_blinds, output_pubkeys, std::vector<CKey>(), std::vector<CKey>(), tx_tmp);
    if (ret != num_pubkeys) {
        // TODO Have more rich return values, communicating to user what has been blinded
        // User may be ok not blinding something that for instance has no corresponding type on input
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Unable to blind transaction: Are you sure each asset type to blind is represented in the inputs?");
    }

    for (size_t i = 0; i < psbtx.outputs.size(); ++i) {
        PSBTOutput& o = psbtx.outputs[i];

        o.value_commitment = tx_tmp.vout[i].nValue;
        o.asset_commitment = tx_tmp.vout[i].nAsset;
        o.nonce_commitment = tx_tmp.vout[i].nNonce;
        o.value_blinding_factor = output_value_blinds[i];
        o.asset_blinding_factor = output_asset_blinds[i];
        o.range_proof = tx_tmp.witness.vtxoutwit[i].vchRangeproof;
        o.surjection_proof = tx_tmp.witness.vtxoutwit[i].vchSurjectionproof;

        o.blinding_pubkey = CPubKey();  // Once we're done blinding, remove the pubkeys to signal that it's complete
    }

    return EncodePSBT(psbtx);
},
    };
}

static RPCHelpMan decodepsbt()
{
    return RPCHelpMan{"decodepsbt",
                "\nReturn a JSON object representing the serialized, base64-encoded partially signed Bitcoin transaction.\n",
                {
                    {"psbt", RPCArg::Type::STR, RPCArg::Optional::NO, "The PSBT base64 string"},
                },
                RPCResult{
                    RPCResult::Type::OBJ, "", "",
                    {
                        {RPCResult::Type::OBJ, "tx", "The decoded network-serialized unsigned transaction.",
                        {
                            {RPCResult::Type::ELISION, "", "The layout is the same as the output of decoderawtransaction."},
                        }},
                        {RPCResult::Type::OBJ_DYN, "unknown", "The unknown global fields",
                        {
                             {RPCResult::Type::STR_HEX, "key", "(key-value pair) An unknown key-value pair"},
                        }},
                        {RPCResult::Type::ARR, "inputs", "",
                        {
                            {RPCResult::Type::OBJ, "", "",
                            {
                                {RPCResult::Type::OBJ, "non_witness_utxo", /* optional */ true, "Decoded network transaction for non-witness UTXOs",
                                {
                                    {RPCResult::Type::ELISION, "",""},
                                }},
                                {RPCResult::Type::OBJ, "witness_utxo", /* optional */ true, "Transaction output for witness UTXOs",
                                {
                                    {RPCResult::Type::NUM, "amount", "The value in " + CURRENCY_UNIT},
                                    {RPCResult::Type::OBJ, "scriptPubKey", "",
                                    {
                                        {RPCResult::Type::STR, "asm", "The asm"},
                                        {RPCResult::Type::STR_HEX, "hex", "The hex"},
                                        {RPCResult::Type::STR, "type", "The type, eg 'pubkeyhash'"},
                                        {RPCResult::Type::STR, "address"," Bitcoin address if there is one"},
                                    }},
                                }},
                                {RPCResult::Type::OBJ_DYN, "partial_signatures", /* optional */ true, "",
                                {
                                    {RPCResult::Type::STR, "pubkey", "The public key and signature that corresponds to it."},
                                }},
                                {RPCResult::Type::STR, "sighash", /* optional */ true, "The sighash type to be used"},
                                {RPCResult::Type::OBJ, "redeem_script", /* optional */ true, "",
                                {
                                    {RPCResult::Type::STR, "asm", "The asm"},
                                    {RPCResult::Type::STR_HEX, "hex", "The hex"},
                                    {RPCResult::Type::STR, "type", "The type, eg 'pubkeyhash'"},
                                }},
                                {RPCResult::Type::OBJ, "witness_script", /* optional */ true, "",
                                {
                                    {RPCResult::Type::STR, "asm", "The asm"},
                                    {RPCResult::Type::STR_HEX, "hex", "The hex"},
                                    {RPCResult::Type::STR, "type", "The type, eg 'pubkeyhash'"},
                                }},
                                {RPCResult::Type::ARR, "bip32_derivs", /* optional */ true, "",
                                {
                                    {RPCResult::Type::OBJ, "pubkey", /* optional */ true, "The public key with the derivation path as the value.",
                                    {
                                        {RPCResult::Type::STR, "master_fingerprint", "The fingerprint of the master key"},
                                        {RPCResult::Type::STR, "path", "The path"},
                                    }},
                                }},
                                {RPCResult::Type::OBJ, "final_scriptsig", /* optional */ true, "",
                                {
                                    {RPCResult::Type::STR, "asm", "The asm"},
                                    {RPCResult::Type::STR, "hex", "The hex"},
                                }},
                                {RPCResult::Type::ARR, "final_scriptwitness", "",
                                {
                                    {RPCResult::Type::STR_HEX, "", "hex-encoded witness data (if any)"},
                                }},
                                {RPCResult::Type::NUM, "value", "The (unblinded) value of the input in " + CURRENCY_UNIT},
                                {RPCResult::Type::STR_HEX, "value_blinding_factor", "The value blinding factor from the output being spent"},
                                {RPCResult::Type::STR_HEX, "asset", "The (unblinded) asset id of the input"},
                                {RPCResult::Type::STR_HEX, "asset_blinding_factor", "The asset blinding factor from the output being spent\n"},
                                {RPCResult::Type::STR_HEX, "pegin_bitcoin_tx", "The tx providing the peg-in in the format of the getrawtransaction RPC"},
                                {RPCResult::Type::STR_HEX, "pegin_claim_script", "The claim script for the peg-in input"},
                                {RPCResult::Type::STR_HEX, "pegin_txout_proof", "The tx providing the peg-in input"},
                                {RPCResult::Type::STR_HEX, "pegin_genesis_hash", "The hash of the genesis block for this peg-in"},
                                {RPCResult::Type::OBJ_DYN, "unknown", "The unknown global fields",
                                {
                                    {RPCResult::Type::STR_HEX, "key", "(key-value pair) An unknown key-value pair"},
                                }},
                            }},
                        }},
                        {RPCResult::Type::ARR, "outputs", "",
                        {
                            {RPCResult::Type::OBJ, "", "",
                            {
                                {RPCResult::Type::OBJ, "redeem_script", /* optional */ true, "",
                                {
                                    {RPCResult::Type::STR, "asm", "The asm"},
                                    {RPCResult::Type::STR_HEX, "hex", "The hex"},
                                    {RPCResult::Type::STR, "type", "The type, eg 'pubkeyhash'"},
                                }},
                                {RPCResult::Type::OBJ, "witness_script", /* optional */ true, "",
                                {
                                    {RPCResult::Type::STR, "asm", "The asm"},
                                    {RPCResult::Type::STR_HEX, "hex", "The hex"},
                                    {RPCResult::Type::STR, "type", "The type, eg 'pubkeyhash'"},
                                }},
                                {RPCResult::Type::ARR, "bip32_derivs", /* optional */ true, "",
                                {
                                    {RPCResult::Type::OBJ, "", "",
                                    {
                                        {RPCResult::Type::STR, "pubkey", "The public key this path corresponds to"},
                                        {RPCResult::Type::STR, "master_fingerprint", "The fingerprint of the master key"},
                                        {RPCResult::Type::STR, "path", "The path"},
                                    }},
                                }},
                                {RPCResult::Type::STR_HEX, "value_commitment", "The blinded value of the output"},
                                {RPCResult::Type::STR_HEX, "value_blinding_factor", "The value blinding factor for the output"},
                                {RPCResult::Type::STR_HEX, "asset_commiment", "The blinded asset id of the output"},
                                {RPCResult::Type::STR_HEX, "asset_blinding_factor", "The asset blinding factor for the output"},
                                {RPCResult::Type::STR_HEX, "nonce_commiment", "The nonce for the output"},
                                {RPCResult::Type::STR_HEX, "surjection_proof", "The surjection proof for the output"},
                                {RPCResult::Type::STR_HEX, "blinding_pubkey", "The blinding pubkey for the output"},
                                {RPCResult::Type::OBJ_DYN, "unknown", "The unknown global fields",
                                {
                                    {RPCResult::Type::STR_HEX, "key", "(key-value pair) An unknown key-value pair"},
                                }},
                            }},
                        }},
                        {RPCResult::Type::STR_AMOUNT, "fee", /* optional */ true, "The transaction fee paid if all UTXOs slots in the PSBT have been filled."},
                    }
                },
                RPCExamples{
                    HelpExampleCli("decodepsbt", "\"psbt\"")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    if (!g_con_elementsmode)
        throw std::runtime_error("PSBT operations are disabled when not in elementsmode.\n");

    RPCTypeCheck(request.params, {UniValue::VSTR});

    // Unserialize the transactions
    PartiallySignedTransaction psbtx;
    std::string error;
    if (!DecodeBase64PSBT(psbtx, request.params[0].get_str(), error)) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, strprintf("TX decode failed %s", error));
    }
    if (!CheckPSBTBlinding(psbtx, error)) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, error);
    }

    UniValue result(UniValue::VOBJ);

    // Add the decoded tx
    UniValue tx_univ(UniValue::VOBJ);
    TxToUniv(CTransaction(*psbtx.tx), uint256(), tx_univ, false);
    result.pushKV("tx", tx_univ);
    result.pushKV("fees", AmountMapToUniv(GetFeeMap(CTransaction(*psbtx.tx)), ""));

    // Unknown data
    UniValue unknowns(UniValue::VOBJ);
    for (auto entry : psbtx.unknown) {
        unknowns.pushKV(HexStr(entry.first), HexStr(entry.second));
    }
    result.pushKV("unknown", unknowns);

    // inputs
    UniValue inputs(UniValue::VARR);
    for (unsigned int i = 0; i < psbtx.inputs.size(); ++i) {
        const PSBTInput& input = psbtx.inputs[i];
        UniValue in(UniValue::VOBJ);
        // UTXOs
        CTxOut txout;
        if (!input.witness_utxo.IsNull()) {
            txout = input.witness_utxo;

            UniValue o(UniValue::VOBJ);
            ScriptToUniv(txout.scriptPubKey, o, true);

            UniValue out(UniValue::VOBJ);
            if (txout.nValue.IsExplicit()) {
                CAmount nValue = txout.nValue.GetAmount();
                out.pushKV("amount", ValueFromAmount(nValue));
            } else {
                out.pushKV("amountcommitment", txout.nValue.GetHex());
            }
            out.pushKV("scriptPubKey", o);

            in.pushKV("witness_utxo", out);
        }
        if (input.non_witness_utxo) {
            txout = input.non_witness_utxo->vout[psbtx.tx->vin[i].prevout.n];

            UniValue non_wit(UniValue::VOBJ);
            TxToUniv(*input.non_witness_utxo, uint256(), non_wit, false);
            in.pushKV("non_witness_utxo", non_wit);
        }

        // Partial sigs
        if (!input.partial_sigs.empty()) {
            UniValue partial_sigs(UniValue::VOBJ);
            for (const auto& sig : input.partial_sigs) {
                partial_sigs.pushKV(HexStr(sig.second.first), HexStr(sig.second.second));
            }
            in.pushKV("partial_signatures", partial_sigs);
        }

        // Sighash
        if (input.sighash_type > 0) {
            in.pushKV("sighash", SighashToStr((unsigned char)input.sighash_type));
        }

        // Redeem script and witness script
        if (!input.redeem_script.empty()) {
            UniValue r(UniValue::VOBJ);
            ScriptToUniv(input.redeem_script, r, false);
            in.pushKV("redeem_script", r);
        }
        if (!input.witness_script.empty()) {
            UniValue r(UniValue::VOBJ);
            ScriptToUniv(input.witness_script, r, false);
            in.pushKV("witness_script", r);
        }

        // keypaths
        if (!input.hd_keypaths.empty()) {
            UniValue keypaths(UniValue::VARR);
            for (auto entry : input.hd_keypaths) {
                UniValue keypath(UniValue::VOBJ);
                keypath.pushKV("pubkey", HexStr(entry.first));

                keypath.pushKV("master_fingerprint", strprintf("%08x", ReadBE32(entry.second.fingerprint)));
                keypath.pushKV("path", WriteHDKeypath(entry.second.path));
                keypaths.push_back(keypath);
            }
            in.pushKV("bip32_derivs", keypaths);
        }

        // Final scriptSig and scriptwitness
        if (!input.final_script_sig.empty()) {
            UniValue scriptsig(UniValue::VOBJ);
            scriptsig.pushKV("asm", ScriptToAsmStr(input.final_script_sig, true));
            scriptsig.pushKV("hex", HexStr(input.final_script_sig));
            in.pushKV("final_scriptSig", scriptsig);
        }
        if (!input.final_script_witness.IsNull()) {
            UniValue txinwitness(UniValue::VARR);
            for (const auto& item : input.final_script_witness.stack) {
                txinwitness.push_back(HexStr(item));
            }
            in.pushKV("final_scriptwitness", txinwitness);
        }

        // Value
        if (input.value) {
            in.pushKV("value", ValueFromAmount(*input.value));
        }

        // Value blinder
        if (!input.value_blinding_factor.IsNull()) {
            in.pushKV("value_blinding_factor", input.value_blinding_factor.GetHex());
        }

        // Asset
        if (!input.asset.IsNull()) {
            in.pushKV("asset", input.asset.id.GetHex());
        }

        // Asset blinder
        if (!input.asset_blinding_factor.IsNull()) {
            in.pushKV("asset_blinding_factor", input.asset_blinding_factor.GetHex());
        }

        // Peg-in stuff
        if (Params().GetConsensus().ParentChainHasPow()) {
            if (input.peg_in_tx.index() > 0) {
                const auto btc_peg_in_tx = std::get_if<Sidechain::Bitcoin::CTransactionRef>(&input.peg_in_tx);
                if (btc_peg_in_tx) {
                    CDataStream ss_tx(SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS);
                    ss_tx << *btc_peg_in_tx;
                    in.pushKV("pegin_bitcoin_tx", HexStr(ss_tx));
                }
            }
            if (input.txout_proof.index() > 0) {
                const auto btc_txout_proof = std::get_if<Sidechain::Bitcoin::CMerkleBlock>(&input.txout_proof);
                if (btc_txout_proof) {
                    CDataStream ss_mb(SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS);
                    ss_mb << *btc_txout_proof;
                    in.pushKV("pegin_txout_proof", HexStr(ss_mb));
                }
            }
        } else {
            if (input.peg_in_tx.index() > 0) {
                const auto elem_peg_in_tx = std::get_if<CTransactionRef>(&input.peg_in_tx);
                if (elem_peg_in_tx) {
                    CDataStream ss_tx(SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS);
                    ss_tx << *elem_peg_in_tx;
                    in.pushKV("pegin_bitcoin_tx", HexStr(ss_tx));
                }
            }
            if (input.txout_proof.index() > 0) {
                const auto elem_txout_proof = std::get_if<CMerkleBlock>(&input.txout_proof);
                if (elem_txout_proof) {
                    CDataStream ss_mb(SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS);
                    ss_mb << *elem_txout_proof;
                    in.pushKV("pegin_txout_proof", HexStr(ss_mb));
                }
            }
        }
        if (!input.claim_script.empty()) {
            in.pushKV("pegin_claim_script", HexStr(input.claim_script));
        }
        if (!input.genesis_hash.IsNull()) {
            in.pushKV("pegin_genesis_hash", input.genesis_hash.GetHex());
        }

        // Unknown data
        if (input.unknown.size() > 0) {
            UniValue unknowns(UniValue::VOBJ);
            for (auto entry : input.unknown) {
                unknowns.pushKV(HexStr(entry.first), HexStr(entry.second));
            }
            in.pushKV("unknown", unknowns);
        }

        inputs.push_back(in);
    }
    result.pushKV("inputs", inputs);

    // outputs
    UniValue outputs(UniValue::VARR);
    for (unsigned int i = 0; i < psbtx.outputs.size(); ++i) {
        const PSBTOutput& output = psbtx.outputs[i];
        UniValue out(UniValue::VOBJ);
        // Redeem script and witness script
        if (!output.redeem_script.empty()) {
            UniValue r(UniValue::VOBJ);
            ScriptToUniv(output.redeem_script, r, false);
            out.pushKV("redeem_script", r);
        }
        if (!output.witness_script.empty()) {
            UniValue r(UniValue::VOBJ);
            ScriptToUniv(output.witness_script, r, false);
            out.pushKV("witness_script", r);
        }

        // keypaths
        if (!output.hd_keypaths.empty()) {
            UniValue keypaths(UniValue::VARR);
            for (auto entry : output.hd_keypaths) {
                UniValue keypath(UniValue::VOBJ);
                keypath.pushKV("pubkey", HexStr(entry.first));
                keypath.pushKV("master_fingerprint", strprintf("%08x", ReadBE32(entry.second.fingerprint)));
                keypath.pushKV("path", WriteHDKeypath(entry.second.path));
                keypaths.push_back(keypath);
            }
            out.pushKV("bip32_derivs", keypaths);
        }

        // Value commitment
        if (!output.value_commitment.IsNull()) {
            out.pushKV("value_commitment", output.value_commitment.GetHex());
        }

        // Value blinder
        if (!output.value_blinding_factor.IsNull()) {
            out.pushKV("value_blinding_factor", output.value_blinding_factor.GetHex());
        }

        // Asset commitment
        if (!output.asset_commitment.IsNull()) {
            out.pushKV("asset_commitment", output.asset_commitment.GetHex());
        }

        // Asset blinder
        if (!output.asset_blinding_factor.IsNull()) {
            out.pushKV("asset_blinding_factor", output.asset_blinding_factor.GetHex());
        }

        // Nonce commitment
        if (!output.nonce_commitment.IsNull()) {
            out.pushKV("nonce_commitment", output.nonce_commitment.GetHex());
        }

        // Range proof omitted due to size

        // Surjection proof
        if (!output.surjection_proof.empty()) {
            out.pushKV("surjection_proof", HexStr(output.surjection_proof));
        }

        // Blinding pubkey
        if (output.blinding_pubkey.IsValid()) {
            out.pushKV("blinding_pubkey", HexStr(output.blinding_pubkey));
        }

        // Unknown data
        if (output.unknown.size() > 0) {
            UniValue unknowns(UniValue::VOBJ);
            for (auto entry : output.unknown) {
                unknowns.pushKV(HexStr(entry.first), HexStr(entry.second));
            }
            out.pushKV("unknown", unknowns);
        }

        outputs.push_back(out);
    }
    result.pushKV("outputs", outputs);

    return result;
},
    };
}

static RPCHelpMan combinepsbt()
{
    return RPCHelpMan{"combinepsbt",
                "\nCombine multiple partially signed Bitcoin transactions into one transaction.\n"
                "Implements the Combiner role.\n",
                {
                    {"txs", RPCArg::Type::ARR, RPCArg::Optional::NO, "The base64 strings of partially signed transactions",
                        {
                            {"psbt", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "A base64 string of a PSBT"},
                        },
                        },
                },
                RPCResult{
                    RPCResult::Type::STR, "", "The base64-encoded partially signed transaction"
                },
                RPCExamples{
                    HelpExampleCli("combinepsbt", R"('["mybase64_1", "mybase64_2", "mybase64_3"]')")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    if (!g_con_elementsmode)
        throw std::runtime_error("PSBT operations are disabled when not in elementsmode.\n");

    RPCTypeCheck(request.params, {UniValue::VARR}, true);

    // Unserialize the transactions
    std::vector<PartiallySignedTransaction> psbtxs;
    UniValue txs = request.params[0].get_array();
    if (txs.empty()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Parameter 'txs' cannot be empty");
    }
    for (unsigned int i = 0; i < txs.size(); ++i) {
        PartiallySignedTransaction psbtx;
        std::string error;
        if (!DecodeBase64PSBT(psbtx, txs[i].get_str(), error)) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR, strprintf("TX decode failed %s", error));
        }
        psbtxs.push_back(psbtx);
    }

    PartiallySignedTransaction merged_psbt;
    const TransactionError error = CombinePSBTs(merged_psbt, psbtxs);
    if (error != TransactionError::OK) {
        throw JSONRPCTransactionError(error);
    }

    return EncodePSBT(merged_psbt);
},
    };
}

static RPCHelpMan finalizepsbt()
{
    return RPCHelpMan{"finalizepsbt",
                "Finalize the inputs of a PSBT. If the transaction is fully signed, it will produce a\n"
                "network serialized transaction which can be broadcast with sendrawtransaction. Otherwise a PSBT will be\n"
                "created which has the final_scriptSig and final_scriptWitness fields filled for inputs that are complete.\n"
                "Implements the Finalizer and Extractor roles.\n",
                {
                    {"psbt", RPCArg::Type::STR, RPCArg::Optional::NO, "A base64 string of a PSBT"},
                    {"extract", RPCArg::Type::BOOL, /* default */ "true", "If true and the transaction is complete,\n"
            "                             extract and return the complete transaction in normal network serialization instead of the PSBT."},
                },
                RPCResult{
                    RPCResult::Type::OBJ, "", "",
                    {
                        {RPCResult::Type::STR, "psbt", "The base64-encoded partially signed transaction if not extracted"},
                        {RPCResult::Type::STR_HEX, "hex", "The hex-encoded network transaction if extracted"},
                        {RPCResult::Type::BOOL, "complete", "If the transaction has a complete set of signatures"},
                    }
                },
                RPCExamples{
                    HelpExampleCli("finalizepsbt", "\"psbt\"")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    if (!g_con_elementsmode)
        throw std::runtime_error("PSBT operations are disabled when not in elementsmode.\n");

    RPCTypeCheck(request.params, {UniValue::VSTR, UniValue::VBOOL}, true);

    // Unserialize the transactions
    PartiallySignedTransaction psbtx;
    std::string error;
    if (!DecodeBase64PSBT(psbtx, request.params[0].get_str(), error)) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, strprintf("TX decode failed %s", error));
    }

    bool extract = request.params[1].isNull() || (!request.params[1].isNull() && request.params[1].get_bool());

    CMutableTransaction mtx;
    bool complete = FinalizeAndExtractPSBT(psbtx, mtx);

    UniValue result(UniValue::VOBJ);
    CDataStream ssTx(SER_NETWORK, PROTOCOL_VERSION);
    std::string result_str;

    if (complete && extract) {
        ssTx << mtx;
        result_str = HexStr(ssTx);
        result.pushKV("hex", result_str);
    } else {
        ssTx << psbtx;
        result_str = EncodeBase64(ssTx.str());
        result.pushKV("psbt", result_str);
    }
    result.pushKV("complete", complete);
    return result;
},
    };
}

static RPCHelpMan createpsbt()
{
    return RPCHelpMan{"createpsbt",
                "\nCreates a transaction in the Partially Signed Transaction format.\n"
                "Implements the Creator role.\n",
                {
                    {"inputs", RPCArg::Type::ARR, RPCArg::Optional::NO, "The json objects",
                        {
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                                {
                                    {"txid", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The transaction id"},
                                    {"vout", RPCArg::Type::NUM, RPCArg::Optional::NO, "The output number"},
                                    {"sequence", RPCArg::Type::NUM, /* default */ "depends on the value of the 'replaceable' and 'locktime' arguments", "The sequence number"},
                                    {"pegin_bitcoin_tx", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The raw bitcoin transaction (in hex) depositing bitcoin to the mainchain_address generated by getpeginaddress"},
                                    {"pegin_txout_proof", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "A rawtxoutproof (in hex) generated by the mainchain daemon's `gettxoutproof` containing a proof of only bitcoin_tx"},
                                    {"pegin_claim_script", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The witness program generated by getpeginaddress."},
                                },
                                },
                        },
                        },
                    {"outputs", RPCArg::Type::ARR, RPCArg::Optional::NO, "The outputs (key-value pairs), where none of the keys are duplicated.\n"
                            "That is, each address can only appear once and there can only be one 'data' object.\n"
                            "For compatibility reasons, a dictionary, which holds the key-value pairs directly, is also\n"
                            "                             accepted as second parameter.",
                        {
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                                {
                                    {"address", RPCArg::Type::AMOUNT, RPCArg::Optional::NO, "A key-value pair. The key (string) is the bitcoin address, the value (float or string) is the amount in " + CURRENCY_UNIT},
                                },
                                },
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                                {
                                    {"data", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "A key-value pair. The key must be \"data\", the value is hex-encoded data"},
                                },
                                },
                        },
                        },
                    {"locktime", RPCArg::Type::NUM, /* default */ "0", "Raw locktime. Non-0 value also locktime-activates inputs"},
                    {"replaceable", RPCArg::Type::BOOL, /* default */ "false", "Marks this transaction as BIP125 replaceable.\n"
                            "                             Allows this transaction to be replaced by a transaction with higher fees. If provided, it is an error if explicit sequence numbers are incompatible."},
                    {"output_assets", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "A json object of addresses to the assets (label or hex ID) used to pay them. (default: bitcoin)",
                        {
                            {"address", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "A key-value pair. The key (string) is the bitcoin address, the value is the asset label or asset ID."},
                            {"fee", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "A key-value pair. The key (string) is the bitcoin address, the value is the asset label or asset ID."},
                        },
                        },
                },
                RPCResult{
                    RPCResult::Type::STR, "", "The resulting raw transaction (base64-encoded string)"
                },
                RPCExamples{
                    HelpExampleCli("createpsbt", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\" \"[{\\\"data\\\":\\\"00010203\\\"}]\"")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    if (!g_con_elementsmode)
        throw std::runtime_error("PSBT operations are disabled when not in elementsmode.\n");

    RPCTypeCheck(request.params, {
        UniValue::VARR,
        UniValueType(), // ARR or OBJ, checked later
        UniValue::VNUM,
        UniValue::VBOOL,
        }, true
    );

    std::vector<CPubKey> output_pubkeys;
    bool rbf = false;
    if (!request.params[3].isNull()) {
        rbf = request.params[3].isTrue();
    }
    CMutableTransaction rawTx = ConstructTransaction(request.params[0], request.params[1], request.params[2], rbf, request.params[4], &output_pubkeys);

    // Make a blank psbt
    PartiallySignedTransaction psbtx(rawTx);
    for (unsigned int i = 0; i < rawTx.vout.size(); ++i) {
        psbtx.outputs[i].blinding_pubkey = output_pubkeys[i];
    }

    // Add peg-in stuff if it's there
    for (unsigned int i = 0; i < rawTx.vin.size(); ++i) {
        if (psbtx.tx->vin[i].m_is_pegin) {
            CScriptWitness& pegin_witness = psbtx.tx->witness.vtxinwit[i].m_pegin_witness;
            CAmount val;
            VectorReader vr_val(SER_NETWORK, PROTOCOL_VERSION, pegin_witness.stack[0], 0);
            vr_val >> val;
            psbtx.inputs[i].value = val;
            VectorReader vr_asset(SER_NETWORK, PROTOCOL_VERSION, pegin_witness.stack[1], 0);
            vr_asset >> psbtx.inputs[i].asset;
            VectorReader vr_genesis(SER_NETWORK, PROTOCOL_VERSION, pegin_witness.stack[2], 0);
            vr_genesis >> psbtx.inputs[i].genesis_hash;
            psbtx.inputs[i].claim_script.assign(pegin_witness.stack[3].begin(), pegin_witness.stack[3].end());

            VectorReader vr_tx(SER_NETWORK, PROTOCOL_VERSION, pegin_witness.stack[4], 0);
            VectorReader vr_proof(SER_NETWORK, PROTOCOL_VERSION, pegin_witness.stack[5], 0);
            if (Params().GetConsensus().ParentChainHasPow()) {
                Sidechain::Bitcoin::CTransactionRef tx_btc;
                vr_tx >> tx_btc;
                psbtx.inputs[i].peg_in_tx = tx_btc;
                Sidechain::Bitcoin::CMerkleBlock tx_proof;
                vr_proof >> tx_proof;
                psbtx.inputs[i].txout_proof = tx_proof;
            } else {
                CTransactionRef tx_btc;
                vr_tx >> tx_btc;
                psbtx.inputs[i].peg_in_tx = tx_btc;
                CMerkleBlock tx_proof;
                vr_proof >> tx_proof;
                psbtx.inputs[i].txout_proof = tx_proof;
            }
            pegin_witness.SetNull();
            psbtx.tx->vin[i].m_is_pegin = false;
        }
    }

    return EncodePSBT(psbtx);
},
    };
}

static RPCHelpMan converttopsbt()
{
    return RPCHelpMan{"converttopsbt",
                "\nConverts a network serialized transaction to a PSBT. This should be used only with createrawtransaction and fundrawtransaction\n"
                "createpsbt and walletcreatefundedpsbt should be used for new applications.\n",
                {
                    {"hexstring", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The hex string of a raw transaction"},
                    {"permitsigdata", RPCArg::Type::BOOL, /* default */ "false", "If true, any signatures in the input will be discarded and conversion\n"
                            "                              will continue. If false, RPC will fail if any signatures are present."},
                    {"iswitness", RPCArg::Type::BOOL, /* default */ "depends on heuristic tests", "Whether the transaction hex is a serialized witness transaction.\n"
                        "If iswitness is not present, heuristic tests will be used in decoding.\n"
                        "If true, only witness deserialization will be tried.\n"
                        "If false, only non-witness deserialization will be tried.\n"
                        "This boolean should reflect whether the transaction has inputs\n"
                        "(e.g. fully valid, or on-chain transactions), if known by the caller."
                    },
                },
                RPCResult{
                    RPCResult::Type::STR, "", "The resulting raw transaction (base64-encoded string)"
                },
                RPCExamples{
                            "\nCreate a transaction\n"
                            + HelpExampleCli("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\" \"[{\\\"data\\\":\\\"00010203\\\"}]\"") +
                            "\nConvert the transaction to a PSBT\n"
                            + HelpExampleCli("converttopsbt", "\"rawtransaction\"")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    if (!g_con_elementsmode)
        throw std::runtime_error("PSBT operations are disabled when not in elementsmode.\n");

    RPCTypeCheck(request.params, {UniValue::VSTR, UniValue::VBOOL, UniValue::VBOOL}, true);

    // parse hex string from parameter
    CMutableTransaction tx;
    bool permitsigdata = request.params[1].isNull() ? false : request.params[1].get_bool();
    bool witness_specified = !request.params[2].isNull();
    bool iswitness = witness_specified ? request.params[2].get_bool() : false;
    const bool try_witness = witness_specified ? iswitness : true;
    const bool try_no_witness = witness_specified ? !iswitness : true;
    if (!DecodeHexTx(tx, request.params[0].get_str(), try_no_witness, try_witness)) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    }

    // Remove all scriptSigs and scriptWitnesses from inputs
    for (CTxIn& input : tx.vin) {
        if (!input.scriptSig.empty() && !permitsigdata) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Inputs must not have scriptSigs");
        }
        input.scriptSig.clear();
    }
    for (CTxInWitness& witness: tx.witness.vtxinwit) {
        if (!witness.scriptWitness.IsNull() && !permitsigdata) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Inputs must not have scriptWitnesses");
        }
    }
    tx.witness.SetNull();

    // Make a blank psbt
    PartiallySignedTransaction psbtx;
    for (unsigned int i = 0; i < tx.vin.size(); ++i) {
        psbtx.inputs.push_back(PSBTInput());
    }
    for (unsigned int i = 0; i < tx.vout.size(); ++i) {
        psbtx.outputs.push_back(PSBTOutput());
        // At this point, if the nonce field is present it should be a smuggled
        //   pubkey, and not a real nonce. Convert it back to a pubkey and strip
        //   it out.
        psbtx.outputs[i].blinding_pubkey = CPubKey(tx.vout[i].nNonce.vchCommitment);
        tx.vout[i].nNonce.SetNull();
    }

    psbtx.tx = tx;

    // Serialize the PSBT
    CDataStream ssTx(SER_NETWORK, PROTOCOL_VERSION);
    ssTx << psbtx;

    return EncodeBase64(ssTx);
},
    };
}

static RPCHelpMan utxoupdatepsbt()
{
    return RPCHelpMan{"utxoupdatepsbt",
            "\nUpdates all segwit inputs and outputs in a PSBT with data from output descriptors, the UTXO set or the mempool.\n",
            {
                {"psbt", RPCArg::Type::STR, RPCArg::Optional::NO, "A base64 string of a PSBT"},
                {"descriptors", RPCArg::Type::ARR, RPCArg::Optional::OMITTED_NAMED_ARG, "An array of either strings or objects", {
                    {"", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "An output descriptor"},
                    {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "An object with an output descriptor and extra information", {
                         {"desc", RPCArg::Type::STR, RPCArg::Optional::NO, "An output descriptor"},
                         {"range", RPCArg::Type::RANGE, "1000", "Up to what index HD chains should be explored (either end or [begin,end])"},
                    }},
                }},
            },
            RPCResult {
                    RPCResult::Type::STR, "", "The base64-encoded partially signed transaction with inputs updated"
            },
            RPCExamples {
                HelpExampleCli("utxoupdatepsbt", "\"psbt\"")
            },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    RPCTypeCheck(request.params, {UniValue::VSTR, UniValue::VARR}, true);

    // Unserialize the transactions
    PartiallySignedTransaction psbtx;
    std::string error;
    if (!DecodeBase64PSBT(psbtx, request.params[0].get_str(), error)) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, strprintf("TX decode failed %s", error));
    }

    // Parse descriptors, if any.
    FlatSigningProvider provider;
    if (!request.params[1].isNull()) {
        auto descs = request.params[1].get_array();
        for (size_t i = 0; i < descs.size(); ++i) {
            EvalDescriptorStringOrObject(descs[i], provider);
        }
    }
    // We don't actually need private keys further on; hide them as a precaution.
    HidingSigningProvider public_provider(&provider, /* nosign */ true, /* nobip32derivs */ false);

    // Fetch previous transactions (inputs):
    CCoinsView viewDummy;
    CCoinsViewCache view(&viewDummy);
    {
        const CTxMemPool& mempool = EnsureMemPool(request.context);
        LOCK2(cs_main, mempool.cs);
        CCoinsViewCache &viewChain = ::ChainstateActive().CoinsTip();
        CCoinsViewMemPool viewMempool(&viewChain, mempool);
        view.SetBackend(viewMempool); // temporarily switch cache backend to db+mempool view

        for (const CTxIn& txin : psbtx.tx->vin) {
            view.AccessCoin(txin.prevout); // Load entries from viewChain into view; can fail.
        }

        view.SetBackend(viewDummy); // switch back to avoid locking mempool for too long
    }

    // Fill the inputs
    for (unsigned int i = 0; i < psbtx.tx->vin.size(); ++i) {
        PSBTInput& input = psbtx.inputs.at(i);

        if (input.non_witness_utxo || !input.witness_utxo.IsNull()) {
            continue;
        }

        const Coin& coin = view.AccessCoin(psbtx.tx->vin[i].prevout);

        if (IsSegWitOutput(provider, coin.out.scriptPubKey)) {
            input.witness_utxo = coin.out;
        }

        // Update script/keypath information using descriptor data.
        // Note that SignPSBTInput does a lot more than just constructing ECDSA signatures
        // we don't actually care about those here, in fact.
        SignPSBTInput(public_provider, psbtx, i, /* sighash_type */ 1);
    }

    // Update script/keypath information using descriptor data.
    for (unsigned int i = 0; i < psbtx.tx->vout.size(); ++i) {
        UpdatePSBTOutput(public_provider, psbtx, i);
    }

    CDataStream ssTx(SER_NETWORK, PROTOCOL_VERSION);
    ssTx << psbtx;
    return EncodeBase64(ssTx);
},
    };
}

static RPCHelpMan joinpsbts()
{
    return RPCHelpMan{"joinpsbts",
            "\nJoins multiple distinct PSBTs with different inputs and outputs into one PSBT with inputs and outputs from all of the PSBTs\n"
            "No input in any of the PSBTs can be in more than one of the PSBTs.\n",
            {
                {"txs", RPCArg::Type::ARR, RPCArg::Optional::NO, "The base64 strings of partially signed transactions",
                    {
                        {"psbt", RPCArg::Type::STR, RPCArg::Optional::NO, "A base64 string of a PSBT"}
                    }}
            },
            RPCResult {
                    RPCResult::Type::STR, "", "The base64-encoded partially signed transaction"
            },
            RPCExamples {
                HelpExampleCli("joinpsbts", "\"psbt\"")
            },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    RPCTypeCheck(request.params, {UniValue::VARR}, true);

    // Unserialize the transactions
    std::vector<PartiallySignedTransaction> psbtxs;
    UniValue txs = request.params[0].get_array();

    if (txs.size() <= 1) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "At least two PSBTs are required to join PSBTs.");
    }

    uint32_t best_version = 1;
    uint32_t best_locktime = 0xffffffff;
    for (unsigned int i = 0; i < txs.size(); ++i) {
        PartiallySignedTransaction psbtx;
        std::string error;
        if (!DecodeBase64PSBT(psbtx, txs[i].get_str(), error)) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR, strprintf("TX decode failed %s", error));
        }
        psbtxs.push_back(psbtx);
        // Choose the highest version number
        if (static_cast<uint32_t>(psbtx.tx->nVersion) > best_version) {
            best_version = static_cast<uint32_t>(psbtx.tx->nVersion);
        }
        // Choose the lowest lock time
        if (psbtx.tx->nLockTime < best_locktime) {
            best_locktime = psbtx.tx->nLockTime;
        }
    }

    // Create a blank psbt where everything will be added
    PartiallySignedTransaction merged_psbt;
    merged_psbt.tx = CMutableTransaction();
    merged_psbt.tx->nVersion = static_cast<int32_t>(best_version);
    merged_psbt.tx->nLockTime = best_locktime;

    // Merge
    for (auto& psbt : psbtxs) {
        for (unsigned int i = 0; i < psbt.tx->vin.size(); ++i) {
            if (!merged_psbt.AddInput(psbt.tx->vin[i], psbt.inputs[i])) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Input %s:%d exists in multiple PSBTs", psbt.tx->vin[i].prevout.hash.ToString(), psbt.tx->vin[i].prevout.n));
            }
        }
        for (unsigned int i = 0; i < psbt.tx->vout.size(); ++i) {
            merged_psbt.AddOutput(psbt.tx->vout[i], psbt.outputs[i]);
        }
        merged_psbt.unknown.insert(psbt.unknown.begin(), psbt.unknown.end());
    }

    // Generate list of shuffled indices for shuffling inputs and outputs of the merged PSBT
    std::vector<int> input_indices(merged_psbt.inputs.size());
    std::iota(input_indices.begin(), input_indices.end(), 0);
    std::vector<int> output_indices(merged_psbt.outputs.size());
    std::iota(output_indices.begin(), output_indices.end(), 0);

    // Shuffle input and output indices lists
    Shuffle(input_indices.begin(), input_indices.end(), FastRandomContext());
    Shuffle(output_indices.begin(), output_indices.end(), FastRandomContext());

    PartiallySignedTransaction shuffled_psbt;
    shuffled_psbt.tx = CMutableTransaction();
    shuffled_psbt.tx->nVersion = merged_psbt.tx->nVersion;
    shuffled_psbt.tx->nLockTime = merged_psbt.tx->nLockTime;
    for (int i : input_indices) {
        shuffled_psbt.AddInput(merged_psbt.tx->vin[i], merged_psbt.inputs[i]);
    }
    for (int i : output_indices) {
        shuffled_psbt.AddOutput(merged_psbt.tx->vout[i], merged_psbt.outputs[i]);
    }
    shuffled_psbt.unknown.insert(merged_psbt.unknown.begin(), merged_psbt.unknown.end());

    CDataStream ssTx(SER_NETWORK, PROTOCOL_VERSION);
    ssTx << shuffled_psbt;
    return EncodeBase64(ssTx);
},
    };
}

static RPCHelpMan analyzepsbt()
{
    return RPCHelpMan{"analyzepsbt",
            "\nAnalyzes and provides information about the current status of a PSBT and its inputs\n",
            {
                {"psbt", RPCArg::Type::STR, RPCArg::Optional::NO, "A base64 string of a PSBT"}
            },
            RPCResult {
                RPCResult::Type::OBJ, "", "",
                {
                    {RPCResult::Type::ARR, "inputs", "",
                    {
                        {RPCResult::Type::OBJ, "", "",
                        {
                            {RPCResult::Type::BOOL, "has_utxo", "Whether a UTXO is provided"},
                            {RPCResult::Type::BOOL, "is_final", "Whether the input is finalized"},
                            {RPCResult::Type::OBJ, "missing", /* optional */ true, "Things that are missing that are required to complete this input",
                            {
                                {RPCResult::Type::ARR, "pubkeys", /* optional */ true, "",
                                {
                                    {RPCResult::Type::STR_HEX, "keyid", "Public key ID, hash160 of the public key, of a public key whose BIP 32 derivation path is missing"},
                                }},
                                {RPCResult::Type::ARR, "signatures", /* optional */ true, "",
                                {
                                    {RPCResult::Type::STR_HEX, "keyid", "Public key ID, hash160 of the public key, of a public key whose signature is missing"},
                                }},
                                {RPCResult::Type::STR_HEX, "redeemscript", /* optional */ true, "Hash160 of the redeemScript that is missing"},
                                {RPCResult::Type::STR_HEX, "witnessscript", /* optional */ true, "SHA256 of the witnessScript that is missing"},
                            }},
                            {RPCResult::Type::STR, "next", /* optional */ true, "Role of the next person that this input needs to go to"},
                        }},
                    }},
                    {RPCResult::Type::NUM, "estimated_vsize", /* optional */ true, "Estimated vsize of the final signed transaction"},
                    {RPCResult::Type::STR_AMOUNT, "estimated_feerate", /* optional */ true, "Estimated feerate of the final signed transaction in " + CURRENCY_UNIT + "/kB. Shown only if all UTXO slots in the PSBT have been filled"},
                    {RPCResult::Type::STR_AMOUNT, "fee", /* optional */ true, "The transaction fee paid. Shown only if all UTXO slots in the PSBT have been filled"},
                    {RPCResult::Type::STR, "next", "Role of the next person that this psbt needs to go to"},
                    {RPCResult::Type::STR, "error", /* optional */ true, "Error message (if there is one)"},
                }
            },
            RPCExamples {
                HelpExampleCli("analyzepsbt", "\"psbt\"")
            },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    RPCTypeCheck(request.params, {UniValue::VSTR});

    // Unserialize the transaction
    PartiallySignedTransaction psbtx;
    std::string error;
    if (!DecodeBase64PSBT(psbtx, request.params[0].get_str(), error)) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, strprintf("TX decode failed %s", error));
    }

    PSBTAnalysis psbta = AnalyzePSBT(psbtx);

    UniValue result(UniValue::VOBJ);
    UniValue inputs_result(UniValue::VARR);
    for (const auto& input : psbta.inputs) {
        UniValue input_univ(UniValue::VOBJ);
        UniValue missing(UniValue::VOBJ);

        input_univ.pushKV("has_utxo", input.has_utxo);
        input_univ.pushKV("is_final", input.is_final);
        input_univ.pushKV("next", PSBTRoleName(input.next));

        if (!input.missing_pubkeys.empty()) {
            UniValue missing_pubkeys_univ(UniValue::VARR);
            for (const CKeyID& pubkey : input.missing_pubkeys) {
                missing_pubkeys_univ.push_back(HexStr(pubkey));
            }
            missing.pushKV("pubkeys", missing_pubkeys_univ);
        }
        if (!input.missing_redeem_script.IsNull()) {
            missing.pushKV("redeemscript", HexStr(input.missing_redeem_script));
        }
        if (!input.missing_witness_script.IsNull()) {
            missing.pushKV("witnessscript", HexStr(input.missing_witness_script));
        }
        if (!input.missing_sigs.empty()) {
            UniValue missing_sigs_univ(UniValue::VARR);
            for (const CKeyID& pubkey : input.missing_sigs) {
                missing_sigs_univ.push_back(HexStr(pubkey));
            }
            missing.pushKV("signatures", missing_sigs_univ);
        }
        if (!missing.getKeys().empty()) {
            input_univ.pushKV("missing", missing);
        }
        inputs_result.push_back(input_univ);
    }
    if (!inputs_result.empty()) result.pushKV("inputs", inputs_result);

    if (psbta.estimated_vsize != nullopt) {
        result.pushKV("estimated_vsize", (int)*psbta.estimated_vsize);
    }
    if (psbta.estimated_feerate != nullopt) {
        result.pushKV("estimated_feerate", ValueFromAmount(psbta.estimated_feerate->GetFeePerK()));
    }
    if (psbta.fee != nullopt) {
        result.pushKV("fee", AmountMapToUniv(*psbta.fee, ""));
    }
    result.pushKV("next", PSBTRoleName(psbta.next));
    if (!psbta.error.empty()) {
        result.pushKV("error", psbta.error);
    }

    return result;
},
    };
}

//
// ELEMENTS:

static RPCHelpMan rawblindrawtransaction()
{
    return RPCHelpMan{"rawblindrawtransaction",
                "\nConvert one or more outputs of a raw transaction into confidential ones.\n"
                "Returns the hex-encoded raw transaction.\n"
                "The input raw transaction cannot have already-blinded outputs.\n"
                "The output keys used can be specified by using a confidential address in createrawtransaction.\n"
                "If an additional blinded output is required to make a balanced blinding, a 0-value unspendable output will be added. Since there is no access to the wallet the blinding pubkey from the last output with blinding key will be repeated.\n"
                "You can not blind issuances with this call.\n",
                {
                    {"hexstring", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "A hex-encoded raw transaction."},
                    {"inputamountblinders", RPCArg::Type::ARR, RPCArg::Optional::NO, "An array with one entry per transaction input.",
                        {
                            {"inputamountblinder", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "A hex-encoded blinding factor, one for each input."
            "                           Blinding factors can be found in the \"blinder\" output of listunspent."},
                        }
                    },
                    {"inputamounts", RPCArg::Type::ARR, RPCArg::Optional::NO, "An array with one entry per transaction input.",
                        {
                            {"inputamount", RPCArg::Type::AMOUNT, RPCArg::Optional::NO, "An amount for each input."},
                        }
                    },
                    {"inputassets", RPCArg::Type::ARR, RPCArg::Optional::NO, "An array with one entry per transaction input.",
                        {
                            {"inputasset", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "A hex-encoded asset id, one for each input."},
                        }
                    },
                    {"inputassetblinders", RPCArg::Type::ARR, RPCArg::Optional::NO, "An array with one entry per transaction input.",
                        {
                            {"inputassetblinder", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "A hex-encoded asset blinding factor, one for each input."},
                        }
                    },
                    {"totalblinder", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "Ignored for now."},
                    {"ignoreblindfail", RPCArg::Type::BOOL, /* default */ "true", "Return a transaction even when a blinding attempt fails due to number of blinded inputs/outputs."},
                },
                RPCResult{
                     RPCResult::Type::STR, "transaction", "hex string of the transaction"
                },
                RPCExamples{""},
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    std::vector<unsigned char> txData(ParseHexV(request.params[0], "argument 1"));
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
    if (!request.params[6].isNull()) {
        fIgnoreBlindFail = request.params[6].get_bool();
    }

    int n_blinded_ins = 0;

    if (inputBlinds.size() != tx.vin.size()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER,
            "Invalid parameter: one (potentially empty) input blind for each input must be provided");
    }
    if (inputAmounts.size() != tx.vin.size()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER,
            "Invalid parameter: one (potentially empty) input blind for each input must be provided");
    }
    if (inputAssets.size() != tx.vin.size()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER,
            "Invalid parameter: one (potentially empty) input asset id for each input must be provided");
    }
    if (inputAssetBlinds.size() != tx.vin.size()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER,
            "Invalid parameter: one (potentially empty) input asset blind for each input must be provided");
    }

    const auto& fedpegscripts = GetValidFedpegScripts(::ChainActive().Tip(), Params().GetConsensus(), true /* nextblock_validation */);

    std::vector<CAmount> input_amounts;
    std::vector<uint256> input_blinds;
    std::vector<uint256> input_asset_blinds;
    std::vector<CAsset> input_assets;
    std::vector<uint256> output_value_blinds;
    std::vector<uint256> output_asset_blinds;
    std::vector<CAsset> output_assets;
    std::vector<CPubKey> output_pubkeys;
    for (size_t nIn = 0; nIn < tx.vin.size(); nIn++) {
        // Special handling for pegin inputs: no blinds and explicit amount/asset.
        if (tx.vin[nIn].m_is_pegin) {
            std::string err;
            if (tx.witness.vtxinwit.size() != tx.vin.size() || !IsValidPeginWitness(tx.witness.vtxinwit[nIn].m_pegin_witness, fedpegscripts, tx.vin[nIn].prevout, err, false)) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Transaction contains invalid peg-in input: %s", err));
            }
            CTxOut pegin_output = GetPeginOutputFromWitness(tx.witness.vtxinwit[nIn].m_pegin_witness);
            input_blinds.push_back(uint256());
            input_asset_blinds.push_back(uint256());
            input_assets.push_back(pegin_output.nAsset.GetAsset());
            input_amounts.push_back(pegin_output.nValue.GetAmount());
            continue;
        }

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

    RawFillBlinds(tx, output_value_blinds, output_asset_blinds, output_pubkeys);

    // How many are we trying to blind?
    int num_pubkeys = 0;
    unsigned int keyIndex = (unsigned) -1;
    for (unsigned int i = 0; i < output_pubkeys.size(); i++) {
        const CPubKey& key = output_pubkeys[i];
        if (key.IsValid()) {
            num_pubkeys++;
            keyIndex = i;
        }
    }

    if (num_pubkeys == 0 && n_blinded_ins == 0) {
        // Vacuous, just return the transaction
        return EncodeHexTx(CTransaction(tx));
    } else if (n_blinded_ins > 0 && num_pubkeys == 0) {
        // No notion of wallet, cannot complete this blinding without passed-in pubkey
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Unable to blind transaction: Add another output to blind in order to complete the blinding.");
    } else if (n_blinded_ins == 0 && num_pubkeys == 1) {
        if (fIgnoreBlindFail) {
            // Just get rid of the ECDH key in the nonce field and return
            tx.vout[keyIndex].nNonce.SetNull();
            return EncodeHexTx(CTransaction(tx));
        } else {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Unable to blind transaction: Add another output to blind in order to complete the blinding.");
        }
    }

    int ret = BlindTransaction(input_blinds, input_asset_blinds, input_assets, input_amounts, output_value_blinds, output_asset_blinds, output_pubkeys, std::vector<CKey>(), std::vector<CKey>(), tx);
    if (ret != num_pubkeys) {
        // TODO Have more rich return values, communicating to user what has been blinded
        // User may be ok not blinding something that for instance has no corresponding type on input
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Unable to blind transaction: Are you sure each asset type to blind is represented in the inputs?");
    }

    return EncodeHexTx(CTransaction(tx));
},
    };
}

struct RawIssuanceDetails
{
    int input_index;
    uint256 entropy;
    CAsset asset;
    CAsset token;
};

// Appends a single issuance to the first input that doesn't have one, and includes
// a single output per asset type in shuffled positions. Requires at least one output
// to exist (the fee output, which must be last).
void issueasset_base(CMutableTransaction& mtx, RawIssuanceDetails& issuance_details, const CAmount asset_amount, const CAmount token_amount, const CTxDestination& asset_dest, const CTxDestination& token_dest, const bool blind_issuance, const uint256& contract_hash)
{
    CHECK_NONFATAL(asset_amount > 0 || token_amount > 0);
    CHECK_NONFATAL(mtx.vout.size() > 0);

    CScript asset_script = GetScriptForDestination(asset_dest);
    CScript token_script = GetScriptForDestination(token_dest);

    // Find an input with no issuance field
    size_t issuance_input_index = 0;
    for (; issuance_input_index < mtx.vin.size(); issuance_input_index++) {
        if (mtx.vin[issuance_input_index].assetIssuance.IsNull()) {
            break;
        }
    }
    // Can't add another one, exit
    if (issuance_input_index == mtx.vin.size()) {
        issuance_details.input_index = -1;
        return;
    }

    uint256 entropy;
    CAsset asset;
    CAsset token;
    GenerateAssetEntropy(entropy, mtx.vin[issuance_input_index].prevout, contract_hash);
    CalculateAsset(asset, entropy);
    CalculateReissuanceToken(token, entropy, blind_issuance);

    issuance_details.input_index = issuance_input_index;
    issuance_details.entropy = entropy;
    issuance_details.asset = asset;
    issuance_details.token = token;

    mtx.vin[issuance_input_index].assetIssuance.assetEntropy = contract_hash;

    if (asset_amount > 0) {
        // Fee output is required to be last. We will insert _before_ the selected position, which preserves that.
        int asset_place = GetRandInt(mtx.vout.size());

        CTxOut asset_out(asset, asset_amount, asset_script);
        // If blinded address, insert the pubkey into the nonce field for later substitution by blinding
        if (IsBlindDestination(asset_dest)) {
            CPubKey asset_blind = GetDestinationBlindingKey(asset_dest);
            asset_out.nNonce.vchCommitment = std::vector<unsigned char>(asset_blind.begin(), asset_blind.end());
        }

        mtx.vout.insert(mtx.vout.begin()+asset_place, asset_out);
    }
    // Explicit 0 is represented by a null value, don't set to non-null in that case
    if (blind_issuance || asset_amount != 0) {
        mtx.vin[issuance_input_index].assetIssuance.nAmount = asset_amount;
    }

    if (token_amount > 0) {
        // Calculate this _after_ we conditionally insert the asset output, which changes mtx.vout.size().
        int token_place = GetRandInt(mtx.vout.size());

        CTxOut token_out(token, token_amount, token_script);
        // If blinded address, insert the pubkey into the nonce field for later substitution by blinding
        if (IsBlindDestination(token_dest)) {
            CPubKey token_blind = GetDestinationBlindingKey(token_dest);
            token_out.nNonce.vchCommitment = std::vector<unsigned char>(token_blind.begin(), token_blind.end());
        }

        mtx.vin[issuance_input_index].assetIssuance.nInflationKeys = token_amount;
        mtx.vout.insert(mtx.vout.begin()+token_place, token_out);
    }
}

// Appends a single reissuance to the specified input if none exists, and the
// corresponding output in a shuffled position. Errors otherwise. Requires at
// least one output to exist (the fee output, which must be last).
void reissueasset_base(CMutableTransaction& mtx, size_t issuance_input_index, const CAmount asset_amount, const CTxDestination& asset_dest, const uint256& asset_blinder, const uint256& entropy)
{
    CHECK_NONFATAL(mtx.vout.size() > 0);
    CHECK_NONFATAL(asset_amount > 0);
    CHECK_NONFATAL(mtx.vin[issuance_input_index].assetIssuance.IsNull());

    CScript asset_script = GetScriptForDestination(asset_dest);

    CAsset asset;
    CalculateAsset(asset, entropy);

    mtx.vin[issuance_input_index].assetIssuance.assetEntropy = entropy;
    mtx.vin[issuance_input_index].assetIssuance.assetBlindingNonce = asset_blinder;
    mtx.vin[issuance_input_index].assetIssuance.nAmount = asset_amount;

    // Place assets into randomly placed output slots, before change output, inserted in place
    int asset_place = GetRandInt(mtx.vout.size());

    CTxOut asset_out(asset, asset_amount, asset_script);
    // If blinded address, insert the pubkey into the nonce field for later substitution by blinding
    if (IsBlindDestination(asset_dest)) {
        CPubKey asset_blind = GetDestinationBlindingKey(asset_dest);
        asset_out.nNonce.vchCommitment = std::vector<unsigned char>(asset_blind.begin(), asset_blind.end());
    }
    mtx.vout.insert(mtx.vout.begin()+asset_place, asset_out);
    mtx.vin[issuance_input_index].assetIssuance.nAmount = asset_amount;
}

static RPCHelpMan rawissueasset()
{
    return RPCHelpMan{"rawissueasset",
                "\nCreate an asset by attaching issuances to transaction inputs. Returns the transaction hex. There must be as many inputs as issuances requested. The final transaction hex is the final version of the transaction appended to the last object in the array.\n",
                {
                    {"transaction", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "Transaction in hex in which to include an issuance input."},
                    {"issuances", RPCArg::Type::ARR, RPCArg::Optional::NO, "List of issuances to create. Each issuance must have one non-zero amount.",
                        {
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::NO, "",
                                {
                                    {"asset_amount", RPCArg::Type::AMOUNT, RPCArg::Optional::OMITTED_NAMED_ARG, "Amount of asset to generate, if any."},
                                    {"asset_address", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "Destination address of generated asset. Required if `asset_amount` given."},
                                    {"token_amount", RPCArg::Type::AMOUNT, RPCArg::Optional::OMITTED_NAMED_ARG, "Amount of reissuance token to generate, if any."},
                                    {"token_address", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "Destination address of generated reissuance tokens. Required if `token_amount` given."},
                                    {"blind", RPCArg::Type::BOOL, /* default */ "true", "Whether to mark the issuance input for blinding or not. Only affects issuances with re-issuance tokens."},
                                    {"contract_hash", RPCArg::Type::STR_HEX, /* default */ "0000...0000", "Contract hash that is put into issuance definition. Must be 32 bytes worth in hex string form. This will affect the asset id."},
                                }
                            }
                        }
                    },
                },
                RPCResult{
                    RPCResult::Type::ARR, "", "Results of issuances, in the order of `issuances` arguments",
                    {
                        {RPCResult::Type::OBJ, "", "",
                        {
                            {RPCResult::Type::STR_HEX, "hex", "The transaction with issuances appended. Only appended to final index in returned array"},
                            {RPCResult::Type::NUM, "vin", "The input position of the issuance in the transaction"},
                            {RPCResult::Type::STR_HEX, "entropy", "Entropy of the asset type"},
                            {RPCResult::Type::STR_HEX, "asset", "Asset type for issuance if known"},
                            {RPCResult::Type::STR_HEX, "token", "Token type for issuance"},
                        }},
                    },
                },
                RPCExamples{""},
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    CMutableTransaction mtx;

    if (!DecodeHexTx(mtx, request.params[0].get_str()))
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");

    UniValue issuances = request.params[1].get_array();

    UniValue ret(UniValue::VARR);

    // Count issuances, only append hex to final one
    unsigned int issuances_til_now = 0;

    // Validate fee output location, required by the implementation of issueasset_base
    if (mtx.vout.size() == 0){
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Transaction must have at least one output.");
    }
    if (!mtx.vout[mtx.vout.size() - 1].IsFee()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Last transaction output must be fee.");
    }
    for (size_t i = 0; i < mtx.vout.size() - 1; i++) {
        if (mtx.vout[i].IsFee()) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Transaction can only have one fee output.");
        }
    }

    for (unsigned int idx = 0; idx < issuances.size(); idx++) {
        const UniValue& issuance = issuances[idx];
        const UniValue& issuance_o = issuance.get_obj();

        CTxDestination asset_dest = CNoDestination();
        CTxDestination token_dest = CNoDestination();

        CAmount asset_amount = 0;
        const UniValue& asset_amount_uni = issuance_o["asset_amount"];
        if (asset_amount_uni.isNum()) {
            asset_amount = AmountFromValue(asset_amount_uni);
            if (asset_amount <= 0) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, asset_amount must be positive");
            }
            const UniValue& asset_address_uni = issuance_o["asset_address"];
            if (!asset_address_uni.isStr()) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, missing corresponding asset_address");
            }
            asset_dest = DecodeDestination(asset_address_uni.get_str());
            if (std::get_if<CNoDestination>(&asset_dest)) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Invalid asset address provided: %s", asset_address_uni.get_str()));
            }
        }

        CAmount token_amount = 0;
        const UniValue& token_amount_uni = issuance_o["token_amount"];
        if (token_amount_uni.isNum()) {
            token_amount = AmountFromValue(token_amount_uni);
            if (token_amount <= 0) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, token_amount must be positive");
            }
            const UniValue& token_address_uni = issuance_o["token_address"];
            if (!token_address_uni.isStr()) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, missing corresponding token_address");
            }
            token_dest = DecodeDestination(token_address_uni.get_str());
            if (std::get_if<CNoDestination>(&token_dest)) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Invalid token address provided: %s", token_address_uni.get_str()));
            }
        }

        if (asset_amount == 0 && token_amount == 0) {
            throw JSONRPCError(RPC_TYPE_ERROR, "Issuance must have one non-zero component");
        }

        // If we have issuances, check if reissuance tokens will be generated via blinding path
        const UniValue blind_uni = issuance_o["blind"];
        const bool blind_issuance = !blind_uni.isBool() || blind_uni.get_bool();

        // Check for optional contract to hash into definition
        uint256 contract_hash;
        if (!issuance_o["contract_hash"].isNull()) {
            contract_hash = ParseHashV(issuance_o["contract_hash"], "contract_hash");
        }

        RawIssuanceDetails details;

        issueasset_base(mtx, details, asset_amount, token_amount, asset_dest, token_dest, blind_issuance, contract_hash);
        if (details.input_index == -1) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Failed to find enough blank inputs for listed issuances.");
        }

        issuances_til_now++;

        UniValue obj(UniValue::VOBJ);
        if (issuances_til_now == issuances.size()) {
            obj.pushKV("hex", EncodeHexTx(CTransaction(mtx)));
        }
        obj.pushKV("vin", details.input_index);
        obj.pushKV("entropy", details.entropy.GetHex());
        obj.pushKV("asset", details.asset.GetHex());
        obj.pushKV("token", details.token.GetHex());

        ret.push_back(obj);
    }

    return ret;
},
    };
}

static RPCHelpMan rawreissueasset()
{
    return RPCHelpMan{"rawreissueasset",
                "\nRe-issue an asset by attaching pseudo-inputs to transaction inputs, revealing the underlying reissuance token of the input. Returns the transaction hex.\n",
                {
                    {"transaction", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "Transaction in hex in which to include an issuance input."},
                    {"reissuances", RPCArg::Type::ARR, RPCArg::Optional::NO, "List of re-issuances to create. Each issuance must have one non-zero amount.",
                        {
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::NO, "",
                                {
                                    {"asset_amount", RPCArg::Type::AMOUNT, RPCArg::Optional::NO, "Amount of asset to generate, if any."},
                                    {"asset_address", RPCArg::Type::STR, RPCArg::Optional::NO, "Destination address of generated asset. Required if `asset_amount` given."},
                                    {"input_index", RPCArg::Type::NUM, RPCArg::Optional::NO, "The input position of the reissuance in the transaction."},
                                    {"asset_blinder", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The blinding factor of the reissuance token output being spent."},
                                    {"entropy", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The `entropy` returned during initial issuance for the asset being reissued."},
                                }
                            }
                        }
                    },
                },
                RPCResult{
                    RPCResult::Type::OBJ, "", "",
                    {
                        {RPCResult::Type::STR_HEX, "hex", "The transaction with reissuances appended"},
                    },
                },
                RPCExamples{""},
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    CMutableTransaction mtx;

    if (!DecodeHexTx(mtx, request.params[0].get_str()))
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");

    if (mtx.vout.empty()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Transaction must have at least one output.");
    }

    // Validate fee output location, required by the implementation of reissueasset_base
    if (!mtx.vout[mtx.vout.size() - 1].IsFee()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Last transaction output must be fee.");
    }
    for (size_t i = 0; i < mtx.vout.size() - 1; i++) {
        if (mtx.vout[i].IsFee()) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Transaction can only have one fee output.");
        }
    }

    UniValue issuances = request.params[1].get_array();

    for (unsigned int idx = 0; idx < issuances.size(); idx++) {
        const UniValue& issuance = issuances[idx];
        const UniValue& issuance_o = issuance.get_obj();

        CAmount asset_amount = 0;
        const UniValue& asset_amount_uni = issuance_o["asset_amount"];
        if (asset_amount_uni.isNum()) {
            asset_amount = AmountFromValue(asset_amount_uni);
            if (asset_amount <= 0) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, asset_amount must be positive");
            }
        } else {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Asset amount must be given for each reissuance.");
        }

        const UniValue& asset_address_uni = issuance_o["asset_address"];
        if (!asset_address_uni.isStr()) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Reissuance missing asset_address");
        }
        CTxDestination asset_dest = DecodeDestination(asset_address_uni.get_str());
        if (std::get_if<CNoDestination>(&asset_dest)) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Invalid asset address provided: %s", asset_address_uni.get_str()));
        }

        int input_index = -1;
        const UniValue& input_index_o = issuance_o["input_index"];
        if (input_index_o.isNum()) {
            input_index = input_index_o.get_int();
            if (input_index < 0) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Input index must be non-negative.");
            } else if ((size_t) input_index >= mtx.vin.size()) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Input index must exist in transaction.");
            } else if (!mtx.vin[input_index].assetIssuance.IsNull()) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Selected transaction input already has issuance data.");
            }
        } else {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Input indexes for all reissuances are required.");
        }

        uint256 asset_blinder = ParseHashV(issuance_o["asset_blinder"], "asset_blinder");
        uint256 entropy = ParseHashV(issuance_o["entropy"], "entropy");
        reissueasset_base(mtx, input_index, asset_amount, asset_dest, asset_blinder, entropy);
    }

    UniValue ret(UniValue::VOBJ);
    ret.pushKV("hex", EncodeHexTx(CTransaction(mtx)));
    return ret;
},
    };
}

// END ELEMENTS
//

void RegisterRawTransactionRPCCommands(CRPCTable &t)
{
// clang-format off
static const CRPCCommand commands[] =
{ //  category              actor (function)            argNames
  //  --------------------- ------------------------        -----------------------     ----------
    { "rawtransactions",    &getrawtransaction,           },
    { "rawtransactions",    &createrawtransaction,        },
    { "rawtransactions",    &decoderawtransaction,        },
    { "rawtransactions",    &decodescript,                },
    { "rawtransactions",    &sendrawtransaction,          },
    { "rawtransactions",    &combinerawtransaction,       },
    { "rawtransactions",    &signrawtransactionwithkey,   },
    { "rawtransactions",    &testmempoolaccept,           },
    { "rawtransactions",    &decodepsbt,                  },
    { "rawtransactions",    &combinepsbt,                 },
    { "rawtransactions",    &blindpsbt,                   },
    { "rawtransactions",    &finalizepsbt,                },
    { "rawtransactions",    &createpsbt,                  },
    { "rawtransactions",    &converttopsbt,               },
    { "rawtransactions",    &utxoupdatepsbt,              },
    { "rawtransactions",    &joinpsbts,                   },
    { "rawtransactions",    &analyzepsbt,                 },

    { "blockchain",         &gettxoutproof,               },
    { "blockchain",         &verifytxoutproof,            },
    { "rawtransactions",    &rawissueasset,               },
    { "rawtransactions",    &rawreissueasset,             },
    { "rawtransactions",    &rawblindrawtransaction,      },
};
// clang-format on
    for (const auto& c : commands) {
        t.appendCommand(c.name, &c);
    }
}
