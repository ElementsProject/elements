// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2019 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <asset.h>
#include <chain.h>
#include <coins.h>
#include <compat/byteswap.h>
#include <consensus/tx_verify.h>
#include <consensus/validation.h>
#include <core_io.h>
#include <index/txindex.h>
#include <init.h>
#include <key_io.h>
#include <keystore.h>
#include <merkleblock.h>
#include <net.h>
#include <pegins.h>
#include <node/transaction.h>
#include <policy/policy.h>
#include <policy/rbf.h>
#include <primitives/transaction.h>
#include <psbt.h>
#include <rpc/rawtransaction.h>
#include <rpc/server.h>
#include <rpc/util.h>
#include <script/script.h>
#include <script/script_error.h>
#include <script/sign.h>
#include <script/standard.h>
#include <uint256.h>
#include <util/bip32.h>
#include <util/strencodings.h>
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
        CBlockIndex* pindex = LookupBlockIndex(hashBlock);
        if (pindex) {
            if (chainActive.Contains(pindex)) {
                entry.pushKV("confirmations", 1 + chainActive.Height() - pindex->nHeight);
                entry.pushKV("time", pindex->GetBlockTime());
                entry.pushKV("blocktime", pindex->GetBlockTime());
            }
            else
                entry.pushKV("confirmations", 0);
        }
    }
}

void RPCCheckPSBTBlinding(const PartiallySignedTransaction& psbtx) {
    // Plausibly, we may want a way to let the user continue anyway. However, we
    //   want to fail by default, to make it as hard as possible to do something
    //   really dangerous. And since this way of handling blinded PSBTs is going
    //   away "real soon now" in favor of a better one, no sense in trying too
    //   hard about it.

    for (size_t i = 0; i < psbtx.outputs.size(); ++i) {
        const PSBTOutput& output = psbtx.outputs[i];
        const CTxOut& txo = psbtx.tx->vout[i];

        if (txo.nValue.IsCommitment() || txo.nAsset.IsCommitment()) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "PSBT's 'tx' field may not have pre-blinded outputs.");
        }

        if (!output.value_commitment.IsCommitment() &&
            !output.asset_commitment.IsCommitment() &&
            output.value_blinding_factor.IsNull() &&
            output.asset_blinding_factor.IsNull()) {
            // Nothing blinded, nothing to check.
            continue;
        } else if (!output.value_commitment.IsCommitment() ||
            !output.asset_commitment.IsCommitment() ||
            output.value_blinding_factor.IsNull() ||
            output.asset_blinding_factor.IsNull()) {
            // Something blinded, but not everything? That's not expected.
            throw JSONRPCError(RPC_INVALID_PARAMETER, "PSBT has a partially-blinded output. Blinded outputs must be fully blinded.");
        }

        if (!VerifyConfidentialPair(output.value_commitment, output.asset_commitment, txo.nValue.GetAmount(), txo.nAsset.GetAsset(), output.value_blinding_factor, output.asset_blinding_factor)) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "PSBT's 'tx' field output values do not match blinded output values (or are invalid in some way)! Either there is a bug, or the blinder is attacking you.");
        }
    }
}

static UniValue getrawtransaction(const JSONRPCRequest& request)
{
    const RPCHelpMan help{
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
            "\"data\"      (string) The serialized, hex-encoded data for 'txid'\n"
                     },
                     RPCResult{"if verbose is set to true",
            "{\n"
            "  \"in_active_chain\": b, (bool) Whether specified block is in the active chain or not (only present with explicit \"blockhash\" argument)\n"
            "  \"hex\" : \"data\",       (string) The serialized, hex-encoded data for 'txid'\n"
            "  \"txid\" : \"id\",        (string) The transaction id (same as provided)\n"
            "  \"hash\" : \"id\",        (string) The transaction hash (differs from txid for witness transactions)\n"
            "  \"size\" : n,             (numeric) The serialized transaction size\n"
            "  \"vsize\" : n,            (numeric) The virtual transaction size (differs from size for witness transactions)\n"
            "  \"weight\" : n,           (numeric) The transaction's weight (between vsize*4-3 and vsize*4)\n"
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
            "       \"n\" : n,                    (numeric) index\n"
            "       \"scriptPubKey\" : {          (json object)\n"
            "         \"asm\" : \"asm\",          (string) the asm\n"
            "         \"hex\" : \"hex\",          (string) the hex\n"
            "         \"reqSigs\" : n,            (numeric) The required sigs\n"
            "         \"type\" : \"pubkeyhash\",  (string) The type, eg 'pubkeyhash'\n"
            "         \"addresses\" : [           (json array of string)\n"
            "           \"address\"        (string) bitcoin address\n"
            "           ,...\n"
            "         ],\n"
            "         \"pegout_chain\" : \"hex\", (string) (only pegout) Hash of genesis block of parent chain'\n"
            "         \"pegout_asm\":\"asm\",     (string) (only pegout) pegout scriptpubkey (asm)'\n"
            "         \"pegout_hex\":\"hex\",     (string) (only pegout) pegout scriptpubkey (hex)'\n"
            "         \"pegout_type\" : \"pubkeyhash\", (string) (only pegout) The pegout type, eg 'pubkeyhash'\n"
            "         \"pegout_addresses\" : [    (json array of string) (only pegout)\n"
            "       }\n"
            "     }\n"
            "     ,...\n"
            "  ],\n"
            "  \"blockhash\" : \"hash\",   (string) the block hash\n"
            "  \"confirmations\" : n,      (numeric) The confirmations\n"
            "  \"blocktime\" : ttt         (numeric) The block time in seconds since epoch (Jan 1 1970 GMT)\n"
            "  \"time\" : ttt,             (numeric) Same as \"blocktime\"\n"
            "}\n"
                    },
                },
                RPCExamples{
                    HelpExampleCli("getrawtransaction", "\"mytxid\"")
            + HelpExampleCli("getrawtransaction", "\"mytxid\" true")
            + HelpExampleRpc("getrawtransaction", "\"mytxid\", true")
            + HelpExampleCli("getrawtransaction", "\"mytxid\" false \"myblockhash\"")
            + HelpExampleCli("getrawtransaction", "\"mytxid\" true \"myblockhash\"")
                },
    };

    if (request.fHelp || !help.IsValidNumArgs(request.params.size())) {
        throw std::runtime_error(help.ToString());
    }

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
        blockindex = LookupBlockIndex(blockhash);
        if (!blockindex) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Block hash not found");
        }
        in_active_chain = chainActive.Contains(blockindex);
    }

    bool f_txindex_ready = false;
    if (g_txindex && !blockindex) {
        f_txindex_ready = g_txindex->BlockUntilSyncedToCurrentChain();
    }

    CTransactionRef tx;
    uint256 hash_block;
    if (!GetTransaction(hash, tx, Params().GetConsensus(), hash_block, blockindex)) {
        std::string errmsg;
        if (blockindex) {
            if (!(blockindex->nStatus & BLOCK_HAVE_DATA)) {
                throw JSONRPCError(RPC_MISC_ERROR, "Block not available");
            }
            errmsg = "No such transaction found in the provided block";
        } else if (!g_txindex) {
            errmsg = "No such mempool transaction. Use -txindex to enable blockchain transaction queries";
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
}

static UniValue gettxoutproof(const JSONRPCRequest& request)
{
    if (request.fHelp || (request.params.size() != 1 && request.params.size() != 2))
        throw std::runtime_error(
            RPCHelpMan{"gettxoutproof",
                "\nReturns a hex-encoded proof that \"txid\" was included in a block.\n"
                "\nNOTE: By default this function only works sometimes. This is when there is an\n"
                "unspent output in the utxo for this transaction. To make it always work,\n"
                "you need to maintain a transaction index, using the -txindex command line option or\n"
                "specify the block in which the transaction is included manually (by blockhash).\n",
                {
                    {"txids", RPCArg::Type::ARR, RPCArg::Optional::NO, "A json array of txids to filter",
                        {
                            {"txid", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "A transaction hash"},
                        },
                        },
                    {"blockhash", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED_NAMED_ARG, "If specified, looks for txid in the block with this hash"},
                },
                RPCResult{
            "\"data\"           (string) A string that is a serialized, hex-encoded data for the proof.\n"
                },
                RPCExamples{""},
            }.ToString()
        );

    std::set<uint256> setTxids;
    uint256 oneTxid;
    UniValue txids = request.params[0].get_array();
    for (unsigned int idx = 0; idx < txids.size(); idx++) {
        const UniValue& txid = txids[idx];
        uint256 hash(ParseHashV(txid, "txid"));
        if (setTxids.count(hash))
            throw JSONRPCError(RPC_INVALID_PARAMETER, std::string("Invalid parameter, duplicated txid: ")+txid.get_str());
       setTxids.insert(hash);
       oneTxid = hash;
    }

    CBlockIndex* pblockindex = nullptr;
    uint256 hashBlock;
    if (!request.params[1].isNull()) {
        LOCK(cs_main);
        hashBlock = ParseHashV(request.params[1], "blockhash");
        pblockindex = LookupBlockIndex(hashBlock);
        if (!pblockindex) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Block not found");
        }
    } else {
        LOCK(cs_main);

        // Loop through txids and try to find which block they're in. Exit loop once a block is found.
        for (const auto& tx : setTxids) {
            const Coin& coin = AccessByTxid(*pcoinsTip, tx);
            if (!coin.IsSpent()) {
                pblockindex = chainActive[coin.nHeight];
                break;
            }
        }
    }


    // Allow txindex to catch up if we need to query it and before we acquire cs_main.
    if (g_txindex && !pblockindex) {
        g_txindex->BlockUntilSyncedToCurrentChain();
    }

    LOCK(cs_main);

    if (pblockindex == nullptr)
    {
        CTransactionRef tx;
        if (!GetTransaction(oneTxid, tx, Params().GetConsensus(), hashBlock) || hashBlock.IsNull())
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Transaction not yet in block");
        pblockindex = LookupBlockIndex(hashBlock);
        if (!pblockindex) {
            throw JSONRPCError(RPC_INTERNAL_ERROR, "Transaction index corrupt");
        }
    }

    CBlock block;
    if(!ReadBlockFromDisk(block, pblockindex, Params().GetConsensus()))
        throw JSONRPCError(RPC_INTERNAL_ERROR, "Can't read block from disk");

    unsigned int ntxFound = 0;
    for (const auto& tx : block.vtx)
        if (setTxids.count(tx->GetHash()))
            ntxFound++;
    if (ntxFound != setTxids.size())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Not all transactions found in specified or retrieved block");

    CDataStream ssMB(SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS);
    CMerkleBlock mb(block, setTxids);
    ssMB << mb;
    std::string strHex = HexStr(ssMB.begin(), ssMB.end());
    return strHex;
}

static UniValue verifytxoutproof(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 1)
        throw std::runtime_error(
            RPCHelpMan{"verifytxoutproof",
                "\nVerifies that a proof points to a transaction in a block, returning the transaction it commits to\n"
                "and throwing an RPC error if the block is not in our best chain\n",
                {
                    {"proof", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The hex-encoded proof generated by gettxoutproof"},
                },
                RPCResult{
            "[\"txid\"]      (array, strings) The txid(s) which the proof commits to, or empty array if the proof can not be validated.\n"
                },
                RPCExamples{""},
            }.ToString()
        );

    CDataStream ssMB(ParseHexV(request.params[0], "proof"), SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS);
    CMerkleBlock merkleBlock;
    ssMB >> merkleBlock;

    UniValue res(UniValue::VARR);

    std::vector<uint256> vMatch;
    std::vector<unsigned int> vIndex;
    if (merkleBlock.txn.ExtractMatches(vMatch, vIndex) != merkleBlock.header.hashMerkleRoot)
        return res;

    LOCK(cs_main);

    const CBlockIndex* pindex = LookupBlockIndex(merkleBlock.header.GetHash());
    if (!pindex || !chainActive.Contains(pindex) || pindex->nTx == 0) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Block not found in chain");
    }

    // Check if proof is valid, only add results if so
    if (pindex->nTx == merkleBlock.txn.GetNumTransactions()) {
        for (const uint256& hash : vMatch) {
            res.push_back(hash.GetHex());
        }
    }

    return res;
}

CMutableTransaction ConstructTransaction(const UniValue& inputs_in, const UniValue& outputs_in, const UniValue& locktime, bool rbf, const UniValue& assets_in, std::vector<CPubKey>* output_pubkeys_out)
{
    if (inputs_in.isNull() || outputs_in.isNull())
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, arguments 1 and 2 must be non-null");

    UniValue inputs = inputs_in.get_array();
    const bool outputs_is_obj = outputs_in.isObject();
    UniValue outputs = outputs_is_obj ? outputs_in.get_obj() : outputs_in.get_array();

    CMutableTransaction rawTx;

    if (!locktime.isNull()) {
        int64_t nLockTime = locktime.get_int64();
        if (nLockTime < 0 || nLockTime > LOCKTIME_MAX)
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, locktime out of range");
        rawTx.nLockTime = nLockTime;
    }

    UniValue assets;
    if (!assets_in.isNull()) {
        assets = assets_in.get_obj();
    }

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

        uint32_t nSequence;
        if (rbf) {
            nSequence = MAX_BIP125_RBF_SEQUENCE; /* CTxIn::SEQUENCE_FINAL - 2 */
        } else if (rawTx.nLockTime) {
            nSequence = CTxIn::SEQUENCE_FINAL - 1;
        } else {
            nSequence = CTxIn::SEQUENCE_FINAL;
        }

        // set the sequence number if passed in the parameters object
        const UniValue& sequenceObj = find_value(o, "sequence");
        if (sequenceObj.isNum()) {
            int64_t seqNr64 = sequenceObj.get_int64();
            if (seqNr64 < 0 || seqNr64 > CTxIn::SEQUENCE_FINAL) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, sequence number is out of range");
            } else {
                nSequence = (uint32_t)seqNr64;
            }
        }

        CTxIn in(COutPoint(txid, nOutput), CScript(), nSequence);

        rawTx.vin.push_back(in);
    }

    if (!outputs_is_obj) {
        // Translate array of key-value pairs into dict
        UniValue outputs_dict = UniValue(UniValue::VOBJ);
        for (size_t i = 0; i < outputs.size(); ++i) {
            const UniValue& output = outputs[i];
            if (!output.isObject()) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, key-value pair not an object as expected");
            }
            if (output.size() != 1) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, key-value pair must contain exactly one key");
            }
            outputs_dict.pushKVs(output);
        }
        outputs = std::move(outputs_dict);
    }
    // Keep track of the fee output so we can add it in the very end of the transaction.
    CTxOut fee_out;

    // Duplicate checking
    std::set<CTxDestination> destinations;
    bool has_data{false};

    for (const std::string& name_ : outputs.getKeys()) {
        // ELEMENTS:
        // Asset defaults to policyAsset
        CAsset asset(::policyAsset);
        if (!assets.isNull()) {
            if (!find_value(assets, name_).isNull()) {
                asset = CAsset(ParseHashO(assets, name_));
            }
        }

        if (name_ == "data") {
            if (has_data) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, duplicate key: data");
            }
            has_data = true;
            std::vector<unsigned char> data = ParseHexV(outputs[name_].getValStr(), "Data");

            CTxOut out(asset, 0, CScript() << OP_RETURN << data);
            rawTx.vout.push_back(out);
            if (output_pubkeys_out) {
                output_pubkeys_out->push_back(CPubKey());
            }
        } else if (name_ == "vdata") {
            // ELEMENTS: support multi-push OP_RETURN
            UniValue vdata = outputs[name_].get_array();
            CScript datascript = CScript() << OP_RETURN;
            for (size_t i = 0; i < vdata.size(); i++) {
                std::vector<unsigned char> data = ParseHexV(vdata[i].get_str(), "Data");
                datascript << data;
            }

            CTxOut out(asset, 0, datascript);
            rawTx.vout.push_back(out);
            if (output_pubkeys_out) {
                output_pubkeys_out->push_back(CPubKey());
            }
        } else if (name_ == "fee") {
            // ELEMENTS: explicit fee outputs
            CAmount nAmount = AmountFromValue(outputs[name_]);
            fee_out = CTxOut(asset, nAmount, CScript());
        } else if (name_ == "burn") {
            CScript datascript = CScript() << OP_RETURN;
            CAmount nAmount = AmountFromValue(outputs[name_]);
            CTxOut out(asset, nAmount, datascript);
            rawTx.vout.push_back(out);
            if (output_pubkeys_out) {
                output_pubkeys_out->push_back(CPubKey());
            }
        } else {
            CTxDestination destination = DecodeDestination(name_);
            if (!IsValidDestination(destination)) {
                throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, std::string("Invalid Bitcoin address: ") + name_);
            }

            if (!destinations.insert(destination).second) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, std::string("Invalid parameter, duplicated address: ") + name_);
            }

            CScript scriptPubKey = GetScriptForDestination(destination);
            CAmount nAmount = AmountFromValue(outputs[name_]);

            CTxOut out(asset, nAmount, scriptPubKey);
            CPubKey blind_pub;
            if (IsBlindDestination(destination)) {
                blind_pub = GetDestinationBlindingKey(destination);
                if (!output_pubkeys_out) {
                    // Only use the pubkey-in-nonce hack if the caller is not getting the pubkeys the nice way.
                    out.nNonce.vchCommitment = std::vector<unsigned char>(blind_pub.begin(), blind_pub.end());
                }
            }
            rawTx.vout.push_back(out);
            if (output_pubkeys_out) {
                output_pubkeys_out->push_back(blind_pub);
            }
        }
    }

    // Add fee output in the end.
    if (!fee_out.nValue.IsNull() && fee_out.nValue.GetAmount() > 0) {
        rawTx.vout.push_back(fee_out);
        if (output_pubkeys_out) {
            output_pubkeys_out->push_back(CPubKey());
        }
    }

    if (rbf && rawTx.vin.size() > 0 && !SignalsOptInRBF(CTransaction(rawTx))) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter combination: Sequence number(s) contradict replaceable option");
    }

    return rawTx;
}

static UniValue createrawtransaction(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() < 2 || request.params.size() > 5) {
        throw std::runtime_error(
            RPCHelpMan{"createrawtransaction",
                "\nCreate a transaction spending the given inputs and creating new outputs.\n"
                "Outputs can be addresses or data.\n"
                "Returns hex-encoded raw transaction.\n"
                "Note that the transaction's inputs are not signed, and\n"
                "it is not stored in the wallet or transmitted to the network.\n",
                {
                    {"inputs", RPCArg::Type::ARR, RPCArg::Optional::NO, "A json array of json objects",
                        {
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                                {
                                    {"txid", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The transaction id"},
                                    {"vout", RPCArg::Type::NUM, RPCArg::Optional::NO, "The output number"},
                                    {"sequence", RPCArg::Type::NUM, /* default */ "depends on the value of the 'replaceable' and 'locktime' arguments", "The sequence number"},
                                },
                                },
                        },
                        },
                    {"outputs", RPCArg::Type::ARR, RPCArg::Optional::NO, "a json array with outputs (key-value pairs), where none of the keys are duplicated.\n"
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
            "\"transaction\"              (string) hex string of the transaction\n"
                },
                RPCExamples{
                    HelpExampleCli("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\" \"[{\\\"address\\\":0.01}]\"")
            + HelpExampleCli("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\" \"[{\\\"data\\\":\\\"00010203\\\"}]\"")
            + HelpExampleRpc("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\", \"[{\\\"address\\\":0.01}]\"")
            + HelpExampleRpc("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\", \"[{\\\"data\\\":\\\"00010203\\\"}]\"")
                },
            }.ToString());
    }

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
}

static UniValue decoderawtransaction(const JSONRPCRequest& request)
{
    const RPCHelpMan help{"decoderawtransaction",
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
            "{\n"
            "  \"txid\" : \"id\",        (string) The transaction id\n"
            "  \"hash\" : \"id\",        (string) The transaction hash (differs from txid for witness transactions)\n"
            "  \"size\" : n,             (numeric) The transaction size\n"
            "  \"vsize\" : n,            (numeric) The virtual transaction size (differs from size for witness transactions)\n"
            "  \"weight\" : n,           (numeric) The transaction's weight (between vsize*4 - 3 and vsize*4)\n"
            "  \"version\" : n,          (numeric) The version\n"
            "  \"locktime\" : ttt,       (numeric) The lock time\n"
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
                },
                RPCExamples{
                    HelpExampleCli("decoderawtransaction", "\"hexstring\"")
            + HelpExampleRpc("decoderawtransaction", "\"hexstring\"")
                },
    };

    if (request.fHelp || !help.IsValidNumArgs(request.params.size())) {
        throw std::runtime_error(help.ToString());
    }

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
}

static UniValue decodescript(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 1)
        throw std::runtime_error(
            RPCHelpMan{"decodescript",
                "\nDecode a hex-encoded script.\n",
                {
                    {"hexstring", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "the hex-encoded script"},
                },
                RPCResult{
            "{\n"
            "  \"asm\":\"asm\",   (string) Script public key\n"
            "  \"hex\":\"hex\",   (string) hex-encoded public key\n"
            "  \"type\":\"type\", (string) The output type\n"
            "  \"reqSigs\": n,    (numeric) The required signatures\n"
            "  \"addresses\": [   (json array of string)\n"
            "     \"address\"     (string) bitcoin address\n"
            "     ,...\n"
            "  ],\n"
            "  \"p2sh\",\"address\" (string) address of P2SH script wrapping this redeem script (not returned if the script is already a P2SH).\n"
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("decodescript", "\"hexstring\"")
            + HelpExampleRpc("decodescript", "\"hexstring\"")
                },
            }.ToString());

    RPCTypeCheck(request.params, {UniValue::VSTR});

    UniValue r(UniValue::VOBJ);
    CScript script;
    if (request.params[0].get_str().size() > 0){
        std::vector<unsigned char> scriptData(ParseHexV(request.params[0], "argument"));
        script = CScript(scriptData.begin(), scriptData.end());
    } else {
        // Empty scripts are valid
    }
    ScriptPubKeyToUniv(script, r, false);

    UniValue type;
    type = find_value(r, "type");

    if (type.isStr() && type.get_str() != "scripthash") {
        // P2SH cannot be wrapped in a P2SH. If this script is already a P2SH,
        // don't return the address for a P2SH of the P2SH.
        r.pushKV("p2sh", EncodeDestination(ScriptHash(CScriptID(script))));
        // P2SH and witness programs cannot be wrapped in P2WSH, if this script
        // is a witness program, don't return addresses for a segwit programs.
        if (type.get_str() == "pubkey" || type.get_str() == "pubkeyhash" || type.get_str() == "multisig" || type.get_str() == "nonstandard" || type.get_str() == "true") {
            std::vector<std::vector<unsigned char>> solutions_data;
            txnouttype which_type = Solver(script, solutions_data);
            // Uncompressed pubkeys cannot be used with segwit checksigs.
            // If the script contains an uncompressed pubkey, skip encoding of a segwit program.
            if ((which_type == TX_PUBKEY) || (which_type == TX_MULTISIG)) {
                for (const auto& solution : solutions_data) {
                    if ((solution.size() != 1) && !CPubKey(solution).IsCompressed()) {
                        return r;
                    }
                }
            }
            UniValue sr(UniValue::VOBJ);
            CScript segwitScr;
            if (which_type == TX_PUBKEY) {
                segwitScr = GetScriptForDestination(WitnessV0KeyHash(Hash160(solutions_data[0].begin(), solutions_data[0].end())));
            } else if (which_type == TX_PUBKEYHASH) {
                segwitScr = GetScriptForDestination(WitnessV0KeyHash(solutions_data[0]));
            } else {
                // Scripts that are not fit for P2WPKH are encoded as P2WSH.
                // Newer segwit program versions should be considered when then become available.
                segwitScr = GetScriptForDestination(WitnessV0ScriptHash(script));
            }
            ScriptPubKeyToUniv(segwitScr, sr, true);
            sr.pushKV("p2sh-segwit", EncodeDestination(ScriptHash(CScriptID(segwitScr))));
            r.pushKV("segwit", sr);
        }
    }

    return r;
}

/** Pushes a JSON object for script verification or signing errors to vErrorsRet. */
static void TxInErrorToJSON(const CTxIn& txin, const CTxInWitness& txinwit, UniValue& vErrorsRet, const std::string& strMessage)
{
    UniValue entry(UniValue::VOBJ);
    entry.pushKV("txid", txin.prevout.hash.ToString());
    entry.pushKV("vout", (uint64_t)txin.prevout.n);
    UniValue witness(UniValue::VARR);
    for (unsigned int i = 0; i < txinwit.scriptWitness.stack.size(); i++) {
        witness.push_back(HexStr(txinwit.scriptWitness.stack[i].begin(), txinwit.scriptWitness.stack[i].end()));
    }
    entry.pushKV("witness", witness);
    entry.pushKV("scriptSig", HexStr(txin.scriptSig.begin(), txin.scriptSig.end()));
    entry.pushKV("sequence", (uint64_t)txin.nSequence);
    entry.pushKV("error", strMessage);
    vErrorsRet.push_back(entry);
}

static UniValue combinerawtransaction(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 1)
        throw std::runtime_error(
            RPCHelpMan{"combinerawtransaction",
                "\nCombine multiple partially signed transactions into one transaction.\n"
                "The combined transaction may be another partially signed transaction or a \n"
                "fully signed transaction.",
                {
                    {"txs", RPCArg::Type::ARR, RPCArg::Optional::NO, "A json array of hex strings of partially signed transactions",
                        {
                            {"hexstring", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "A transaction hash"},
                        },
                        },
                },
                RPCResult{
            "\"hex\"            (string) The hex-encoded raw transaction with signature(s)\n"
                },
                RPCExamples{
                    HelpExampleCli("combinerawtransaction", "[\"myhex1\", \"myhex2\", \"myhex3\"]")
                },
            }.ToString());


    UniValue txs = request.params[0].get_array();
    std::vector<CMutableTransaction> txVariants(txs.size());

    for (unsigned int idx = 0; idx < txs.size(); idx++) {
        if (!DecodeHexTx(txVariants[idx], txs[idx].get_str(), true)) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR, strprintf("TX decode failed for tx %d", idx));
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
        LOCK(cs_main);
        LOCK(mempool.cs);
        CCoinsViewCache &viewChain = *pcoinsTip;
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
}

UniValue SignTransaction(interfaces::Chain& chain, CMutableTransaction& mtx, const UniValue& prevTxsUnival, CBasicKeyStore *keystore, bool is_temp_keystore, const UniValue& hashType)
{
    // Fetch previous transactions (inputs):
    CCoinsView viewDummy;
    CCoinsViewCache view(&viewDummy);
    {
        LOCK2(cs_main, mempool.cs);
        CCoinsViewCache &viewChain = *pcoinsTip;
        CCoinsViewMemPool viewMempool(&viewChain, mempool);
        view.SetBackend(viewMempool); // temporarily switch cache backend to db+mempool view

        for (const CTxIn& txin : mtx.vin) {
            view.AccessCoin(txin.prevout); // Load entries from viewChain into view; can fail.
        }

        view.SetBackend(viewDummy); // switch back to avoid locking mempool for too long
    }

    // Add previous txouts given in the RPC call:
    if (!prevTxsUnival.isNull()) {
        UniValue prevTxs = prevTxsUnival.get_array();
        for (unsigned int idx = 0; idx < prevTxs.size(); ++idx) {
            const UniValue& p = prevTxs[idx];
            if (!p.isObject()) {
                throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "expected object with {\"txid'\",\"vout\",\"scriptPubKey\"}");
            }

            UniValue prevOut = p.get_obj();

            RPCTypeCheckObj(prevOut,
                {
                    {"txid", UniValueType(UniValue::VSTR)},
                    {"vout", UniValueType(UniValue::VNUM)},
                    {"scriptPubKey", UniValueType(UniValue::VSTR)},
                });

            uint256 txid = ParseHashO(prevOut, "txid");

            int nOut = find_value(prevOut, "vout").get_int();
            if (nOut < 0) {
                throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "vout must be positive");
            }

            COutPoint out(txid, nOut);
            std::vector<unsigned char> pkData(ParseHexO(prevOut, "scriptPubKey"));
            CScript scriptPubKey(pkData.begin(), pkData.end());

            {
                const Coin& coin = view.AccessCoin(out);
                if (!coin.IsSpent() && coin.out.scriptPubKey != scriptPubKey) {
                    std::string err("Previous output scriptPubKey mismatch:\n");
                    err = err + ScriptToAsmStr(coin.out.scriptPubKey) + "\nvs:\n"+
                        ScriptToAsmStr(scriptPubKey);
                    throw JSONRPCError(RPC_DESERIALIZATION_ERROR, err);
                }
                Coin newcoin;
                newcoin.out.scriptPubKey = scriptPubKey;
                newcoin.out.nValue = CConfidentialValue(MAX_MONEY);
                if (prevOut.exists("amount")) {
                    newcoin.out.nValue = CConfidentialValue(AmountFromValue(find_value(prevOut, "amount")));
                } else if (prevOut.exists("amountcommitment")) {
                    // Segwit sigs require the amount commitment to be sighashed
                    newcoin.out.nValue.vchCommitment = ParseHexO(prevOut, "amountcommitment");
                }
                newcoin.nHeight = 1;
                view.AddCoin(out, std::move(newcoin), true);
            }

            // if redeemScript and private keys were given, add redeemScript to the keystore so it can be signed
            if (is_temp_keystore && (scriptPubKey.IsPayToScriptHash() || scriptPubKey.IsPayToWitnessScriptHash())) {
                RPCTypeCheckObj(prevOut,
                    {
                        {"redeemScript", UniValueType(UniValue::VSTR)},
                        {"witnessScript", UniValueType(UniValue::VSTR)},
                    }, true);
                UniValue rs = find_value(prevOut, "redeemScript");
                if (!rs.isNull()) {
                    std::vector<unsigned char> rsData(ParseHexV(rs, "redeemScript"));
                    CScript redeemScript(rsData.begin(), rsData.end());
                    keystore->AddCScript(redeemScript);
                    // Automatically also add the P2WSH wrapped version of the script (to deal with P2SH-P2WSH).
                    // This is only for compatibility, it is encouraged to use the explicit witnessScript field instead.
                    keystore->AddCScript(GetScriptForWitness(redeemScript));
                }
                UniValue ws = find_value(prevOut, "witnessScript");
                if (!ws.isNull()) {
                    std::vector<unsigned char> wsData(ParseHexV(ws, "witnessScript"));
                    CScript witnessScript(wsData.begin(), wsData.end());
                    keystore->AddCScript(witnessScript);
                    // Automatically also add the P2WSH wrapped version of the script (to deal with P2SH-P2WSH).
                    keystore->AddCScript(GetScriptForWitness(witnessScript));
                }
                if (rs.isNull() && ws.isNull()) {
                    throw JSONRPCError(RPC_INVALID_PARAMETER, "Missing redeemScript/witnessScript");
                }
            }
        }
    }

    int nHashType = ParseSighashString(hashType);

    bool fHashSingle = ((nHashType & ~SIGHASH_ANYONECANPAY) == SIGHASH_SINGLE);

    // Script verification errors
    UniValue vErrors(UniValue::VARR);

    const auto& fedpegscripts = GetValidFedpegScripts(chainActive.Tip(), Params().GetConsensus(), true /* nextblock_validation */);

    // ELEMENTS:
    // Track an immature peg-in that's otherwise valid, give warning
    bool immature_pegin = false;

    // Use CTransaction for the constant parts of the
    // transaction to avoid rehashing.
    const CTransaction txConst(mtx);
    // Sign what we can, including pegin inputs:
    mtx.witness.vtxinwit.resize(mtx.vin.size());
    for (unsigned int i = 0; i < mtx.vin.size(); i++) {
        CTxIn& txin = mtx.vin[i];
        const CTxInWitness& inWitness = mtx.witness.vtxinwit[i];
        const Coin& coin = view.AccessCoin(txin.prevout);

        std::string err;
        if (!txin.m_is_pegin && coin.IsSpent()) {
            TxInErrorToJSON(txin, inWitness, vErrors, "Input not found or already spent");
            continue;
        } else if (txin.m_is_pegin && (txConst.witness.vtxinwit.size() <= i || !IsValidPeginWitness(txConst.witness.vtxinwit[i].m_pegin_witness, fedpegscripts, txin.prevout, err, false))) {
            TxInErrorToJSON(txin, inWitness, vErrors, "Peg-in input has invalid proof.");
            continue;
        }
        // Report warning about immature peg-in though
        bool depth_failed = false;
        if(txin.m_is_pegin && !IsValidPeginWitness(txConst.witness.vtxinwit[i].m_pegin_witness, fedpegscripts, txin.prevout, err, true, &depth_failed)) {
            assert(depth_failed);
            immature_pegin = true;
        }

        const CScript& prevPubKey = txin.m_is_pegin ? GetPeginOutputFromWitness(txConst.witness.vtxinwit[i].m_pegin_witness).scriptPubKey : coin.out.scriptPubKey;
        const CConfidentialValue& amount = txin.m_is_pegin ? GetPeginOutputFromWitness(txConst.witness.vtxinwit[i].m_pegin_witness).nValue : coin.out.nValue;

        SignatureData sigdata = DataFromTransaction(mtx, i, coin.out);
        // Only sign SIGHASH_SINGLE if there's a corresponding output:
        if (!fHashSingle || (i < mtx.vout.size())) {
            ProduceSignature(*keystore, MutableTransactionSignatureCreator(&mtx, i, amount, nHashType), prevPubKey, sigdata);
        }

        UpdateTransaction(mtx, i, sigdata);

        // amount must be specified for valid segwit signature
        if (amount.IsExplicit() && amount.GetAmount() == MAX_MONEY && !mtx.witness.vtxinwit[i].scriptWitness.IsNull()) {
            throw JSONRPCError(RPC_TYPE_ERROR, strprintf("Missing amount for %s", coin.out.ToString()));
        }

        ScriptError serror = SCRIPT_ERR_OK;
        if (!VerifyScript(txin.scriptSig, prevPubKey, &inWitness.scriptWitness, STANDARD_SCRIPT_VERIFY_FLAGS, TransactionSignatureChecker(&txConst, i, amount), &serror)) {
            if (serror == SCRIPT_ERR_INVALID_STACK_OPERATION) {
                // Unable to sign input and verification failed (possible attempt to partially sign).
                TxInErrorToJSON(txin, inWitness, vErrors, "Unable to sign input, invalid stack size (possibly missing key)");
            } else {
                TxInErrorToJSON(txin, inWitness, vErrors, ScriptErrorString(serror));
            }
        }
    }
    bool fComplete = vErrors.empty();

    UniValue result(UniValue::VOBJ);
    result.pushKV("hex", EncodeHexTx(CTransaction(mtx)));
    result.pushKV("complete", fComplete);
    if (!vErrors.empty()) {
        result.pushKV("errors", vErrors);
    }
    if (immature_pegin) {
        result.pushKV("warning", "Possibly immature peg-in input(s) detected, signed anyways.");
    }

    return result;
}

static UniValue signrawtransactionwithkey(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() < 2 || request.params.size() > 4)
        throw std::runtime_error(
            RPCHelpMan{"signrawtransactionwithkey",
                "\nSign inputs for raw transaction (serialized, hex-encoded).\n"
                "The second argument is an array of base58-encoded private\n"
                "keys that will be the only keys used to sign the transaction.\n"
                "The third optional argument (may be null) is an array of previous transaction outputs that\n"
                "this transaction depends on but may not yet be in the block chain.\n",
                {
                    {"hexstring", RPCArg::Type::STR, RPCArg::Optional::NO, "The transaction hex string"},
                    {"privkeys", RPCArg::Type::ARR, RPCArg::Optional::NO, "A json array of base58-encoded private keys for signing",
                        {
                            {"privatekey", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "private key in base58-encoding"},
                        },
                        },
                    {"prevtxs", RPCArg::Type::ARR, RPCArg::Optional::OMITTED_NAMED_ARG, "A json array of previous dependent transaction outputs",
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
            "{\n"
            "  \"hex\" : \"value\",                  (string) The hex-encoded raw transaction with signature(s)\n"
            "  \"complete\" : true|false,          (boolean) If the transaction has a complete set of signatures\n"
            "  \"errors\" : [                      (json array of objects) Script verification errors (if there are any)\n"
            "    {\n"
            "      \"txid\" : \"hash\",              (string) The hash of the referenced, previous transaction\n"
            "      \"vout\" : n,                   (numeric) The index of the output to spent and used as input\n"
            "      \"scriptSig\" : \"hex\",          (string) The hex-encoded signature script\n"
            "      \"sequence\" : n,               (numeric) Script sequence number\n"
            "      \"error\" : \"text\"              (string) Verification or signing error related to the input\n"
            "    }\n"
            "    ,...\n"
            "  ]\n"
            "  \"warning\" : \"text\"            (string) Warning that a peg-in input signed may be immature. This could mean lack of connectivity to or misconfiguration of the daemon."
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("signrawtransactionwithkey", "\"myhex\" \"[\\\"key1\\\",\\\"key2\\\"]\"")
            + HelpExampleRpc("signrawtransactionwithkey", "\"myhex\", \"[\\\"key1\\\",\\\"key2\\\"]\"")
                },
            }.ToString());

    RPCTypeCheck(request.params, {UniValue::VSTR, UniValue::VARR, UniValue::VARR, UniValue::VSTR}, true);

    CMutableTransaction mtx;
    if (!DecodeHexTx(mtx, request.params[0].get_str(), true)) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    }

    CBasicKeyStore keystore;
    const UniValue& keys = request.params[1].get_array();
    for (unsigned int idx = 0; idx < keys.size(); ++idx) {
        UniValue k = keys[idx];
        CKey key = DecodeSecret(k.get_str());
        if (!key.IsValid()) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid private key");
        }
        keystore.AddKey(key);
    }

    return SignTransaction(*g_rpc_interfaces->chain, mtx, request.params[2], &keystore, true, request.params[3]);
}

UniValue signrawtransaction(const JSONRPCRequest& request)
{
    // This method should be removed entirely in V0.19, along with the entries in the
    // CRPCCommand table and rpc/client.cpp.
    throw JSONRPCError(RPC_METHOD_DEPRECATED, "signrawtransaction was removed in v0.18.\n"
        "Clients should transition to using signrawtransactionwithkey and signrawtransactionwithwallet");
}

UniValue sendrawtransaction(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() < 1 || request.params.size() > 2)
        throw std::runtime_error(
            RPCHelpMan{"sendrawtransaction",
                "\nSubmits raw transaction (serialized, hex-encoded) to local node and network.\n"
                "\nAlso see createrawtransaction and signrawtransactionwithkey calls.\n",
                {
                    {"hexstring", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The hex string of the raw transaction"},
                    {"allowhighfees", RPCArg::Type::BOOL, /* default */ "false", "Allow high fees"},
                },
                RPCResult{
            "\"hex\"             (string) The transaction hash in hex\n"
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
            }.ToString());

    RPCTypeCheck(request.params, {UniValue::VSTR, UniValue::VBOOL});

    // parse hex string from parameter
    CMutableTransaction mtx;
    if (!DecodeHexTx(mtx, request.params[0].get_str()))
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    CTransactionRef tx(MakeTransactionRef(std::move(mtx)));

    for (const auto& out : tx->vout) {
        // If we have a nonce, it could be a smuggled pubkey, or it could be a
        //   proper nonce produced by blinding. In the latter case, the value
        //   will always be blinded and not explicit. In the former case, we
        //   error out because the transaction is not blinded properly.
        if (!out.nNonce.IsNull() && out.nValue.IsExplicit()) {
            throw JSONRPCError(RPC_TRANSACTION_ERROR, "Transaction output has nonce, but is not blinded. Did you forget to call blindpsbt, blindrawtranssaction, or rawblindrawtransaction?");
        }
    }

    bool allowhighfees = false;
    if (!request.params[1].isNull()) allowhighfees = request.params[1].get_bool();
    const CAmount highfee{allowhighfees ? 0 : ::maxTxFee};
    uint256 txid;
    std::string err_string;
    const TransactionError err = BroadcastTransaction(tx, txid, err_string, highfee);
    if (TransactionError::OK != err) {
        throw JSONRPCTransactionError(err, err_string);
    }

    return txid.GetHex();
}

static UniValue testmempoolaccept(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() < 1 || request.params.size() > 2) {
        throw std::runtime_error(
            RPCHelpMan{"testmempoolaccept",
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
                    {"allowhighfees", RPCArg::Type::BOOL, /* default */ "false", "Allow high fees"},
                },
                RPCResult{
            "[                   (array) The result of the mempool acceptance test for each raw transaction in the input array.\n"
            "                            Length is exactly one for now.\n"
            " {\n"
            "  \"txid\"           (string) The transaction hash in hex\n"
            "  \"allowed\"        (boolean) If the mempool allows this tx to be inserted\n"
            "  \"reject-reason\"  (string) Rejection string (only present when 'allowed' is false)\n"
            " }\n"
            "]\n"
                },
                RPCExamples{
            "\nCreate a transaction\n"
            + HelpExampleCli("createrawtransaction", "\"[{\\\"txid\\\" : \\\"mytxid\\\",\\\"vout\\\":0}]\" \"{\\\"myaddress\\\":0.01}\"") +
            "Sign the transaction, and get back the hex\n"
            + HelpExampleCli("signrawtransactionwithwallet", "\"myhex\"") +
            "\nTest acceptance of the transaction (signed hex)\n"
            + HelpExampleCli("testmempoolaccept", "[\"signedhex\"]") +
            "\nAs a JSON-RPC call\n"
            + HelpExampleRpc("testmempoolaccept", "[\"signedhex\"]")
                },
            }.ToString());
    }

    RPCTypeCheck(request.params, {UniValue::VARR, UniValue::VBOOL});
    if (request.params[0].get_array().size() != 1) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Array must contain exactly one raw transaction for now");
    }

    CMutableTransaction mtx;
    if (!DecodeHexTx(mtx, request.params[0].get_array()[0].get_str())) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    }
    CTransactionRef tx(MakeTransactionRef(std::move(mtx)));
    const uint256& tx_hash = tx->GetHash();

    CAmount max_raw_tx_fee = ::maxTxFee;
    if (!request.params[1].isNull() && request.params[1].get_bool()) {
        max_raw_tx_fee = 0;
    }

    UniValue result(UniValue::VARR);
    UniValue result_0(UniValue::VOBJ);
    result_0.pushKV("txid", tx_hash.GetHex());

    CValidationState state;
    bool missing_inputs;
    bool test_accept_res;
    {
        LOCK(cs_main);
        test_accept_res = AcceptToMemoryPool(mempool, state, std::move(tx), &missing_inputs,
            nullptr /* plTxnReplaced */, false /* bypass_limits */, max_raw_tx_fee, /* test_accept */ true);
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

    result.push_back(std::move(result_0));
    return result;
}

static std::string WriteHDKeypath(std::vector<uint32_t>& keypath)
{
    std::string keypath_str = "m";
    for (uint32_t num : keypath) {
        keypath_str += "/";
        bool hardened = false;
        if (num & 0x80000000) {
            hardened = true;
            num &= ~0x80000000;
        }

        keypath_str += std::to_string(num);
        if (hardened) {
            keypath_str += "'";
        }
    }
    return keypath_str;
}

UniValue blindpsbt(const JSONRPCRequest& request)
{
    if (!g_con_elementsmode)
        throw std::runtime_error("PSBT operations are disabled when not in elementsmode.\n");

    if (request.fHelp || request.params.size() < 1 || request.params.size() > 2)
        throw std::runtime_error(
            RPCHelpMan{"blindpsbt",
                "\nUses the blinding data from the PSBT inputs to generate the blinding data for the PSBT outputs.\n",
                {
                    {"psbt", RPCArg::Type::STR, RPCArg::Optional::NO, "The PSBT base64 string"},
                    {"ignoreblindfail", RPCArg::Type::BOOL, /* default*/ "true", "Return a transaction even when a blinding attempt fails due to number of blinded inputs/outputs."},
                },
                RPCResult{
                    "\"psbt\"       (string) The base64-encoded partially signed transaction\n"
                },
                RPCExamples{
                    HelpExampleCli("blindpsbt", "\"psbt\"")
                    + HelpExampleRpc("blindpsbt", "\"psbt\"")
                }
            }.ToString()
        );

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
    unsigned int keyIndex = -1;
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
}

UniValue decodepsbt(const JSONRPCRequest& request)
{
    if (!g_con_elementsmode)
        throw std::runtime_error("PSBT operations are disabled when not in elementsmode.\n");

    if (request.fHelp || request.params.size() != 1)
        throw std::runtime_error(
            RPCHelpMan{"decodepsbt",
                "\nReturn a JSON object representing the serialized, base64-encoded partially signed Bitcoin transaction.\n",
                {
                    {"psbt", RPCArg::Type::STR, RPCArg::Optional::NO, "The PSBT base64 string"},
                },
                RPCResult{
            "{\n"
            "  \"tx\" : {                   (json object) The decoded network-serialized unsigned transaction.\n"
            "    ...                                      The layout is the same as the output of decoderawtransaction.\n"
            "  },\n"
            "  \"unknown\" : {                (json object) The unknown global fields\n"
            "    \"key\" : \"value\"            (key-value pair) An unknown key-value pair\n"
            "     ...\n"
            "  },\n"
            "  \"inputs\" : [                 (array of json objects)\n"
            "    {\n"
            "      \"non_witness_utxo\" : {   (json object, optional) Decoded network transaction for non-witness UTXOs\n"
            "        ...\n"
            "      },\n"
            "      \"witness_utxo\" : {            (json object, optional) Transaction output for witness UTXOs\n"
            "        \"amount\" : x.xxx,           (numeric) The value in " + CURRENCY_UNIT + "\n"
            "        \"scriptPubKey\" : {          (json object)\n"
            "          \"asm\" : \"asm\",            (string) The asm\n"
            "          \"hex\" : \"hex\",            (string) The hex\n"
            "          \"type\" : \"pubkeyhash\",    (string) The type, eg 'pubkeyhash'\n"
            "          \"address\" : \"address\"     (string) Bitcoin address if there is one\n"
            "        }\n"
            "      },\n"
            "      \"partial_signatures\" : {             (json object, optional)\n"
            "        \"pubkey\" : \"signature\",           (string) The public key and signature that corresponds to it.\n"
            "        ,...\n"
            "      },\n"
            "      \"sighash\" : \"type\",                  (string, optional) The sighash type to be used\n"
            "      \"redeem_script\" : {       (json object, optional)\n"
            "        \"asm\" : \"asm\",            (string) The asm\n"
            "        \"hex\" : \"hex\",            (string) The hex\n"
            "        \"type\" : \"pubkeyhash\",    (string) The type, eg 'pubkeyhash'\n"
            "      },\n"
            "      \"witness_script\" : {       (json object, optional)\n"
            "        \"asm\" : \"asm\",            (string) The asm\n"
            "        \"hex\" : \"hex\",            (string) The hex\n"
            "        \"type\" : \"pubkeyhash\",    (string) The type, eg 'pubkeyhash'\n"
            "      },\n"
            "      \"bip32_derivs\" : {          (json object, optional)\n"
            "        \"pubkey\" : {                     (json object, optional) The public key with the derivation path as the value.\n"
            "          \"master_fingerprint\" : \"fingerprint\"     (string) The fingerprint of the master key\n"
            "          \"path\" : \"path\",                         (string) The path\n"
            "        }\n"
            "        ,...\n"
            "      },\n"
            "      \"final_scriptsig\" : {       (json object, optional)\n"
            "        \"asm\" : \"asm\",            (string) The asm\n"
            "        \"hex\" : \"hex\",            (string) The hex\n"
            "      },\n"
            "      \"final_scriptwitness\": [\"hex\", ...], (array of string) hex-encoded witness data (if any)\n"
            "      \"value\": x.xxx,                      (numeric) The (unblinded) value of the input in " + CURRENCY_UNIT + "\n"
            "      \"value_blinding_factor\": \"hex\" ,   (string) The value blinding factor from the output being spent\n"
            "      \"asset\": \"hex\" ,                   (string) The (unblinded) asset id of the input\n"
            "      \"asset_blinding_factor\": \"hex\" ,   (string) The asset blinding factor from the output being spent\n"
            "      \"unknown\" : {                (json object) The unknown input fields\n"
            "        \"key\" : \"value\"            (key-value pair) An unknown key-value pair\n"
            "        ...\n"
            "      }\n"
            "    }\n"
            "    ,...\n"
            "  ]\n"
            "  \"outputs\" : [                 (array of json objects)\n"
            "    {\n"
            "      \"redeem_script\" : {       (json object, optional)\n"
            "          \"asm\" : \"asm\",            (string) The asm\n"
            "          \"hex\" : \"hex\",            (string) The hex\n"
            "          \"type\" : \"pubkeyhash\",    (string) The type, eg 'pubkeyhash'\n"
            "        }\n"
            "      \"witness_script\" : {       (json object, optional)\n"
            "          \"asm\" : \"asm\",            (string) The asm\n"
            "          \"hex\" : \"hex\",            (string) The hex\n"
            "          \"type\" : \"pubkeyhash\",    (string) The type, eg 'pubkeyhash'\n"
            "      }\n"
            "      \"bip32_derivs\" : [          (array of json objects, optional)\n"
            "        {\n"
            "          \"pubkey\" : \"pubkey\",                     (string) The public key this path corresponds to\n"
            "          \"master_fingerprint\" : \"fingerprint\"     (string) The fingerprint of the master key\n"
            "          \"path\" : \"path\",                         (string) The path\n"
            "          }\n"
            "        }\n"
            "        ,...\n"
            "      ],\n"
            "      \"value_commitment\": \"hex\" ,        (string) The blinded value of the output\n"
            "      \"value_blinding_factor\": \"hex\" ,   (string) The value blinding factor for the output\n"
            "      \"asset_commitment\": \"hex\" ,        (string) The blinded asset id of the output\n"
            "      \"asset_blinding_factor\": \"hex\" ,   (string) The asset blinding factor for the output\n"
            "      \"nonce_commitment\": \"hex\" ,        (string) The nonce for the output\n"
            "      \"surjection_proof\": \"hex\" ,        (string) The surjection proof for the output\n"
            "      \"blinding_pubkey\": \"hex\" ,         (string) The blinding pubkey for the output\n"
            "      \"unknown\" : {                (json object) The unknown output fields\n"
            "        \"key\" : \"value\"            (key-value pair) An unknown key-value pair\n"
            "         ...\n"
            "      },\n"
            "    }\n"
            "    ,...\n"
            "  ]\n"
            "  \"fee\" : fee                      (numeric, optional) The transaction fee paid if all UTXOs slots in the PSBT have been filled.\n"
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("decodepsbt", "\"psbt\"")
                },
            }.ToString());

    RPCTypeCheck(request.params, {UniValue::VSTR});

    // Unserialize the transactions
    PartiallySignedTransaction psbtx;
    std::string error;
    if (!DecodeBase64PSBT(psbtx, request.params[0].get_str(), error)) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, strprintf("TX decode failed %s", error));
    }
    RPCCheckPSBTBlinding(psbtx);

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
        if (!input.witness_utxo.IsNull()) {
            const CTxOut& txout = input.witness_utxo;

            UniValue out(UniValue::VOBJ);

            if (txout.nValue.IsExplicit()) {
                out.pushKV("amount", ValueFromAmount(txout.nValue.GetAmount()));
            } else {
                out.pushKV("amountcommitment", txout.nValue.GetHex());
            }

            UniValue o(UniValue::VOBJ);
            ScriptToUniv(txout.scriptPubKey, o, true);
            out.pushKV("scriptPubKey", o);
            in.pushKV("witness_utxo", out);
        } else if (input.non_witness_utxo) {
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
                txinwitness.push_back(HexStr(item.begin(), item.end()));
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
}

UniValue combinepsbt(const JSONRPCRequest& request)
{
    if (!g_con_elementsmode)
        throw std::runtime_error("PSBT operations are disabled when not in elementsmode.\n");

    if (request.fHelp || request.params.size() != 1)
        throw std::runtime_error(
            RPCHelpMan{"combinepsbt",
                "\nCombine multiple partially signed Bitcoin transactions into one transaction.\n"
                "Implements the Combiner role.\n",
                {
                    {"txs", RPCArg::Type::ARR, RPCArg::Optional::NO, "A json array of base64 strings of partially signed transactions",
                        {
                            {"psbt", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "A base64 string of a PSBT"},
                        },
                        },
                },
                RPCResult{
            "  \"psbt\"          (string) The base64-encoded partially signed transaction\n"
                },
                RPCExamples{
                    HelpExampleCli("combinepsbt", "[\"mybase64_1\", \"mybase64_2\", \"mybase64_3\"]")
                },
            }.ToString());

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
}

UniValue finalizepsbt(const JSONRPCRequest& request)
{
    if (!g_con_elementsmode)
        throw std::runtime_error("PSBT operations are disabled when not in elementsmode.\n");

    if (request.fHelp || request.params.size() < 1 || request.params.size() > 2)
        throw std::runtime_error(
            RPCHelpMan{"finalizepsbt",
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
            "{\n"
            "  \"psbt\" : \"value\",          (string) The base64-encoded partially signed transaction if not extracted\n"
            "  \"hex\" : \"value\",           (string) The hex-encoded network transaction if extracted\n"
            "  \"complete\" : true|false,   (boolean) If the transaction has a complete set of signatures\n"
            "  ]\n"
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("finalizepsbt", "\"psbt\"")
                },
            }.ToString());

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
        result_str = HexStr(ssTx.str());
        result.pushKV("hex", result_str);
    } else {
        ssTx << psbtx;
        result_str = EncodeBase64(ssTx.str());
        result.pushKV("psbt", result_str);
    }
    result.pushKV("complete", complete);
    return result;
}

UniValue createpsbt(const JSONRPCRequest& request)
{
    if (!g_con_elementsmode)
        throw std::runtime_error("PSBT operations are disabled when not in elementsmode.\n");

    if (request.fHelp || request.params.size() < 2 || request.params.size() > 4)
        throw std::runtime_error(
            RPCHelpMan{"createpsbt",
                "\nCreates a transaction in the Partially Signed Transaction format.\n"
                "Implements the Creator role.\n",
                {
                    {"inputs", RPCArg::Type::ARR, RPCArg::Optional::NO, "A json array of json objects",
                        {
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                                {
                                    {"txid", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The transaction id"},
                                    {"vout", RPCArg::Type::NUM, RPCArg::Optional::NO, "The output number"},
                                    {"sequence", RPCArg::Type::NUM, /* default */ "depends on the value of the 'replaceable' and 'locktime' arguments", "The sequence number"},
                                },
                                },
                        },
                        },
                    {"outputs", RPCArg::Type::ARR, RPCArg::Optional::NO, "a json array with outputs (key-value pairs), where none of the keys are duplicated.\n"
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
                            "  \"psbt\"        (string)  The resulting raw transaction (base64-encoded string)\n"
                },
                RPCExamples{
                    HelpExampleCli("createpsbt", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\" \"[{\\\"data\\\":\\\"00010203\\\"}]\"")
                },
            }.ToString());


    RPCTypeCheck(request.params, {
        UniValue::VARR,
        UniValueType(), // ARR or OBJ, checked later
        UniValue::VNUM,
        UniValue::VBOOL,
        }, true
    );

    bool rbf = false;
    if (!request.params[3].isNull()) {
        rbf = request.params[3].isTrue();
    }
    std::vector<CPubKey> output_pubkeys;
    CMutableTransaction rawTx = ConstructTransaction(request.params[0], request.params[1], request.params[2], rbf, request.params[4], &output_pubkeys);

    // Make a blank psbt
    PartiallySignedTransaction psbtx(rawTx);
    for (unsigned int i = 0; i < rawTx.vout.size(); ++i) {
        psbtx.outputs[i].blinding_pubkey = output_pubkeys[i];
    }

    return EncodePSBT(psbtx);
}

UniValue converttopsbt(const JSONRPCRequest& request)
{
    if (!g_con_elementsmode)
        throw std::runtime_error("PSBT operations are disabled when not in elementsmode.\n");

    const RPCHelpMan help{"converttopsbt",
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
                            "  \"psbt\"        (string)  The resulting raw transaction (base64-encoded string)\n"
                },
                RPCExamples{
                            "\nCreate a transaction\n"
                            + HelpExampleCli("createrawtransaction", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\" \"[{\\\"data\\\":\\\"00010203\\\"}]\"") +
                            "\nConvert the transaction to a PSBT\n"
                            + HelpExampleCli("converttopsbt", "\"rawtransaction\"")
                },
    };

    if (request.fHelp || !help.IsValidNumArgs(request.params.size())) {
        throw std::runtime_error(help.ToString());
    }

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

    return EncodeBase64((unsigned char*)ssTx.data(), ssTx.size());
}

UniValue utxoupdatepsbt(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 1) {
        throw std::runtime_error(
            RPCHelpMan{"utxoupdatepsbt",
            "\nUpdates a PSBT with witness UTXOs retrieved from the UTXO set or the mempool.\n",
            {
                {"psbt", RPCArg::Type::STR, RPCArg::Optional::NO, "A base64 string of a PSBT"}
            },
            RPCResult {
                "  \"psbt\"          (string) The base64-encoded partially signed transaction with inputs updated\n"
            },
            RPCExamples {
                HelpExampleCli("utxoupdatepsbt", "\"psbt\"")
            }}.ToString());
    }

    RPCTypeCheck(request.params, {UniValue::VSTR}, true);

    // Unserialize the transactions
    PartiallySignedTransaction psbtx;
    std::string error;
    if (!DecodeBase64PSBT(psbtx, request.params[0].get_str(), error)) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, strprintf("TX decode failed %s", error));
    }

    // Fetch previous transactions (inputs):
    CCoinsView viewDummy;
    CCoinsViewCache view(&viewDummy);
    {
        LOCK2(cs_main, mempool.cs);
        CCoinsViewCache &viewChain = *pcoinsTip;
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

        std::vector<std::vector<unsigned char>> solutions_data;
        txnouttype which_type = Solver(coin.out.scriptPubKey, solutions_data);
        if (which_type == TX_WITNESS_V0_SCRIPTHASH || which_type == TX_WITNESS_V0_KEYHASH || which_type == TX_WITNESS_UNKNOWN) {
            input.witness_utxo = coin.out;
        }
    }

    CDataStream ssTx(SER_NETWORK, PROTOCOL_VERSION);
    ssTx << psbtx;
    return EncodeBase64((unsigned char*)ssTx.data(), ssTx.size());
}

UniValue joinpsbts(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 1) {
        throw std::runtime_error(
            RPCHelpMan{"joinpsbts",
            "\nJoins multiple distinct PSBTs with different inputs and outputs into one PSBT with inputs and outputs from all of the PSBTs\n"
            "No input in any of the PSBTs can be in more than one of the PSBTs.\n",
            {
                {"txs", RPCArg::Type::ARR, RPCArg::Optional::NO, "A json array of base64 strings of partially signed transactions",
                    {
                        {"psbt", RPCArg::Type::STR, RPCArg::Optional::NO, "A base64 string of a PSBT"}
                    }}
            },
            RPCResult {
                "  \"psbt\"          (string) The base64-encoded partially signed transaction\n"
            },
            RPCExamples {
                HelpExampleCli("joinpsbts", "\"psbt\"")
            }}.ToString());
    }

    RPCTypeCheck(request.params, {UniValue::VARR}, true);

    // Unserialize the transactions
    std::vector<PartiallySignedTransaction> psbtxs;
    UniValue txs = request.params[0].get_array();

    if (txs.size() <= 1) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "At least two PSBTs are required to join PSBTs.");
    }

    int32_t best_version = 1;
    uint32_t best_locktime = 0xffffffff;
    for (unsigned int i = 0; i < txs.size(); ++i) {
        PartiallySignedTransaction psbtx;
        std::string error;
        if (!DecodeBase64PSBT(psbtx, txs[i].get_str(), error)) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR, strprintf("TX decode failed %s", error));
        }
        psbtxs.push_back(psbtx);
        // Choose the highest version number
        if (psbtx.tx->nVersion > best_version) {
            best_version = psbtx.tx->nVersion;
        }
        // Choose the lowest lock time
        if (psbtx.tx->nLockTime < best_locktime) {
            best_locktime = psbtx.tx->nLockTime;
        }
    }

    // Create a blank psbt where everything will be added
    PartiallySignedTransaction merged_psbt;
    merged_psbt.tx = CMutableTransaction();
    merged_psbt.tx->nVersion = best_version;
    merged_psbt.tx->nLockTime = best_locktime;

    // Merge
    for (auto& psbt : psbtxs) {
        for (unsigned int i = 0; i < psbt.tx->vin.size(); ++i) {
            if (!merged_psbt.AddInput(psbt.tx->vin[i], psbt.inputs[i])) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Input %s:%d exists in multiple PSBTs", psbt.tx->vin[i].prevout.hash.ToString().c_str(), psbt.tx->vin[i].prevout.n));
            }
        }
        for (unsigned int i = 0; i < psbt.tx->vout.size(); ++i) {
            merged_psbt.AddOutput(psbt.tx->vout[i], psbt.outputs[i]);
        }
        merged_psbt.unknown.insert(psbt.unknown.begin(), psbt.unknown.end());
    }

    CDataStream ssTx(SER_NETWORK, PROTOCOL_VERSION);
    ssTx << merged_psbt;
    return EncodeBase64((unsigned char*)ssTx.data(), ssTx.size());
}

UniValue analyzepsbt(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 1) {
        throw std::runtime_error(
            RPCHelpMan{"analyzepsbt",
            "\nAnalyzes and provides information about the current status of a PSBT and its inputs\n",
            {
                {"psbt", RPCArg::Type::STR, RPCArg::Optional::NO, "A base64 string of a PSBT"}
            },
            RPCResult {
                "{\n"
                "  \"inputs\" : [                      (array of json objects)\n"
                "    {\n"
                "      \"has_utxo\" : true|false     (boolean) Whether a UTXO is provided\n"
                "      \"is_final\" : true|false     (boolean) Whether the input is finalized\n"
                "      \"missing\" : {               (json object, optional) Things that are missing that are required to complete this input\n"
                "        \"pubkeys\" : [             (array, optional)\n"
                "          \"keyid\"                 (string) Public key ID, hash160 of the public key, of a public key whose BIP 32 derivation path is missing\n"
                "        ]\n"
                "        \"signatures\" : [          (array, optional)\n"
                "          \"keyid\"                 (string) Public key ID, hash160 of the public key, of a public key whose signature is missing\n"
                "        ]\n"
                "        \"redeemscript\" : \"hash\"   (string, optional) Hash160 of the redeemScript that is missing\n"
                "        \"witnessscript\" : \"hash\"  (string, optional) SHA256 of the witnessScript that is missing\n"
                "      }\n"
                "      \"next\" : \"role\"             (string, optional) Role of the next person that this input needs to go to\n"
                "    }\n"
                "    ,...\n"
                "  ]\n"
                "  \"estimated_vsize\" : vsize       (numeric, optional) Estimated vsize of the final signed transaction\n"
                "  \"estimated_feerate\" : feerate   (numeric, optional) Estimated feerate of the final signed transaction in " + CURRENCY_UNIT + "/kB. Shown only if all UTXO slots in the PSBT have been filled.\n"
                "  \"fee\" : fee                     (numeric, optional) The transaction fee paid. Shown only if all UTXO slots in the PSBT have been filled.\n"
                "  \"next\" : \"role\"                 (string) Role of the next person that this psbt needs to go to\n"
                "}\n"
            },
            RPCExamples {
                HelpExampleCli("analyzepsbt", "\"psbt\"")
            }}.ToString());
    }

    RPCTypeCheck(request.params, {UniValue::VSTR});

    // Unserialize the transaction
    PartiallySignedTransaction psbtx;
    std::string error;
    if (!DecodeBase64PSBT(psbtx, request.params[0].get_str(), error)) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, strprintf("TX decode failed %s", error));
    }

    // Go through each input and build status
    UniValue result(UniValue::VOBJ);
    UniValue inputs_result(UniValue::VARR);
    bool calc_fee = true;
    bool all_final = true;
    bool only_missing_sigs = true;
    bool only_missing_final = false;
    CAmountMap in_amts;
    for (unsigned int i = 0; i < psbtx.tx->vin.size(); ++i) {
        PSBTInput& input = psbtx.inputs[i];
        UniValue input_univ(UniValue::VOBJ);
        UniValue missing(UniValue::VOBJ);

        // Check for a UTXO
        CTxOut utxo;
        if (psbtx.GetInputUTXO(utxo, i)) {
            //TODO(gwillen) do PSBT inputs always have explicit assets & amounts?
            in_amts[utxo.nAsset.GetAsset()] += utxo.nValue.GetAmount();
            input_univ.pushKV("has_utxo", true);
        } else {
            input_univ.pushKV("has_utxo", false);
            input_univ.pushKV("is_final", false);
            input_univ.pushKV("next", "updater");
            calc_fee = false;
        }

        // Check if it is final
        if (!utxo.IsNull() && !PSBTInputSigned(input)) {
            input_univ.pushKV("is_final", false);
            all_final = false;

            // Figure out what is missing
            SignatureData outdata;
            bool complete = SignPSBTInput(DUMMY_SIGNING_PROVIDER, psbtx, i, 1, &outdata);

            // Things are missing
            if (!complete) {
                if (!outdata.missing_pubkeys.empty()) {
                    // Missing pubkeys
                    UniValue missing_pubkeys_univ(UniValue::VARR);
                    for (const CKeyID& pubkey : outdata.missing_pubkeys) {
                        missing_pubkeys_univ.push_back(HexStr(pubkey));
                    }
                    missing.pushKV("pubkeys", missing_pubkeys_univ);
                }
                if (!outdata.missing_redeem_script.IsNull()) {
                    // Missing redeemScript
                    missing.pushKV("redeemscript", HexStr(outdata.missing_redeem_script));
                }
                if (!outdata.missing_witness_script.IsNull()) {
                    // Missing witnessScript
                    missing.pushKV("witnessscript", HexStr(outdata.missing_witness_script));
                }
                if (!outdata.missing_sigs.empty()) {
                    // Missing sigs
                    UniValue missing_sigs_univ(UniValue::VARR);
                    for (const CKeyID& pubkey : outdata.missing_sigs) {
                        missing_sigs_univ.push_back(HexStr(pubkey));
                    }
                    missing.pushKV("signatures", missing_sigs_univ);
                }
                input_univ.pushKV("missing", missing);

                // If we are only missing signatures and nothing else, then next is signer
                if (outdata.missing_pubkeys.empty() && outdata.missing_redeem_script.IsNull() && outdata.missing_witness_script.IsNull() && !outdata.missing_sigs.empty()) {
                    input_univ.pushKV("next", "signer");
                } else {
                    only_missing_sigs = false;
                    input_univ.pushKV("next", "updater");
                }
            } else {
                only_missing_final = true;
                input_univ.pushKV("next", "finalizer");
            }
        } else if (!utxo.IsNull()){
            input_univ.pushKV("is_final", true);
        }
        inputs_result.push_back(input_univ);
    }
    result.pushKV("inputs", inputs_result);

    if (all_final) {
        only_missing_sigs = false;
        result.pushKV("next", "extractor");
    }
    if (calc_fee) {
        // Get the output amount
        CAmountMap out_amts = std::accumulate(psbtx.tx->vout.begin(), psbtx.tx->vout.end(), CAmountMap(),
            [](CAmountMap map, const CTxOut& b) {
                map[b.nAsset.GetAsset()] += b.nValue.GetAmount();
                return map;
            }
        );

        // Get the fee
        CAmountMap fee = in_amts - out_amts;

        // Estimate the size
        CMutableTransaction mtx(*psbtx.tx);
        CCoinsView view_dummy;
        CCoinsViewCache view(&view_dummy);
        bool success = true;

        for (unsigned int i = 0; i < psbtx.tx->vin.size(); ++i) {
            PSBTInput& input = psbtx.inputs[i];
            if (SignPSBTInput(DUMMY_SIGNING_PROVIDER, psbtx, i, 1, nullptr, true)) {
                mtx.vin[i].scriptSig = input.final_script_sig;
                mtx.witness.vtxinwit[i].scriptWitness = input.final_script_witness;

                Coin newcoin;
                if (!psbtx.GetInputUTXO(newcoin.out, i)) {
                    success = false;
                    break;
                }
                newcoin.nHeight = 1;
                view.AddCoin(psbtx.tx->vin[i].prevout, std::move(newcoin), true);
            } else {
                success = false;
                break;
            }
        }

        if (success) {
            CTransaction ctx = CTransaction(mtx);
            size_t size = GetVirtualTransactionSize(ctx, GetTransactionSigOpCost(ctx, view, STANDARD_SCRIPT_VERIFY_FLAGS));
            result.pushKV("estimated_vsize", (int)size);
            // Estimate fee rate
            CFeeRate feerate(fee[::policyAsset], size);
            result.pushKV("estimated_feerate", ValueFromAmount(feerate.GetFeePerK()));
        }
        result.pushKV("fee", AmountMapToUniv(fee, ""));

        if (only_missing_sigs) {
            result.pushKV("next", "signer");
        } else if (only_missing_final) {
            result.pushKV("next", "finalizer");
        } else if (all_final) {
            result.pushKV("next", "extractor");
        } else {
            result.pushKV("next", "updater");
        }
    } else {
        result.pushKV("next", "updater");
    }
    return result;
}

//
// ELEMENTS:

UniValue rawblindrawtransaction(const JSONRPCRequest& request)
{
    if (request.fHelp || (request.params.size() < 5 || request.params.size() > 7))
        throw std::runtime_error(
            RPCHelpMan{"rawblindrawtransaction",
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
            "\"transaction\"              (string) hex string of the transaction\n"
                },
                RPCExamples{""},
            }.ToString());

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

    const auto& fedpegscripts = GetValidFedpegScripts(chainActive.Tip(), Params().GetConsensus(), true /* nextblock_validation */);

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
    unsigned int keyIndex = -1;
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
    assert(asset_amount > 0 || token_amount > 0);
    assert(mtx.vout.size() > 0);

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
    assert(mtx.vout.size() > 0);
    assert(asset_amount > 0);
    assert(mtx.vin[issuance_input_index].assetIssuance.IsNull());

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

UniValue rawissueasset(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 2)
        throw std::runtime_error(
            RPCHelpMan{"rawissueasset",
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
            "[                           (json array) Results of issuances, in the order of `issuances` argument\n"
            "  {                           (json object)\n"
            "    \"hex\":<hex>,            (string) The transaction with issuances appended. Only appended to final index in returned array.\n"
            "    \"vin\":\"n\",            (numeric) The input position of the issuance in the transaction.\n"
            "    \"entropy\":\"<entropy>\" (string) Entropy of the asset type.\n"
            "    \"asset\":\"<asset>\",    (string) Asset type for issuance if known.\n"
            "    \"token\":\"<token>\",    (string) Token type for issuance.\n"
            "  },\n"
            "  ...\n"
            "]"
                },
                RPCExamples{""},
            }.ToString());

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
            if (boost::get<CNoDestination>(&asset_dest)) {
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
            if (boost::get<CNoDestination>(&token_dest)) {
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
}

UniValue rawreissueasset(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 2)
        throw std::runtime_error(
            RPCHelpMan{"rawreissueasset",
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
            "{                             (json object)\n"
            "    \"hex\":<hex>,            (string) The transaction with reissuances appended.\n"
            "}\n"
                },
                RPCExamples{""},
            }.ToString());

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
        if (boost::get<CNoDestination>(&asset_dest)) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Invalid asset address provided: %s", asset_address_uni.get_str()));
        }

        size_t input_index = -1;
        const UniValue& input_index_o = issuance_o["input_index"];
        if (input_index_o.isNum()) {
            input_index = input_index_o.get_int();
            if (input_index < 0) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Input index must be non-negative.");
            } else if (input_index >= mtx.vin.size()) {
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
}

// END ELEMENTS
//

// clang-format off
static const CRPCCommand commands[] =
{ //  category              name                            actor (function)            argNames
  //  --------------------- ------------------------        -----------------------     ----------
    { "rawtransactions",    "getrawtransaction",            &getrawtransaction,         {"txid","verbose","blockhash"} },
    { "rawtransactions",    "createrawtransaction",         &createrawtransaction,      {"inputs","outputs","locktime","replaceable", "output_assets"} },
    { "rawtransactions",    "decoderawtransaction",         &decoderawtransaction,      {"hexstring","iswitness"} },
    { "rawtransactions",    "decodescript",                 &decodescript,              {"hexstring"} },
    { "rawtransactions",    "sendrawtransaction",           &sendrawtransaction,        {"hexstring","allowhighfees"} },
    { "rawtransactions",    "combinerawtransaction",        &combinerawtransaction,     {"txs"} },
    { "hidden",             "signrawtransaction",           &signrawtransaction,        {"hexstring","prevtxs","privkeys","sighashtype"} },
    { "rawtransactions",    "signrawtransactionwithkey",    &signrawtransactionwithkey, {"hexstring","privkeys","prevtxs","sighashtype"} },
    { "rawtransactions",    "testmempoolaccept",            &testmempoolaccept,         {"rawtxs","allowhighfees"} },
    { "rawtransactions",    "decodepsbt",                   &decodepsbt,                {"psbt"} },
    { "rawtransactions",    "combinepsbt",                  &combinepsbt,               {"txs"} },
    { "rawtransactions",    "blindpsbt",                    &blindpsbt,                 {"psbt","ignoreblindfail"} },
    { "rawtransactions",    "finalizepsbt",                 &finalizepsbt,              {"psbt", "extract"} },
    { "rawtransactions",    "createpsbt",                   &createpsbt,                {"inputs","outputs","locktime","replaceable"} },
    { "rawtransactions",    "converttopsbt",                &converttopsbt,             {"hexstring","permitsigdata","iswitness"} },
    { "rawtransactions",    "utxoupdatepsbt",               &utxoupdatepsbt,            {"psbt"} },
    { "rawtransactions",    "joinpsbts",                    &joinpsbts,                 {"txs"} },
    { "rawtransactions",    "analyzepsbt",                  &analyzepsbt,               {"psbt"} },

    { "blockchain",         "gettxoutproof",                &gettxoutproof,             {"txids", "blockhash"} },
    { "blockchain",         "verifytxoutproof",             &verifytxoutproof,          {"proof"} },
    { "rawtransactions",    "rawissueasset",                &rawissueasset,             {"transaction", "issuances"}},
    { "rawtransactions",    "rawreissueasset",              &rawreissueasset,           {"transaction", "reissuances"}},
    { "rawtransactions",    "rawblindrawtransaction",       &rawblindrawtransaction,    {"hexstring", "inputblinder", "inputamount", "inputasset", "inputassetblinder", "totalblinder", "ignoreblindfail"} },
};
// clang-format on

void RegisterRawTransactionRPCCommands(CRPCTable &t)
{
    for (unsigned int vcidx = 0; vcidx < ARRAYLEN(commands); vcidx++)
        t.appendCommand(commands[vcidx].name, &commands[vcidx]);
}
