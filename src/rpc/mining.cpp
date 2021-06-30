// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <amount.h>
#include <chain.h>
#include <chainparams.h>
#include <consensus/consensus.h>
#include <consensus/params.h>
#include <consensus/validation.h>
#include <core_io.h>
#include <key_io.h>
#include <miner.h>
#include <net.h>
#include <node/context.h>
#include <policy/fees.h>
#include <policy/policy.h>
#include <pow.h>
#include <rpc/blockchain.h>
#include <rpc/mining.h>
#include <rpc/server.h>
#include <rpc/util.h>
#include <script/descriptor.h>
#include <script/script.h>
#include <script/signingprovider.h>
#include <shutdown.h>
#include <txmempool.h>
#include <univalue.h>
#include <util/fees.h>
#include <util/strencodings.h>
#include <util/string.h>
#include <util/system.h>
#include <util/translation.h>
#include <validation.h>
#include <validationinterface.h>
#include <versionbitsinfo.h>
#include <warnings.h>

#include <block_proof.h> // CheckProof
#include <script/signingprovider.h> // combineblocksigs
#include <script/generic.hpp> // combineblocksigs
#include <blockencodings.h> // getcompactsketch
#include <policy/settings.h> // IsStandardTx

#include <memory>
#include <stdint.h>

/**
 * Return average network hashes per second based on the last 'lookup' blocks,
 * or from the last difficulty change if 'lookup' is nonpositive.
 * If 'height' is nonnegative, compute the estimate at the time when a given block was found.
 */
static UniValue GetNetworkHashPS(int lookup, int height, const CChain& active_chain) {
    const CBlockIndex* pb = active_chain.Tip();

    if (height >= 0 && height < active_chain.Height()) {
        pb = active_chain[height];
    }

    if (pb == nullptr || !pb->nHeight)
        return 0;

    // If lookup is -1, then use blocks since last difficulty change.
    if (lookup <= 0)
        lookup = pb->nHeight % Params().GetConsensus().DifficultyAdjustmentInterval() + 1;

    // If lookup is larger than chain, then set it to chain length.
    if (lookup > pb->nHeight)
        lookup = pb->nHeight;

    const CBlockIndex* pb0 = pb;
    int64_t minTime = pb0->GetBlockTime();
    int64_t maxTime = minTime;
    for (int i = 0; i < lookup; i++) {
        pb0 = pb0->pprev;
        int64_t time = pb0->GetBlockTime();
        minTime = std::min(time, minTime);
        maxTime = std::max(time, maxTime);
    }

    // In case there's a situation where minTime == maxTime, we don't want a divide by zero exception.
    if (minTime == maxTime)
        return 0;

    arith_uint256 workDiff = pb->nChainWork - pb0->nChainWork;
    int64_t timeDiff = maxTime - minTime;

    return workDiff.getdouble() / timeDiff;
}

static RPCHelpMan getnetworkhashps()
{
    return RPCHelpMan{"getnetworkhashps",
                "\nReturns the estimated network hashes per second based on the last n blocks.\n"
                "Pass in [blocks] to override # of blocks, -1 specifies since last difficulty change.\n"
                "Pass in [height] to estimate the network speed at the time when a certain block was found.\n",
                {
                    {"nblocks", RPCArg::Type::NUM, /* default */ "120", "The number of blocks, or -1 for blocks since last difficulty change."},
                    {"height", RPCArg::Type::NUM, /* default */ "-1", "To estimate at the time of the given height."},
                },
                RPCResult{
                    RPCResult::Type::NUM, "", "Hashes per second estimated"},
                RPCExamples{
                    HelpExampleCli("getnetworkhashps", "")
            + HelpExampleRpc("getnetworkhashps", "")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    ChainstateManager& chainman = EnsureAnyChainman(request.context);
    LOCK(cs_main);
    return GetNetworkHashPS(!request.params[0].isNull() ? request.params[0].get_int() : 120, !request.params[1].isNull() ? request.params[1].get_int() : -1, chainman.ActiveChain());
},
    };
}

static bool GenerateBlock(ChainstateManager& chainman, CBlock& block, uint64_t& max_tries, unsigned int& extra_nonce, uint256& block_hash)
{
    block_hash.SetNull();

    {
        LOCK(cs_main);
        CHECK_NONFATAL(std::addressof(::ChainActive()) == std::addressof(chainman.ActiveChain()));
        IncrementExtraNonce(&block, chainman.ActiveChain().Tip(), extra_nonce);
    }

    CChainParams chainparams(Params());

    // Signed blocks have no PoW requirements, but merkle root computed above in
    // IncrementExtraNonce
    if (!g_signed_blocks) {
        while (max_tries > 0 && block.nNonce < std::numeric_limits<uint32_t>::max() && !CheckProofOfWork(block.GetHash(), block.nBits, chainparams.GetConsensus()) && !ShutdownRequested()) {
            ++block.nNonce;
            --max_tries;
        }
        if (max_tries == 0 || ShutdownRequested()) {
            return false;
        }
        if (block.nNonce == std::numeric_limits<uint32_t>::max()) {
            return true;
        }
    }

    // Handle OP_TRUE m_signblockscript case
    CScript op_true(OP_TRUE);
    if (block.m_dynafed_params.m_current.m_signblockscript ==
            GetScriptForDestination(WitnessV0ScriptHash(op_true))) {
        block.m_signblock_witness.stack.push_back(std::vector<unsigned char>(op_true.begin(), op_true.end()));
    } else if (!block.m_dynafed_params.IsNull()) {
        throw JSONRPCError(RPC_MISC_ERROR, "Unable to fill out dynamic federation signblockscript witness, are you sure it's WSH(OP_TRUE)?");
    }

    std::shared_ptr<const CBlock> shared_pblock = std::make_shared<const CBlock>(block);
    if (!chainman.ProcessNewBlock(chainparams, shared_pblock, true, nullptr)) {
        throw JSONRPCError(RPC_INTERNAL_ERROR, "ProcessNewBlock, block not accepted");
    }

    block_hash = block.GetHash();
    return true;
}

static UniValue generateBlocks(ChainstateManager& chainman, const CTxMemPool& mempool, const CScript& coinbase_script, int nGenerate, uint64_t nMaxTries)
{
    int nHeightEnd = 0;
    int nHeight = 0;

    {   // Don't keep cs_main locked
        LOCK(cs_main);
        CHECK_NONFATAL(std::addressof(::ChainActive()) == std::addressof(chainman.ActiveChain()));
        nHeight = chainman.ActiveChain().Height();
        nHeightEnd = nHeight+nGenerate;
    }
    unsigned int nExtraNonce = 0;
    UniValue blockHashes(UniValue::VARR);
    while (nHeight < nHeightEnd && !ShutdownRequested())
    {
        std::unique_ptr<CBlockTemplate> pblocktemplate(BlockAssembler(chainman.ActiveChainstate(), mempool, Params()).CreateNewBlock(coinbase_script));
        if (!pblocktemplate.get())
            throw JSONRPCError(RPC_INTERNAL_ERROR, "Couldn't create new block");
        CBlock *pblock = &pblocktemplate->block;

        uint256 block_hash;
        if (!GenerateBlock(chainman, *pblock, nMaxTries, nExtraNonce, block_hash)) {
            break;
        }

        if (!block_hash.IsNull()) {
            ++nHeight;
            blockHashes.push_back(block_hash.GetHex());
        }
    }
    return blockHashes;
}

static bool getScriptFromDescriptor(const std::string& descriptor, CScript& script, std::string& error)
{
    FlatSigningProvider key_provider;
    const auto desc = Parse(descriptor, key_provider, error, /* require_checksum = */ false);
    if (desc) {
        if (desc->IsRange()) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Ranged descriptor not accepted. Maybe pass through deriveaddresses first?");
        }

        FlatSigningProvider provider;
        std::vector<CScript> scripts;
        if (!desc->Expand(0, key_provider, scripts, provider)) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, strprintf("Cannot derive script without private keys"));
        }

        // Combo descriptors can have 2 or 4 scripts, so we can't just check scripts.size() == 1
        CHECK_NONFATAL(scripts.size() > 0 && scripts.size() <= 4);

        if (scripts.size() == 1) {
            script = scripts.at(0);
        } else if (scripts.size() == 4) {
            // For uncompressed keys, take the 3rd script, since it is p2wpkh
            script = scripts.at(2);
        } else {
            // Else take the 2nd script, since it is p2pkh
            script = scripts.at(1);
        }

        return true;
    } else {
        return false;
    }
}

static RPCHelpMan generatetodescriptor()
{
    return RPCHelpMan{
        "generatetodescriptor",
        "\nMine blocks immediately to a specified descriptor (before the RPC call returns)\n",
        {
            {"num_blocks", RPCArg::Type::NUM, RPCArg::Optional::NO, "How many blocks are generated immediately."},
            {"descriptor", RPCArg::Type::STR, RPCArg::Optional::NO, "The descriptor to send the newly generated bitcoin to."},
            {"maxtries", RPCArg::Type::NUM, /* default */ ToString(DEFAULT_MAX_TRIES), "How many iterations to try."},
        },
        RPCResult{
            RPCResult::Type::ARR, "", "hashes of blocks generated",
            {
                {RPCResult::Type::STR_HEX, "", "blockhash"},
            }
        },
        RPCExamples{
            "\nGenerate 11 blocks to mydesc\n" + HelpExampleCli("generatetodescriptor", "11 \"mydesc\"")},
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    const int num_blocks{request.params[0].get_int()};
    const uint64_t max_tries{request.params[2].isNull() ? DEFAULT_MAX_TRIES : request.params[2].get_int()};

    CScript coinbase_script;
    std::string error;
    if (!getScriptFromDescriptor(request.params[1].get_str(), coinbase_script, error)) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, error);
    }

    NodeContext& node = EnsureAnyNodeContext(request.context);
    const CTxMemPool& mempool = EnsureMemPool(node);
    ChainstateManager& chainman = EnsureChainman(node);

    return generateBlocks(chainman, mempool, coinbase_script, num_blocks, max_tries);
},
    };
}

static RPCHelpMan generate()
{
    return RPCHelpMan{"generate", "has been replaced by the -generate cli option. Refer to -help for more information.", {}, {}, RPCExamples{""}, [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue {
        throw JSONRPCError(RPC_METHOD_NOT_FOUND, self.ToString());
    }};
}

static RPCHelpMan generatetoaddress()
{
    return RPCHelpMan{"generatetoaddress",
                "\nMine blocks immediately to a specified address (before the RPC call returns)\n",
                {
                    {"nblocks", RPCArg::Type::NUM, RPCArg::Optional::NO, "How many blocks are generated immediately."},
                    {"address", RPCArg::Type::STR, RPCArg::Optional::NO, "The address to send the newly generated bitcoin to."},
                    {"maxtries", RPCArg::Type::NUM, /* default */ ToString(DEFAULT_MAX_TRIES), "How many iterations to try."},
                },
                RPCResult{
                    RPCResult::Type::ARR, "", "hashes of blocks generated",
                    {
                        {RPCResult::Type::STR_HEX, "", "blockhash"},
                    }},
                RPCExamples{
            "\nGenerate 11 blocks to myaddress\n"
            + HelpExampleCli("generatetoaddress", "11 \"myaddress\"")
            + "If you are using the " PACKAGE_NAME " wallet, you can get a new address to send the newly generated bitcoin to with:\n"
            + HelpExampleCli("getnewaddress", "")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    const int num_blocks{request.params[0].get_int()};
    const uint64_t max_tries{request.params[2].isNull() ? DEFAULT_MAX_TRIES : request.params[2].get_int()};

    CTxDestination destination = DecodeDestination(request.params[1].get_str());
    if (!IsValidDestination(destination)) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Error: Invalid address");
    }

    NodeContext& node = EnsureAnyNodeContext(request.context);
    const CTxMemPool& mempool = EnsureMemPool(node);
    ChainstateManager& chainman = EnsureChainman(node);

    CScript coinbase_script = GetScriptForDestination(destination);

    return generateBlocks(chainman, mempool, coinbase_script, num_blocks, max_tries);
},
    };
}

static RPCHelpMan generateblock()
{
    return RPCHelpMan{"generateblock",
        "\nMine a block with a set of ordered transactions immediately to a specified address or descriptor (before the RPC call returns)\n",
        {
            {"output", RPCArg::Type::STR, RPCArg::Optional::NO, "The address or descriptor to send the newly generated bitcoin to."},
            {"transactions", RPCArg::Type::ARR, RPCArg::Optional::NO, "An array of hex strings which are either txids or raw transactions.\n"
                "Txids must reference transactions currently in the mempool.\n"
                "All transactions must be valid and in valid order, otherwise the block will be rejected.",
                {
                    {"rawtx/txid", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, ""},
                },
            },
        },
        RPCResult{
            RPCResult::Type::OBJ, "", "",
            {
                {RPCResult::Type::STR_HEX, "hash", "hash of generated block"},
            }
        },
        RPCExamples{
            "\nGenerate a block to myaddress, with txs rawtx and mempool_txid\n"
            + HelpExampleCli("generateblock", R"("myaddress" '["rawtx", "mempool_txid"]')")
        },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    const auto address_or_descriptor = request.params[0].get_str();
    CScript coinbase_script;
    std::string error;

    if (!getScriptFromDescriptor(address_or_descriptor, coinbase_script, error)) {
        const auto destination = DecodeDestination(address_or_descriptor);
        if (!IsValidDestination(destination)) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Error: Invalid address or descriptor");
        }

        coinbase_script = GetScriptForDestination(destination);
    }

    NodeContext& node = EnsureAnyNodeContext(request.context);
    const CTxMemPool& mempool = EnsureMemPool(node);

    std::vector<CTransactionRef> txs;
    const auto raw_txs_or_txids = request.params[1].get_array();
    for (size_t i = 0; i < raw_txs_or_txids.size(); i++) {
        const auto str(raw_txs_or_txids[i].get_str());

        uint256 hash;
        CMutableTransaction mtx;
        if (ParseHashStr(str, hash)) {

            const auto tx = mempool.get(hash);
            if (!tx) {
                throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, strprintf("Transaction %s not in mempool.", str));
            }

            txs.emplace_back(tx);

        } else if (DecodeHexTx(mtx, str)) {
            txs.push_back(MakeTransactionRef(std::move(mtx)));

        } else {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR, strprintf("Transaction decode failed for %s. Make sure the tx has at least one input.", str));
        }
    }

    CChainParams chainparams(Params());
    CBlock block;

    ChainstateManager& chainman = EnsureChainman(node);
    {
        LOCK(cs_main);

        CTxMemPool empty_mempool;
        std::unique_ptr<CBlockTemplate> blocktemplate(BlockAssembler(chainman.ActiveChainstate(), empty_mempool, chainparams).CreateNewBlock(coinbase_script));
        if (!blocktemplate) {
            throw JSONRPCError(RPC_INTERNAL_ERROR, "Couldn't create new block");
        }
        block = blocktemplate->block;
    }

    CHECK_NONFATAL(block.vtx.size() == 1);

    // Add transactions
    block.vtx.insert(block.vtx.end(), txs.begin(), txs.end());
    CBlockIndex* prev_block = WITH_LOCK(::cs_main, return chainman.m_blockman.LookupBlockIndex(block.hashPrevBlock));
    RegenerateCommitments(block, prev_block);

    {
        LOCK(cs_main);

        BlockValidationState state;
        if (!TestBlockValidity(state, chainparams, chainman.ActiveChainstate(), block, chainman.m_blockman.LookupBlockIndex(block.hashPrevBlock), false, false)) {
            throw JSONRPCError(RPC_VERIFY_ERROR, strprintf("TestBlockValidity failed: %s", state.ToString()));
        }
    }

    uint256 block_hash;
    uint64_t max_tries{DEFAULT_MAX_TRIES};
    unsigned int extra_nonce{0};

    if (!GenerateBlock(chainman, block, max_tries, extra_nonce, block_hash) || block_hash.IsNull()) {
        throw JSONRPCError(RPC_MISC_ERROR, "Failed to make block.");
    }

    UniValue obj(UniValue::VOBJ);
    obj.pushKV("hash", block_hash.GetHex());
    return obj;
},
    };
}

static RPCHelpMan getmininginfo()
{
    return RPCHelpMan{"getmininginfo",
                "\nReturns a json object containing mining-related information.",
                {},
                RPCResult{
                    RPCResult::Type::OBJ, "", "",
                    {
                        {RPCResult::Type::NUM, "blocks", "The current block"},
                        {RPCResult::Type::NUM, "currentblockweight", /* optional */ true, "The block weight of the last assembled block (only present if a block was ever assembled)"},
                        {RPCResult::Type::NUM, "currentblocktx", /* optional */ true, "The number of block transactions of the last assembled block (only present if a block was ever assembled)"},
                        {RPCResult::Type::NUM, "difficulty", "The current difficulty"},
                        {RPCResult::Type::NUM, "networkhashps", "The network hashes per second"},
                        {RPCResult::Type::NUM, "pooledtx", "The size of the mempool"},
                        {RPCResult::Type::STR, "chain", "current network name (main, test, signet, regtest)"},
                        {RPCResult::Type::STR, "warnings", "any network and blockchain warnings"},
                    }},
                RPCExamples{
                    HelpExampleCli("getmininginfo", "")
            + HelpExampleRpc("getmininginfo", "")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    NodeContext& node = EnsureAnyNodeContext(request.context);
    const CTxMemPool& mempool = EnsureMemPool(node);
    ChainstateManager& chainman = EnsureChainman(node);
    LOCK(cs_main);
    const CChain& active_chain = chainman.ActiveChain();

    UniValue obj(UniValue::VOBJ);
    obj.pushKV("blocks",           active_chain.Height());
    if (BlockAssembler::m_last_block_weight) obj.pushKV("currentblockweight", *BlockAssembler::m_last_block_weight);
    if (BlockAssembler::m_last_block_num_txs) obj.pushKV("currentblocktx", *BlockAssembler::m_last_block_num_txs);
    if (!g_signed_blocks) {
        obj.pushKV("difficulty",       (double)GetDifficulty(active_chain.Tip()));
        obj.pushKV("networkhashps",    getnetworkhashps().HandleRequest(request));
    }
    obj.pushKV("pooledtx",         (uint64_t)mempool.size());
    obj.pushKV("chain",            Params().NetworkIDString());
    obj.pushKV("warnings",         GetWarnings(false).original);
    return obj;
},
    };
}


// NOTE: Unlike wallet RPC (which use BTC values), mining RPCs follow GBT (BIP 22) in using satoshi amounts
static RPCHelpMan prioritisetransaction()
{
    return RPCHelpMan{"prioritisetransaction",
                "Accepts the transaction into mined blocks at a higher (or lower) priority\n",
                {
                    {"txid", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The transaction id."},
                    {"dummy", RPCArg::Type::NUM, RPCArg::Optional::OMITTED_NAMED_ARG, "API-Compatibility for previous API. Must be zero or null.\n"
            "                  DEPRECATED. For forward compatibility use named arguments and omit this parameter."},
                    {"fee_delta", RPCArg::Type::NUM, RPCArg::Optional::NO, "The fee value (in satoshis) to add (or subtract, if negative).\n"
            "                  Note, that this value is not a fee rate. It is a value to modify absolute fee of the TX.\n"
            "                  The fee is not actually paid, only the algorithm for selecting transactions into a block\n"
            "                  considers the transaction as it would have paid a higher (or lower) fee."},
                },
                RPCResult{
                    RPCResult::Type::BOOL, "", "Returns true"},
                RPCExamples{
                    HelpExampleCli("prioritisetransaction", "\"txid\" 0.0 10000")
            + HelpExampleRpc("prioritisetransaction", "\"txid\", 0.0, 10000")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    LOCK(cs_main);

    uint256 hash(ParseHashV(request.params[0], "txid"));
    CAmount nAmount = request.params[2].get_int64();

    if (!(request.params[1].isNull() || request.params[1].get_real() == 0)) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Priority is no longer supported, dummy argument to prioritisetransaction must be 0.");
    }

    EnsureAnyMemPool(request.context).PrioritiseTransaction(hash, nAmount);
    return true;
},
    };
}


// NOTE: Assumes a conclusive result; if result is inconclusive, it must be handled by caller
static UniValue BIP22ValidationResult(const BlockValidationState& state)
{
    if (state.IsValid())
        return NullUniValue;

    if (state.IsError())
        throw JSONRPCError(RPC_VERIFY_ERROR, state.ToString());
    if (state.IsInvalid())
    {
        std::string strRejectReason = state.GetRejectReason();
        if (strRejectReason.empty())
            return "rejected";
        return strRejectReason;
    }
    // Should be impossible
    return "valid?";
}

static std::string gbt_vb_name(const Consensus::DeploymentPos pos) {
    const struct VBDeploymentInfo& vbinfo = VersionBitsDeploymentInfo[pos];
    std::string s = vbinfo.name;
    if (!vbinfo.gbt_force) {
        s.insert(s.begin(), '!');
    }
    return s;
}

static RPCHelpMan getblocktemplate()
{
    return RPCHelpMan{"getblocktemplate",
        "\nIf the request parameters include a 'mode' key, that is used to explicitly select between the default 'template' request or a 'proposal'.\n"
        "It returns data needed to construct a block to work on.\n"
        "For full specification, see BIPs 22, 23, 9, and 145:\n"
        "    https://github.com/bitcoin/bips/blob/master/bip-0022.mediawiki\n"
        "    https://github.com/bitcoin/bips/blob/master/bip-0023.mediawiki\n"
        "    https://github.com/bitcoin/bips/blob/master/bip-0009.mediawiki#getblocktemplate_changes\n"
        "    https://github.com/bitcoin/bips/blob/master/bip-0145.mediawiki\n",
        {
            {"template_request", RPCArg::Type::OBJ, "{}", "Format of the template",
            {
                {"mode", RPCArg::Type::STR, /* treat as named arg */ RPCArg::Optional::OMITTED_NAMED_ARG, "This must be set to \"template\", \"proposal\" (see BIP 23), or omitted"},
                {"capabilities", RPCArg::Type::ARR, /* treat as named arg */ RPCArg::Optional::OMITTED_NAMED_ARG, "A list of strings",
                {
                    {"str", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "client side supported feature, 'longpoll', 'coinbasevalue', 'proposal', 'serverlist', 'workid'"},
                }},
                {"rules", RPCArg::Type::ARR, RPCArg::Optional::NO, "A list of strings",
                {
                    {"segwit", RPCArg::Type::STR, RPCArg::Optional::NO, "(literal) indicates client side segwit support"},
                    {"str", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "other client side supported softfork deployment"},
                }},
            },
                        "\"template_request\""},
        },
        {
            RPCResult{"If the proposal was accepted with mode=='proposal'", RPCResult::Type::NONE, "", ""},
            RPCResult{"If the proposal was not accepted with mode=='proposal'", RPCResult::Type::STR, "", "According to BIP22"},
            RPCResult{"Otherwise", RPCResult::Type::OBJ, "", "",
            {
                {RPCResult::Type::NUM, "version", "The preferred block version"},
                {RPCResult::Type::ARR, "rules", "specific block rules that are to be enforced",
                {
                    {RPCResult::Type::STR, "", "name of a rule the client must understand to some extent; see BIP 9 for format"},
                }},
                {RPCResult::Type::OBJ_DYN, "vbavailable", "set of pending, supported versionbit (BIP 9) softfork deployments",
                {
                    {RPCResult::Type::NUM, "rulename", "identifies the bit number as indicating acceptance and readiness for the named softfork rule"},
                }},
                {RPCResult::Type::NUM, "vbrequired", "bit mask of versionbits the server requires set in submissions"},
                {RPCResult::Type::STR, "previousblockhash", "The hash of current highest block"},
                {RPCResult::Type::ARR, "transactions", "contents of non-coinbase transactions that should be included in the next block",
                {
                    {RPCResult::Type::OBJ, "", "",
                    {
                        {RPCResult::Type::STR_HEX, "data", "transaction data encoded in hexadecimal (byte-for-byte)"},
                        {RPCResult::Type::STR_HEX, "txid", "transaction id encoded in little-endian hexadecimal"},
                        {RPCResult::Type::STR_HEX, "hash", "hash encoded in little-endian hexadecimal (including witness data)"},
                        {RPCResult::Type::ARR, "depends", "array of numbers",
                        {
                            {RPCResult::Type::NUM, "", "transactions before this one (by 1-based index in 'transactions' list) that must be present in the final block if this one is"},
                        }},
                        {RPCResult::Type::NUM, "fee", "difference in value between transaction inputs and outputs (in satoshis); for coinbase transactions, this is a negative Number of the total collected block fees (ie, not including the block subsidy); if key is not present, fee is unknown and clients MUST NOT assume there isn't one"},
                        {RPCResult::Type::NUM, "sigops", "total SigOps cost, as counted for purposes of block limits; if key is not present, sigop cost is unknown and clients MUST NOT assume it is zero"},
                        {RPCResult::Type::NUM, "weight", "total transaction weight, as counted for purposes of block limits"},
                    }},
                }},
                {RPCResult::Type::OBJ_DYN, "coinbaseaux", "data that should be included in the coinbase's scriptSig content",
                {
                    {RPCResult::Type::STR_HEX, "key", "values must be in the coinbase (keys may be ignored)"},
                }},
                {RPCResult::Type::NUM, "coinbasevalue", "maximum allowable input to coinbase transaction, including the generation award and transaction fees (in satoshis)"},
                {RPCResult::Type::STR, "longpollid", "an id to include with a request to longpoll on an update to this template"},
                {RPCResult::Type::STR, "target", "The hash target"},
                {RPCResult::Type::NUM_TIME, "mintime", "The minimum timestamp appropriate for the next block time, expressed in " + UNIX_EPOCH_TIME},
                {RPCResult::Type::ARR, "mutable", "list of ways the block template may be changed",
                {
                    {RPCResult::Type::STR, "value", "A way the block template may be changed, e.g. 'time', 'transactions', 'prevblock'"},
                }},
                {RPCResult::Type::STR_HEX, "noncerange", "A range of valid nonces"},
                {RPCResult::Type::NUM, "sigoplimit", "limit of sigops in blocks"},
                {RPCResult::Type::NUM, "sizelimit", "limit of block size"},
                {RPCResult::Type::NUM, "weightlimit", "limit of block weight"},
                {RPCResult::Type::NUM_TIME, "curtime", "current timestamp in " + UNIX_EPOCH_TIME},
                {RPCResult::Type::STR, "bits", "compressed target of next block"},
                {RPCResult::Type::NUM, "height", "The height of the next block"},
                {RPCResult::Type::STR, "default_witness_commitment", /* optional */ true, "a valid witness commitment for the unmodified block template"},
            }},
        },
        RPCExamples{
                    HelpExampleCli("getblocktemplate", "'{\"rules\": [\"segwit\"]}'")
            + HelpExampleRpc("getblocktemplate", "{\"rules\": [\"segwit\"]}")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    NodeContext& node = EnsureAnyNodeContext(request.context);
    ChainstateManager& chainman = EnsureChainman(node);
    LOCK(cs_main);

    std::string strMode = "template";
    UniValue lpval = NullUniValue;
    std::set<std::string> setClientRules;
    int64_t nMaxVersionPreVB = -1;
    CChainState& active_chainstate = chainman.ActiveChainstate();
    CChain& active_chain = active_chainstate.m_chain;
    if (!request.params[0].isNull())
    {
        const UniValue& oparam = request.params[0].get_obj();
        const UniValue& modeval = find_value(oparam, "mode");
        if (modeval.isStr())
            strMode = modeval.get_str();
        else if (modeval.isNull())
        {
            /* Do nothing */
        }
        else
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid mode");
        lpval = find_value(oparam, "longpollid");

        if (strMode == "proposal")
        {
            const UniValue& dataval = find_value(oparam, "data");
            if (!dataval.isStr())
                throw JSONRPCError(RPC_TYPE_ERROR, "Missing data String key for proposal");

            CBlock block;
            if (!DecodeHexBlk(block, dataval.get_str()))
                throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Block decode failed");

            uint256 hash = block.GetHash();
            const CBlockIndex* pindex = chainman.m_blockman.LookupBlockIndex(hash);
            if (pindex) {
                if (pindex->IsValid(BLOCK_VALID_SCRIPTS))
                    return "duplicate";
                if (pindex->nStatus & BLOCK_FAILED_MASK)
                    return "duplicate-invalid";
                return "duplicate-inconclusive";
            }

            CBlockIndex* const pindexPrev = active_chain.Tip();
            // TestBlockValidity only supports blocks built on the current Tip
            if (block.hashPrevBlock != pindexPrev->GetBlockHash())
                return "inconclusive-not-best-prevblk";
            BlockValidationState state;
            TestBlockValidity(state, Params(), active_chainstate, block, pindexPrev, false, true);
            return BIP22ValidationResult(state);
        }

        const UniValue& aClientRules = find_value(oparam, "rules");
        if (aClientRules.isArray()) {
            for (unsigned int i = 0; i < aClientRules.size(); ++i) {
                const UniValue& v = aClientRules[i];
                setClientRules.insert(v.get_str());
            }
        } else {
            // NOTE: It is important that this NOT be read if versionbits is supported
            const UniValue& uvMaxVersion = find_value(oparam, "maxversion");
            if (uvMaxVersion.isNum()) {
                nMaxVersionPreVB = uvMaxVersion.get_int64();
            }
        }
    }

    if (strMode != "template")
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid mode");

    if(!node.connman)
        throw JSONRPCError(RPC_CLIENT_P2P_DISABLED, "Error: Peer-to-peer functionality missing or disabled");

    if (!Params().IsTestChain()) {
        if (node.connman->GetNodeCount(ConnectionDirection::Both) == 0) {
            throw JSONRPCError(RPC_CLIENT_NOT_CONNECTED, PACKAGE_NAME " is not connected!");
        }

        if (active_chainstate.IsInitialBlockDownload()) {
            throw JSONRPCError(RPC_CLIENT_IN_INITIAL_DOWNLOAD, PACKAGE_NAME " is in initial sync and waiting for blocks...");
        }
    }

    static unsigned int nTransactionsUpdatedLast;
    const CTxMemPool& mempool = EnsureMemPool(node);

    if (!lpval.isNull())
    {
        // Wait to respond until either the best block changes, OR a minute has passed and there are more transactions
        uint256 hashWatchedChain;
        std::chrono::steady_clock::time_point checktxtime;
        unsigned int nTransactionsUpdatedLastLP;

        if (lpval.isStr())
        {
            // Format: <hashBestChain><nTransactionsUpdatedLast>
            std::string lpstr = lpval.get_str();

            hashWatchedChain = ParseHashV(lpstr.substr(0, 64), "longpollid");
            nTransactionsUpdatedLastLP = atoi64(lpstr.substr(64));
        }
        else
        {
            // NOTE: Spec does not specify behaviour for non-string longpollid, but this makes testing easier
            hashWatchedChain = active_chain.Tip()->GetBlockHash();
            nTransactionsUpdatedLastLP = nTransactionsUpdatedLast;
        }

        // Release lock while waiting
        LEAVE_CRITICAL_SECTION(cs_main);
        {
            checktxtime = std::chrono::steady_clock::now() + std::chrono::minutes(1);

            WAIT_LOCK(g_best_block_mutex, lock);
            while (g_best_block == hashWatchedChain && IsRPCRunning())
            {
                if (g_best_block_cv.wait_until(lock, checktxtime) == std::cv_status::timeout)
                {
                    // Timeout: Check transactions for update
                    // without holding the mempool lock to avoid deadlocks
                    if (mempool.GetTransactionsUpdated() != nTransactionsUpdatedLastLP)
                        break;
                    checktxtime += std::chrono::seconds(10);
                }
            }
        }
        ENTER_CRITICAL_SECTION(cs_main);

        if (!IsRPCRunning())
            throw JSONRPCError(RPC_CLIENT_NOT_CONNECTED, "Shutting down");
        // TODO: Maybe recheck connections/IBD and (if something wrong) send an expires-immediately template to stop miners?
    }

    const Consensus::Params& consensusParams = Params().GetConsensus();

    // GBT must be called with 'signet' set in the rules for signet chains
    if (consensusParams.signet_blocks && setClientRules.count("signet") != 1) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "getblocktemplate must be called with the signet rule set (call with {\"rules\": [\"segwit\", \"signet\"]})");
    }

    // GBT must be called with 'segwit' set in the rules
    if (setClientRules.count("segwit") != 1) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "getblocktemplate must be called with the segwit rule set (call with {\"rules\": [\"segwit\"]})");
    }

    // Update block
    static CBlockIndex* pindexPrev;
    static int64_t nStart;
    static std::unique_ptr<CBlockTemplate> pblocktemplate;
    if (pindexPrev != active_chain.Tip() ||
        (mempool.GetTransactionsUpdated() != nTransactionsUpdatedLast && GetTime() - nStart > 5))
    {
        // Clear pindexPrev so future calls make a new block, despite any failures from here on
        pindexPrev = nullptr;

        // Store the pindexBest used before CreateNewBlock, to avoid races
        nTransactionsUpdatedLast = mempool.GetTransactionsUpdated();
        CBlockIndex* pindexPrevNew = active_chain.Tip();
        nStart = GetTime();

        // Create new block
        CScript scriptDummy = CScript() << OP_TRUE;
        pblocktemplate = BlockAssembler(active_chainstate, mempool, Params()).CreateNewBlock(scriptDummy);
        if (!pblocktemplate)
            throw JSONRPCError(RPC_OUT_OF_MEMORY, "Out of memory");

        // Need to update only after we know CreateNewBlock succeeded
        pindexPrev = pindexPrevNew;
    }
    CHECK_NONFATAL(pindexPrev);
    CBlock* pblock = &pblocktemplate->block; // pointer for convenience

    // Update nTime
    UpdateTime(pblock, consensusParams, pindexPrev);
    pblock->nNonce = 0;

    // NOTE: If at some point we support pre-segwit miners post-segwit-activation, this needs to take segwit support into consideration
    const bool fPreSegWit = (pindexPrev->nHeight + 1 < consensusParams.SegwitHeight);

    UniValue aCaps(UniValue::VARR); aCaps.push_back("proposal");

    UniValue transactions(UniValue::VARR);
    std::map<uint256, int64_t> setTxIndex;
    int i = 0;
    for (const auto& it : pblock->vtx) {
        const CTransaction& tx = *it;
        uint256 txHash = tx.GetHash();
        setTxIndex[txHash] = i++;

        if (tx.IsCoinBase())
            continue;

        UniValue entry(UniValue::VOBJ);

        entry.pushKV("data", EncodeHexTx(tx));
        entry.pushKV("txid", txHash.GetHex());
        entry.pushKV("hash", tx.GetWitnessHash().GetHex());

        UniValue deps(UniValue::VARR);
        for (const CTxIn &in : tx.vin)
        {
            if (setTxIndex.count(in.prevout.hash))
                deps.push_back(setTxIndex[in.prevout.hash]);
        }
        entry.pushKV("depends", deps);

        int index_in_template = i - 1;
        entry.pushKV("fee", pblocktemplate->vTxFees[index_in_template]);
        int64_t nTxSigOps = pblocktemplate->vTxSigOpsCost[index_in_template];
        if (fPreSegWit) {
            CHECK_NONFATAL(nTxSigOps % WITNESS_SCALE_FACTOR == 0);
            nTxSigOps /= WITNESS_SCALE_FACTOR;
        }
        entry.pushKV("sigops", nTxSigOps);
        entry.pushKV("weight", GetTransactionWeight(tx));

        transactions.push_back(entry);
    }

    UniValue aux(UniValue::VOBJ);

    arith_uint256 hashTarget = arith_uint256().SetCompact(pblock->nBits);

    UniValue aMutable(UniValue::VARR);
    aMutable.push_back("time");
    aMutable.push_back("transactions");
    aMutable.push_back("prevblock");

    UniValue result(UniValue::VOBJ);
    result.pushKV("capabilities", aCaps);

    UniValue aRules(UniValue::VARR);
    aRules.push_back("csv");
    if (!fPreSegWit) aRules.push_back("!segwit");
    if (consensusParams.signet_blocks) {
        // indicate to miner that they must understand signet rules
        // when attempting to mine with this template
        aRules.push_back("!signet");
    }

    UniValue vbavailable(UniValue::VOBJ);
    for (int j = 0; j < (int)Consensus::MAX_VERSION_BITS_DEPLOYMENTS; ++j) {
        Consensus::DeploymentPos pos = Consensus::DeploymentPos(j);
        ThresholdState state = VersionBitsState(pindexPrev, consensusParams, pos, versionbitscache);
        switch (state) {
            case ThresholdState::DEFINED:
            case ThresholdState::FAILED:
                // Not exposed to GBT at all
                break;
            case ThresholdState::LOCKED_IN:
                // Ensure bit is set in block version
                pblock->nVersion |= VersionBitsMask(consensusParams, pos);
                // FALL THROUGH to get vbavailable set...
            case ThresholdState::STARTED:
            {
                const struct VBDeploymentInfo& vbinfo = VersionBitsDeploymentInfo[pos];
                vbavailable.pushKV(gbt_vb_name(pos), consensusParams.vDeployments[pos].bit);
                if (setClientRules.find(vbinfo.name) == setClientRules.end()) {
                    if (!vbinfo.gbt_force) {
                        // If the client doesn't support this, don't indicate it in the [default] version
                        pblock->nVersion &= ~VersionBitsMask(consensusParams, pos);
                    }
                }
                break;
            }
            case ThresholdState::ACTIVE:
            {
                // Add to rules only
                const struct VBDeploymentInfo& vbinfo = VersionBitsDeploymentInfo[pos];
                aRules.push_back(gbt_vb_name(pos));
                if (setClientRules.find(vbinfo.name) == setClientRules.end()) {
                    // Not supported by the client; make sure it's safe to proceed
                    if (!vbinfo.gbt_force) {
                        // If we do anything other than throw an exception here, be sure version/force isn't sent to old clients
                        throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Support for '%s' rule requires explicit client support", vbinfo.name));
                    }
                }
                break;
            }
        }
    }
    result.pushKV("version", pblock->nVersion);
    result.pushKV("rules", aRules);
    result.pushKV("vbavailable", vbavailable);
    result.pushKV("vbrequired", int(0));

    if (nMaxVersionPreVB >= 2) {
        // If VB is supported by the client, nMaxVersionPreVB is -1, so we won't get here
        // Because BIP 34 changed how the generation transaction is serialized, we can only use version/force back to v2 blocks
        // This is safe to do [otherwise-]unconditionally only because we are throwing an exception above if a non-force deployment gets activated
        // Note that this can probably also be removed entirely after the first BIP9 non-force deployment (ie, probably segwit) gets activated
        aMutable.push_back("version/force");
    }

    result.pushKV("previousblockhash", pblock->hashPrevBlock.GetHex());
    result.pushKV("transactions", transactions);
    result.pushKV("coinbaseaux", aux);
    result.pushKV("coinbasevalue", (int64_t)pblock->vtx[0]->vout[0].nValue.GetAmount());
    result.pushKV("longpollid", active_chain.Tip()->GetBlockHash().GetHex() + ToString(nTransactionsUpdatedLast));
    result.pushKV("target", hashTarget.GetHex());
    result.pushKV("mintime", (int64_t)pindexPrev->GetMedianTimePast()+1);
    result.pushKV("mutable", aMutable);
    result.pushKV("noncerange", "00000000ffffffff");
    int64_t nSigOpLimit = MAX_BLOCK_SIGOPS_COST;
    int64_t nSizeLimit = MAX_BLOCK_SERIALIZED_SIZE;
    if (fPreSegWit) {
        CHECK_NONFATAL(nSigOpLimit % WITNESS_SCALE_FACTOR == 0);
        nSigOpLimit /= WITNESS_SCALE_FACTOR;
        CHECK_NONFATAL(nSizeLimit % WITNESS_SCALE_FACTOR == 0);
        nSizeLimit /= WITNESS_SCALE_FACTOR;
    }
    result.pushKV("sigoplimit", nSigOpLimit);
    result.pushKV("sizelimit", nSizeLimit);
    if (!fPreSegWit) {
        result.pushKV("weightlimit", (int64_t)MAX_BLOCK_WEIGHT);
    }
    result.pushKV("curtime", pblock->GetBlockTime());
    result.pushKV("bits", strprintf("%08x", pblock->nBits));
    result.pushKV("height", (int64_t)(pindexPrev->nHeight+1));

    if (consensusParams.signet_blocks) {
        result.pushKV("signet_challenge", HexStr(consensusParams.signet_challenge));
    }

    if (!pblocktemplate->vchCoinbaseCommitment.empty()) {
        result.pushKV("default_witness_commitment", HexStr(pblocktemplate->vchCoinbaseCommitment));
    }

    return result;
},
    };
}

class submitblock_StateCatcher final : public CValidationInterface
{
public:
    uint256 hash;
    bool found;
    BlockValidationState state;

    explicit submitblock_StateCatcher(const uint256 &hashIn) : hash(hashIn), found(false), state() {}

protected:
    void BlockChecked(const CBlock& block, const BlockValidationState& stateIn) override {
        if (block.GetHash() != hash)
            return;
        found = true;
        state = stateIn;
    }
};

static RPCHelpMan submitblock()
{
    // We allow 2 arguments for compliance with BIP22. Argument 2 is ignored.
    return RPCHelpMan{"submitblock",
        "\nAttempts to submit new block to network.\n"
        "See https://en.bitcoin.it/wiki/BIP_0022 for full specification.\n",
        {
            {"hexdata", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "the hex-encoded block data to submit"},
            {"dummy", RPCArg::Type::STR, /* default */ "ignored", "dummy value, for compatibility with BIP22. This value is ignored."},
        },
        {
            RPCResult{"If the block was accepted", RPCResult::Type::NONE, "", ""},
            RPCResult{"Otherwise", RPCResult::Type::STR, "", "According to BIP22"},
        },
        RPCExamples{
                    HelpExampleCli("submitblock", "\"mydata\"")
            + HelpExampleRpc("submitblock", "\"mydata\"")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    std::shared_ptr<CBlock> blockptr = std::make_shared<CBlock>();
    CBlock& block = *blockptr;
    if (!DecodeHexBlk(block, request.params[0].get_str())) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Block decode failed");
    }

    if (block.vtx.empty() || !block.vtx[0]->IsCoinBase()) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Block does not start with a coinbase");
    }

    ChainstateManager& chainman = EnsureAnyChainman(request.context);
    uint256 hash = block.GetHash();
    {
        LOCK(cs_main);
        const CBlockIndex* pindex = chainman.m_blockman.LookupBlockIndex(hash);
        if (pindex) {
            if (pindex->IsValid(BLOCK_VALID_SCRIPTS)) {
                return "duplicate";
            }
            if (pindex->nStatus & BLOCK_FAILED_MASK) {
                return "duplicate-invalid";
            }
        }
    }

    {
        LOCK(cs_main);
        const CBlockIndex* pindex = chainman.m_blockman.LookupBlockIndex(block.hashPrevBlock);
        if (pindex) {
            UpdateUncommittedBlockStructures(block, pindex, Params().GetConsensus());
        }
    }

    bool new_block;
    auto sc = std::make_shared<submitblock_StateCatcher>(block.GetHash());
    RegisterSharedValidationInterface(sc);
    bool accepted = chainman.ProcessNewBlock(Params(), blockptr, /* fForceProcessing */ true, /* fNewBlock */ &new_block);
    UnregisterSharedValidationInterface(sc);
    if (!new_block && accepted) {
        return "duplicate";
    }
    if (!sc->found) {
        return "inconclusive";
    }
    return BIP22ValidationResult(sc->state);
},
    };
}

static RPCHelpMan submitheader()
{
    return RPCHelpMan{"submitheader",
                "\nDecode the given hexdata as a header and submit it as a candidate chain tip if valid."
                "\nThrows when the header is invalid.\n",
                {
                    {"hexdata", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "the hex-encoded block header data"},
                },
                RPCResult{
                    RPCResult::Type::NONE, "", "None"},
                RPCExamples{
                    HelpExampleCli("submitheader", "\"aabbcc\"") +
                    HelpExampleRpc("submitheader", "\"aabbcc\"")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    CBlockHeader h;
    if (!DecodeHexBlockHeader(h, request.params[0].get_str())) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Block header decode failed");
    }
    ChainstateManager& chainman = EnsureAnyChainman(request.context);
    {
        LOCK(cs_main);
        if (!chainman.m_blockman.LookupBlockIndex(h.hashPrevBlock)) {
            throw JSONRPCError(RPC_VERIFY_ERROR, "Must submit previous header (" + h.hashPrevBlock.GetHex() + ") first");
        }
    }

    BlockValidationState state;
    chainman.ProcessNewBlockHeaders({h}, state, Params());
    if (state.IsValid()) return NullUniValue;
    if (state.IsError()) {
        throw JSONRPCError(RPC_VERIFY_ERROR, state.ToString());
    }
    throw JSONRPCError(RPC_VERIFY_ERROR, state.GetRejectReason());
},
    };
}

static RPCHelpMan estimatesmartfee()
{
    return RPCHelpMan{"estimatesmartfee",
        "\nEstimates the approximate fee per kilobyte needed for a transaction to begin\n"
        "confirmation within conf_target blocks if possible and return the number of blocks\n"
        "for which the estimate is valid. Uses virtual transaction size as defined\n"
        "in BIP 141 (witness data is discounted).\n",
        {
            {"conf_target", RPCArg::Type::NUM, RPCArg::Optional::NO, "Confirmation target in blocks (1 - 1008)"},
            {"estimate_mode", RPCArg::Type::STR, /* default */ "conservative", "The fee estimate mode.\n"
            "                   Whether to return a more conservative estimate which also satisfies\n"
            "                   a longer history. A conservative estimate potentially returns a\n"
            "                   higher feerate and is more likely to be sufficient for the desired\n"
            "                   target, but is not as responsive to short term drops in the\n"
            "                   prevailing fee market. Must be one of (case insensitive):\n"
             "\"" + FeeModes("\"\n\"") + "\""},
                },
                RPCResult{
                    RPCResult::Type::OBJ, "", "",
                    {
                        {RPCResult::Type::NUM, "feerate", /* optional */ true, "estimate fee rate in " + CURRENCY_UNIT + "/kB (only present if no errors were encountered)"},
                        {RPCResult::Type::ARR, "errors", /* optional */ true, "Errors encountered during processing (if there are any)",
                            {
                                {RPCResult::Type::STR, "", "error"},
                            }},
                        {RPCResult::Type::NUM, "blocks", "block number where estimate was found\n"
            "The request target will be clamped between 2 and the highest target\n"
            "fee estimation is able to return based on how long it has been running.\n"
            "An error is returned if not enough transactions and blocks\n"
            "have been observed to make an estimate for any number of blocks."},
                    }},
                RPCExamples{
                    HelpExampleCli("estimatesmartfee", "6")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    RPCTypeCheck(request.params, {UniValue::VNUM, UniValue::VSTR});
    RPCTypeCheckArgument(request.params[0], UniValue::VNUM);

    CBlockPolicyEstimator& fee_estimator = EnsureAnyFeeEstimator(request.context);

    unsigned int max_target = fee_estimator.HighestTargetTracked(FeeEstimateHorizon::LONG_HALFLIFE);
    unsigned int conf_target = ParseConfirmTarget(request.params[0], max_target);
    bool conservative = true;
    if (!request.params[1].isNull()) {
        FeeEstimateMode fee_mode;
        if (!FeeModeFromString(request.params[1].get_str(), fee_mode)) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, InvalidEstimateModeErrorMessage());
        }
        if (fee_mode == FeeEstimateMode::ECONOMICAL) conservative = false;
    }

    UniValue result(UniValue::VOBJ);
    UniValue errors(UniValue::VARR);
    FeeCalculation feeCalc;
    CFeeRate feeRate = fee_estimator.estimateSmartFee(conf_target, &feeCalc, conservative);
    if (feeRate != CFeeRate(0)) {
        result.pushKV("feerate", ValueFromAmount(feeRate.GetFeePerK()));
    } else {
        errors.push_back("Insufficient data or no feerate found");
        result.pushKV("errors", errors);
    }
    result.pushKV("blocks", feeCalc.returnedTarget);
    return result;
},
    };
}

static RPCHelpMan estimaterawfee()
{
    return RPCHelpMan{"estimaterawfee",
                "\nWARNING: This interface is unstable and may disappear or change!\n"
                "\nWARNING: This is an advanced API call that is tightly coupled to the specific\n"
                "         implementation of fee estimation. The parameters it can be called with\n"
                "         and the results it returns will change if the internal implementation changes.\n"
                "\nEstimates the approximate fee per kilobyte needed for a transaction to begin\n"
                "confirmation within conf_target blocks if possible. Uses virtual transaction size as\n"
                "defined in BIP 141 (witness data is discounted).\n",
                {
                    {"conf_target", RPCArg::Type::NUM, RPCArg::Optional::NO, "Confirmation target in blocks (1 - 1008)"},
                    {"threshold", RPCArg::Type::NUM, /* default */ "0.95", "The proportion of transactions in a given feerate range that must have been\n"
            "               confirmed within conf_target in order to consider those feerates as high enough and proceed to check\n"
            "               lower buckets."},
                },
                RPCResult{
                    RPCResult::Type::OBJ, "", "Results are returned for any horizon which tracks blocks up to the confirmation target",
                    {
                        {RPCResult::Type::OBJ, "short", /* optional */ true, "estimate for short time horizon",
                            {
                                {RPCResult::Type::NUM, "feerate", /* optional */ true, "estimate fee rate in " + CURRENCY_UNIT + "/kB"},
                                {RPCResult::Type::NUM, "decay", "exponential decay (per block) for historical moving average of confirmation data"},
                                {RPCResult::Type::NUM, "scale", "The resolution of confirmation targets at this time horizon"},
                                {RPCResult::Type::OBJ, "pass", /* optional */ true, "information about the lowest range of feerates to succeed in meeting the threshold",
                                {
                                        {RPCResult::Type::NUM, "startrange", "start of feerate range"},
                                        {RPCResult::Type::NUM, "endrange", "end of feerate range"},
                                        {RPCResult::Type::NUM, "withintarget", "number of txs over history horizon in the feerate range that were confirmed within target"},
                                        {RPCResult::Type::NUM, "totalconfirmed", "number of txs over history horizon in the feerate range that were confirmed at any point"},
                                        {RPCResult::Type::NUM, "inmempool", "current number of txs in mempool in the feerate range unconfirmed for at least target blocks"},
                                        {RPCResult::Type::NUM, "leftmempool", "number of txs over history horizon in the feerate range that left mempool unconfirmed after target"},
                                }},
                                {RPCResult::Type::OBJ, "fail", /* optional */ true, "information about the highest range of feerates to fail to meet the threshold",
                                {
                                    {RPCResult::Type::ELISION, "", ""},
                                }},
                                {RPCResult::Type::ARR, "errors", /* optional */ true, "Errors encountered during processing (if there are any)",
                                {
                                    {RPCResult::Type::STR, "error", ""},
                                }},
                        }},
                        {RPCResult::Type::OBJ, "medium", /* optional */ true, "estimate for medium time horizon",
                        {
                            {RPCResult::Type::ELISION, "", ""},
                        }},
                        {RPCResult::Type::OBJ, "long", /* optional */ true, "estimate for long time horizon",
                        {
                            {RPCResult::Type::ELISION, "", ""},
                        }},
                    }},
                RPCExamples{
                    HelpExampleCli("estimaterawfee", "6 0.9")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    RPCTypeCheck(request.params, {UniValue::VNUM, UniValue::VNUM}, true);
    RPCTypeCheckArgument(request.params[0], UniValue::VNUM);

    CBlockPolicyEstimator& fee_estimator = EnsureAnyFeeEstimator(request.context);

    unsigned int max_target = fee_estimator.HighestTargetTracked(FeeEstimateHorizon::LONG_HALFLIFE);
    unsigned int conf_target = ParseConfirmTarget(request.params[0], max_target);
    double threshold = 0.95;
    if (!request.params[1].isNull()) {
        threshold = request.params[1].get_real();
    }
    if (threshold < 0 || threshold > 1) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid threshold");
    }

    UniValue result(UniValue::VOBJ);

    for (const FeeEstimateHorizon horizon : ALL_FEE_ESTIMATE_HORIZONS) {
        CFeeRate feeRate;
        EstimationResult buckets;

        // Only output results for horizons which track the target
        if (conf_target > fee_estimator.HighestTargetTracked(horizon)) continue;

        feeRate = fee_estimator.estimateRawFee(conf_target, threshold, horizon, &buckets);
        UniValue horizon_result(UniValue::VOBJ);
        UniValue errors(UniValue::VARR);
        UniValue passbucket(UniValue::VOBJ);
        passbucket.pushKV("startrange", round(buckets.pass.start));
        passbucket.pushKV("endrange", round(buckets.pass.end));
        passbucket.pushKV("withintarget", round(buckets.pass.withinTarget * 100.0) / 100.0);
        passbucket.pushKV("totalconfirmed", round(buckets.pass.totalConfirmed * 100.0) / 100.0);
        passbucket.pushKV("inmempool", round(buckets.pass.inMempool * 100.0) / 100.0);
        passbucket.pushKV("leftmempool", round(buckets.pass.leftMempool * 100.0) / 100.0);
        UniValue failbucket(UniValue::VOBJ);
        failbucket.pushKV("startrange", round(buckets.fail.start));
        failbucket.pushKV("endrange", round(buckets.fail.end));
        failbucket.pushKV("withintarget", round(buckets.fail.withinTarget * 100.0) / 100.0);
        failbucket.pushKV("totalconfirmed", round(buckets.fail.totalConfirmed * 100.0) / 100.0);
        failbucket.pushKV("inmempool", round(buckets.fail.inMempool * 100.0) / 100.0);
        failbucket.pushKV("leftmempool", round(buckets.fail.leftMempool * 100.0) / 100.0);

        // CFeeRate(0) is used to indicate error as a return value from estimateRawFee
        if (feeRate != CFeeRate(0)) {
            horizon_result.pushKV("feerate", ValueFromAmount(feeRate.GetFeePerK()));
            horizon_result.pushKV("decay", buckets.decay);
            horizon_result.pushKV("scale", (int)buckets.scale);
            horizon_result.pushKV("pass", passbucket);
            // buckets.fail.start == -1 indicates that all buckets passed, there is no fail bucket to output
            if (buckets.fail.start != -1) horizon_result.pushKV("fail", failbucket);
        } else {
            // Output only information that is still meaningful in the event of error
            horizon_result.pushKV("decay", buckets.decay);
            horizon_result.pushKV("scale", (int)buckets.scale);
            horizon_result.pushKV("fail", failbucket);
            errors.push_back("Insufficient data or no feerate found which meets threshold");
            horizon_result.pushKV("errors",errors);
        }
        result.pushKV(StringForFeeEstimateHorizon(horizon), horizon_result);
    }
    return result;
},
    };
}

//
// ELEMENTS:

static RPCHelpMan getnewblockhex()
{
    return RPCHelpMan{"getnewblockhex",
                "\nGets hex representation of a proposed, unmined new block\n",
                {
                    {"min_tx_age", RPCArg::Type::NUM, /* default */ "0", "How many seconds a transaction must have been in the mempool to be inluded in the block proposal. This may help with faster block convergence among functionaries using compact blocks."},
                    {"proposed_parameters", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED , "Parameters to be used in dynamic federations blocks as proposals. During a period of `-dynamic_epoch_length` blocks, 4/5 of total blocks must signal these parameters for the proposal to become activated in the next epoch.",
                        {
                            {"signblockscript", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "Hex-encoded block signing script to propose"},
                            {"max_block_witness", RPCArg::Type::NUM, RPCArg::Optional::NO, "Total size in witness bytes that are allowed in the dynamic federations block witness for blocksigning"},
                            {"fedpegscript", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "Hex-encoded fedpegscript for dynamic block proposal. This is interpreted as a v0 segwit witnessScript, and fills out the fedpeg_program as such."},
                            {"extension_space", RPCArg::Type::ARR, RPCArg::Optional::NO, "Array of additional fields to embed in the dynamic blockheader. Has no consensus meaning aside from serialized size changes. This space is currently is only used for PAK enforcement.",
                                {
                                    {"", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "Hex encoded string for extension entries."},
                                },
                            },
                        },
                        "proposed_parameters"},
                        {"commit_data", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED_NAMED_ARG, "Data in hex to be committed to in an additional coinbase output."},
                },
                RPCResult{
                    RPCResult::Type::STR_HEX, "blockhex", "the block hex",
                },
                RPCExamples{
                    HelpExampleCli("getnewblockhex", ""),
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    int required_wait = !request.params[0].isNull() ? request.params[0].get_int() : 0;
    if (required_wait < 0) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "min_tx_age must be non-negative.");
    }

    // Construct proposed parameter entry, if any
    DynaFedParamEntry proposed;
    if (!request.params[1].isNull()) {
        if (!IsDynaFedEnabled(::ChainActive().Tip(), Params().GetConsensus())) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Dynamic federations is not active on this network. Proposed parameters are not needed.");
        }

        UniValue prop = request.params[1].get_obj();

        std::string sbs_str = prop["signblockscript"].get_str();
        if (!IsHex(sbs_str)) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "signblockscript must be hex");
        }
        std::vector<unsigned char> signblock_bytes = ParseHex(sbs_str);
        proposed.m_signblockscript = CScript(signblock_bytes.begin(), signblock_bytes.end());

        int max_sbs_wit = prop["max_block_witness"].get_int();
        if (max_sbs_wit < 0) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "max_block_witness must be non-negative");
        }
        proposed.m_signblock_witness_limit = max_sbs_wit;

        std::string fps_str = prop["fedpegscript"].get_str();
        if (!IsHex(fps_str)) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "fedpegscript must be hex");
        }
        std::vector<unsigned char> fedpeg_bytes = ParseHex(fps_str);
        proposed.m_fedpegscript = CScript(fedpeg_bytes.begin(), fedpeg_bytes.end());
        // Compute the P2WSH scriptPubKey of this fedpegscript
        proposed.m_fedpeg_program = GetScriptForDestination(WitnessV0ScriptHash(proposed.m_fedpegscript));

        UniValue extension_array = prop["extension_space"].get_array();
        for (unsigned int i = 0; i < extension_array.size(); i++) {
            std::string extension_str = extension_array[i].get_str();
            proposed.m_extension_space.push_back(ParseHex(extension_str));
        }
        // All proposals are full serializations
        proposed.m_serialize_type = 2;
    }

    // Any commitment required for non-consensus reasons.
    // This will be placed in the first coinbase output.
    CScript data_commitment;
    if (!request.params[2].isNull()) {
        std::vector<unsigned char> data_bytes = ParseHex(request.params[2].get_str());
        data_commitment = CScript() << OP_RETURN << data_bytes;
    }

    CScript feeDestinationScript = Params().GetConsensus().mandatory_coinbase_destination;
    if (feeDestinationScript == CScript()) feeDestinationScript = CScript() << OP_TRUE;
    const NodeContext& node = EnsureAnyNodeContext(request.context);
    std::unique_ptr<CBlockTemplate> pblocktemplate(BlockAssembler(::ChainstateActive(), *node.mempool, Params()).CreateNewBlock(feeDestinationScript, std::chrono::seconds(required_wait), &proposed, data_commitment.empty() ? nullptr : &data_commitment));
    if (!pblocktemplate.get()) {
        throw JSONRPCError(RPC_INTERNAL_ERROR, "Wallet keypool empty");
    }

    {
        // IncrementExtraNonce sets coinbase flags and builds merkle tree
        LOCK(cs_main);
        unsigned int nExtraNonce = 0;
        IncrementExtraNonce(&pblocktemplate->block, ::ChainActive().Tip(), nExtraNonce);
    }

    // If WSH(OP_TRUE) block, fill in witness
    CScript op_true(OP_TRUE);
    if (pblocktemplate->block.m_dynafed_params.m_current.m_signblockscript ==
            GetScriptForDestination(WitnessV0ScriptHash(op_true))) {
        pblocktemplate->block.m_signblock_witness.stack.push_back(std::vector<unsigned char>(op_true.begin(), op_true.end()));
    }

    CDataStream ssBlock(SER_NETWORK, PROTOCOL_VERSION);
    ssBlock << pblocktemplate->block;
    return HexStr(ssBlock);
},
    };
}

static RPCHelpMan combineblocksigs()
{
    return RPCHelpMan{"combineblocksigs",
                "\nMerges signatures on a block proposal\n",
                {
                    {"blockhex", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The hex-encoded block from getnewblockhex"},
                    {"signatures", RPCArg::Type::ARR, RPCArg::Optional::NO, "A json array of pubkey/signature pairs",
                        {
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                                {
                                    {"pubkey", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The pubkey for the signature in hex"},
                                    {"sig", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "A signature (in the form of a hex-encoded scriptSig)"},
                                },
                            },
                        },
                    },
                    {"witnessScript", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The hex-encoded witnessScript for the signblockscript"},
                },
                RPCResult{
                    RPCResult::Type::OBJ, "", "",
                    {
                        {RPCResult::Type::STR_HEX, "hex", "the signed block"},
                        {RPCResult::Type::BOOL, "complete", "whether the block is complete"},
                    }
                },
                RPCExamples{
                    HelpExampleCli("combineblocksigs", "<hex> '[{\"pubkey\":\"hex\",\"sig\":\"hex\"}, ...]'"),
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    if (!g_signed_blocks) {
        throw JSONRPCError(RPC_MISC_ERROR, "Signed blocks are not active for this network.");
    }

    CBlock block;
    if (!DecodeHexBlk(block, request.params[0].get_str()))
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Block decode failed");

    bool is_dynafed = !block.m_dynafed_params.IsNull();

    const Consensus::Params& params = Params().GetConsensus();
    const UniValue& sigs = request.params[1].get_array();
    FillableSigningProvider keystore;
    SignatureData sig_data;
    SimpleSignatureCreator signature_creator(block.GetHash(), is_dynafed ? SIGHASH_ALL : 0);
    for (unsigned int i = 0; i < sigs.size(); i++) {
        UniValue pubkey_sig = sigs[i];
        const std::string& pubkey_str = pubkey_sig["pubkey"].get_str();
        const std::string& sig_str = pubkey_sig["sig"].get_str();
        if (!IsHex(sig_str) || !IsHex(pubkey_str)) {
            continue;
        }
        std::vector<unsigned char> pubkey_bytes = ParseHex(pubkey_str);
        std::vector<unsigned char> sig_bytes = ParseHex(sig_str);
        CPubKey pubkey(pubkey_bytes.begin(), pubkey_bytes.end());
        if (!pubkey.IsFullyValid()) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Bad pubkey");
        }
        sig_data.signatures[pubkey.GetID()] = std::make_pair(pubkey, sig_bytes);
    }

    if (is_dynafed) {
        if (request.params[2].isNull()) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Signing dynamic blocks requires the witnessScript argument");
        }
        std::vector<unsigned char> witness_bytes(ParseHex(request.params[2].get_str()));
        if (!witness_bytes.empty()) {
            keystore.AddCScript(CScript(witness_bytes.begin(), witness_bytes.end()));
        }
        // Finalizes the signatures, has no access to keys
        ProduceSignature(keystore, signature_creator, block.m_dynafed_params.m_current.m_signblockscript, sig_data, SCRIPT_VERIFY_NONE);
        block.m_signblock_witness = sig_data.scriptWitness;
    } else {
        // Finalizes the signatures, has no access to keys
        ProduceSignature(keystore, signature_creator, block.proof.challenge, sig_data, SCRIPT_NO_SIGHASH_BYTE);
        block.proof.solution = sig_data.scriptSig;
    }

    CDataStream ssBlock(SER_NETWORK, PROTOCOL_VERSION | RPCSerializationFlags());
    ssBlock << block;
    UniValue result(UniValue::VOBJ);
    result.pushKV("hex", HexStr(ssBlock));
    result.pushKV("complete", CheckProof(block, params));
    return result;
},
    };
}

static RPCHelpMan getcompactsketch()
{
    return RPCHelpMan{"getcompactsketch",
                "\nGets hex representation of a proposed compact block sketch.\n"
                "It is consumed by `consumecompactsketch.`\n",
                {
                    {"block_hex", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "Hex serialized block proposal from `getnewblockhex`."},
                },
                RPCResult{
                    RPCResult::Type::STR, "sketch", "serialized block sketch",
                },
                RPCExamples{
                    HelpExampleCli("getcompactsketch", ""),
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    CBlock block;
    std::vector<unsigned char> block_bytes(ParseHex(request.params[0].get_str()));
    CDataStream ssBlock(block_bytes, SER_NETWORK, PROTOCOL_VERSION);
    ssBlock >> block;

    CBlockHeaderAndShortTxIDs cmpctblock(block, true);

    CDataStream ssCompactBlock(SER_NETWORK, PROTOCOL_VERSION);
    ssCompactBlock << cmpctblock;
    return HexStr(ssCompactBlock);
},
    };
}

static RPCHelpMan consumecompactsketch()
{
    return RPCHelpMan{"consumecompactsketch",
                "\nTakes hex representation of a proposed compact block sketch and fills it in\n"
                "using mempool. Returns the block if complete, and a list\n"
                "of missing transaction indices serialized as a native structure."
                "NOTE: The latest instance of this call will have a partially filled block\n"
                "cached in memory to be used in `consumegetblocktxn` to finalize the block.\n",
                {
                    {"sketch", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "Hex string of compact block sketch."},
                },
                RPCResult{
                    RPCResult::Type::OBJ, "", "",
                    {
                        {RPCResult::Type::STR_HEX, "blockhex", "The filled block hex. Only returns when block is final"},
                        {RPCResult::Type::STR_HEX, "block_tx_req", "The serialized structure of missing transaction indices, given to serving node"},
                        {RPCResult::Type::STR_HEX, "found_tranasctions", "The serialized list of found transactions to be used in finalizecompactblock"},
                    },
                },
                RPCExamples{
                    HelpExampleCli("consumecompactsketch", "<sketch>"),
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    UniValue ret(UniValue::VOBJ);

    std::vector<unsigned char> compact_block_bytes(ParseHex(request.params[0].get_str()));
    CDataStream ssBlock(compact_block_bytes, SER_NETWORK, PROTOCOL_VERSION);
    CBlockHeaderAndShortTxIDs cmpctblock;
    ssBlock >> cmpctblock;

    const NodeContext& node = EnsureAnyNodeContext(request.context);
    LOCK(node.mempool->cs);
    PartiallyDownloadedBlock partialBlock(node.mempool.get());
    const std::vector<std::pair<uint256, CTransactionRef>> dummy;
    ReadStatus status = partialBlock.InitData(cmpctblock, dummy);
    if (status != READ_STATUS_OK) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Compact block decode failed");
    }

    BlockTransactionsRequest req;
    std::vector<CTransactionRef> found(partialBlock.GetAvailableTx());
    for (size_t i = 0; i < cmpctblock.BlockTxCount(); i++) {
        if (!partialBlock.IsTxAvailable(i)) {
            req.indexes.push_back(i);
        }
    }

    CDataStream ssReq(SER_NETWORK, PROTOCOL_VERSION);
    ssReq << req;

    if (req.indexes.empty()) {
        std::shared_ptr<CBlock> pblock = std::make_shared<CBlock>();
        std::vector<CTransactionRef> dummy;
        ReadStatus status = partialBlock.FillBlock(*pblock, dummy, false /* don't get pow */);
        if (status == READ_STATUS_INVALID) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Bogus crap sketch.");
        } else if (status == READ_STATUS_FAILED) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Failed to complete block though all transactions were apparently found. Could be random short ID collision; requires full block instead.");
        } else if (status == READ_STATUS_CHECKBLOCK_FAILED) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Checkblock failed.");
        }
        CDataStream ssBlock(SER_NETWORK, PROTOCOL_VERSION);
        ssBlock << *pblock;

        ret.pushKV("blockhex", HexStr(ssBlock));
    } else {
        // Serialize the list of transactions we found
        CDataStream ssFound(SER_NETWORK, PROTOCOL_VERSION);
        ssFound << found;

        ret.pushKV("block_tx_req", HexStr(ssReq));
        ret.pushKV("found_transactions", HexStr(ssFound));
    }
    return ret;
},
    };
}

static RPCHelpMan consumegetblocktxn()
{
    return RPCHelpMan{"consumegetblocktxn",
                "Consumes a transaction request for a compact block sketch.",
                {
                    {"full_block", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "Hex serialied block that corresponds to the block request `block_tx_req`."},
                    {"block_tx_req", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "Hex serialied BlockTransactionsRequest, aka getblocktxn network message."},
                },
                RPCResult{
                    RPCResult::Type::STR_HEX, "block_transactions", "The serialized list of found transactions aka BlockTransactions",
                },
                RPCExamples{
                    HelpExampleCli("consumegetblocktxn", "<block_tx_req>")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    CBlock block;
    std::vector<unsigned char> block_bytes(ParseHex(request.params[0].get_str()));
    CDataStream ssBlock(block_bytes, SER_NETWORK, PROTOCOL_VERSION);
    ssBlock >> block;

    // Take in BlockTransactionsRequest, return BlockTransactions
    std::vector<unsigned char> block_req(ParseHex(request.params[1].get_str()));
    CDataStream ssReq(block_req, SER_NETWORK, PROTOCOL_VERSION);

    BlockTransactionsRequest req;
    ssReq >> req;

    BlockTransactions resp(req);
    for (size_t i = 0; i < req.indexes.size(); i++) {
        if (req.indexes[i] >= block.vtx.size()) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Peer sent us a getblocktxn with out-of-bounds tx indices");
        }
        resp.txn[i] = block.vtx[req.indexes[i]];
    }

    CDataStream ssResp(SER_NETWORK, PROTOCOL_VERSION);
    ssResp << resp;

    return HexStr(ssResp);
},
    };
}

static RPCHelpMan finalizecompactblock()
{
    return RPCHelpMan{"finalizecompactblock",
                "Takes the two transaction lists, fills out the compact block and attempts to finalize it.",
                {
                    {"compact_hex", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "Hex serialized compact block."},
                    {"block_transactions", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "Hex serialized BlockTransactions, the response to getblocktxn."},
                    {"found_transactions", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "Hex serialized list of transactions that were found in response to receiving a compact sketch in `consumecompactsketch`."},
                },
                RPCResult{
                    RPCResult::Type::STR_HEX, "block", "The serialized final block",
                },
                RPCExamples{
                    HelpExampleCli("finalizecompactblock", "<compact_hex> <block_transactions> <found_transactions>")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    // Compact block
    std::vector<unsigned char> compact_block_bytes(ParseHex(request.params[0].get_str()));
    CDataStream ssCompactBlock(compact_block_bytes, SER_NETWORK, PROTOCOL_VERSION);
    CBlockHeaderAndShortTxIDs cmpctblock;
    ssCompactBlock >> cmpctblock;

    // BlockTransactions from the server
    std::vector<unsigned char> block_tx(ParseHex(request.params[1].get_str()));
    CDataStream ssResp(block_tx, SER_NETWORK, PROTOCOL_VERSION);

    BlockTransactions transactions;
    ssResp >> transactions;

    // Cached transactions
    std::vector<unsigned char> found_tx(ParseHex(request.params[2].get_str()));
    CDataStream ssFound(found_tx, SER_NETWORK, PROTOCOL_VERSION);

    std::vector<CTransactionRef> found;
    ssFound >> found;

    // Make mega-list
    found.insert(found.end(), transactions.txn.begin(), transactions.txn.end());

    // Now construct the final block! (use dummy mempool here, otherwise reconstruction may fail)
    CTxMemPool dummy_pool;
    PartiallyDownloadedBlock partialBlock(&dummy_pool);

    // "Extra" list is really our combined list that will be put into place using InitData
    std::vector<std::pair<uint256, CTransactionRef>> extra_txn;
    for (const auto& found_tx : found) {
        extra_txn.push_back(std::make_pair(found_tx->GetWitnessHash(), found_tx));
    }
    std::shared_ptr<CBlock> pblock = std::make_shared<CBlock>();
    if (partialBlock.InitData(cmpctblock, extra_txn) != READ_STATUS_OK) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "compact_hex appears malformed.");
    }
    const std::vector<CTransactionRef> dummy_missing;
    auto result = partialBlock.FillBlock(*pblock, dummy_missing, false /* pow_check*/);
    if (result == READ_STATUS_FAILED) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Failed to complete block though all transactions were apparently found. Could be random short ID collision; requires full block instead.");
    } else if (result != READ_STATUS_OK) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Failed to complete block though all transactions were apparently found.");
    }

    CDataStream ssBlock(SER_NETWORK, PROTOCOL_VERSION);
    ssBlock << *pblock;

    return HexStr(ssBlock);
},
    };
}

static RPCHelpMan testproposedblock()
{
    return RPCHelpMan{"testproposedblock",
                "\nChecks a block proposal for validity, and that it extends chaintip\n",
                {
                    {"blockhex", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The hex-encoded block from getnewblockhex"},
                    {"acceptnonstd", RPCArg::Type::BOOL, RPCArg::Optional::OMITTED_NAMED_ARG, "If set false, returns error if block contains non-standard transaction. Default is set via `-acceptnonstdtxn`. If PAK enforcement is set, block commitment mismatches with configuration PAK lists are rejected as well."},
                },
                RPCResult{RPCResult::Type::NONE, "", ""},
                RPCExamples{
                    HelpExampleCli("testproposedblock", "<hex>")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    CBlock block;
    if (!DecodeHexBlk(block, request.params[0].get_str()))
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Block decode failed");

    ChainstateManager& chainman = EnsureAnyChainman(request.context);
    LOCK(cs_main);

    uint256 hash = block.GetHash();
    BlockMap::iterator mi = chainman.BlockIndex().find(hash);
    if (mi != chainman.BlockIndex().end())
        throw JSONRPCError(RPC_VERIFY_ERROR, "already have block");

    CBlockIndex* const pindexPrev = ::ChainActive().Tip();
    // TestBlockValidity only supports blocks built on the current Tip
    if (block.hashPrevBlock != pindexPrev->GetBlockHash())
        throw JSONRPCError(RPC_VERIFY_ERROR, "proposal was not based on our best chain");

    BlockValidationState state;
    if (!TestBlockValidity(state, Params(), ::ChainstateActive(), block, pindexPrev, false, true) || !state.IsValid()) {
        std::string strRejectReason = state.GetRejectReason();
        if (strRejectReason.empty())
            throw JSONRPCError(RPC_VERIFY_ERROR, state.IsInvalid() ? "Block proposal was invalid" : "Error checking block proposal");
        throw JSONRPCError(RPC_VERIFY_ERROR, strRejectReason);
    }

    const CChainParams& chainparams = Params();
    const bool acceptnonstd = !request.params[1].isNull() ? request.params[1].get_bool() : gArgs.GetBoolArg("-acceptnonstdtxn", !chainparams.RequireStandard());
    if (!acceptnonstd) {
        for (auto& transaction : block.vtx) {
            if (transaction->IsCoinBase()) continue;
            std::string reason;
            if (!IsStandardTx(*transaction, reason)) {
                throw JSONRPCError(RPC_VERIFY_ERROR, "Block proposal included a non-standard transaction: " + reason);
            }
        }
    }

    return NullUniValue;
},
    };
}

// END ELEMENTS
//

void RegisterMiningRPCCommands(CRPCTable &t)
{
// clang-format off

static const CRPCCommand commands[] =
{ //  category              actor (function)
  //  --------------------- ------------------------
    { "mining",             &getnetworkhashps,         },
    { "mining",             &getmininginfo,            },
    { "mining",             &prioritisetransaction,    },
    { "mining",             &getblocktemplate,         },
    { "generating",         &combineblocksigs,         },
    { "mining",             &submitheader,             },
    { "generating",         &getnewblockhex,           },
    { "generating",         &getcompactsketch,         },
    { "generating",         &consumecompactsketch,     },
    { "generating",         &consumegetblocktxn,       },
    { "generating",         &finalizecompactblock,     },
    { "mining",             &testproposedblock,        },

    { "mining",             &submitblock,              },

    { "generating",          &generatetoaddress,       },
    { "generating",          &generatetodescriptor,    },
    { "generating",          &generateblock,           },

    { "util",                &estimatesmartfee,        },

    { "hidden",              &estimaterawfee,          },
    { "hidden",              &generate,                },
};
// clang-format on
    for (const auto& c : commands) {
        t.appendCommand(c.name, &c);
    }
}
