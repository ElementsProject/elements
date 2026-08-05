// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-present The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <bitcoin-build-config.h> // IWYU pragma: keep

#include <chain.h>
#include <chainparams.h>
#include <chainparamsbase.h>
#include <common/system.h>
#include <consensus/amount.h>
#include <consensus/consensus.h>
#include <consensus/merkle.h>
#include <consensus/params.h>
#include <consensus/validation.h>
#include <core_io.h>
#include <deploymentinfo.h>
#include <deploymentstatus.h>
#include <interfaces/mining.h>
#include <key_io.h>
#include <net.h>
#include <node/context.h>
#include <node/mempool_args.h>
#include <node/miner.h>
#include <policy/policy.h>
#include <node/warnings.h>
#include <policy/ephemeral_policy.h>
#include <pow.h>
#include <random.h>
#include <rpc/blockchain.h>
#include <rpc/mining.h>
#include <rpc/server.h>
#include <rpc/server_util.h>
#include <rpc/util.h>
#include <script/descriptor.h>
#include <script/script.h>
#include <script/signingprovider.h>
#include <txmempool.h>
#include <univalue.h>
#include <util/signalinterrupt.h>
#include <util/strencodings.h>
#include <util/string.h>
#include <util/time.h>
#include <util/translation.h>
#include <validation.h>
#include <validationinterface.h>

#include <block_proof.h> // CheckProof
#include <script/signingprovider.h> // combineblocksigs
#include <script/generic.hpp> // combineblocksigs
#include <blockencodings.h> // getcompactsketch
#include <policy/settings.h> // IsStandardTx

#include <memory>
#include <stdint.h>

using interfaces::BlockTemplate;
using interfaces::Mining;
using node::BlockAssembler;
using node::CBlockTemplate;
using node::GetMinimumTime;
using node::NodeContext;
using node::RegenerateCommitments;
using node::UpdateTime;
using util::ToString;

/**
 * Return average network hashes per second based on the last 'lookup' blocks,
 * or from the last difficulty change if 'lookup' is -1.
 * If 'height' is -1, compute the estimate from current chain tip.
 * If 'height' is a valid block height, compute the estimate at the time when a given block was found.
 */
static UniValue GetNetworkHashPS(int lookup, int height, const CChain& active_chain) {
    if (lookup < -1 || lookup == 0) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid nblocks. Must be a positive number or -1.");
    }

    if (height < -1 || height > active_chain.Height()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Block does not exist at specified height");
    }

    const CBlockIndex* pb = active_chain.Tip();

    if (height >= 0) {
        pb = active_chain[height];
    }

    if (pb == nullptr || !pb->nHeight)
        return 0;

    // If lookup is -1, then use blocks since last difficulty change.
    if (lookup == -1)
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
                    {"nblocks", RPCArg::Type::NUM, RPCArg::Default{120}, "The number of previous blocks to calculate estimate from, or -1 for blocks since last difficulty change."},
                    {"height", RPCArg::Type::NUM, RPCArg::Default{-1}, "To estimate at the time of the given height."},
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
    return GetNetworkHashPS(self.Arg<int>("nblocks"), self.Arg<int>("height"), chainman.ActiveChain());
},
    };
}

static bool GenerateBlock(ChainstateManager& chainman, CBlock&& block, uint64_t& max_tries, std::shared_ptr<const CBlock>& block_out, bool process_new_block)
{
    block_out.reset();
    block.hashMerkleRoot = BlockMerkleRoot(block);

    // Signed blocks have no PoW requirements, but merkle root computed above
    if (!g_signed_blocks) {
        while (max_tries > 0 && block.nNonce < std::numeric_limits<uint32_t>::max() && !CheckProofOfWork(block.GetHash(), block.nBits, chainman.GetConsensus()) && !chainman.m_interrupt) {
            ++block.nNonce;
            --max_tries;
        }
        if (max_tries == 0 || chainman.m_interrupt) {
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
        block.m_signblock_witness.stack.emplace_back(op_true.begin(), op_true.end());
    } else if (!block.m_dynafed_params.IsNull()) {
        throw JSONRPCError(RPC_MISC_ERROR, "Unable to fill out dynamic federation signblockscript witness, are you sure it's WSH(OP_TRUE)?");
    }

    block_out = std::make_shared<const CBlock>(std::move(block));

    if (!process_new_block) return true;

    if (!chainman.ProcessNewBlock(block_out, /*force_processing=*/true, /*min_pow_checked=*/true, nullptr)) {
        throw JSONRPCError(RPC_INTERNAL_ERROR, "ProcessNewBlock, block not accepted");
    }

    return true;
}

static UniValue generateBlocks(ChainstateManager& chainman, Mining& miner, const CScript& coinbase_output_script, int nGenerate, uint64_t nMaxTries)
{
    UniValue blockHashes(UniValue::VARR);
    while (nGenerate > 0 && !chainman.m_interrupt) {
        std::unique_ptr<BlockTemplate> block_template(miner.createNewBlock({ .coinbase_output_script = coinbase_output_script }));
        CHECK_NONFATAL(block_template);

        std::shared_ptr<const CBlock> block_out;
        if (!GenerateBlock(chainman, block_template->getBlock(), nMaxTries, block_out, /*process_new_block=*/true)) {
            break;
        }

        if (block_out) {
            --nGenerate;
            blockHashes.push_back(block_out->GetHash().GetHex());
        }
    }
    return blockHashes;
}

static bool getScriptFromDescriptor(const std::string& descriptor, CScript& script, std::string& error)
{
    FlatSigningProvider key_provider;
    const auto descs = Parse(descriptor, key_provider, error, /* require_checksum = */ false);
    if (descs.empty()) return false;
    if (descs.size() > 1) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Multipath descriptor not accepted");
    }
    const auto& desc = descs.at(0);
    if (desc->IsRange()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Ranged descriptor not accepted. Maybe pass through deriveaddresses first?");
    }

    FlatSigningProvider provider;
    std::vector<CScript> scripts;
    if (!desc->Expand(0, key_provider, scripts, provider)) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Cannot derive script without private keys");
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
}

static RPCHelpMan generatetodescriptor()
{
    return RPCHelpMan{
        "generatetodescriptor",
        "Mine to a specified descriptor and return the block hashes.",
        {
            {"num_blocks", RPCArg::Type::NUM, RPCArg::Optional::NO, "How many blocks are generated."},
            {"descriptor", RPCArg::Type::STR, RPCArg::Optional::NO, "The descriptor to send the newly generated bitcoin to."},
            {"maxtries", RPCArg::Type::NUM, RPCArg::Default{DEFAULT_MAX_TRIES}, "How many iterations to try."},
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
    const auto num_blocks{self.Arg<int>("num_blocks")};
    const auto max_tries{self.Arg<uint64_t>("maxtries")};

    CScript coinbase_output_script;
    std::string error;
    if (!getScriptFromDescriptor(self.Arg<std::string>("descriptor"), coinbase_output_script, error)) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, error);
    }

    NodeContext& node = EnsureAnyNodeContext(request.context);
    Mining& miner = EnsureMining(node);
    ChainstateManager& chainman = EnsureChainman(node);

    return generateBlocks(chainman, miner, coinbase_output_script, num_blocks, max_tries);
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
        "Mine to a specified address and return the block hashes.",
         {
             {"nblocks", RPCArg::Type::NUM, RPCArg::Optional::NO, "How many blocks are generated."},
             {"address", RPCArg::Type::STR, RPCArg::Optional::NO, "The address to send the newly generated bitcoin to."},
             {"maxtries", RPCArg::Type::NUM, RPCArg::Default{DEFAULT_MAX_TRIES}, "How many iterations to try."},
         },
         RPCResult{
             RPCResult::Type::ARR, "", "hashes of blocks generated",
             {
                 {RPCResult::Type::STR_HEX, "", "blockhash"},
             }},
         RPCExamples{
            "\nGenerate 11 blocks to myaddress\n"
            + HelpExampleCli("generatetoaddress", "11 \"myaddress\"")
            + "If you are using the " CLIENT_NAME " wallet, you can get a new address to send the newly generated bitcoin to with:\n"
            + HelpExampleCli("getnewaddress", "")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    const int num_blocks{request.params[0].getInt<int>()};
    const uint64_t max_tries{request.params[2].isNull() ? DEFAULT_MAX_TRIES : request.params[2].getInt<int>()};

    CTxDestination destination = DecodeDestination(request.params[1].get_str());
    if (!IsValidDestination(destination)) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Error: Invalid address");
    }

    NodeContext& node = EnsureAnyNodeContext(request.context);
    Mining& miner = EnsureMining(node);
    ChainstateManager& chainman = EnsureChainman(node);

    CScript coinbase_output_script = GetScriptForDestination(destination);

    return generateBlocks(chainman, miner, coinbase_output_script, num_blocks, max_tries);
},
    };
}

static RPCHelpMan generateblock()
{
    return RPCHelpMan{"generateblock",
        "Mine a set of ordered transactions to a specified address or descriptor and return the block hash.",
        {
            {"output", RPCArg::Type::STR, RPCArg::Optional::NO, "The address or descriptor to send the newly generated bitcoin to."},
            {"transactions", RPCArg::Type::ARR, RPCArg::Optional::NO, "An array of hex strings which are either txids or raw transactions.\n"
                "Txids must reference transactions currently in the mempool.\n"
                "All transactions must be valid and in valid order, otherwise the block will be rejected.",
                {
                    {"rawtx/txid", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, ""},
                },
            },
            {"submit", RPCArg::Type::BOOL, RPCArg::Default{true}, "Whether to submit the block before the RPC call returns or to return it as hex."},
        },
        RPCResult{
            RPCResult::Type::OBJ, "", "",
            {
                {RPCResult::Type::STR_HEX, "hash", "hash of generated block"},
                {RPCResult::Type::STR_HEX, "hex", /*optional=*/true, "hex of generated block, only present when submit=false"},
            }
        },
        RPCExamples{
            "\nGenerate a block to myaddress, with txs rawtx and mempool_txid\n"
            + HelpExampleCli("generateblock", R"("myaddress" '["rawtx", "mempool_txid"]')")
        },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    const auto address_or_descriptor = request.params[0].get_str();
    CScript coinbase_output_script;
    std::string error;

    if (!getScriptFromDescriptor(address_or_descriptor, coinbase_output_script, error)) {
        const auto destination = DecodeDestination(address_or_descriptor);
        if (!IsValidDestination(destination)) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Error: Invalid address or descriptor");
        }

        coinbase_output_script = GetScriptForDestination(destination);
    }

    NodeContext& node = EnsureAnyNodeContext(request.context);
    Mining& miner = EnsureMining(node);
    const CTxMemPool& mempool = EnsureMemPool(node);

    std::vector<CTransactionRef> txs;
    const auto raw_txs_or_txids = request.params[1].get_array();
    for (size_t i = 0; i < raw_txs_or_txids.size(); i++) {
        const auto& str{raw_txs_or_txids[i].get_str()};

        CMutableTransaction mtx;
        if (auto hash{uint256::FromHex(str)}) {
            const auto tx{mempool.get(*hash)};
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

    const bool process_new_block{request.params[2].isNull() ? true : request.params[2].get_bool()};
    CBlock block;

    ChainstateManager& chainman = EnsureChainman(node);
    {
        LOCK(chainman.GetMutex());
        {
            std::unique_ptr<BlockTemplate> block_template{miner.createNewBlock({.use_mempool = false, .coinbase_output_script = coinbase_output_script})};
            CHECK_NONFATAL(block_template);

            block = block_template->getBlock();
        }

        CHECK_NONFATAL(block.vtx.size() == 1);

        // Add transactions
        block.vtx.insert(block.vtx.end(), txs.begin(), txs.end());
        RegenerateCommitments(block, chainman);

        BlockValidationState state;
        if (!TestBlockValidity(state, chainman.GetParams(), chainman.ActiveChainstate(), block, chainman.m_blockman.LookupBlockIndex(block.hashPrevBlock), /*fCheckPOW=*/false, /*fCheckMerkleRoot=*/false)) {
            throw JSONRPCError(RPC_VERIFY_ERROR, strprintf("TestBlockValidity failed: %s", state.ToString()));
        }
    }

    std::shared_ptr<const CBlock> block_out;
    uint64_t max_tries{DEFAULT_MAX_TRIES};

    if (!GenerateBlock(chainman, std::move(block), max_tries, block_out, process_new_block) || !block_out) {
        throw JSONRPCError(RPC_MISC_ERROR, "Failed to make block.");
    }

    UniValue obj(UniValue::VOBJ);
    obj.pushKV("hash", block_out->GetHash().GetHex());
    if (!process_new_block) {
        DataStream block_ser;
        block_ser << TX_WITH_WITNESS(*block_out);
        obj.pushKV("hex", HexStr(block_ser));
    }
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
                        {RPCResult::Type::NUM, "currentblockweight", /*optional=*/true, "The block weight (including reserved weight for block header, txs count and coinbase tx) of the last assembled block (only present if a block was ever assembled)"},
                        {RPCResult::Type::NUM, "currentblocktx", /*optional=*/true, "The number of block transactions (excluding coinbase) of the last assembled block (only present if a block was ever assembled)"},
                        {RPCResult::Type::STR_HEX, "bits", /*optional=*/true, "The current nBits, compact representation of the block difficulty target"},
                        {RPCResult::Type::NUM, "difficulty", /*optional=*/true, "The current difficulty"},
                        {RPCResult::Type::STR_HEX, "target", /*optional=*/true, "The current target"},
                        {RPCResult::Type::NUM, "networkhashps", /*optional=*/true, "The network hashes per second"},
                        {RPCResult::Type::NUM, "pooledtx", "The size of the mempool"},
                        {RPCResult::Type::STR, "chain", "current network name (" LIST_CHAIN_NAMES ")"},
                        {RPCResult::Type::OBJ, "next", /*optional=*/true, "The next block",
                        {
                            {RPCResult::Type::NUM, "height", "The next height"},
                            {RPCResult::Type::STR_HEX, "bits", "The next target nBits"},
                            {RPCResult::Type::NUM, "difficulty", "The next difficulty"},
                            {RPCResult::Type::STR_HEX, "target", "The next target"}
                        }},
                        {RPCResult::Type::STR_HEX, "signet_challenge", /*optional=*/true, "The block challenge (aka. block script), in hexadecimal (only present if the current network is a signet)"},
                        (IsDeprecatedRPCEnabled("warnings") ?
                            RPCResult{RPCResult::Type::STR, "warnings", "any network and blockchain warnings (DEPRECATED)"} :
                            RPCResult{RPCResult::Type::ARR, "warnings", "any network and blockchain warnings (run with `-deprecatedrpc=warnings` to return the latest warning as a single string)",
                            {
                                {RPCResult::Type::STR, "", "warning"},
                            }
                            }
                        ),
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
    CBlockIndex& tip{*CHECK_NONFATAL(active_chain.Tip())};

    UniValue obj(UniValue::VOBJ);
    obj.pushKV("blocks",           active_chain.Height());
    if (BlockAssembler::m_last_block_weight) obj.pushKV("currentblockweight", *BlockAssembler::m_last_block_weight);
    if (BlockAssembler::m_last_block_num_txs) obj.pushKV("currentblocktx", *BlockAssembler::m_last_block_num_txs);
    if (!g_signed_blocks) {
    obj.pushKV("bits", strprintf("%08x", tip.nBits));
    obj.pushKV("difficulty", GetDifficulty(*CHECK_NONFATAL(active_chain.Tip())));
    obj.pushKV("target", GetTarget(tip, chainman.GetConsensus().powLimit).GetHex());
    obj.pushKV("networkhashps",    getnetworkhashps().HandleRequest(request));
    }
    obj.pushKV("pooledtx",         (uint64_t)mempool.size());
    obj.pushKV("chain", chainman.GetParams().GetChainTypeString());

    if (!g_signed_blocks) {
    UniValue next(UniValue::VOBJ);
    CBlockIndex next_index;
    NextEmptyBlockIndex(tip, chainman.GetConsensus(), next_index);

    next.pushKV("height", next_index.nHeight);
    next.pushKV("bits", strprintf("%08x", next_index.nBits));
    next.pushKV("difficulty", GetDifficulty(next_index));
    next.pushKV("target", GetTarget(next_index, chainman.GetConsensus().powLimit).GetHex());
    obj.pushKV("next", next);
    }

    if (chainman.GetParams().GetChainTypeMeta().chain_type == ChainType::SIGNET) {
        const std::vector<uint8_t>& signet_challenge =
            chainman.GetConsensus().signet_challenge;
        obj.pushKV("signet_challenge", HexStr(signet_challenge));
    }
    obj.pushKV("warnings", node::GetWarningsForRpc(*CHECK_NONFATAL(node.warnings), IsDeprecatedRPCEnabled("warnings")));
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
                    {"dummy", RPCArg::Type::NUM, RPCArg::Optional::OMITTED, "API-Compatibility for previous API. Must be zero or null.\n"
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
    const auto dummy{self.MaybeArg<double>("dummy")};
    CAmount nAmount = request.params[2].getInt<int64_t>();

    if (dummy && *dummy != 0) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Priority is no longer supported, dummy argument to prioritisetransaction must be 0.");
    }

    CTxMemPool& mempool = EnsureAnyMemPool(request.context);

    // Non-0 fee dust transactions are not allowed for entry, and modification not allowed afterwards
    const auto& tx = mempool.get(hash);
    if (mempool.m_opts.require_standard && tx && !GetDust(*tx, mempool.m_opts.dust_relay_feerate).empty()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Priority is not supported for transactions with dust outputs.");
    }

    mempool.PrioritiseTransaction(hash, nAmount);
    return true;
},
    };
}

static RPCHelpMan getprioritisedtransactions()
{
    return RPCHelpMan{"getprioritisedtransactions",
        "Returns a map of all user-created (see prioritisetransaction) fee deltas by txid, and whether the tx is present in mempool.",
        {},
        RPCResult{
            RPCResult::Type::OBJ_DYN, "", "prioritisation keyed by txid",
            {
                {RPCResult::Type::OBJ, "<transactionid>", "", {
                    {RPCResult::Type::NUM, "fee_delta", "transaction fee delta in satoshis"},
                    {RPCResult::Type::BOOL, "in_mempool", "whether this transaction is currently in mempool"},
                    {RPCResult::Type::NUM, "modified_fee", /*optional=*/true, "modified fee in satoshis. Only returned if in_mempool=true"},
                }}
            },
        },
        RPCExamples{
            HelpExampleCli("getprioritisedtransactions", "")
            + HelpExampleRpc("getprioritisedtransactions", "")
        },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
        {
            NodeContext& node = EnsureAnyNodeContext(request.context);
            CTxMemPool& mempool = EnsureMemPool(node);
            UniValue rpc_result{UniValue::VOBJ};
            for (const auto& delta_info : mempool.GetPrioritisedTransactions()) {
                UniValue result_inner{UniValue::VOBJ};
                result_inner.pushKV("fee_delta", delta_info.delta);
                result_inner.pushKV("in_mempool", delta_info.in_mempool);
                if (delta_info.in_mempool) {
                    result_inner.pushKV("modified_fee", *delta_info.modified_fee);
                }
                rpc_result.pushKV(delta_info.txid.GetHex(), std::move(result_inner));
            }
            return rpc_result;
        },
    };
}


// NOTE: Assumes a conclusive result; if result is inconclusive, it must be handled by caller
static UniValue BIP22ValidationResult(const BlockValidationState& state)
{
    if (state.IsValid())
        return UniValue::VNULL;

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
            {"template_request", RPCArg::Type::OBJ, RPCArg::Optional::NO, "Format of the template",
            {
                {"mode", RPCArg::Type::STR, /* treat as named arg */ RPCArg::Optional::OMITTED, "This must be set to \"template\", \"proposal\" (see BIP 23), or omitted"},
                {"capabilities", RPCArg::Type::ARR, /* treat as named arg */ RPCArg::Optional::OMITTED, "A list of strings",
                {
                    {"str", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "client side supported feature, 'longpoll', 'coinbasevalue', 'proposal', 'serverlist', 'workid'"},
                }},
                {"rules", RPCArg::Type::ARR, RPCArg::Optional::NO, "A list of strings",
                {
                    {"segwit", RPCArg::Type::STR, RPCArg::Optional::NO, "(literal) indicates client side segwit support"},
                    {"str", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "other client side supported softfork deployment"},
                }},
                {"longpollid", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "delay processing request until the result would vary significantly from the \"longpollid\" of a prior template"},
                {"data", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "proposed block data to check, encoded in hexadecimal; valid only for mode=\"proposal\""},
            },
            },
        },
        {
            RPCResult{"If the proposal was accepted with mode=='proposal'", RPCResult::Type::NONE, "", ""},
            RPCResult{"If the proposal was not accepted with mode=='proposal'", RPCResult::Type::STR, "", "According to BIP22"},
            RPCResult{"Otherwise", RPCResult::Type::OBJ, "", "",
            {
                {RPCResult::Type::ARR, "capabilities", "",
                {
                    {RPCResult::Type::STR, "value", "A supported feature, for example 'proposal'"},
                }},
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
                        {RPCResult::Type::STR_HEX, "txid", "transaction hash excluding witness data, shown in byte-reversed hex"},
                        {RPCResult::Type::STR_HEX, "hash", "transaction hash including witness data, shown in byte-reversed hex"},
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
                {RPCResult::Type::NUM_TIME, "mintime", "The minimum timestamp appropriate for the next block time, expressed in " + UNIX_EPOCH_TIME + ". Adjusted for the proposed BIP94 timewarp rule."},
                {RPCResult::Type::ARR, "mutable", "list of ways the block template may be changed",
                {
                    {RPCResult::Type::STR, "value", "A way the block template may be changed, e.g. 'time', 'transactions', 'prevblock'"},
                }},
                {RPCResult::Type::STR_HEX, "noncerange", "A range of valid nonces"},
                {RPCResult::Type::NUM, "sigoplimit", "limit of sigops in blocks"},
                {RPCResult::Type::NUM, "sizelimit", "limit of block size"},
                {RPCResult::Type::NUM, "weightlimit", /*optional=*/true, "limit of block weight"},
                {RPCResult::Type::NUM_TIME, "curtime", "current timestamp in " + UNIX_EPOCH_TIME + ". Adjusted for the proposed BIP94 timewarp rule."},
                {RPCResult::Type::STR, "bits", "compressed target of next block"},
                {RPCResult::Type::NUM, "height", "The height of the next block"},
                {RPCResult::Type::STR_HEX, "signet_challenge", /*optional=*/true, "Only on signet"},
                {RPCResult::Type::STR_HEX, "default_witness_commitment", /*optional=*/true, "a valid witness commitment for the unmodified block template"},
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
    Mining& miner = EnsureMining(node);
    LOCK(cs_main);
    uint256 tip{CHECK_NONFATAL(miner.getTip()).value().hash};

    std::string strMode = "template";
    UniValue lpval = NullUniValue;
    std::set<std::string> setClientRules;
    if (!request.params[0].isNull())
    {
        const UniValue& oparam = request.params[0].get_obj();
        const UniValue& modeval = oparam.find_value("mode");
        if (modeval.isStr())
            strMode = modeval.get_str();
        else if (modeval.isNull())
        {
            /* Do nothing */
        }
        else
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid mode");
        lpval = oparam.find_value("longpollid");

        if (strMode == "proposal")
        {
            const UniValue& dataval = oparam.find_value("data");
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

            // TestBlockValidity only supports blocks built on the current Tip
            if (block.hashPrevBlock != tip) {
                return "inconclusive-not-best-prevblk";
            }
            BlockValidationState state;
            TestBlockValidity(state, chainman.GetParams(), chainman.ActiveChainstate(), block, chainman.m_blockman.LookupBlockIndex(block.hashPrevBlock), /*fCheckPOW=*/false, /*fCheckMerkleRoot=*/true);
            return BIP22ValidationResult(state);
        }

        const UniValue& aClientRules = oparam.find_value("rules");
        if (aClientRules.isArray()) {
            for (unsigned int i = 0; i < aClientRules.size(); ++i) {
                const UniValue& v = aClientRules[i];
                setClientRules.insert(v.get_str());
            }
        }
    }

    if (strMode != "template")
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid mode");

    if (!miner.isTestChain()) {
        const CConnman& connman = EnsureConnman(node);
        if (connman.GetNodeCount(ConnectionDirection::Both) == 0) {
            throw JSONRPCError(RPC_CLIENT_NOT_CONNECTED, CLIENT_NAME " is not connected!");
        }

        if (miner.isInitialBlockDownload()) {
            throw JSONRPCError(RPC_CLIENT_IN_INITIAL_DOWNLOAD, CLIENT_NAME " is in initial sync and waiting for blocks...");
        }
    }

    static unsigned int nTransactionsUpdatedLast;
    const CTxMemPool& mempool = EnsureMemPool(node);

    if (!lpval.isNull())
    {
        // Wait to respond until either the best block changes, OR a minute has passed and there are more transactions
        uint256 hashWatchedChain;
        unsigned int nTransactionsUpdatedLastLP;

        if (lpval.isStr())
        {
            // Format: <hashBestChain><nTransactionsUpdatedLast>
            const std::string& lpstr = lpval.get_str();

            hashWatchedChain = ParseHashV(lpstr.substr(0, 64), "longpollid");
            nTransactionsUpdatedLastLP = LocaleIndependentAtoi<int64_t>(lpstr.substr(64));
        }
        else
        {
            // NOTE: Spec does not specify behaviour for non-string longpollid, but this makes testing easier
            hashWatchedChain = tip;
            nTransactionsUpdatedLastLP = nTransactionsUpdatedLast;
        }

        // Release lock while waiting
        LEAVE_CRITICAL_SECTION(cs_main);
        {
            MillisecondsDouble checktxtime{std::chrono::minutes(1)};
            while (tip == hashWatchedChain && IsRPCRunning()) {
                tip = miner.waitTipChanged(hashWatchedChain, checktxtime).hash;
                // Timeout: Check transactions for update
                // without holding the mempool lock to avoid deadlocks
                if (mempool.GetTransactionsUpdated() != nTransactionsUpdatedLastLP)
                    break;
                checktxtime = std::chrono::seconds(10);
            }
        }
        ENTER_CRITICAL_SECTION(cs_main);

        tip = CHECK_NONFATAL(miner.getTip()).value().hash;

        if (!IsRPCRunning())
            throw JSONRPCError(RPC_CLIENT_NOT_CONNECTED, "Shutting down");
        // TODO: Maybe recheck connections/IBD and (if something wrong) send an expires-immediately template to stop miners?
    }

    const Consensus::Params& consensusParams = chainman.GetParams().GetConsensus();

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
    static int64_t time_start;
    static std::unique_ptr<BlockTemplate> block_template;
    if (!pindexPrev || pindexPrev->GetBlockHash() != tip ||
        (mempool.GetTransactionsUpdated() != nTransactionsUpdatedLast && GetTime() - time_start > 5))
    {
        // Clear pindexPrev so future calls make a new block, despite any failures from here on
        pindexPrev = nullptr;

        // Store the pindexBest used before createNewBlock, to avoid races
        nTransactionsUpdatedLast = mempool.GetTransactionsUpdated();
        CBlockIndex* pindexPrevNew = chainman.m_blockman.LookupBlockIndex(tip);
        time_start = GetTime();

        // Create new block
        block_template = miner.createNewBlock();
        CHECK_NONFATAL(block_template);


        // Need to update only after we know createNewBlock succeeded
        pindexPrev = pindexPrevNew;
    }
    CHECK_NONFATAL(pindexPrev);
    CBlock block{block_template->getBlock()};

    // Update nTime
    UpdateTime(&block, consensusParams, pindexPrev);
    block.nNonce = 0;

    // NOTE: If at some point we support pre-segwit miners post-segwit-activation, this needs to take segwit support into consideration
    const bool fPreSegWit = !DeploymentActiveAfter(pindexPrev, chainman, Consensus::DEPLOYMENT_SEGWIT);

    UniValue aCaps(UniValue::VARR); aCaps.push_back("proposal");

    UniValue transactions(UniValue::VARR);
    std::map<uint256, int64_t> setTxIndex;
    std::vector<CAmount> tx_fees{block_template->getTxFees()};
    std::vector<CAmount> tx_sigops{block_template->getTxSigops()};

    int i = 0;
    for (const auto& it : block.vtx) {
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
        entry.pushKV("depends", std::move(deps));

        int index_in_template = i - 1;
        entry.pushKV("fee", tx_fees.at(index_in_template));
        int64_t nTxSigOps{tx_sigops.at(index_in_template)};
        if (fPreSegWit) {
            CHECK_NONFATAL(nTxSigOps % WITNESS_SCALE_FACTOR == 0);
            nTxSigOps /= WITNESS_SCALE_FACTOR;
        }
        entry.pushKV("sigops", nTxSigOps);
        entry.pushKV("weight", GetTransactionWeight(tx));

        transactions.push_back(std::move(entry));
    }

    UniValue aux(UniValue::VOBJ);

    arith_uint256 hashTarget = arith_uint256().SetCompact(block.nBits);

    UniValue aMutable(UniValue::VARR);
    aMutable.push_back("time");
    aMutable.push_back("transactions");
    aMutable.push_back("prevblock");

    UniValue result(UniValue::VOBJ);
    result.pushKV("capabilities", std::move(aCaps));

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
        ThresholdState state = chainman.m_versionbitscache.State(pindexPrev, consensusParams, pos);
        switch (state) {
            case ThresholdState::DEFINED:
            case ThresholdState::FAILED:
                // Not exposed to GBT at all
                break;
            case ThresholdState::LOCKED_IN:
                // Ensure bit is set in block version
                block.nVersion |= chainman.m_versionbitscache.Mask(consensusParams, pos);
                [[fallthrough]];
            case ThresholdState::STARTED:
            {
                const struct VBDeploymentInfo& vbinfo = VersionBitsDeploymentInfo[pos];
                vbavailable.pushKV(gbt_vb_name(pos), consensusParams.vDeployments[pos].bit);
                if (setClientRules.find(vbinfo.name) == setClientRules.end()) {
                    if (!vbinfo.gbt_force) {
                        // If the client doesn't support this, don't indicate it in the [default] version
                        block.nVersion &= ~chainman.m_versionbitscache.Mask(consensusParams, pos);
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
                        throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Support for '%s' rule requires explicit client support", vbinfo.name));
                    }
                }
                break;
            }
        }
    }
    result.pushKV("version", block.nVersion);
    result.pushKV("rules", std::move(aRules));
    result.pushKV("vbavailable", std::move(vbavailable));
    result.pushKV("vbrequired", int(0));

    result.pushKV("previousblockhash", block.hashPrevBlock.GetHex());
    result.pushKV("transactions", std::move(transactions));
    result.pushKV("coinbaseaux", std::move(aux));
    result.pushKV("coinbasevalue", (int64_t)block.vtx[0]->vout[0].nValue.GetAmount());
    result.pushKV("longpollid", tip.GetHex() + ToString(nTransactionsUpdatedLast));
    result.pushKV("target", hashTarget.GetHex());
    result.pushKV("mintime", GetMinimumTime(pindexPrev, consensusParams.DifficultyAdjustmentInterval()));
    result.pushKV("mutable", std::move(aMutable));
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
    result.pushKV("curtime", block.GetBlockTime());
    result.pushKV("bits", strprintf("%08x", block.nBits));
    result.pushKV("height", (int64_t)(pindexPrev->nHeight+1));

    if (consensusParams.signet_blocks) {
        result.pushKV("signet_challenge", HexStr(consensusParams.signet_challenge));
    }

    if (!block_template->getCoinbaseCommitment().empty()) {
        result.pushKV("default_witness_commitment", HexStr(block_template->getCoinbaseCommitment()));
    }

    return result;
},
    };
}

class submitblock_StateCatcher final : public CValidationInterface
{
public:
    uint256 hash;
    bool found{false};
    BlockValidationState state;

    explicit submitblock_StateCatcher(const uint256 &hashIn) : hash(hashIn), state() {}

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
            {"dummy", RPCArg::Type::STR, RPCArg::DefaultHint{"ignored"}, "dummy value, for compatibility with BIP22. This value is ignored."},
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

    ChainstateManager& chainman = EnsureAnyChainman(request.context);
    {
        LOCK(cs_main);
        const CBlockIndex* pindex = chainman.m_blockman.LookupBlockIndex(block.hashPrevBlock);
        if (pindex) {
            chainman.UpdateUncommittedBlockStructures(block, pindex);
        }
    }

    bool new_block;
    auto sc = std::make_shared<submitblock_StateCatcher>(block.GetHash());
    CHECK_NONFATAL(chainman.m_options.signals)->RegisterSharedValidationInterface(sc);
    bool accepted = chainman.ProcessNewBlock(blockptr, /*force_processing=*/true, /*min_pow_checked=*/true, /*new_block=*/&new_block);
    CHECK_NONFATAL(chainman.m_options.signals)->UnregisterSharedValidationInterface(sc);
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
    chainman.ProcessNewBlockHeaders({{h}}, /*min_pow_checked=*/true, state);
    if (state.IsValid()) return UniValue::VNULL;
    if (state.IsError()) {
        throw JSONRPCError(RPC_VERIFY_ERROR, state.ToString());
    }
    throw JSONRPCError(RPC_VERIFY_ERROR, state.GetRejectReason());
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
                    {"min_tx_age", RPCArg::Type::NUM, RPCArg::Default{0}, "How many seconds a transaction must have been in the mempool to be included in the block proposal. This may help with faster block convergence among functionaries using compact blocks."},
                    {"proposed_parameters", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "Parameters to be used in dynamic federations blocks as proposals. During a period of `-dynamic_epoch_length` blocks, 4/5 of total blocks must signal these parameters for the proposal to become activated in the next epoch.",
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
                    },
                    {"commit_data", RPCArg::Type::ARR, RPCArg::Optional::OMITTED, "Array of data in hex to be committed to in additional coinbase outputs.",
                        {
                            {"", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "Hex encoded string for commit data"},
                        },
                    {RPCArgOptions{.skip_type_check=true}}},
                },
                RPCResult{
                    RPCResult::Type::STR_HEX, "blockhex", "the block hex",
                },
                RPCExamples{
                    HelpExampleCli("getnewblockhex", ""),
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    ChainstateManager& chainman = EnsureAnyChainman(request.context);

    int required_wait = !request.params[0].isNull() ? request.params[0].getInt<int>() : 0;
    if (required_wait < 0) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "min_tx_age must be non-negative.");
    }

    // Construct proposed parameter entry, if any
    DynaFedParamEntry proposed;
    if (!request.params[1].isNull()) {
        auto tip = WITH_LOCK(::cs_main, return chainman.ActiveChain().Tip());
        if (!DeploymentActiveAfter(tip, chainman, Consensus::DEPLOYMENT_DYNA_FED)) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Dynamic federations is not active on this network. Proposed parameters are not needed.");
        }

        UniValue prop = request.params[1].get_obj();

        std::string sbs_str = prop["signblockscript"].get_str();
        if (!IsHex(sbs_str)) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "signblockscript must be hex");
        }
        std::vector<unsigned char> signblock_bytes = ParseHex(sbs_str);
        proposed.m_signblockscript = CScript(signblock_bytes.begin(), signblock_bytes.end());

        int max_sbs_wit = prop["max_block_witness"].getInt<int>();
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

    // Any commitments required for non-consensus reasons.
    // These will be placed in the first coinbase outputs.
    std::vector<CScript> data_commitments;
    if (!request.params[2].isNull()) {
        UniValue commitments(UniValue::VARR);

        // backwards compatibility: attempt to parse as a string first
        if (request.params[2].isStr()) {
            UniValue hex = request.params[2].get_str();
            commitments.push_back(hex);
        } else {
            commitments = request.params[2].get_array();
        }

        for (unsigned int i = 0; i < commitments.size(); i++) {
            std::vector<unsigned char> data_bytes = ParseHex(commitments[i].get_str());
            CScript data_commitment = CScript() << OP_RETURN << data_bytes;
            data_commitments.push_back(data_commitment);
        }
    }

    CScript feeDestinationScript = Params().GetConsensus().mandatory_coinbase_destination;
    if (feeDestinationScript == CScript()) feeDestinationScript = CScript() << OP_TRUE;
    const NodeContext& node = EnsureAnyNodeContext(request.context);

    BlockAssembler::Options options;
    ApplyArgsManOptions(gArgs, options);
    options.coinbase_output_script = feeDestinationScript;
    options.min_tx_age = std::chrono::seconds(required_wait);
    options.proposed_entry = proposed;
    options.commit_scripts = data_commitments;

    std::unique_ptr<CBlockTemplate> pblocktemplate(BlockAssembler(chainman.ActiveChainstate(), node.mempool.get(), options).CreateNewBlock());
    if (!pblocktemplate.get()) {
        throw JSONRPCError(RPC_INTERNAL_ERROR, "Block template empty");
    }

    {
        // Set coinbase flags and builds merkle tree
        LOCK(cs_main);
        unsigned int nExtraNonce = 0;
        pblocktemplate->block.hashMerkleRoot = BlockMerkleRoot(pblocktemplate->block);

        unsigned int nHeight = chainman.ActiveChain().Tip()->nHeight + 1; // Height first in coinbase required for block.version=2
        CMutableTransaction txCoinbase(*pblocktemplate->block.vtx[0]);
        txCoinbase.vin[0].scriptSig = (CScript() << nHeight << CScriptNum(nExtraNonce));
        CHECK_NONFATAL(txCoinbase.vin[0].scriptSig.size() <= 100);

        pblocktemplate->block.vtx[0] = MakeTransactionRef(std::move(txCoinbase));
        pblocktemplate->block.hashMerkleRoot = BlockMerkleRoot(pblocktemplate->block);
    }

    // If WSH(OP_TRUE) block, fill in witness
    CScript op_true(OP_TRUE);
    if (pblocktemplate->block.m_dynafed_params.m_current.m_signblockscript ==
            GetScriptForDestination(WitnessV0ScriptHash(op_true))) {
        pblocktemplate->block.m_signblock_witness.stack.emplace_back(op_true.begin(), op_true.end());
    }

    DataStream ssBlock{};
    ssBlock << TX_WITH_WITNESS(pblocktemplate->block);
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
                    {"witnessScript", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "The hex-encoded witnessScript for the signblockscript. Required for dynafed blocks; omitted for non-dynafed blocks."},
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

    DataStream ssBlock;
    ssBlock << TX_WITH_WITNESS(block);
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
                    RPCResult::Type::STR_HEX, "sketch", "serialized block sketch",
                },
                RPCExamples{
                    HelpExampleCli("getcompactsketch", ""),
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    CBlock block;
    std::vector<unsigned char> block_bytes(ParseHex(request.params[0].get_str()));
    DataStream ssBlock(block_bytes);
    ssBlock >> TX_WITH_WITNESS(block);

    if (block.vtx.empty()) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Cannot obtain sketch of empty block.");
    }

    uint64_t nonce = FastRandomContext().rand64();
    CBlockHeaderAndShortTxIDs cmpctblock(block, nonce);

    DataStream ssCompactBlock;
    ssCompactBlock << TX_WITH_WITNESS(cmpctblock);
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
                        {RPCResult::Type::STR_HEX, "blockhex", /*optional=*/true, "The filled block hex. Only returns when block is final"},
                        {RPCResult::Type::STR_HEX, "block_tx_req", /*optional=*/true, "The serialized structure of missing transaction indices, given to serving node"},
                        {RPCResult::Type::STR_HEX, "found_transactions", /*optional=*/true, "The serialized list of found transactions to be used in finalizecompactblock"},
                    },
                },
                RPCExamples{
                    HelpExampleCli("consumecompactsketch", "<sketch>"),
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    UniValue ret(UniValue::VOBJ);

    std::vector<unsigned char> compact_block_bytes(ParseHex(request.params[0].get_str()));
    DataStream ssBlock(compact_block_bytes);
    CBlockHeaderAndShortTxIDs cmpctblock;
    ssBlock >> TX_WITH_WITNESS(cmpctblock);

    const NodeContext& node = EnsureAnyNodeContext(request.context);
    LOCK(node.mempool->cs);
    PartiallyDownloadedBlock partialBlock(node.mempool.get());
    const std::vector<CTransactionRef> dummy;
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

    DataStream ssReq{};
    ssReq << req;

    if (req.indexes.empty()) {
        std::shared_ptr<CBlock> pblock = std::make_shared<CBlock>();
        std::vector<CTransactionRef> dummy;
        ReadStatus status = partialBlock.FillBlock(*pblock, dummy, /*segwit_active=*/true);
        if (status == READ_STATUS_INVALID) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Bogus crap sketch.");
        } else if (status == READ_STATUS_FAILED) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Failed to complete block though all transactions were apparently found. Could be random short ID collision; requires full block instead.");
        }
        DataStream ssBlock{};
        ssBlock << TX_WITH_WITNESS(*pblock);

        ret.pushKV("blockhex", HexStr(ssBlock));
    } else {
        // Serialize the list of transactions we found
        DataStream ssFound;
        ssFound << TX_WITH_WITNESS(found);

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
                    {"full_block", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "Hex serialized block that corresponds to the block request `block_tx_req`."},
                    {"block_tx_req", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "Hex serialized BlockTransactionsRequest, aka getblocktxn network message."},
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
    DataStream ssBlock(block_bytes);
    ssBlock >> TX_WITH_WITNESS(block);

    // Take in BlockTransactionsRequest, return BlockTransactions
    std::vector<unsigned char> block_req(ParseHex(request.params[1].get_str()));
    DataStream ssReq(block_req);

    BlockTransactionsRequest req;
    ssReq >> TX_WITH_WITNESS(req);

    BlockTransactions resp(req);
    for (size_t i = 0; i < req.indexes.size(); i++) {
        if (req.indexes[i] >= block.vtx.size()) {
            throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Peer sent us a getblocktxn with out-of-bounds tx indices");
        }
        resp.txn[i] = block.vtx[req.indexes[i]];
    }

    DataStream ssResp{};
    ssResp << TX_WITH_WITNESS(resp);

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
    DataStream ssCompactBlock(compact_block_bytes);
    CBlockHeaderAndShortTxIDs cmpctblock;
    ssCompactBlock >> TX_WITH_WITNESS(cmpctblock);

    // BlockTransactions from the server
    std::vector<unsigned char> block_tx(ParseHex(request.params[1].get_str()));
    DataStream ssResp{block_tx};

    BlockTransactions transactions;
    ssResp >> transactions;

    // Cached transactions
    std::vector<unsigned char> found_tx(ParseHex(request.params[2].get_str()));
    DataStream ssFound(found_tx);

    std::vector<CTransactionRef> found;
    ssFound >> TX_WITH_WITNESS(found);

    // Make mega-list
    found.insert(found.end(), transactions.txn.begin(), transactions.txn.end());

    // Now construct the final block! (use dummy mempool here, otherwise reconstruction may fail)
    bilingual_str dummy_error;
    CTxMemPool dummy_pool{CTxMemPool::Options(), dummy_error};
    PartiallyDownloadedBlock partialBlock(&dummy_pool);

    // "Extra" list is really our combined list that will be put into place using InitData
    std::vector<CTransactionRef> extra_txn(found.size());
    for (const auto& found_tx : found) {
        extra_txn.emplace_back(found_tx);
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

    DataStream ssBlock{};
    ssBlock << TX_WITH_WITNESS(*pblock);

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
                    {"acceptnonstd", RPCArg::Type::BOOL, RPCArg::Optional::OMITTED, "If set false, returns error if block contains non-standard transaction. Default is set via `-acceptnonstdtxn`."},
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
    node::BlockMap::iterator mi = chainman.BlockIndex().find(hash);
    if (mi != chainman.BlockIndex().end())
        throw JSONRPCError(RPC_VERIFY_ALREADY_IN_UTXO_SET, "already have block");

    CBlockIndex* const pindexPrev = chainman.ActiveChain().Tip();
    // TestBlockValidity only supports blocks built on the current Tip
    if (block.hashPrevBlock != pindexPrev->GetBlockHash())
        throw JSONRPCError(RPC_VERIFY_ERROR, "proposal was not based on our best chain");

    BlockValidationState state;
    if (!TestBlockValidity(state, Params(), chainman.ActiveChainstate(), block, pindexPrev, false, true) || !state.IsValid()) {
        std::string strRejectReason = state.GetRejectReason();
        if (strRejectReason.empty())
            throw JSONRPCError(RPC_VERIFY_ERROR, state.IsInvalid() ? "Block proposal was invalid" : "Error checking block proposal");
        throw JSONRPCError(RPC_VERIFY_ERROR, strRejectReason);
    }

    const bool acceptnonstd = !request.params[1].isNull() ? request.params[1].get_bool() : gArgs.GetBoolArg("-acceptnonstdtxn", DEFAULT_ACCEPT_NON_STD_TXN);
    if (!acceptnonstd) {
        for (auto& transaction : block.vtx) {
            if (transaction->IsCoinBase()) continue;
            std::string reason;
            if (!IsStandardTx(*transaction, std::nullopt, DEFAULT_PERMIT_BAREMULTISIG, CFeeRate{DUST_RELAY_TX_FEE}, reason)) {
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

void RegisterMiningRPCCommands(CRPCTable& t)
{
    static const CRPCCommand commands[] =
    {
        {"mining", &getnetworkhashps},
        {"mining", &getmininginfo},
        {"mining", &prioritisetransaction},
        {"mining", &getprioritisedtransactions},
        {"mining", &getblocktemplate},
        {"generating", &combineblocksigs},
        {"mining", &submitheader},
        {"generating", &getnewblockhex},
        {"generating", &getcompactsketch},
        {"generating", &consumecompactsketch},
        {"generating", &consumegetblocktxn},
        {"generating", &finalizecompactblock},
        {"mining", &testproposedblock},

        {"mining", &submitblock},
        {"hidden", &generate},
        {"hidden", &generatetoaddress},
        {"hidden", &generatetodescriptor},
        {"hidden", &generateblock},
    };
    for (const auto& c : commands) {
        t.appendCommand(c.name, &c);
    }
}
