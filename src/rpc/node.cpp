// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2022 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <consensus/merkle.h>
#include <validation.h>
#include <chainparams.h>
#include <httpserver.h>
#include <index/blockfilterindex.h>
#include <index/coinstatsindex.h>
#include <index/txindex.h>
#include <interfaces/chain.h>
#include <interfaces/echo.h>
#include <interfaces/init.h>
#include <interfaces/ipc.h>
#include <key_io.h>
#include <kernel/cs_main.h>
#include <node/context.h>
#include <outputtype.h>
#include <pegins.h>
#include <rpc/server.h>
#include <rpc/server_util.h>
#include <rpc/util.h>
#include <scheduler.h>
#include <univalue.h>
#include <util/check.h>
#include <util/syscall_sandbox.h>
#include <util/system.h>

#include <stdint.h>
#ifdef HAVE_MALLOC_INFO
#include <malloc.h>
#endif

#include <assetsdir.h>

using node::NodeContext;

static RPCHelpMan setmocktime()
{
    return RPCHelpMan{"setmocktime",
        "\nSet the local time to given timestamp (-regtest only)\n",
        {
            {"timestamp", RPCArg::Type::NUM, RPCArg::Optional::NO, UNIX_EPOCH_TIME + "\n"
             "Pass 0 to go back to using the system time."},
        },
        RPCResult{RPCResult::Type::NONE, "", ""},
        RPCExamples{""},
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    if (!Params().IsMockableChain()) {
        throw std::runtime_error("setmocktime is for regression testing (-regtest mode) only");
    }

    // For now, don't change mocktime if we're in the middle of validation, as
    // this could have an effect on mempool time-based eviction, as well as
    // IsCurrentForFeeEstimation() and IsInitialBlockDownload().
    // TODO: figure out the right way to synchronize around mocktime, and
    // ensure all call sites of GetTime() are accessing this safely.
    LOCK(cs_main);

    const int64_t time{request.params[0].getInt<int64_t>()};
    if (time < 0) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Mocktime cannot be negative: %s.", time));
    }
    SetMockTime(time);
    auto node_context = util::AnyPtr<NodeContext>(request.context);
    if (node_context) {
        for (const auto& chain_client : node_context->chain_clients) {
            chain_client->setMockTime(time);
        }
    }

    return UniValue::VNULL;
},
    };
}

#if defined(USE_SYSCALL_SANDBOX)
static RPCHelpMan invokedisallowedsyscall()
{
    return RPCHelpMan{
        "invokedisallowedsyscall",
        "\nInvoke a disallowed syscall to trigger a syscall sandbox violation. Used for testing purposes.\n",
        {},
        RPCResult{RPCResult::Type::NONE, "", ""},
        RPCExamples{
            HelpExampleCli("invokedisallowedsyscall", "") + HelpExampleRpc("invokedisallowedsyscall", "")},
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue {
            if (!Params().IsTestChain()) {
                throw std::runtime_error("invokedisallowedsyscall is used for testing only.");
            }
            TestDisallowedSandboxCall();
            return UniValue::VNULL;
        },
    };
}
#endif // USE_SYSCALL_SANDBOX

static RPCHelpMan mockscheduler()
{
    return RPCHelpMan{"mockscheduler",
        "\nBump the scheduler into the future (-regtest only)\n",
        {
            {"delta_time", RPCArg::Type::NUM, RPCArg::Optional::NO, "Number of seconds to forward the scheduler into the future." },
        },
        RPCResult{RPCResult::Type::NONE, "", ""},
        RPCExamples{""},
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    if (!Params().IsMockableChain()) {
        throw std::runtime_error("mockscheduler is for regression testing (-regtest mode) only");
    }

    int64_t delta_seconds = request.params[0].getInt<int64_t>();
    if (delta_seconds <= 0 || delta_seconds > 3600) {
        throw std::runtime_error("delta_time must be between 1 and 3600 seconds (1 hr)");
    }

    auto node_context = CHECK_NONFATAL(util::AnyPtr<NodeContext>(request.context));
    // protect against null pointer dereference
    CHECK_NONFATAL(node_context->scheduler);
    node_context->scheduler->MockForward(std::chrono::seconds(delta_seconds));

    return UniValue::VNULL;
},
    };
}

static UniValue RPCLockedMemoryInfo()
{
    LockedPool::Stats stats = LockedPoolManager::Instance().stats();
    UniValue obj(UniValue::VOBJ);
    obj.pushKV("used", uint64_t(stats.used));
    obj.pushKV("free", uint64_t(stats.free));
    obj.pushKV("total", uint64_t(stats.total));
    obj.pushKV("locked", uint64_t(stats.locked));
    obj.pushKV("chunks_used", uint64_t(stats.chunks_used));
    obj.pushKV("chunks_free", uint64_t(stats.chunks_free));
    return obj;
}

#ifdef HAVE_MALLOC_INFO
static std::string RPCMallocInfo()
{
    char *ptr = nullptr;
    size_t size = 0;
    FILE *f = open_memstream(&ptr, &size);
    if (f) {
        malloc_info(0, f);
        fclose(f);
        if (ptr) {
            std::string rv(ptr, size);
            free(ptr);
            return rv;
        }
    }
    return "";
}
#endif

static RPCHelpMan getmemoryinfo()
{
    /* Please, avoid using the word "pool" here in the RPC interface or help,
     * as users will undoubtedly confuse it with the other "memory pool"
     */
    return RPCHelpMan{"getmemoryinfo",
                "Returns an object containing information about memory usage.\n",
                {
                    {"mode", RPCArg::Type::STR, RPCArg::Default{"stats"}, "determines what kind of information is returned.\n"
            "  - \"stats\" returns general statistics about memory usage in the daemon.\n"
            "  - \"mallocinfo\" returns an XML string describing low-level heap state (only available if compiled with glibc 2.10+)."},
                },
                {
                    RPCResult{"mode \"stats\"",
                        RPCResult::Type::OBJ, "", "",
                        {
                            {RPCResult::Type::OBJ, "locked", "Information about locked memory manager",
                            {
                                {RPCResult::Type::NUM, "used", "Number of bytes used"},
                                {RPCResult::Type::NUM, "free", "Number of bytes available in current arenas"},
                                {RPCResult::Type::NUM, "total", "Total number of bytes managed"},
                                {RPCResult::Type::NUM, "locked", "Amount of bytes that succeeded locking. If this number is smaller than total, locking pages failed at some point and key data could be swapped to disk."},
                                {RPCResult::Type::NUM, "chunks_used", "Number allocated chunks"},
                                {RPCResult::Type::NUM, "chunks_free", "Number unused chunks"},
                            }},
                        }
                    },
                    RPCResult{"mode \"mallocinfo\"",
                        RPCResult::Type::STR, "", "\"<malloc version=\"1\">...\""
                    },
                },
                RPCExamples{
                    HelpExampleCli("getmemoryinfo", "")
            + HelpExampleRpc("getmemoryinfo", "")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    std::string mode = request.params[0].isNull() ? "stats" : request.params[0].get_str();
    if (mode == "stats") {
        UniValue obj(UniValue::VOBJ);
        obj.pushKV("locked", RPCLockedMemoryInfo());
        return obj;
    } else if (mode == "mallocinfo") {
#ifdef HAVE_MALLOC_INFO
        return RPCMallocInfo();
#else
        throw JSONRPCError(RPC_INVALID_PARAMETER, "mallocinfo mode not available");
#endif
    } else {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "unknown mode " + mode);
    }
},
    };
}

static void EnableOrDisableLogCategories(UniValue cats, bool enable) {
    cats = cats.get_array();
    for (unsigned int i = 0; i < cats.size(); ++i) {
        std::string cat = cats[i].get_str();

        bool success;
        if (enable) {
            success = LogInstance().EnableCategory(cat);
        } else {
            success = LogInstance().DisableCategory(cat);
        }

        if (!success) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "unknown logging category " + cat);
        }
    }
}

static RPCHelpMan logging()
{
    return RPCHelpMan{"logging",
            "Gets and sets the logging configuration.\n"
            "When called without an argument, returns the list of categories with status that are currently being debug logged or not.\n"
            "When called with arguments, adds or removes categories from debug logging and return the lists above.\n"
            "The arguments are evaluated in order \"include\", \"exclude\".\n"
            "If an item is both included and excluded, it will thus end up being excluded.\n"
            "The valid logging categories are: " + LogInstance().LogCategoriesString() + "\n"
            "In addition, the following are available as category names with special meanings:\n"
            "  - \"all\",  \"1\" : represent all logging categories.\n"
            "  - \"none\", \"0\" : even if other logging categories are specified, ignore all of them.\n"
            ,
                {
                    {"include", RPCArg::Type::ARR, RPCArg::Optional::OMITTED_NAMED_ARG, "The categories to add to debug logging",
                        {
                            {"include_category", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "the valid logging category"},
                        }},
                    {"exclude", RPCArg::Type::ARR, RPCArg::Optional::OMITTED_NAMED_ARG, "The categories to remove from debug logging",
                        {
                            {"exclude_category", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "the valid logging category"},
                        }},
                },
                RPCResult{
                    RPCResult::Type::OBJ_DYN, "", "keys are the logging categories, and values indicates its status",
                    {
                        {RPCResult::Type::BOOL, "category", "if being debug logged or not. false:inactive, true:active"},
                    }
                },
                RPCExamples{
                    HelpExampleCli("logging", "\"[\\\"all\\\"]\" \"[\\\"http\\\"]\"")
            + HelpExampleRpc("logging", "[\"all\"], [\"libevent\"]")
                },
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    uint32_t original_log_categories = LogInstance().GetCategoryMask();
    if (request.params[0].isArray()) {
        EnableOrDisableLogCategories(request.params[0], true);
    }
    if (request.params[1].isArray()) {
        EnableOrDisableLogCategories(request.params[1], false);
    }
    uint32_t updated_log_categories = LogInstance().GetCategoryMask();
    uint32_t changed_log_categories = original_log_categories ^ updated_log_categories;

    // Update libevent logging if BCLog::LIBEVENT has changed.
    if (changed_log_categories & BCLog::LIBEVENT) {
        UpdateHTTPServerLogging(LogInstance().WillLogCategory(BCLog::LIBEVENT));
    }

    UniValue result(UniValue::VOBJ);
    for (const auto& logCatActive : LogInstance().LogCategoriesList()) {
        result.pushKV(logCatActive.category, logCatActive.active);
    }

    return result;
},
    };
}

static RPCHelpMan echo(const std::string& name)
{
    return RPCHelpMan{name,
                "\nSimply echo back the input arguments. This command is for testing.\n"
                "\nIt will return an internal bug report when arg9='trigger_internal_bug' is passed.\n"
                "\nThe difference between echo and echojson is that echojson has argument conversion enabled in the client-side table in "
                "elements-cli and the GUI. There is no server-side difference.",
        {
            {"arg0", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "", RPCArgOptions{.skip_type_check = true}},
            {"arg1", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "", RPCArgOptions{.skip_type_check = true}},
            {"arg2", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "", RPCArgOptions{.skip_type_check = true}},
            {"arg3", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "", RPCArgOptions{.skip_type_check = true}},
            {"arg4", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "", RPCArgOptions{.skip_type_check = true}},
            {"arg5", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "", RPCArgOptions{.skip_type_check = true}},
            {"arg6", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "", RPCArgOptions{.skip_type_check = true}},
            {"arg7", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "", RPCArgOptions{.skip_type_check = true}},
            {"arg8", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "", RPCArgOptions{.skip_type_check = true}},
            {"arg9", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "", RPCArgOptions{.skip_type_check = true}},
        },
                RPCResult{RPCResult::Type::ANY, "", "Returns whatever was passed in"},
                RPCExamples{""},
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    if (request.params[9].isStr()) {
        CHECK_NONFATAL(request.params[9].get_str() != "trigger_internal_bug");
    }

    return request.params;
},
    };
}

static RPCHelpMan echo() { return echo("echo"); }
static RPCHelpMan echojson() { return echo("echojson"); }

static RPCHelpMan echoipc()
{
    return RPCHelpMan{
        "echoipc",
        "\nEcho back the input argument, passing it through a spawned process in a multiprocess build.\n"
        "This command is for testing.\n",
        {{"arg", RPCArg::Type::STR, RPCArg::Optional::NO, "The string to echo",}},
        RPCResult{RPCResult::Type::STR, "echo", "The echoed string."},
        RPCExamples{HelpExampleCli("echo", "\"Hello world\"") +
                    HelpExampleRpc("echo", "\"Hello world\"")},
        [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue {
            interfaces::Init& local_init = *EnsureAnyNodeContext(request.context).init;
            std::unique_ptr<interfaces::Echo> echo;
            if (interfaces::Ipc* ipc = local_init.ipc()) {
                // Spawn a new bitcoin-node process and call makeEcho to get a
                // client pointer to a interfaces::Echo instance running in
                // that process. This is just for testing. A slightly more
                // realistic test spawning a different executable instead of
                // the same executable would add a new bitcoin-echo executable,
                // and spawn bitcoin-echo below instead of bitcoin-node. But
                // using bitcoin-node avoids the need to build and install a
                // new executable just for this one test.
                auto init = ipc->spawnProcess("bitcoin-node");
                echo = init->makeEcho();
                ipc->addCleanup(*echo, [init = init.release()] { delete init; });
            } else {
                // IPC support is not available because this is a bitcoind
                // process not a bitcoind-node process, so just create a local
                // interfaces::Echo object and return it so the `echoipc` RPC
                // method will work, and the python test calling `echoipc`
                // can expect the same result.
                echo = local_init.makeEcho();
            }
            return echo->echo(request.params[0].get_str());
        },
    };
}

static UniValue SummaryToJSON(const IndexSummary&& summary, std::string index_name)
{
    UniValue ret_summary(UniValue::VOBJ);
    if (!index_name.empty() && index_name != summary.name) return ret_summary;

    UniValue entry(UniValue::VOBJ);
    entry.pushKV("synced", summary.synced);
    entry.pushKV("best_block_height", summary.best_block_height);
    ret_summary.pushKV(summary.name, entry);
    return ret_summary;
}

static RPCHelpMan getindexinfo()
{
    return RPCHelpMan{"getindexinfo",
                "\nReturns the status of one or all available indices currently running in the node.\n",
                {
                    {"index_name", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "Filter results for an index with a specific name."},
                },
                RPCResult{
                    RPCResult::Type::OBJ_DYN, "", "", {
                        {
                            RPCResult::Type::OBJ, "name", "The name of the index",
                            {
                                {RPCResult::Type::BOOL, "synced", "Whether the index is synced or not"},
                                {RPCResult::Type::NUM, "best_block_height", "The block height to which the index is synced"},
                            }
                        },
                    },
                },
                RPCExamples{
                    HelpExampleCli("getindexinfo", "")
                  + HelpExampleRpc("getindexinfo", "")
                  + HelpExampleCli("getindexinfo", "txindex")
                  + HelpExampleRpc("getindexinfo", "txindex")
                },
                [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    UniValue result(UniValue::VOBJ);
    const std::string index_name = request.params[0].isNull() ? "" : request.params[0].get_str();

    if (g_txindex) {
        result.pushKVs(SummaryToJSON(g_txindex->GetSummary(), index_name));
    }

    if (g_coin_stats_index) {
        result.pushKVs(SummaryToJSON(g_coin_stats_index->GetSummary(), index_name));
    }

    ForEachBlockFilterIndex([&result, &index_name](const BlockFilterIndex& index) {
        result.pushKVs(SummaryToJSON(index.GetSummary(), index_name));
    });

    return result;
},
    };
}

//
// ELEMENTS CALLS

static RPCHelpMan tweakfedpegscript()
{
    return RPCHelpMan{"tweakfedpegscript",
                "\nReturns a tweaked fedpegscript.\n",
                {
                    {"claim_script", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "Script to tweak the fedpegscript with. For example obtained as a result of getpeginaddress."},
                    {"fedpegscript", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED_NAMED_ARG, "Fedpegscript to be used with the claim_script. By default this is the current fedpegscript."},
                },
                RPCResult{
                    RPCResult::Type::OBJ, "", "",
                    {
                        {RPCResult::Type::STR_HEX, "script", "The fedpegscript tweaked with claim_script"},
                        {RPCResult::Type::STR, "address", "The address corresponding to the tweaked fedpegscript"},
                    }
                },
                RPCExamples{""},
                [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    if (!IsHex(request.params[0].get_str())) {
        throw JSONRPCError(RPC_TYPE_ERROR, "the first argument must be a hex string");
    }

    ChainstateManager& chainman = EnsureAnyChainman(request.context);
    auto tip = WITH_LOCK(::cs_main, return chainman.ActiveChain().Tip());
    CScript fedpegscript = GetValidFedpegScripts(tip, Params().GetConsensus(), true /* nextblock_validation */).front().second;

    if (!request.params[1].isNull()) {
        if (IsHex(request.params[1].get_str())) {
            std::vector<unsigned char> fedpeg_byte = ParseHex(request.params[1].get_str());
            fedpegscript = CScript(fedpeg_byte.begin(), fedpeg_byte.end());
        } else {
            throw JSONRPCError(RPC_TYPE_ERROR, "fedpegscript must be a hex string");
        }
    }

    std::vector<unsigned char> scriptData = ParseHex(request.params[0].get_str());
    CScript claim_script = CScript(scriptData.begin(), scriptData.end());

    CScript tweaked_script = calculate_contract(fedpegscript, claim_script);
    CScript redeem_script = GetScriptForDestination(WitnessV0ScriptHash(tweaked_script));
    CTxDestination parent_addr{ScriptHash(redeem_script)};

    UniValue ret(UniValue::VOBJ);
    ret.pushKV("script", HexStr(tweaked_script));
    ret.pushKV("address", EncodeParentDestination(parent_addr));

    return ret;
},
    };
}

UniValue FormatPAKList(CPAKList &paklist) {
    UniValue paklist_value(UniValue::VOBJ);
    std::vector<std::vector<unsigned char> > offline_keys;
    std::vector<std::vector<unsigned char> > online_keys;
    paklist.ToBytes(offline_keys, online_keys);

    UniValue retOnline(UniValue::VARR);
    UniValue retOffline(UniValue::VARR);
    for (unsigned int i = 0; i < offline_keys.size(); i++) {
        retOffline.push_back(HexStr(offline_keys[i]));
        retOnline.push_back(HexStr(online_keys[i]));

    }
    paklist_value.pushKV("online", retOnline);
    paklist_value.pushKV("offline", retOffline);
    paklist_value.pushKV("reject", retOffline.empty());
    return paklist_value;
}

static RPCHelpMan getpakinfo()
{
    return RPCHelpMan{"getpakinfo",
                "\nReturns relevant pegout authorization key (PAK) information about this node, both from blockchain data.\n",
                {},
                RPCResult{
                    RPCResult::Type::OBJ, "", "",
                    {
                        {RPCResult::Type::ARR, "block_paklist", "The PAK list loaded from latest epoch",
                        {
                            {RPCResult::Type::ELISION, "", ""}
                        }},
                    }
                },
                RPCExamples{""},
                [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    LOCK(cs_main);

    UniValue ret(UniValue::VOBJ);
    ChainstateManager& chainman = EnsureAnyChainman(request.context);
    CPAKList paklist = GetActivePAKList(chainman.ActiveChain().Tip(), Params().GetConsensus());
    ret.pushKV("block_paklist", FormatPAKList(paklist));

    return ret;
},
    };
}

static RPCHelpMan calcfastmerkleroot()
{
    return RPCHelpMan{"calcfastmerkleroot",
                "\nhidden utility RPC for computing sha2 midstates\n",
                {
                    {"leaves", RPCArg::Type::ARR, RPCArg::Optional::NO, "array of data to compute the fast merkle root of.",
                        {
                            {"data", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "hex-encoded data"},
                        }},
                },
                RPCResult{
                    RPCResult::Type::STR_HEX, "", "merkle root of provided data"
                },
                RPCExamples{
                    HelpExampleCli("calcfastmerkleroot", "[\"a\", \"b\", \"c\"]")
                },
                [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    std::vector<uint256> leaves;
    for (const UniValue& leaf : request.params[0].get_array().getValues()) {
        uint256 l;
        l.SetHex(leaf.get_str());
        leaves.push_back(l);
    }

    uint256 root = ComputeFastMerkleRoot(leaves);

    UniValue ret(UniValue::VOBJ);
    ret.setStr(root.GetHex());
    return ret;
},
    };
}

static RPCHelpMan dumpassetlabels()
{
    return RPCHelpMan{"dumpassetlabels",
                "\nLists all known asset id/label pairs in this wallet. This list can be modified with `-assetdir` configuration argument.\n",
                {},
                RPCResult{
                    RPCResult::Type::OBJ, "labels", "",
                    {
                        {RPCResult::Type::ELISION, "", "the label for each asset id"},
                    },
                },
                RPCExamples{
                    HelpExampleCli("dumpassetlabels", "" )
            + HelpExampleRpc("dumpassetlabels", "" )
                },
                [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    UniValue obj(UniValue::VOBJ);
    for (const auto& as : gAssetsDir.GetKnownAssets()) {
        obj.pushKV(gAssetsDir.GetLabel(as), as.GetHex());
    }
    return obj;
},
    };
}

class BlindingPubkeyAdderVisitor
{
public:
    CPubKey blind_key;
    explicit BlindingPubkeyAdderVisitor(const CPubKey& blind_key_in) : blind_key(blind_key_in) {}

    void operator()(const CNoDestination& dest) const {}

    void operator()(PKHash& keyID) const
    {
        keyID.blinding_pubkey = blind_key;
    }

    void operator()(ScriptHash& scriptID) const
    {
        scriptID.blinding_pubkey = blind_key;
    }

    void operator()(WitnessV0KeyHash& id) const
    {
        id.blinding_pubkey = blind_key;
    }

    void operator()(WitnessV0ScriptHash& id) const
    {
        id.blinding_pubkey = blind_key;
    }

    void operator()(WitnessV1Taproot& tap) const
    {
        tap.blinding_pubkey = blind_key;
    }

    void operator()(WitnessUnknown& id) const
    {
        id.blinding_pubkey = blind_key;
    }

    void operator()(const NullData& id) const {}
};


static RPCHelpMan createblindedaddress()
{
    return RPCHelpMan{"createblindedaddress",
                "\nCreates a blinded address using the provided blinding key.\n",
                {
                    {"address", RPCArg::Type::STR, RPCArg::Optional::NO, "The unblinded address to be blinded."},
                    {"blinding_key", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The blinding public key. This can be obtained for a given address using `getaddressinfo` (`confidential_key` field)."},
                },
                RPCResult{
                    RPCResult::Type::STR, "blinded_address", "The blinded address"
                },
                RPCExamples{
            "\nCreate a blinded address\n"
            + HelpExampleCli("createblindedaddress", "HEZk3iQi1jC49bxUriTtynnXgWWWdAYx16 ec09811118b6febfa5ebe68642e5091c418fbace07e655da26b4a845a691fc2d") +
            "\nAs a json rpc call\n"
            + HelpExampleRpc("createblindedaddress", "HEZk3iQi1jC49bxUriTtynnXgWWWdAYx16, ec09811118b6febfa5ebe68642e5091c418fbace07e655da26b4a845a691fc2d")
                },
                [&](const RPCHelpMan& self, const JSONRPCRequest& request) -> UniValue
{
    CTxDestination address = DecodeDestination(request.params[0].get_str());
    if (!IsValidDestination(address)) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid Bitcoin address or script");
    }
    if (IsBlindDestination(address)) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Not an unblinded address");
    }

    if (!IsHex(request.params[1].get_str())) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid hexadecimal for key");
    }
    std::vector<unsigned char> keydata = ParseHex(request.params[1].get_str());
    if (keydata.size() != 33) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid hexadecimal key length, must be length 66.");
    }

    CPubKey key;
    key.Set(keydata.begin(), keydata.end());

    // Append blinding key and return
    std::visit(BlindingPubkeyAdderVisitor(key), address);
    return EncodeDestination(address);
},
    };
}


// END ELEMENTS CALLS
//

void RegisterNodeRPCCommands(CRPCTable& t)
{
    static const CRPCCommand commands[] =
    {
        {"control", &getmemoryinfo},
        {"control", &logging},
        {"util", &getindexinfo},

        {"hidden", &setmocktime},
        {"hidden", &mockscheduler},
        {"hidden", &echo},
        {"hidden", &echojson},
        {"hidden", &echoipc},
#if defined(USE_SYSCALL_SANDBOX)
        {"hidden", &invokedisallowedsyscall},
#endif // USE_SYSCALL_SANDBOX

        // ELEMENTS:
        {"util", &getpakinfo},
        {"util", &tweakfedpegscript},
        {"util", &createblindedaddress},
        {"util", &dumpassetlabels},
        {"hidden", &calcfastmerkleroot},
    };
    for (const auto& c : commands) {
        t.appendCommand(c.name, &c);
    }
}
