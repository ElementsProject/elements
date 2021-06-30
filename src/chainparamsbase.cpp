// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <chainparamsbase.h>

#include <tinyformat.h>
#include <util/system.h>

#include <assert.h>

const std::string CBaseChainParams::MAIN = "main";
const std::string CBaseChainParams::TESTNET = "test";
const std::string CBaseChainParams::SIGNET = "signet";
const std::string CBaseChainParams::REGTEST = "regtest";
const std::string CBaseChainParams::LIQUID1 = "liquidv1";
const std::string CBaseChainParams::LIQUID1TEST = "liquidv1test";

const std::string CBaseChainParams::DEFAULT = CBaseChainParams::LIQUID1;

void SetupChainParamsBaseOptions(ArgsManager& argsman)
{
    argsman.AddArg("-chain=<chain>", "Use the chain <chain> (default: liquidv1). Reserved values: main, test, signet, regtest, liquidv1, liquidv1test", ArgsManager::ALLOW_ANY, OptionsCategory::CHAINPARAMS);
    argsman.AddArg("-regtest", "Enter regression test mode, which uses a special chain in which blocks can be solved instantly. "
                 "This is intended for regression testing tools and app development. Equivalent to -chain=regtest.", ArgsManager::ALLOW_ANY | ArgsManager::DEBUG_ONLY, OptionsCategory::CHAINPARAMS);
    argsman.AddArg("-segwitheight=<n>", "Set the activation height of segwit. -1 to disable. (regtest-only)", ArgsManager::ALLOW_ANY | ArgsManager::DEBUG_ONLY, OptionsCategory::DEBUG_TEST);
    argsman.AddArg("-testnet", "Use the test chain. Equivalent to -chain=test.", ArgsManager::ALLOW_ANY, OptionsCategory::CHAINPARAMS);
    argsman.AddArg("-vbparams=deployment:start:end[:min_activation_height]", "Use given start/end times and min_activation_height for specified version bits deployment (regtest or custom only)", ArgsManager::ALLOW_ANY | ArgsManager::DEBUG_ONLY, OptionsCategory::CHAINPARAMS);
    argsman.AddArg("-seednode=<ip>", "Use specified node as seed node. This option can be specified multiple times to connect to multiple nodes. (custom only)", ArgsManager::ALLOW_ANY | ArgsManager::DEBUG_ONLY, OptionsCategory::CHAINPARAMS);

    argsman.AddArg("-signet", "Use the signet chain. Equivalent to -chain=signet. Note that the network is defined by the -signetchallenge parameter", ArgsManager::ALLOW_ANY, OptionsCategory::CHAINPARAMS);
    argsman.AddArg("-signetchallenge", "Blocks must satisfy the given script to be considered valid (only for signet networks; defaults to the global default signet test network challenge)", ArgsManager::ALLOW_STRING, OptionsCategory::CHAINPARAMS);
    argsman.AddArg("-signetseednode", "Specify a seed node for the signet network, in the hostname[:port] format, e.g. sig.net:1234 (may be used multiple times to specify multiple seed nodes; defaults to the global default signet test network seed node(s))", ArgsManager::ALLOW_STRING, OptionsCategory::CHAINPARAMS);

    //
    // ELEMENTS
    argsman.AddArg("-con_mandatorycoinbase", "All non-zero valued coinbase outputs must go to this scriptPubKey, if set.", ArgsManager::ALLOW_ANY, OptionsCategory::ELEMENTS);
    argsman.AddArg("-con_blocksubsidy", "Defines the amount of block subsidy to start with, at genesis block, in satoshis.", ArgsManager::ALLOW_ANY, OptionsCategory::ELEMENTS);
    argsman.AddArg("-con_connect_genesis_outputs", "Connect outputs in genesis block to utxo database.", ArgsManager::ALLOW_ANY, OptionsCategory::ELEMENTS);
    argsman.AddArg("-con_elementsmode", "Use Elements-like instead of Core-like witness encoding.  This is required for CA/CT. (default: true)", ArgsManager::ALLOW_ANY, OptionsCategory::ELEMENTS);
    argsman.AddArg("-con_blockheightinheader", "Whether the chain includes the block height directly in the header, for easier validation of block height in low-resource environments. (default: true)", ArgsManager::ALLOW_ANY, OptionsCategory::CHAINPARAMS);
    argsman.AddArg("-con_genesis_style=<style>", "Use genesis style <style> (default: elements). Results in genesis block compatibility with various networks. Allowed values: elements, bitcoin", ArgsManager::ALLOW_ANY | ArgsManager::DEBUG_ONLY, OptionsCategory::ELEMENTS);
    argsman.AddArg("-con_signed_blocks", "Signed blockchain. Uses input of `-signblockscript` to define what signatures are necessary to solve it.", ArgsManager::ALLOW_ANY, OptionsCategory::CHAINPARAMS);
    argsman.AddArg("-signblockscript", "Signed blockchain enumberance. Only active when `-con_signed_blocks` set to true.", ArgsManager::ALLOW_ANY, OptionsCategory::CHAINPARAMS);
    argsman.AddArg("-con_max_block_sig_size", "Max allowed witness data for the signed block header.", ArgsManager::ALLOW_ANY, OptionsCategory::CHAINPARAMS);

    argsman.AddArg("-con_has_parent_chain", "Whether or not there is a parent chain.", ArgsManager::ALLOW_ANY, OptionsCategory::CHAINPARAMS);
    argsman.AddArg("-parentgenesisblockhash", "The genesis blockhash of the parent chain.", ArgsManager::ALLOW_ANY, OptionsCategory::CHAINPARAMS);
    argsman.AddArg("-con_parentpowlimit", "The proof-of-work limit value for the parent chain.", ArgsManager::ALLOW_ANY, OptionsCategory::CHAINPARAMS);
    argsman.AddArg("-con_parent_chain_signblockscript", "Whether parent chain uses pow or signed blocks. If the parent chain uses signed blocks, the challenge (scriptPubKey) script. If not, an empty string. (default: empty script [ie parent uses pow])", ArgsManager::ALLOW_ANY, OptionsCategory::CHAINPARAMS);

    argsman.AddArg("-fedpegscript", "The script for the federated peg enforce from genesis block. This script may stop being enforced once dynamic federations activates.", ArgsManager::ALLOW_ANY, OptionsCategory::CHAINPARAMS);
    argsman.AddArg("-enforce_pak", "Causes standardness checks to enforce Pegout Authorization Key(PAK) validation before dynamic federations, and consensus enforcement after.", ArgsManager::ALLOW_ANY, OptionsCategory::ELEMENTS);
    argsman.AddArg("-pak", "Sets the 'first extension space' field to the pak entries ala pre-dynamic federations. Only used for testing in custom chains.", ArgsManager::ALLOW_ANY, OptionsCategory::ELEMENTS);
    argsman.AddArg("-multi_data_permitted", "Allow relay of multiple OP_RETURN outputs. (default: -enforce_pak)", ArgsManager::ALLOW_ANY, OptionsCategory::ELEMENTS);
    argsman.AddArg("-con_csv_deploy_start", "Starting height for CSV deployment. (default: -1, which means ACTIVE from genesis)", ArgsManager::ALLOW_ANY, OptionsCategory::ELEMENTS);
    argsman.AddArg("-con_dyna_deploy_start", "Starting height for Dynamic Federations deployment. Once active, signblockscript becomes a BIP141 WSH scriptPubKey of the original signblockscript. All other dynamic parameters stay constant.(default: -1, which means ACTIVE from genesis)", ArgsManager::ALLOW_ANY, OptionsCategory::ELEMENTS);
    argsman.AddArg("-con_dyna_deploy_signal", "Whether to signal for the Dynamic Federations deployment (default: false).", ArgsManager::ALLOW_ANY, OptionsCategory::ELEMENTS);
    argsman.AddArg("-dynamic_epoch_length", "Per-chain parameter that sets how many blocks dynamic federation voting and enforcement are in effect for.", ArgsManager::ALLOW_ANY, OptionsCategory::ELEMENTS);
    argsman.AddArg("-total_valid_epochs", "Per-chain parameter that sets how long a particular fedpegscript is in effect for.", ArgsManager::ALLOW_ANY, OptionsCategory::ELEMENTS);
    // END ELEMENTS
    //
}

static std::unique_ptr<CBaseChainParams> globalChainBaseParams;

const CBaseChainParams& BaseParams()
{
    assert(globalChainBaseParams);
    return *globalChainBaseParams;
}

/**
 * Port numbers for incoming Tor connections (8334, 18334, 38334, 18445) have
 * been chosen arbitrarily to keep ranges of used ports tight.
 */
std::unique_ptr<CBaseChainParams> CreateBaseChainParams(const std::string& chain)
{
    if (chain == CBaseChainParams::MAIN) {
        return std::make_unique<CBaseChainParams>("", 8332, 18332, 8334);
    } else if (chain == CBaseChainParams::TESTNET) {
        return std::make_unique<CBaseChainParams>("testnet3", 18332, 8332, 18334);
    } else if (chain == CBaseChainParams::SIGNET) {
        return std::make_unique<CBaseChainParams>("signet", 38332, 18332, 38334);
    } else if (chain == CBaseChainParams::REGTEST) {
        return std::make_unique<CBaseChainParams>("regtest", 18443, 18332, 18445);
    } else if (chain == CBaseChainParams::LIQUID1) {
        return std::make_unique<CBaseChainParams>("liquidv1", 7041, 8332, 37041);
    } else if (chain == CBaseChainParams::LIQUID1TEST) {
        return std::make_unique<CBaseChainParams>("liquidv1test", 7040, 18332, 37040);  // Use same ports as customparams
    }

    // ELEMENTS:
    return std::make_unique<CBaseChainParams>(chain, 7040, 18332, 37040);
}

void SelectBaseParams(const std::string& chain)
{
    globalChainBaseParams = CreateBaseChainParams(chain);
    gArgs.SelectConfigNetwork(chain);
}
