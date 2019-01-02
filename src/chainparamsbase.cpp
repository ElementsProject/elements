// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <chainparamsbase.h>

#include <tinyformat.h>
#include <util.h>
#include <utilmemory.h>

#include <assert.h>

const std::string CBaseChainParams::MAIN = "main";
const std::string CBaseChainParams::TESTNET = "test";
const std::string CBaseChainParams::REGTEST = "regtest";

void SetupChainParamsBaseOptions()
{
    gArgs.AddArg("-chain=<chain>", "Use the chain <chain> (default: main). Reserved values: main, test, regtest", false, OptionsCategory::CHAINPARAMS);
    gArgs.AddArg("-regtest", "Enter regression test mode, which uses a special chain in which blocks can be solved instantly. "
                                   "This is intended for regression testing tools and app development.", true, OptionsCategory::CHAINPARAMS);
    gArgs.AddArg("-testnet", "Use the test chain", false, OptionsCategory::CHAINPARAMS);
    gArgs.AddArg("-vbparams=deployment:start:end", "Use given start/end times for specified version bits deployment (regtest or custom only)", true, OptionsCategory::CHAINPARAMS);
    gArgs.AddArg("-seednode=<ip>", "Use specified node as seed node. This option can be specified multiple times to connect to multiple nodes. (custom only)", true, OptionsCategory::CHAINPARAMS);
    gArgs.AddArg("-con_mandatorycoinbase", "All non-zero valued coinbase outputs must go to this scriptPubKey, if set.", false, OptionsCategory::ELEMENTS);
    gArgs.AddArg("-con_blocksubsidy", "Defines the amount of block subsidy to start with, at genesis block.", false, OptionsCategory::ELEMENTS);
    gArgs.AddArg("-con_connect_coinbase", "Connect outputs in genesis block to utxo database.", false, OptionsCategory::ELEMENTS);
    gArgs.AddArg("-con_blockheightinheader", "Whether the chain includes the block height directly in the header, for easier validation of block height in low-resource environments. (default: true)", false, OptionsCategory::CHAINPARAMS);
    gArgs.AddArg("-con_genesis_style=<style>", "Use genesis style <style> (default: elements). Results in genesis block compatibility with various networks. Allowed values: elements, bitcoin", true, OptionsCategory::ELEMENTS);
    gArgs.AddArg("-con_signed_blocks", "Signed blockchain. Uses input of `-signblockscript` to define what signatures are necessary to solve it.", false, OptionsCategory::CHAINPARAMS);
    gArgs.AddArg("-signblockscript", "Signed blockchain enumberance. Only active when `-con_signed_blocks` set to true.", false, OptionsCategory::CHAINPARAMS);
    gArgs.AddArg("-con_max_block_sig_size", "Max allowed witness data for the signed block header.", false, OptionsCategory::CHAINPARAMS);

    gArgs.AddArg("-con_has_parent_chain", "Whether or not there is a parent chain.", false, OptionsCategory::CHAINPARAMS);
    gArgs.AddArg("-parentgenesisblockhash", "The genesis blockhash of the parent chain.", false, OptionsCategory::CHAINPARAMS);
    gArgs.AddArg("-con_parentpowlimit", "The proof-of-work limit value for the parent chain.", false, OptionsCategory::CHAINPARAMS);
    gArgs.AddArg("-con_parent_chain_signblockscript", "Whether parent chain uses pow or signed blocks. If the parent chain uses signed blocks, the challenge (scriptPubKey) script. If not, an empty string. (default: empty script [ie parent uses pow])", false, OptionsCategory::CHAINPARAMS);

    gArgs.AddArg("-fedpegscript", "The script for the federated peg.", false, OptionsCategory::CHAINPARAMS);
}

static std::unique_ptr<CBaseChainParams> globalChainBaseParams;

const CBaseChainParams& BaseParams()
{
    assert(globalChainBaseParams);
    return *globalChainBaseParams;
}

std::unique_ptr<CBaseChainParams> CreateBaseChainParams(const std::string& chain)
{
    if (chain == CBaseChainParams::MAIN)
        return MakeUnique<CBaseChainParams>("", 8332, 18332);
    else if (chain == CBaseChainParams::TESTNET)
        return MakeUnique<CBaseChainParams>("testnet3", 18332, 8332);
    else if (chain == CBaseChainParams::REGTEST)
        return MakeUnique<CBaseChainParams>("regtest", 18443, 18332);

    // ELEMENTS:
    return MakeUnique<CBaseChainParams>(chain, 7041, 18332);
}

void SelectBaseParams(const std::string& chain)
{
    globalChainBaseParams = CreateBaseChainParams(chain);
    gArgs.SelectConfigNetwork(chain);
}
