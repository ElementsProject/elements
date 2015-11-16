// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2015 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "chainparamsbase.h"

#include "tinyformat.h"
#include "util.h"

#include <assert.h>

const std::string CBaseChainParams::MAIN = "main";
const std::string CBaseChainParams::REGTEST = "regtest";
const std::string CBaseChainParams::CUSTOM = "custom";

void AppendParamsHelpMessages(std::string& strUsage, bool debugHelp)
{
    strUsage += HelpMessageGroup(_("Chain selection options:"));
    strUsage += HelpMessageOpt("-chain=<chain>", _("Use the chain <chain> (default: main). Allowed values: main, testnet, regtest, custom"));
    if (debugHelp) {
        strUsage += HelpMessageOpt("-regtest", "Enter regression test mode, which uses a special chain in which blocks can be solved instantly. "
                                   "This is intended for regression testing tools and app development.");
        strUsage += HelpMessageGroup(_("Custom chain selection options (only for -chain=custom):"));
        strUsage += HelpMessageOpt("-chainpetname=<name>", _("Alternative name for custom chain (default: custom). This changes the genesis block."));
    }
}

/**
 * Main network
 */
class CBaseMainParams : public CBaseChainParams
{
public:
    CBaseMainParams()
    {
        nRPCPort = 8332;
    }
};

/**
 * Regression test
 */
class CBaseRegTestParams : public CBaseChainParams
{
public:
    CBaseRegTestParams()
    {
        nRPCPort = 18332;
        strDataDir = "regtest";
    }
};

/** Custom tests */
class CBaseCustomParams : public CBaseChainParams
{
public:
    CBaseCustomParams()
    {
        nRPCPort = 18332;
        strDataDir = "custom";
    }
};

static std::unique_ptr<CBaseChainParams> globalChainBaseParams;

const CBaseChainParams& BaseParams()
{
    assert(globalChainBaseParams);
    return *globalChainBaseParams;
}

std::unique_ptr<CBaseChainParams> CreateBaseChainParams(const std::string& chain)
{
    if (chain == CBaseChainParams::MAIN)
        return std::unique_ptr<CBaseChainParams>(new CBaseMainParams());
    else if (chain == CBaseChainParams::REGTEST)
        return std::unique_ptr<CBaseChainParams>(new CBaseRegTestParams());
    else if (chain == CBaseChainParams::CUSTOM)
        return std::unique_ptr<CBaseChainParams>(new CBaseCustomParams());
    else
        throw std::runtime_error(strprintf("%s: Unknown chain %s.", __func__, chain));
}

void SelectBaseParams(const std::string& chain)
{
    globalChainBaseParams = CreateBaseChainParams(chain);
}

std::string ChainNameFromCommandLine()
{
    if (GetBoolArg("-testnet", false))
        throw std::runtime_error(strprintf("%s: Invalid option -testnet: elements/%s is a testchain too.", __func__, CBaseChainParams::MAIN));
    if (GetBoolArg("-regtest", false))
        return CBaseChainParams::REGTEST;
    return GetArg("-chain", CBaseChainParams::MAIN);
}
