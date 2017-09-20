// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2015 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "chainparamsbase.h"

#include "tinyformat.h"
#include "util.h"

#include <assert.h>

const std::string CBaseChainParams::MAIN = CHAINPARAMS_OLD_MAIN;
const std::string CBaseChainParams::REGTEST = CHAINPARAMS_REGTEST;

void AppendParamsHelpMessages(std::string& strUsage, bool debugHelp)
{
    strUsage += HelpMessageGroup(_("Chain selection options:"));
    strUsage += HelpMessageOpt("-chain=<chain>", strprintf(_("Use the chain <chain> (default: %s). Allowed values: anything except %s"), CHAINPARAMS_CUSTOM, CHAINPARAMS_OLD_MAIN));
    if (debugHelp) {
        strUsage += HelpMessageOpt("-regtest", "Enter regression test mode, which uses a special chain in which blocks can be solved instantly. "
                                   "This is intended for regression testing tools and app development.");
    }
}

/**
 * Old Main network
 */
class CBaseMainParams : public CBaseChainParams
{
public:
    CBaseMainParams()
    {
        nRPCPort = 8332;
        strDataDir = CHAINPARAMS_OLD_MAIN;
    }
};

/**
 * Main network for elements
 */
class CBaseElementsParams : public CBaseChainParams
{
public:
    CBaseElementsParams()
    {
        nRPCPort = 9041;
        nMainchainRPCPort = 18332;
        strDataDir = CHAINPARAMS_ELEMENTS;
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
        nRPCPort = 7041;
        nMainchainRPCPort = 18332;
        strDataDir = CHAINPARAMS_REGTEST;
    }
};

/** Custom tests */
class CBaseCustomParams : public CBaseChainParams
{
public:
    CBaseCustomParams(const std::string& chain)
    {
        nRPCPort = 18332;
        strDataDir = chain;
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
    else if (chain == CHAINPARAMS_ELEMENTS)
        return std::unique_ptr<CBaseChainParams>(new CBaseElementsParams());
    else if (chain == CBaseChainParams::REGTEST)
        return std::unique_ptr<CBaseChainParams>(new CBaseRegTestParams());
    return std::unique_ptr<CBaseChainParams>(new CBaseCustomParams(chain));
}

void SelectBaseParams(const std::string& chain)
{
    globalChainBaseParams = CreateBaseChainParams(chain);
}

std::string ChainNameFromCommandLine()
{
    if (GetBoolArg("-testnet", false))
        throw std::runtime_error(strprintf("%s: Deprecated option -testnet: try -chain=%s instead.", __func__, CHAINPARAMS_CUSTOM));
    if (GetBoolArg("-regtest", false))
        return CBaseChainParams::REGTEST;
    return GetArg("-chain", CHAINPARAMS_CUSTOM);
}
