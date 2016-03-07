// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2015 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "chainparamsbase.h"

#include "tinyformat.h"
#include "util.h"

#include <boost/scoped_ptr.hpp>

const std::string CBaseChainParams::MAIN = CHAINPARAMS_OLD_MAIN;
const std::string CBaseChainParams::REGTEST = CHAINPARAMS_REGTEST;

void AppendParamsHelpMessages(std::string& strUsage, bool debugHelp)
{
    strUsage += HelpMessageGroup(_("Chain selection options:"));
    strUsage += HelpMessageOpt("-chain=<chain>", strprintf(_("Use the chain <chain> (default: %s). Allowed values: main, testnet, regtest"), CHAINPARAMS_ELEMENTS));
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
        strDataDir = CHAINPARAMS_REGTEST;
    }
};

static boost::scoped_ptr<CBaseChainParams> globalChainBaseParams;

const CBaseChainParams& BaseParams()
{
    assert(globalChainBaseParams.get());
    return *globalChainBaseParams;
}

CBaseChainParams* CBaseChainParams::Factory(const std::string& chain)
{
    if (chain == CBaseChainParams::MAIN)
        return new CBaseMainParams();
    else if (chain == CHAINPARAMS_ELEMENTS)
        return new CBaseElementsParams();
    else if (chain == CBaseChainParams::REGTEST)
        return new CBaseRegTestParams();
    else
        throw std::runtime_error(strprintf("%s: Unknown chain %s.", __func__, chain));
}

void SelectBaseParams(const std::string& chain)
{
    globalChainBaseParams.reset(CBaseChainParams::Factory(chain));
}

std::string ChainNameFromCommandLine()
{
    if (GetBoolArg("-testnet", false))
        throw std::runtime_error(strprintf("%s: Invalid option -testnet: elements/%s is a testchain too.", __func__, CHAINPARAMS_ELEMENTS));
    if (GetBoolArg("-regtest", false))
        return CBaseChainParams::REGTEST;
    return GetArg("-chain", CHAINPARAMS_ELEMENTS);
}

bool AreBaseParamsConfigured()
{
    return globalChainBaseParams.get();
}
