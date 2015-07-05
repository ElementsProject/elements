// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2014 The Bitcoin developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "chainparamsbase.h"

#include "util.h"

#include <assert.h>

/**
 * Alpha (pegged to Testnet3)
 */
class CBaseAlphaParams : public CBaseChainParams
{
public:
    CBaseAlphaParams()
    {
        nRPCPort = 4241;
        strDataDir = "alpha";
    }
};
static CBaseAlphaParams alphaParams;

/**
 * Regression test
 */
class CBaseRegTestParams : public CBaseAlphaParams
{
public:
    CBaseRegTestParams()
    {
        strDataDir = "alpharegtest";
    }
};
static CBaseRegTestParams regTestParams;

static CBaseChainParams* pCurrentBaseParams = 0;

const CBaseChainParams& BaseParams()
{
    assert(pCurrentBaseParams);
    return *pCurrentBaseParams;
}

void SelectBaseParams(CBaseChainParams::Network network)
{
    switch (network) {
    case CBaseChainParams::MAIN:
    case CBaseChainParams::FAKE_MAIN:
        pCurrentBaseParams = &alphaParams;
        break;
    case CBaseChainParams::REGTEST:
        pCurrentBaseParams = &regTestParams;
        break;
    default:
        assert(false && "Unimplemented network");
        return;
    }
}

CBaseChainParams::Network NetworkIdFromCommandLine()
{
    bool fRegTest = GetBoolArg("-regtest", false);

    if (GetBoolArg("-testnet", false))
        return CBaseChainParams::MAX_NETWORK_TYPES;
    if (fRegTest)
        return CBaseChainParams::REGTEST;
    return CBaseChainParams::MAIN;
}

bool SelectBaseParamsFromCommandLine()
{
    CBaseChainParams::Network network = NetworkIdFromCommandLine();
    if (network == CBaseChainParams::MAX_NETWORK_TYPES)
        return false;

    SelectBaseParams(network);
    return true;
}

bool AreBaseParamsConfigured()
{
    return pCurrentBaseParams != NULL;
}
