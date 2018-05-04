// Copyright (c) 2014-2015 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_CHAINPARAMSBASE_H
#define BITCOIN_CHAINPARAMSBASE_H

#include <memory>
#include <string>
#include <vector>

#define CHAINPARAMS_OLD_MAIN "___old_main"
#define CHAINPARAMS_OCEAN_MAIN "ocean_main"
#define CHAINPARAMS_REGTEST "elementsregtest"

/**
 * CBaseChainParams defines the base parameters (shared between bitcoin-cli and bitcoind)
 * of a given instance of the Bitcoin system.
 */
class CBaseChainParams
{
public:
    static const std::string MAIN;
    static const std::string REGTEST;

    const std::string& DataDir() const { return strDataDir; }
    int RPCPort() const { return nRPCPort; }
    int MainchainRPCPort() const { return nMainchainRPCPort; }
    CBaseChainParams() = delete;
    CBaseChainParams(const std::string& data_dir, int rpc_port, int mainchain_rpc_port) :
        nRPCPort(rpc_port), nMainchainRPCPort(mainchain_rpc_port), strDataDir(data_dir) {}

private:
    int nRPCPort;
    int nMainchainRPCPort;
    std::string strDataDir;
};

/**
 * Creates and returns a std::unique_ptr<CBaseChainParams> of the chosen chain.
 * @returns a CBaseChainParams* of the chosen chain.
 * @throws a std::runtime_error if the chain is not supported.
 */
std::unique_ptr<CBaseChainParams> CreateBaseChainParams(const std::string& chain);

/**
 * Append the help messages for the chainparams options to the
 * parameter string.
 */
void AppendParamsHelpMessages(std::string& strUsage, bool debugHelp=true);

/**
 * Return the currently selected parameters. This won't change after app
 * startup, except for unit tests.
 */
const CBaseChainParams& BaseParams();

/** Sets the params returned by Params() to those for the given network. */
void SelectBaseParams(const std::string& chain);

/**
 * Looks for -regtest, -testnet and returns the appropriate BIP70 chain name.
 * @return CBaseChainParams::MAX_NETWORK_TYPES if an invalid combination is given. CBaseChainParams::MAIN by default.
 */
std::string ChainNameFromCommandLine();

#endif // BITCOIN_CHAINPARAMSBASE_H
