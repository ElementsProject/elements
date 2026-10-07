// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2014 The Bitcoin developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_MAINCHAINRPC_H
#define BITCOIN_MAINCHAINRPC_H

#include <rpc/client.h>
#include <rpc/protocol.h>
#include <uint256.h>

#include <string>
#include <stdexcept>

#include <univalue.h>

class ArgsManager;

static const bool DEFAULT_NAMED=false;
static const char DEFAULT_RPCCONNECT[] = "127.0.0.1";
static const int DEFAULT_HTTP_CLIENT_TIMEOUT=900;
// Hard cap (in seconds) on the timeout of mainchain RPC calls made while
// validating peg-ins. These calls are issued synchronously while cs_main is
// held, so the cap bounds how long an unresponsive mainchain daemon can
// stall block connection and mempool acceptance.
static const int MAX_VALIDATION_RPC_TIMEOUT=30;

//
// Exception thrown on connection error.  This error is used to determine
// when to wait if -rpcwait is given.
//
class CConnectionFailed : public std::runtime_error
{
public:

    explicit inline CConnectionFailed(const std::string& msg) :
        std::runtime_error(msg)
    {}

};

// If timeout is negative (the default), the value of -mainchainrpctimeout
// (or DEFAULT_HTTP_CLIENT_TIMEOUT if unset) is used.
UniValue CallMainChainRPC(const std::string& strMethod, const UniValue& params, int timeout = -1);

// Returns the timeout to use for mainchain RPC calls made while validating
// peg-ins: the value of -mainchainrpctimeout clamped into the range
// [1, MAX_VALIDATION_RPC_TIMEOUT]. Note that a -mainchainrpctimeout of 0
// does not disable the timeout (libevent substitutes its own internal
// defaults), so it is clamped like any other out-of-range value.
int GetValidationRPCTimeout(const ArgsManager& argsman);

// Verify if the block with given hash has at least the specified minimum number
// of confirmations.
// For validating merkle blocks, you can provide the nbTxs parameter to verify if
// it equals the number of transactions in the block.
bool IsConfirmedBitcoinBlock(const uint256& hash, const int nMinConfirmationDepth, const int nbTxs);

#endif // BITCOIN_MAINCHAINRPC_H

