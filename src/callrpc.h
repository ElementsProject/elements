// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2014 The Bitcoin developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_CALLRPC_H
#define BITCOIN_CALLRPC_H

#include "rpc/client.h"
#include "rpc/protocol.h"
#include "uint256.h"

#include <string>
#include <stdexcept>

//#include <univalue.h>
#include "univalue/include/univalue.h"

static const bool DEFAULT_NAMED=false;
static const char DEFAULT_RPCCONNECT[] = "127.0.0.1";
static const int DEFAULT_HTTP_CLIENT_TIMEOUT=900;

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

UniValue CallRPC(const std::string& strMethod, const UniValue& params, bool connectToMainchain=false);
bool IsConfirmedBitcoinBlock(const uint256& hash, int nMinConfirmationDepth);

#endif // BITCOIN_CALLRPC_H
