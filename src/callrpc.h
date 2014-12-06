// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2014 The Bitcoin developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_CALLRPC_H
#define BITCOIN_CALLRPC_H

#include "rpcclient.h"
#include "rpcprotocol.h"
#include "uint256.h"

#include <string>

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

json_spirit::Object CallRPC(const std::string& strMethod, const json_spirit::Array& params, std::string port="");
bool IsConfirmedBitcoinBlock(const uint256& hash, int nMinConfirmationDepth);

#endif // BITCOIN_CALLRPC_H
