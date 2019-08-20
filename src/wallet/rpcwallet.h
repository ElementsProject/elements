// Copyright (c) 2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_WALLET_RPCWALLET_H
#define BITCOIN_WALLET_RPCWALLET_H

#include <univalue.h>

class CRPCTable;

void RegisterWalletRPCCommands(CRPCTable &t);

UniValue RemoveKYCPubKey(const CPubKey& kycPubKey);

#endif //BITCOIN_WALLET_RPCWALLET_H
