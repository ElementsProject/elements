// Copyright (c) 2018-2019 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

//An implementation of Eth Addresses

#ifndef BITCOIN_ETHADDRESS_H
#define BITCOIN_ETHADDRESS_H

#include "pubkey.h"

class CEthAddress
{
public:
    static constexpr unsigned int ETH_ADDRESS_SIZE = 20;

private:
    unsigned char vch[ETH_ADDRESS_SIZE];
    bool fValid;

public:
    std::string ToString() const;

    bool Set(const CPubKey &pubKey);
    bool IsValid() { return fValid; };

    CEthAddress() {}
    CEthAddress(const CPubKey &pubKey) { fValid = Set(pubKey); }
};

#endif // BITCOIN_ETHADDRESS_H
