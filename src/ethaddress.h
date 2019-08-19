// Copyright (c) 2018-2019 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

//An implementation of Eth Addresses

#ifndef BITCOIN_ETHADDRESS_H
#define BITCOIN_ETHADDRESS_H

#include "uint256.h"
#include "pubkey.h"

class CEthAddress
{
public:
    static constexpr unsigned int ETH_ADDRESS_SIZE = 20;
private:
    unsigned char vch[ETH_ADDRESS_SIZE];
    bool fValid;
public:
    unsigned int size() const { return ETH_ADDRESS_SIZE; }
    const unsigned char* begin() const { return vch; }
    const unsigned char* end() const { return vch + size(); }
    const unsigned char& operator[](unsigned int pos) const { return vch[pos]; }

    inline int Compare(const CEthAddress& other) const { return memcmp(vch, other.vch, sizeof(vch)); }
    friend inline bool operator==(const CEthAddress& a, const CEthAddress& b) { return a.Compare(b) == 0; }
    friend inline bool operator!=(const CEthAddress& a, const CEthAddress& b) { return a.Compare(b) != 0; }

    bool Set(const CPubKey &pubKey);
    bool Set(const std::vector<unsigned char>& data);
    bool IsValid() { return fValid; };

    CEthAddress()
    {
        memset(vch, 0, sizeof(vch));
    }

    CEthAddress(const CPubKey &pubKey) { fValid = Set(pubKey); }
    CEthAddress(const std::vector<unsigned char>& data) { fValid = Set(data); }

    std::string ToString() const;
};

#endif // BITCOIN_ETHADDRESS_H
