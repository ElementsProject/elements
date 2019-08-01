// Copyright (c) 2018-2019 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "ethaddress.h"
#include "crypto/ethash/keccak.hpp"
#include "utilstrencodings.h"

bool CEthAddress::Set(const CPubKey &pubKey)
{
    memset(vch, 0, sizeof(vch));
    if (pubKey.IsCompressed()) {
        return false;
    }
    auto hashBytes = ethash::keccak256(pubKey.begin() + 1, pubKey.size() - 1);
    memcpy(vch, hashBytes.bytes + 12, 20);
    return true;
}

bool CEthAddress::Set(const std::vector<unsigned char>& data)
{
    memset(vch, 0, sizeof(vch));
    if (data.size() != ETH_ADDRESS_SIZE) {
        return false;
    }
    memcpy(vch, &data[0], ETH_ADDRESS_SIZE);
    return true;
}

std::string CEthAddress::ToString() const
{
    return HexStr(vch, vch + ETH_ADDRESS_SIZE);
}
