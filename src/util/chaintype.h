// Copyright (c) 2023 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#if defined(HAVE_CONFIG_H)
#include <config/bitcoin-config.h>
#endif

#ifndef BITCOIN_UTIL_CHAINTYPE_H
#define BITCOIN_UTIL_CHAINTYPE_H

#include <optional>
#include <string>

enum class ChainType {
    MAIN,
    TESTNET,
    TESTNET4,
    SIGNET,
    REGTEST,
    // ELEMENTS
    LIQUID1,
    LIQUID1TEST,
    LIQUIDTESTNET,
    CUSTOM,
};

std::string ChainTypeToString(ChainType chain);

std::optional<ChainType> ChainTypeFromString(std::string_view chain);

// ELEMENTS
struct ChainTypeMeta {
    ChainType chain_type;
    std::string chain_name;
};

ChainTypeMeta ChainTypeMetaFrom(std::string chain_name);
ChainTypeMeta ChainTypeMetaFrom(ChainType chain_type);

inline bool IsRegTest(ChainTypeMeta chain_type) {
    return chain_type.chain_name.find("regtest") != std::string::npos;
};

#endif // BITCOIN_UTIL_CHAINTYPE_H
