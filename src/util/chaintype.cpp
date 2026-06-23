// Copyright (c) 2023 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#if defined(HAVE_CONFIG_H)
#include <config/bitcoin-config.h>
#endif

#include <util/chaintype.h>

#include <cassert>
#include <optional>
#include <string>

std::string ChainTypeToString(ChainType chain)
{
    switch (chain) {
    case ChainType::MAIN:
        return "main";
    case ChainType::TESTNET:
        return "test";
    case ChainType::TESTNET4:
        return "testnet4";
    case ChainType::SIGNET:
        return "signet";
    case ChainType::REGTEST:
        return "regtest";
    case ChainType::LIQUID1:
        return "liquidv1";
    case ChainType::LIQUID1TEST:
        return "liquidv1test";
    case ChainType::LIQUIDTESTNET:
        return "liquidtestnet";
    case ChainType::CUSTOM:
        return "custom";
    }
    assert(false);
}

std::optional<ChainType> ChainTypeFromString(std::string_view chain)
{
    if (chain == "main") {
        return ChainType::MAIN;
    } else if (chain == "test") {
        return ChainType::TESTNET;
    } else if (chain == "testnet4") {
        return ChainType::TESTNET4;
    } else if (chain == "signet") {
        return ChainType::SIGNET;
    } else if (chain == "regtest") {
        return ChainType::REGTEST;
    } else if (chain == "liquidv1") {
        return ChainType::LIQUID1;
    } else if (chain == "liquidv1test") {
        return ChainType::LIQUID1TEST;
    } else if (chain == "liquidtestnet") {
        return ChainType::LIQUIDTESTNET;
    } else {
        return std::nullopt;
    }
}

// ELEMENTS
ChainTypeMeta ChainTypeMetaFrom(std::string chain_name) {
    if (auto chain = ChainTypeFromString(chain_name)) {
        return { *chain, chain_name };
    }

    return { ChainType::CUSTOM, chain_name };
}

ChainTypeMeta ChainTypeMetaFrom(ChainType chain_type) {
    return { chain_type, ChainTypeToString(chain_type) };
}
