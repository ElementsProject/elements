// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_OUTPUTTYPE_H
#define BITCOIN_OUTPUTTYPE_H

#include <script/signingprovider.h>
#include <script/standard.h>

#include <array>
#include <optional>
#include <string>
#include <vector>

enum class OutputType {
    LEGACY,
    P2SH_SEGWIT,
    BECH32,
    BECH32M,
    UNKNOWN,
};

static constexpr auto OUTPUT_TYPES = std::array{
    OutputType::LEGACY,
    OutputType::P2SH_SEGWIT,
    OutputType::BECH32,
    OutputType::BECH32M,
};

std::optional<OutputType> ParseOutputType(const std::string& str);
const std::string& FormatOutputType(OutputType type);

/**
 * Get a destination of the requested type (if possible) to the specified key.
 * The caller must make sure LearnRelatedScripts has been called beforehand.
 */
CTxDestination GetDestinationForKey(const CPubKey& key, OutputType);

/** Get all destinations (potentially) supported by the wallet for the given key. */
std::vector<CTxDestination> GetAllDestinationsForKey(const CPubKey& key);

/**
 * Get a destination of the requested type (if possible) to the specified script.
 * This function will automatically add the script (and any other
 * necessary scripts) to the keystore.
 */
CTxDestination AddAndGetDestinationForScript(FillableSigningProvider& keystore, const CScript& script, OutputType);

/** Get the OutputType for a CTxDestination */
std::optional<OutputType> OutputTypeFromDestination(const CTxDestination& dest);

#endif // BITCOIN_OUTPUTTYPE_H
