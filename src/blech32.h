// Copyright (c) 2017 Pieter Wuille
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// Blech32 is a string encoding format used in newer address types.
// The output consists of a human-readable part (alphanumeric), a
// separator character (1), and a base32 data section, the last
// 12 characters of which are a checksum.

#ifndef BITCOIN_BLECH32_H
#define BITCOIN_BLECH32_H

#include <stdint.h>
#include <string>
#include <vector>

namespace blech32
{

/** Encode a Blech32 string. Returns the empty string in case of failure. */
std::string Encode(const std::string& hrp, const std::vector<uint8_t>& values);

/** Decode a Blech32 string. Returns (hrp, data). Empty hrp means failure. */
std::pair<std::string, std::vector<uint8_t>> Decode(const std::string& str);

/// Exported for testing.
uint64_t PolyMod(const std::vector<uint8_t>& v);
/// Exported for testing.
std::vector<uint8_t> CreateChecksum(const std::string& hrp, const std::vector<uint8_t>& values);

} // namespace blech32

#endif // BITCOIN_BLECH32_H
