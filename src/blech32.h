// Copyright (c) 2017 Pieter Wuille
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// Bech32 and Bech32m are string encoding formats used in newer
// address types. The outputs consist of a human-readable part
// (alphanumeric), a separator character (1), and a base32 data
// section, the last 6 characters of which are a checksum. The
// module is namespaced under bech32 for historical reasons.
//
// For more information, see BIP 173 and BIP 350.

#ifndef BITCOIN_BLECH32_H
#define BITCOIN_BLECH32_H

#include <stdint.h>
#include <string>
#include <vector>

namespace blech32
{

enum class Encoding {
    INVALID,  //!< Failed decoding

    BLECH32,  //!< Original blech32
    BLECH32M, //!< Blech32m tweaked a la bech32
};

/** Encode a Blech32 or Blech32m string. If hrp contains uppercase characters, this will cause an
 *  assertion error. Encoding must be one of BLECH32 or BLECH32M. */
std::string Encode(Encoding encoding, const std::string& hrp, const std::vector<uint8_t>& values);

struct DecodeResult
{
    Encoding encoding;         //!< What encoding was detected in the result; Encoding::INVALID if failed.
    std::string hrp;           //!< The human readable part
    std::vector<uint8_t> data; //!< The payload (excluding checksum)

    DecodeResult() : encoding(Encoding::INVALID) {}
    DecodeResult(Encoding enc, std::string&& h, std::vector<uint8_t>&& d) : encoding(enc), hrp(std::move(h)), data(std::move(d)) {}
};

/** Decode a Blech32 or Blech32m string */
DecodeResult Decode(const std::string& str);

/// Exported for testing.
uint64_t PolyMod(const std::vector<uint8_t>& v);
/// Exported for testing.
std::vector<uint8_t> CreateChecksum(Encoding encoding, const std::string& hrp, const std::vector<uint8_t>& values);

} // namespace blech32

#endif // BITCOIN_BLECH32_H
