// Copyright (c) 2017 Pieter Wuille
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <blech32.h>
#include <random.h>
#include <util/strencodings.h>

#include <boost/test/unit_test.hpp>

BOOST_AUTO_TEST_SUITE(blech32_tests)

BOOST_AUTO_TEST_CASE(blech32_polymod_sanity)
{
    std::vector<unsigned char> data(40);
    // GetRandBytes only allows 32 bytes at a time
    GetRandBytes(data.data(), 32);
    GetRandBytes(data.data() + 32, data.size() - 32);

    std::vector<unsigned char> base32;
    ConvertBits<8, 5, true>([&](unsigned char c) { base32.push_back(c); }, data.begin(), data.end());
    uint64_t plm1 = blech32::PolyMod(base32);

    // Now add 1023 zeros.
    for (auto i = 0; i < 1023; i++) {
        base32.push_back(0);
    }
    uint64_t plm2 = blech32::PolyMod(base32);

    BOOST_CHECK_EQUAL(plm1, plm2);
}

BOOST_AUTO_TEST_CASE(blech32_checksum)
{
    std::vector<unsigned char> vector{7,2,3,4,5,6,7,8,9,234,123,213,16};
    std::vector<unsigned char> b32;
    ConvertBits<8, 5, true>([&](unsigned char c) { b32.push_back(c); }, vector.begin(), vector.end());
    std::vector<unsigned char> cs = blech32::CreateChecksum("lq", b32);

    std::vector<unsigned char> expected_cs{22,13,13,5,4,4,23,7,28,21,30,12};
    for (size_t i = 0; i < expected_cs.size(); i++) {
        BOOST_CHECK_EQUAL(expected_cs[i], cs[i]);
    }
}

BOOST_AUTO_TEST_SUITE_END()

