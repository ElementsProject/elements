// Copyright (c) 2017 Pieter Wuille
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <blech32.cpp>
#include <random.h>
#include <utilstrencodings.h>
#include <test/test_bitcoin.h>

#include <boost/test/unit_test.hpp>

BOOST_FIXTURE_TEST_SUITE(blech32_tests, BasicTestingSetup)

BOOST_AUTO_TEST_CASE(blech32_polymod_sanity)
{
    std::vector<unsigned char> data(40);
    GetRandBytes(data.data(), data.size());

    std::vector<unsigned char> base32;
    ConvertBits<8, 5, true>([&](unsigned char c) { base32.push_back(c); }, data.begin(), data.end());
    uint64_t plm1 = PolyMod(base32);

    // Now add 1023 zeros.
    for (auto i = 0; i < 1023; i++) {
        base32.push_back(0);
    }
    uint64_t plm2 = PolyMod(base32);

    BOOST_CHECK_EQUAL(plm1, plm2);
}

BOOST_AUTO_TEST_SUITE_END()

