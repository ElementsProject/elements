// Copyright (c) 2019 CommerceBlock developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "utilstrencodings.h"
#include "ethaddress.h"
#include "key.h"
#include "test/test_bitcoin.h"

#include <boost/foreach.hpp>
#include <boost/test/unit_test.hpp>

BOOST_FIXTURE_TEST_SUITE(ethaddress_tests, BasicTestingSetup)

BOOST_AUTO_TEST_CASE(ethaddress_ConstructEthAddress)
{
    std::vector<unsigned char> keyBytes = ParseHex("3ecb44df2159c26e0f995712d4f39b6f6e499b40749b1cf1246c37f9516cb6a4");
    CKey keyCompressed;
    keyCompressed.Set(keyBytes.begin(), keyBytes.end(), true);

    BOOST_CHECK_EQUAL(true, keyCompressed.IsValid());

    CPubKey pubkey = keyCompressed.GetPubKey();
    CEthAddress addr(pubkey);
    BOOST_CHECK_EQUAL(false, addr.IsValid());
    BOOST_CHECK_EQUAL("0397466f2b32bc3bb76d4741ae51cd1d8578b48d3f1e68da206d47321aec267ce7",
        HexStr(pubkey.begin(), pubkey.end()));

    pubkey.Decompress();
    CEthAddress addr2(pubkey);
    BOOST_CHECK_EQUAL(true, addr2.IsValid());
    BOOST_CHECK_EQUAL("8a40bfaa73256b60764c1bf40675a99083efb075", addr2.ToString());
    BOOST_CHECK_EQUAL("0497466f2b32bc3bb76d4741ae51cd1d8578b48d3f1e68da206d47321aec267ce78549b514e4453d74ef11b0cd5e4e4c364effddac8b51bcfc8de80682f952896f",
        HexStr(pubkey.begin(), pubkey.end()));

    CKey key;
    key.Set(keyBytes.begin(), keyBytes.end(), false);
    pubkey = key.GetPubKey();
    CEthAddress addr3(pubkey);
    BOOST_CHECK_EQUAL(true, addr3.IsValid());
    BOOST_CHECK_EQUAL("8a40bfaa73256b60764c1bf40675a99083efb075", addr3.ToString());
    BOOST_CHECK_EQUAL("0497466f2b32bc3bb76d4741ae51cd1d8578b48d3f1e68da206d47321aec267ce78549b514e4453d74ef11b0cd5e4e4c364effddac8b51bcfc8de80682f952896f",
        HexStr(pubkey.begin(), pubkey.end()));
}

BOOST_AUTO_TEST_SUITE_END()
