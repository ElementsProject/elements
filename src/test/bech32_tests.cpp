// Copyright (c) 2017 Pieter Wuille
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <bech32.h>
#include <test/util/setup_common.h>
#include <test/util/str.h>

#include <boost/test/unit_test.hpp>

BOOST_FIXTURE_TEST_SUITE(bech32_tests, BasicTestingSetup)

BOOST_AUTO_TEST_CASE(bip173_testvectors_valid)
{
    static const std::string CASES[] = {
        "A12UEL5L",
        "a12uel5l",
        "an83characterlonghumanreadablepartthatcontainsthenumber1andtheexcludedcharactersbio1tt5tgs",
        "abcdef1qpzry9x8gf2tvdw0s3jn54khce6mua7lmqqqxw",
        "11qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqc8247j",
        "split1checkupstagehandshakeupstreamerranterredcaperred2y9e3w",
        "?1ezyfcl",
    };
    for (const std::string& str : CASES) {
        const auto dec = bech32::Decode(str);
        BOOST_CHECK(dec.encoding == bech32::Encoding::BECH32);
        std::string recode = bech32::Encode(bech32::Encoding::BECH32, dec.hrp, dec.data);
        BOOST_CHECK(!recode.empty());
        BOOST_CHECK(CaseInsensitiveEqual(str, recode));
    }
}

BOOST_AUTO_TEST_CASE(bip173_testvectors_invalid)
{
    static const std::string CASES[] = {
        " 1nwldj5",
        "\x7f""1axkwrx",
        "\x80""1eym55h",
        "an84characterslonghumanreadablepartthatcontainsthenumber1andtheexcludedcharactersbio1569pvx",
        "pzry9x0s0muk",
        "1pzry9x0s0muk",
        "x1b4n0q5v",
        "li1dgmt3",
        "de1lg7wt\xff",
        "A1G7SGD8",
        "10a06t8",
        "1qzzfhee",
        "a12UEL5L",
        "A12uEL5L",
    };
    for (const std::string& str : CASES) {
        const auto dec = bech32::Decode(str);
        BOOST_CHECK(dec.encoding != bech32::Encoding::BECH32);
    }
}

BOOST_AUTO_TEST_CASE(bech32_polymod_sanity)
{
    std::vector<unsigned char> data(40);
    // GetRandBytes only allows 32 bytes at a time
    GetRandBytes(data.data(), 32);
    GetRandBytes(data.data() + 32, data.size() - 32);

    std::vector<unsigned char> base32;
    ConvertBits<8, 5, true>([&](unsigned char c) { base32.push_back(c); }, data.begin(), data.end());
    uint64_t plm1 = bech32::PolyMod(base32);

    // Now add 1023 zeros.
    for (auto i = 0; i < 1023; i++) {
        base32.push_back(0);
    }
    uint64_t plm2 = bech32::PolyMod(base32);

    BOOST_CHECK_EQUAL(plm1, plm2);
}

BOOST_AUTO_TEST_SUITE_END()
