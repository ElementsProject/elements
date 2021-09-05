// Copyright (c) 2017 Pieter Wuille
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <blech32.h>
#include <random.h>
#include <util/strencodings.h>
#include <test/util/setup_common.h>
#include <test/util/str.h>

#include <boost/test/unit_test.hpp>

BOOST_AUTO_TEST_SUITE(blech32_tests)

BOOST_AUTO_TEST_CASE(blech32_testvectors_valid)
{
    static const std::string CASES[] = {
        "A133NZFWEYK7UT",
        "a133nzfweyk7ut",
        "an83characterlonghumanreadablepartthatcontainsthenumber1andtheexcludedcharactersbio195jhgldwsn5j",
        "abcdef1qpzry9x8gf2tvdw0s3jn54khce6mua7lgmcn7l7t7xve",
        "11qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq3xldwlutcw2l",
        "split1checkupstagehandshakeupstreamerranterredcaperredegneyqml9esp",
        "?19dv34t3p4s35",
    };
    for (const std::string& str : CASES) {
        const auto dec = blech32::Decode(str);
        BOOST_CHECK(dec.encoding == blech32::Encoding::BLECH32);
        std::string recode = blech32::Encode(blech32::Encoding::BLECH32, dec.hrp, dec.data);
        BOOST_CHECK(!recode.empty());
        BOOST_CHECK(CaseInsensitiveEqual(str, recode));
    }
}

BOOST_AUTO_TEST_CASE(blech32m_testvectors_valid)
{
    static const std::string CASES[] = {
        "A1EYL4VXQ3HRPT",
        "a1eyl4vxq3hrpt",
        "an83characterlonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber11yatn6l85muud",
        "abcdef1l7aum6echk45nj3s0wdvt2fg8x9yrzpqg8m5pqg67zq3",
        "11llllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllllll09wxh8ajdvxv",
        "split1checkupstagehandshakeupstreamerranterredcaperred3alwpgz2yydp",
        "?1dcqxsrg55dv5"
    };
    for (const std::string& str : CASES) {
        const auto dec = blech32::Decode(str);
        BOOST_CHECK(dec.encoding == blech32::Encoding::BLECH32M);
        std::string recode = blech32::Encode(blech32::Encoding::BLECH32M, dec.hrp, dec.data);
        BOOST_CHECK(!recode.empty());
        BOOST_CHECK(CaseInsensitiveEqual(str, recode));
    }
}

BOOST_AUTO_TEST_CASE(blech32m_testvectors_invalid)
{
    static const std::string CASES[] = {
        " 1xj0phk",
        "\x7f""1g6xzxy",
        "\x80""1vctc34",
        "an84characterslonghumanreadablepartthatcontainsthetheexcludedcharactersbioandnumber11d6pts4",
        "qyrz8wqd2c9m",
        "1qyrz8wqd2c9m",
        "y1b0jsk6g",
        "lt1igcx5c0",
        "in1muywd",
        "mm1crxm3i",
        "au1s5cgom",
        "M1VUXWEZ",
        "16plkw9",
        "1p2gdwpf"
    };
    for (const std::string& str : CASES) {
        const auto dec = blech32::Decode(str);
        BOOST_CHECK(dec.encoding == blech32::Encoding::INVALID);
    }
}

BOOST_AUTO_TEST_CASE(blech32_testvectors_invalid)
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
        const auto dec = blech32::Decode(str);
        BOOST_CHECK(dec.encoding == blech32::Encoding::INVALID);
    }
}

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
    std::vector<unsigned char> cs = blech32::CreateChecksum(blech32::Encoding::BLECH32, "lq", b32);

    std::vector<unsigned char> expected_cs{22,13,13,5,4,4,23,7,28,21,30,12};
    for (size_t i = 0; i < expected_cs.size(); i++) {
        BOOST_CHECK_EQUAL(expected_cs[i], cs[i]);
    }
}

BOOST_AUTO_TEST_SUITE_END()

