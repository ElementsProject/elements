// Copyright (c) 2011-2014 The Bitcoin Core developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "chainparams.h"
#include "uint256.h"
#include "utilstrencodings.h"

#include <boost/test/unit_test.hpp>

BOOST_AUTO_TEST_SUITE(genesis_tests)

// Goal: check that the standard mainnet genesis block is computed correctly
BOOST_AUTO_TEST_CASE(genesis_mainnet)
{
    SelectParams(CBaseChainParams::MAIN);
    const CChainParams *params = &Params();
    BOOST_CHECK_EQUAL(params->HashGenesisBlock().GetHex(),
                      "b811a5eeaf27432278c032a0b520f829be2b92fafff9789efe2755fff8ef547b");
    // Check that unittest genesis hash is same as the mainnet one
    const CChainParams *params2 = &Params();
    BOOST_CHECK_EQUAL(params2->HashGenesisBlock().GetHex(),
                      "b811a5eeaf27432278c032a0b520f829be2b92fafff9789efe2755fff8ef547b");
}

// Goal: check that the standard testnet genesis block is computed correctly
BOOST_AUTO_TEST_CASE(genesis_testnet)
{
    SelectParams(CBaseChainParams::TESTNET);
    const CChainParams *params = &Params();
    BOOST_CHECK_EQUAL(params->HashGenesisBlock().GetHex(),
                      "f7f0ca371b1003dc7346bab766b4a131f9e3a5d68820a364d70921cb15b95eaa");
    // Return params to base case for other tests
    SelectParams(CBaseChainParams::UNITTEST);
}

// Goal: check that the default regtest genesis block is computed correctly
BOOST_AUTO_TEST_CASE(genesis_regtest)
{
    SelectParams(CBaseChainParams::REGTEST);
    const CChainParams *params1 = &Params();
    BOOST_CHECK_EQUAL(params1->HashGenesisBlock().GetHex(),
                      "b41d03dc310957765223df2bf2f4b3609c79b8b6ac0a0764b20754f972d48b6c");
    // Return params to base case for other tests
    SelectParams(CBaseChainParams::UNITTEST);
}

BOOST_AUTO_TEST_SUITE_END()

