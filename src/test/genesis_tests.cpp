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
                      params->GenesisBlock().GetHash().GetHex());
    BOOST_CHECK_EQUAL(params->HashGenesisBlock().GetHex(),
                      "b811a5eeaf27432278c032a0b520f829be2b92fafff9789efe2755fff8ef547b");
    // Check that unittest genesis hash is same as the mainnet one
    const CChainParams *params2 = &Params();
    BOOST_CHECK_EQUAL(params2->HashGenesisBlock().GetHex(),
                      params2->GenesisBlock().GetHash().GetHex());
    BOOST_CHECK_EQUAL(params2->HashGenesisBlock().GetHex(),
                      "b811a5eeaf27432278c032a0b520f829be2b92fafff9789efe2755fff8ef547b");
}

// Goal: check that the standard testnet genesis block is computed correctly
BOOST_AUTO_TEST_CASE(genesis_testnet)
{
    SelectParams(CBaseChainParams::TESTNET);
    const CChainParams *params = &Params();
    BOOST_CHECK_EQUAL(params->HashGenesisBlock().GetHex(),
                      params->GenesisBlock().GetHash().GetHex());
    BOOST_CHECK_EQUAL(params->HashGenesisBlock().GetHex(),
                      "f7f0ca371b1003dc7346bab766b4a131f9e3a5d68820a364d70921cb15b95eaa");
    // Return params to base case for other tests
    SelectParams(CBaseChainParams::MAIN);
}

// Goal: check that the default regtest genesis block is computed correctly
BOOST_AUTO_TEST_CASE(genesis_regtest)
{
    SelectParams(CBaseChainParams::REGTEST);
    const CChainParams *params = &Params();
    BOOST_CHECK_EQUAL(params->HashGenesisBlock().GetHex(),
                      params->GenesisBlock().GetHash().GetHex());
    BOOST_CHECK_EQUAL(params->HashGenesisBlock().GetHex(),
                      "b41d03dc310957765223df2bf2f4b3609c79b8b6ac0a0764b20754f972d48b6c");
    // Return params to base case for other tests
    SelectParams(CBaseChainParams::MAIN);
}

// Goal: check that the replacing the signing script pubkey works correctly
BOOST_AUTO_TEST_CASE(genesis_customscript)
{
    CScript unsignable = CScript() << OP_FALSE;

    SelectParams(CBaseChainParams::MAIN, unsignable);
    const CChainParams *params1 = &Params();
    BOOST_CHECK_EQUAL(params1->HashGenesisBlock().GetHex(),
                      params1->GenesisBlock().GetHash().GetHex());
    BOOST_CHECK_EQUAL(params1->HashGenesisBlock().GetHex(),
                      "2ec431e3858cef95882cd7d627599fd757afa81938f0b886bee691a48b1e9b58");

    SelectParams(CBaseChainParams::TESTNET, unsignable);
    const CChainParams *params2 = &Params();
    BOOST_CHECK_EQUAL(params2->HashGenesisBlock().GetHex(),
                      params2->GenesisBlock().GetHash().GetHex());
    BOOST_CHECK_EQUAL(params2->HashGenesisBlock().GetHex(),
                      "e28e10e75c6f55edfdb914831b8d48c79fd858b6020963a038ee97dcaae2b355");

    SelectParams(CBaseChainParams::REGTEST, unsignable);
    const CChainParams *params3 = &Params();
    BOOST_CHECK_EQUAL(params3->HashGenesisBlock().GetHex(),
                      params3->GenesisBlock().GetHash().GetHex());
    BOOST_CHECK_EQUAL(params3->HashGenesisBlock().GetHex(),
                      "a99a962c80d71fe1eb0b30217a6f14bc571e3eee97bc16663cf42d9e22eb6cb2");

    // Return params to base case for other tests
    SelectParams(CBaseChainParams::MAIN);
}

BOOST_AUTO_TEST_SUITE_END()

