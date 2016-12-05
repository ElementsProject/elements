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
                      "4d055eb17dad11aec976bc4b46b2708f91aac0ffedb3b9a3f3451b64d106a9a6");
}

// Goal: check that the standard testnet genesis block is computed correctly
BOOST_AUTO_TEST_CASE(genesis_testnet)
{
    SelectParams(CBaseChainParams::TESTNET);
    const CChainParams *params = &Params();
    BOOST_CHECK_EQUAL(params->HashGenesisBlock().GetHex(),
                      params->GenesisBlock().GetHash().GetHex());
    BOOST_CHECK_EQUAL(params->HashGenesisBlock().GetHex(),
                      "ad5cb13bc360f0cbc4ba3dca881e6a771d05052469edb73e54956b5225918846");
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
                      "095cdb4b50450887a3fba5fa77bdd7ce969868b78e2e7a75886d8e324c9e331d");
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
                      "431a10b6cfd6b593adcc1f243b348042a3d46efdf9ac7c939994647349754d21");

    SelectParams(CBaseChainParams::TESTNET, unsignable);
    const CChainParams *params2 = &Params();
    BOOST_CHECK_EQUAL(params2->HashGenesisBlock().GetHex(),
                      params2->GenesisBlock().GetHash().GetHex());
    BOOST_CHECK_EQUAL(params2->HashGenesisBlock().GetHex(),
                      "24e37fa582f78e10706be56a3ad166d92517c9eab9bbf9861fd5d6b6ac3d560b");

    SelectParams(CBaseChainParams::REGTEST, unsignable);
    const CChainParams *params3 = &Params();
    BOOST_CHECK_EQUAL(params3->HashGenesisBlock().GetHex(),
                      params3->GenesisBlock().GetHash().GetHex());
    BOOST_CHECK_EQUAL(params3->HashGenesisBlock().GetHex(),
                      "dac4000e5ed09f558c27b442c555f4ea4fa8ce60e11d39898881412741c571a5");

    // Return params to base case for other tests
    SelectParams(CBaseChainParams::MAIN);
}

BOOST_AUTO_TEST_SUITE_END()

