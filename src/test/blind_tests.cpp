// Copyright (c) 2011-2014 The Bitcoin Core developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "blind.h"
#include "coins.h"

#include <boost/test/unit_test.hpp>

BOOST_AUTO_TEST_SUITE(bind_tests)

BOOST_AUTO_TEST_CASE(naive_blinding_test)
{
    CCoinsView viewBase;
    CCoinsViewCache cache(&viewBase);

    CKey key1;
    CKey key2;

    unsigned char k1[32] = {1,2,3};
    unsigned char k2[32] = {22,33,44};
    key1.Set(&k1[0], &k1[32], true);
    key2.Set(&k2[0], &k2[32], true);
    CPubKey pubkey1 = key1.GetPubKey();
    CPubKey pubkey2 = key2.GetPubKey();

    uint256 blind3, blind4;

    {
        CCoinsModifier tx1 = cache.ModifyCoins(uint256(1));
        tx1->vout.resize(1);
        tx1->vout[0].nValue = 11;
    }

    {
        CCoinsModifier tx2 = cache.ModifyCoins(uint256(2));
        tx2->vout.resize(2);
        tx2->vout[0].nValue = 111;
    }

    {
        // Build a transaction that spends 2 unblinded coins (11, 111), and produces a single blinded one (100) and fee (22).
        CMutableTransaction tx3;
        tx3.vin.resize(2);
        tx3.vin[0].prevout.hash = uint256(1);

        tx3.vin[0].prevout.n = 0;
        tx3.vin[1].prevout.hash = uint256(2);
        tx3.vin[1].prevout.n = 0;
        tx3.vout.resize(1);
        tx3.vout[0].nValue = 100;
        // tx3.nTxFee = 22;
        // BOOST_CHECK(cache.VerifyAmounts(tx3));

        std::vector<uint256> input_blinds;
        std::vector<uint256> output_blinds;
        std::vector<CPubKey> output_pubkeys;
        input_blinds.push_back(uint256());
        input_blinds.push_back(uint256());
        output_blinds.push_back(uint256());
        output_pubkeys.push_back(pubkey1);
        BlindOutputs(input_blinds, output_blinds, output_pubkeys, tx3);
        BOOST_CHECK(!tx3.vout[0].nValue.IsAmount());
        // BOOST_CHECK(cache.VerifyAmounts(tx3));

        CAmount unblinded_amount;
        BOOST_CHECK(UnblindOutput(key2, tx3.vout[0], unblinded_amount, blind3) == 0);
        BOOST_CHECK(UnblindOutput(key1, tx3.vout[0], unblinded_amount, blind3) == 1);
        BOOST_CHECK(unblinded_amount == 100);

        CCoinsModifier in3 = cache.ModifyCoins(uint256(3));
        in3->vout.resize(1);
        in3->vout[0] = tx3.vout[0];

        // tx3.nTxFee--;
        BOOST_CHECK(!cache.VerifyAmounts(tx3));
    }

    {
        // Build a transactions that spends an unblinded (111) and blinded (100) coin, and produces a blinded (30), unblinded (40), and blinded (50) coin and fee (91)
        CMutableTransaction tx4;
        tx4.vin.resize(2);
        tx4.vin[0].prevout.hash = uint256(2);
        tx4.vin[0].prevout.n = 0;
        tx4.vin[1].prevout.hash = uint256(3);
        tx4.vin[1].prevout.n = 0;
        tx4.vout.resize(3);
        tx4.vout[0].nValue = 30;
        tx4.vout[1].nValue = 40;
        tx4.vout[2].nValue = 50;
        // tx4.nTxFee = 100 + 111 - 30 - 40 - 50;
        // BOOST_CHECK(cache.VerifyAmounts(tx4));

        std::vector<uint256> input_blinds;
        std::vector<uint256> output_blinds;
        std::vector<CPubKey> output_pubkeys;
        input_blinds.push_back(uint256());
        input_blinds.push_back(blind3);
        output_blinds.push_back(uint256());
        output_blinds.push_back(uint256());
        output_blinds.push_back(uint256());
        output_pubkeys.push_back(pubkey2);
        output_pubkeys.push_back(CPubKey());
        output_pubkeys.push_back(pubkey2);
        BlindOutputs(input_blinds, output_blinds, output_pubkeys, tx4);
        BOOST_CHECK(!tx4.vout[0].nValue.IsAmount());
        BOOST_CHECK(tx4.vout[1].nValue.IsAmount());
        BOOST_CHECK(!tx4.vout[2].nValue.IsAmount());
        // BOOST_CHECK(cache.VerifyAmounts(tx4));

        CAmount unblinded_amount;
        BOOST_CHECK(UnblindOutput(key1, tx4.vout[0], unblinded_amount, blind4) == 0);
        BOOST_CHECK(UnblindOutput(key2, tx4.vout[0], unblinded_amount, blind4) == 1);
        BOOST_CHECK(unblinded_amount == 30);
        BOOST_CHECK(UnblindOutput(key2, tx4.vout[2], unblinded_amount, blind4) == 1);
        BOOST_CHECK(unblinded_amount == 50);

        CCoinsModifier in4 = cache.ModifyCoins(uint256(4));
        in4->vout.resize(3);
        in4->vout[0] = tx4.vout[0];
        in4->vout[1] = tx4.vout[1];
        in4->vout[2] = tx4.vout[2];

        // tx4.nTxFee--;
        BOOST_CHECK(!cache.VerifyAmounts(tx4));
    }
}

BOOST_AUTO_TEST_SUITE_END()
