// Copyright (c) 2011-2014 The Bitcoin Core developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "arith_uint256.h"
#include "blind.h"
#include "coins.h"
#include "uint256.h"
#include "wallet/wallet.h"
#include "main.h"

#include "test/test_bitcoin.h"

#include <boost/test/unit_test.hpp>


BOOST_FIXTURE_TEST_SUITE(blind_tests, TestingSetup)

#ifdef ENABLE_WALLET
static CWallet wallet;
#endif

BOOST_AUTO_TEST_CASE(naive_blinding_test)
{
    CCoinsView viewBase;
    CCoinsViewCache cache(&viewBase);

    CKey key1;
    CKey key2;
    CKey keyDummy;

    unsigned char k1[32] = {1,2,3};
    unsigned char k2[32] = {22,33,44};
    unsigned char kDummy[32] = {133,144,155};
    key1.Set(&k1[0], &k1[32], true);
    key2.Set(&k2[0], &k2[32], true);
    keyDummy.Set(&kDummy[0], &kDummy[32], true);
    CPubKey pubkey1 = key1.GetPubKey();
    CPubKey pubkey2 = key2.GetPubKey();
    CPubKey pubkeyDummy = keyDummy.GetPubKey();

    uint256 blind3, blind4, blindDummy;

    {
        CCoinsModifier tx1 = cache.ModifyCoins(ArithToUint256(1));
        tx1->vout.resize(1);
        tx1->vout[0].nValue = 11;
    }

    {
        CCoinsModifier tx2 = cache.ModifyCoins(ArithToUint256(2));
        tx2->vout.resize(2);
        tx2->vout[0].nValue = 111;
    }

    {
        // Build a transaction that spends 2 unblinded coins (11, 111), and produces a single blinded one (100) and fee (22).
        CMutableTransaction tx3;
        tx3.vin.resize(2);
        tx3.vin[0].prevout.hash = ArithToUint256(1);

        tx3.vin[0].prevout.n = 0;
        tx3.vin[1].prevout.hash = ArithToUint256(2);
        tx3.vin[1].prevout.n = 0;
        tx3.vout.resize(1);
        tx3.vout[0].nValue = 100;
        tx3.nTxFee = 22;
        BOOST_CHECK(VerifyAmounts(cache, tx3, tx3.nTxFee));

        // Try to blind with a single output, which fails as its blinding factor ends up being zero.
        std::vector<uint256> input_blinds;
        std::vector<uint256> output_blinds;
        std::vector<CPubKey> output_pubkeys;
        input_blinds.push_back(uint256());
        input_blinds.push_back(uint256());
        output_blinds.push_back(uint256());
        output_pubkeys.push_back(pubkey1);
        BOOST_CHECK(!BlindOutputs(input_blinds, output_blinds, output_pubkeys, tx3));

        // Add a dummy output.
        tx3.vout.resize(2);
        tx3.vout[1].nValue = 0;
        output_blinds.push_back(uint256());
        output_pubkeys.push_back(pubkeyDummy);
        BOOST_CHECK(BlindOutputs(input_blinds, output_blinds, output_pubkeys, tx3));
        BOOST_CHECK(!tx3.vout[0].nValue.IsAmount());
        BOOST_CHECK(!tx3.vout[1].nValue.IsAmount());
        BOOST_CHECK(VerifyAmounts(cache, tx3, tx3.nTxFee));

        CAmount unblinded_amount;
        BOOST_CHECK(UnblindOutput(key2, tx3.vout[0], unblinded_amount, blind3) == 0);
        BOOST_CHECK(UnblindOutput(key1, tx3.vout[0], unblinded_amount, blind3) == 1);
        BOOST_CHECK(unblinded_amount == 100);
        BOOST_CHECK(UnblindOutput(keyDummy, tx3.vout[1], unblinded_amount, blindDummy) == 1);
        BOOST_CHECK(unblinded_amount == 0);

        CCoinsModifier in3 = cache.ModifyCoins(ArithToUint256(3));
        in3->vout.resize(2);
        in3->vout[0] = tx3.vout[0];
        in3->vout[1] = tx3.vout[1];

        tx3.nTxFee--;
        BOOST_CHECK(!VerifyAmounts(cache, tx3, tx3.nTxFee));
    }

    {
        // Build a transactions that spends an unblinded (111) and blinded (100) coin, and produces only unblinded coins (impossible)
        CMutableTransaction tx4;
        tx4.vin.resize(2);
        tx4.vin[0].prevout.hash = ArithToUint256(2);
        tx4.vin[0].prevout.n = 0;
        tx4.vin[1].prevout.hash = ArithToUint256(3);
        tx4.vin[1].prevout.n = 0;
        tx4.vout.resize(2);
        tx4.vout[0].nValue = 30;
        tx4.vout[1].nValue = 40;
        tx4.nTxFee = 100 + 111 - 30 - 40;
        BOOST_CHECK(!VerifyAmounts(cache, tx4, tx4.nTxFee)); // Spends a blinded coin with no blinded outputs to compensate.

        std::vector<uint256> input_blinds;
        std::vector<uint256> output_blinds;
        std::vector<CPubKey> output_pubkeys;
        input_blinds.push_back(uint256());
        input_blinds.push_back(blind3);
        output_blinds.push_back(uint256());
        output_blinds.push_back(uint256());
        output_pubkeys.push_back(CPubKey());
        output_pubkeys.push_back(CPubKey());
        BOOST_CHECK(!BlindOutputs(input_blinds, output_blinds, output_pubkeys, tx4)); // fails as there is no place to put the blinding factor
    }

    {
        // Build a transactions that spends an unblinded (111) and blinded (100) coin, and produces a blinded (30), unblinded (40), and blinded (50) coin and fee (91)
        CMutableTransaction tx4;
        tx4.vin.resize(2);
        tx4.vin[0].prevout.hash = ArithToUint256(2);
        tx4.vin[0].prevout.n = 0;
        tx4.vin[1].prevout.hash = ArithToUint256(3);
        tx4.vin[1].prevout.n = 0;
        tx4.vout.resize(3);
        tx4.vout[0].nValue = 30;
        tx4.vout[1].nValue = 40;
        tx4.vout[2].nValue = 50;
        tx4.nTxFee = 100 + 111 - 30 - 40 - 50;
        BOOST_CHECK(!VerifyAmounts(cache, tx4, tx4.nTxFee)); // Spends a blinded coin with no blinded outputs to compensate.

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
        BOOST_CHECK(BlindOutputs(input_blinds, output_blinds, output_pubkeys, tx4));
        BOOST_CHECK(!tx4.vout[0].nValue.IsAmount());
        BOOST_CHECK(tx4.vout[1].nValue.IsAmount());
        BOOST_CHECK(!tx4.vout[2].nValue.IsAmount());
        BOOST_CHECK(VerifyAmounts(cache, tx4, tx4.nTxFee));

#ifdef ENABLE_WALLET
        //This tests the wallet blinding caching functionality
        CWalletTx wtx(&wallet, tx4);
        uint256 factor = wtx.GetBlindingFactor(0);
        CPubKey pubkey = wtx.GetBlindingPubKey(0);
        CAmount amount = wtx.GetValueOut(0);

        BOOST_CHECK(factor == uint256());
        BOOST_CHECK(pubkey == CPubKey());
        BOOST_CHECK(amount == -1);

        wtx.SetBlindingData(0, 42, output_pubkeys[0], output_blinds[0]);

        factor = wtx.GetBlindingFactor(0);
        pubkey = wtx.GetBlindingPubKey(0);
        amount = wtx.GetValueOut(0);

        BOOST_CHECK(factor == output_blinds[0]);
        BOOST_CHECK(pubkey == output_pubkeys[0]);
        BOOST_CHECK(amount == 42);

        wtx.SetBlindingData(1, 11, output_pubkeys[1], output_blinds[1]);

        factor = wtx.GetBlindingFactor(0);
        pubkey = wtx.GetBlindingPubKey(0);
        amount = wtx.GetValueOut(0);

        BOOST_CHECK(factor == output_blinds[0]);
        BOOST_CHECK(pubkey == output_pubkeys[0]);
        BOOST_CHECK(amount == 42);

        factor = wtx.GetBlindingFactor(1);
        pubkey = wtx.GetBlindingPubKey(1);
        amount = wtx.GetValueOut(1);

        BOOST_CHECK(factor == output_blinds[1]);
        BOOST_CHECK(pubkey == output_pubkeys[1]);
        BOOST_CHECK(amount == 11);
#endif
        CAmount unblinded_amount;
        BOOST_CHECK(UnblindOutput(key1, tx4.vout[0], unblinded_amount, blind4) == 0);
        BOOST_CHECK(UnblindOutput(key2, tx4.vout[0], unblinded_amount, blind4) == 1);
        BOOST_CHECK(unblinded_amount == 30);
        BOOST_CHECK(UnblindOutput(key2, tx4.vout[2], unblinded_amount, blind4) == 1);
        BOOST_CHECK(unblinded_amount == 50);

        CCoinsModifier in4 = cache.ModifyCoins(ArithToUint256(4));
        in4->vout.resize(3);
        in4->vout[0] = tx4.vout[0];
        in4->vout[1] = tx4.vout[1];
        in4->vout[2] = tx4.vout[2];

        tx4.nTxFee--;
        BOOST_CHECK(!VerifyAmounts(cache, tx4, tx4.nTxFee));
    }
}

BOOST_AUTO_TEST_SUITE_END()
