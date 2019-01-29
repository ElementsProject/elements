// Copyright (c) 2013-2019 The Elements Core developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <arith_uint256.h>
#include <blind.h>
#include <coins.h>
#include <uint256.h>
#include <validation.h>

#include <test/test_bitcoin.h>

#include <boost/test/unit_test.hpp>

// For elements serialization rules
struct ElementsSetup : public TestingSetup {
        ElementsSetup() : TestingSetup("custom") {}
};

BOOST_FIXTURE_TEST_SUITE(blind_tests, ElementsSetup)

// TODO: Make deterministic blinding wrapper function, test caching more exactly

BOOST_AUTO_TEST_CASE(naive_blinding_test)
{
    CKey key1;
    CKey key2;
    CKey keyDummy;

    // Any asset id will do
    CAsset bitcoinID(GetRandHash());
    CAsset otherID(GetRandHash());
    CAsset unblinded_id;
    uint256 asset_blind;
    CScript op_true(OP_TRUE);
    std::vector<CKey> vDummy;

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

    std::vector<CTxOut> inputs;
    CTxOut btc_oo(bitcoinID, 11, CScript());
    CTxOut btc_ooo(bitcoinID, 111, CScript());
    CTxOut other_fzz(otherID, 500, CScript());
    CTxOut blind_ozz; // Will be computed later

    {
        inputs.clear();
        inputs.push_back(btc_oo);
        inputs.push_back(btc_ooo);

        // Build a transaction that spends 2 unblinded coins (11, 111), and produces a single blinded one (100) and fee (22).
        CMutableTransaction tx3;
        tx3.vin.resize(2);
        tx3.vin[0].prevout.hash = ArithToUint256(1);

        tx3.vin[0].prevout.n = 0;
        tx3.vin[1].prevout.hash = ArithToUint256(2);
        tx3.vin[1].prevout.n = 0;
        tx3.vout.resize(0);
        tx3.vout.push_back(CTxOut(bitcoinID, 100, CScript() << OP_TRUE));
        // Fee outputs are blank scriptpubkeys, and unblinded value/asset
        tx3.vout.push_back(CTxOut(bitcoinID, 22, CScript()));
        BOOST_CHECK(VerifyAmounts(inputs, tx3, nullptr, false));

        // Malleate the output and check for correct handling of bad commitments
        // These will fail IsValid checks
        std::vector<unsigned char> asset_copy(tx3.vout[0].nAsset.vchCommitment);
        std::vector<unsigned char> value_copy(tx3.vout[0].nValue.vchCommitment);
        tx3.vout[0].nAsset.vchCommitment[0] = 122;
        BOOST_CHECK(!VerifyAmounts(inputs, tx3, nullptr, false));
        tx3.vout[0].nAsset.vchCommitment = asset_copy;
        tx3.vout[0].nValue.vchCommitment[0] = 122;
        BOOST_CHECK(!VerifyAmounts(inputs, tx3, nullptr, false));
        tx3.vout[0].nValue.vchCommitment = value_copy;

        // Make sure null values are handled correctly
        tx3.vout[0].nAsset.SetNull();
        BOOST_CHECK(!VerifyAmounts(inputs, tx3, nullptr, false));
        tx3.vout[0].nAsset.vchCommitment = asset_copy;
        tx3.vout[0].nValue.SetNull();
        BOOST_CHECK(!VerifyAmounts(inputs, tx3, nullptr, false));
        tx3.vout[0].nValue.vchCommitment = value_copy;

        // Bad nonce values will result in failure to deserialize
        tx3.vout[0].nNonce.SetNull();
        BOOST_CHECK(VerifyAmounts(inputs, tx3, nullptr, false));
        tx3.vout[0].nNonce.vchCommitment = tx3.vout[0].nValue.vchCommitment;
        BOOST_CHECK(!VerifyAmounts(inputs, tx3, nullptr, false));

        // Try to blind with a single non-fee output, which fails as its blinding factor ends up being zero.
        std::vector<uint256> input_blinds;
        std::vector<uint256> input_asset_blinds;
        std::vector<CAsset> input_assets;
        std::vector<CAmount> input_amounts;
        std::vector<uint256> output_blinds;
        std::vector<uint256> output_asset_blinds;
        std::vector<CPubKey> output_pubkeys;
        input_blinds.push_back(uint256());
        input_blinds.push_back(uint256());
        input_asset_blinds.push_back(uint256());
        input_asset_blinds.push_back(uint256());
        input_assets.push_back(bitcoinID);
        input_assets.push_back(bitcoinID);
        input_amounts.push_back(11);
        input_amounts.push_back(111);
        output_pubkeys.push_back(pubkey1);
        output_pubkeys.push_back(CPubKey());
        BOOST_CHECK(BlindTransaction(input_blinds, input_asset_blinds, input_assets, input_amounts, output_blinds, output_asset_blinds, output_pubkeys, vDummy, vDummy, tx3) == 0);

        // Add a dummy output. Must be unspendable since it's 0-valued.
        tx3.vout.push_back(CTxOut(bitcoinID, 0, CScript() << OP_RETURN));
        output_pubkeys.push_back(pubkeyDummy);
        BOOST_CHECK(BlindTransaction(input_blinds, input_asset_blinds, input_assets, input_amounts, output_blinds, output_asset_blinds, output_pubkeys, vDummy, vDummy, tx3) == 2);
        BOOST_CHECK(!tx3.vout[0].nValue.IsExplicit());
        BOOST_CHECK(!tx3.vout[2].nValue.IsExplicit());
        BOOST_CHECK(VerifyAmounts(inputs, tx3, nullptr, false));

        CAmount unblinded_amount;
        BOOST_CHECK(UnblindConfidentialPair(key2, tx3.vout[0].nValue, tx3.vout[0].nAsset, tx3.vout[0].nNonce, op_true, tx3.witness.vtxoutwit[0].vchRangeproof, unblinded_amount, blind3, unblinded_id, asset_blind) == 0);
        // Saving unblinded_id and asset_blind for later since we need for input
        BOOST_CHECK(UnblindConfidentialPair(key1, tx3.vout[0].nValue, tx3.vout[0].nAsset, tx3.vout[0].nNonce, op_true, tx3.witness.vtxoutwit[0].vchRangeproof, unblinded_amount, blind3, unblinded_id, asset_blind) == 1);
        BOOST_CHECK(unblinded_amount == 100);
        BOOST_CHECK(unblinded_id == bitcoinID);
        CAsset temp_asset;
        uint256 temp_asset_blinder;
        BOOST_CHECK(UnblindConfidentialPair(keyDummy, tx3.vout[2].nValue, tx3.vout[2].nAsset, tx3.vout[2].nNonce, CScript() << OP_RETURN, tx3.witness.vtxoutwit[2].vchRangeproof, unblinded_amount, blindDummy, temp_asset, temp_asset_blinder) == 1);
        BOOST_CHECK(unblinded_amount == 0);

        // Storing for next section
        BOOST_CHECK(tx3.vout[0].nValue.IsCommitment());
        BOOST_CHECK(tx3.vout[0].nAsset.IsCommitment());
        blind_ozz = tx3.vout[0];

        tx3.vout[1].nValue = CConfidentialValue(tx3.vout[1].nValue.GetAmount() - 1);
        BOOST_CHECK(!VerifyAmounts(inputs, tx3, nullptr, false));
    }

    {
        inputs.clear();
        inputs.push_back(btc_ooo);
        inputs.push_back(blind_ozz);

        // Build a transactions that spends an unblinded (111) and blinded (100) coin, and produces only unblinded coins (impossible)
        CMutableTransaction tx4;
        tx4.vin.resize(2);
        tx4.vin[0].prevout.hash = ArithToUint256(2);
        tx4.vin[0].prevout.n = 0;
        tx4.vin[1].prevout.hash = ArithToUint256(3);
        tx4.vin[1].prevout.n = 0;
        tx4.vout.push_back(CTxOut(bitcoinID, 30, CScript() << OP_TRUE));
        tx4.vout.push_back(CTxOut(bitcoinID, 40, CScript() << OP_TRUE));
        tx4.vout.push_back(CTxOut(bitcoinID, 111+100-30-40, CScript()));
        BOOST_CHECK(!VerifyAmounts(inputs, tx4, nullptr, false)); // Spends a blinded coin with no blinded outputs to compensate.

        std::vector<uint256> input_blinds;
        std::vector<uint256> input_asset_blinds;
        std::vector<CAsset> input_assets;
        std::vector<CAmount> input_amounts;
        std::vector<uint256> output_blinds;
        std::vector<uint256> output_asset_blinds;
        std::vector<CPubKey> output_pubkeys;
        input_blinds.push_back(uint256());
        input_blinds.push_back(blind3);
        input_asset_blinds.push_back(uint256());
        input_asset_blinds.push_back(asset_blind);
        input_amounts.push_back(111);
        input_amounts.push_back(100);
        input_assets.push_back(unblinded_id);
        input_assets.push_back(unblinded_id);
        output_pubkeys.push_back(CPubKey());
        output_pubkeys.push_back(CPubKey());
        output_pubkeys.push_back(CPubKey());
        BOOST_CHECK(BlindTransaction(input_blinds, input_asset_blinds, input_assets, input_amounts, output_blinds, output_asset_blinds, output_pubkeys, vDummy, vDummy, tx4) == 0); // Blinds nothing
    }

    {
        inputs.clear();
        inputs.push_back(btc_ooo);
        inputs.push_back(blind_ozz);

        // Build a transactions that spends an unblinded (111) and blinded (100) coin, and produces a blinded (30), unblinded (40), and blinded (50) coin and fee (91)
        CMutableTransaction tx4;
        tx4.vin.resize(2);
        tx4.vin[0].prevout.hash = ArithToUint256(2);
        tx4.vin[0].prevout.n = 0;
        tx4.vin[1].prevout.hash = ArithToUint256(3);
        tx4.vin[1].prevout.n = 0;
        tx4.vout.push_back(CTxOut(bitcoinID, 30, CScript() << OP_TRUE));
        tx4.vout.push_back(CTxOut(bitcoinID, 40, CScript() << OP_TRUE));
        tx4.vout.push_back(CTxOut(bitcoinID, 50, CScript() << OP_TRUE));
        // Fee
        tx4.vout.push_back(CTxOut(bitcoinID, 111+100-30-40-50, CScript()));
        BOOST_CHECK(!VerifyAmounts(inputs, tx4, nullptr, false)); // Spends a blinded coin with no blinded outputs to compensate.

        std::vector<uint256> input_blinds;
        std::vector<uint256> input_asset_blinds;
        std::vector<CAsset> input_assets;
        std::vector<CAmount> input_amounts;
        std::vector<uint256> output_blinds;
        std::vector<uint256> output_asset_blinds;
        std::vector<CPubKey> output_pubkeys;

        input_blinds.push_back(uint256());
        input_blinds.push_back(blind3);
        input_asset_blinds.push_back(uint256());
        input_asset_blinds.push_back(asset_blind);
        input_amounts.push_back(111);
        input_amounts.push_back(100);
        input_assets.push_back(unblinded_id);
        input_assets.push_back(unblinded_id);

        output_pubkeys.push_back(pubkey2);
        output_pubkeys.push_back(CPubKey());
        output_pubkeys.push_back(pubkey2);
        output_pubkeys.push_back(CPubKey());

        BOOST_CHECK(BlindTransaction(input_blinds, input_asset_blinds, input_assets, input_amounts, output_blinds, output_asset_blinds, output_pubkeys, vDummy, vDummy, tx4) == 2);
        BOOST_CHECK(!tx4.vout[0].nValue.IsExplicit());
        BOOST_CHECK(tx4.vout[1].nValue.IsExplicit());
        BOOST_CHECK(!tx4.vout[2].nValue.IsExplicit());
        // This one broken
        BOOST_CHECK(VerifyAmounts(inputs, tx4, nullptr, false));

        CAmount unblinded_amount;
        CAsset asset_out;
        uint256 asset_blinder_out;
        BOOST_CHECK(UnblindConfidentialPair(key1, tx4.vout[0].nValue, tx4.vout[0].nAsset, tx4.vout[0].nNonce, op_true, tx4.witness.vtxoutwit[0].vchRangeproof, unblinded_amount, blind4, asset_out, asset_blinder_out) == 0);
        BOOST_CHECK(UnblindConfidentialPair(key2, tx4.vout[0].nValue, tx4.vout[0].nAsset, tx4.vout[0].nNonce, op_true, tx4.witness.vtxoutwit[0].vchRangeproof, unblinded_amount, blind4, asset_out, asset_blinder_out) == 1);
        BOOST_CHECK(unblinded_amount == 30);
        BOOST_CHECK(asset_out == unblinded_id);
        BOOST_CHECK(UnblindConfidentialPair(key2, tx4.vout[2].nValue, tx4.vout[2].nAsset, tx4.vout[2].nNonce, op_true, tx4.witness.vtxoutwit[2].vchRangeproof, unblinded_amount, blind4, asset_out, asset_blinder_out) == 1);
        BOOST_CHECK(asset_out == unblinded_id);
        BOOST_CHECK(unblinded_amount == 50);

        // Commit to the wrong script in the rangeproof
        BOOST_CHECK(UnblindConfidentialPair(key2, tx4.vout[2].nValue, tx4.vout[2].nAsset, tx4.vout[2].nNonce, CScript() << OP_FALSE, tx4.witness.vtxoutwit[2].vchRangeproof, unblinded_amount, blind4, asset_out, asset_blinder_out) == 0);

        // Make invalid public keys in nonce commitment, first of right size
        tx4.vout[2].nNonce.vchCommitment = std::vector<unsigned char>(33, 0);
        tx4.vout[2].nNonce.vchCommitment[0] = 0x03;
        BOOST_CHECK(UnblindConfidentialPair(key2, tx4.vout[2].nValue, tx4.vout[2].nAsset, tx4.vout[2].nNonce, op_true, tx4.witness.vtxoutwit[2].vchRangeproof, unblinded_amount, blind4, asset_out, asset_blinder_out) == 0);

        // Next, leading byte claiming to be 33 bytes in size
        tx4.vout[2].nNonce.vchCommitment.resize(1);
        BOOST_CHECK(UnblindConfidentialPair(key2, tx4.vout[2].nValue, tx4.vout[2].nAsset, tx4.vout[2].nNonce, op_true, tx4.witness.vtxoutwit[2].vchRangeproof, unblinded_amount, blind4, asset_out, asset_blinder_out) == 0);

        // Last, blank nonce commitment
        tx4.vout[2].nNonce.vchCommitment.clear();
        BOOST_CHECK(UnblindConfidentialPair(key2, tx4.vout[2].nValue, tx4.vout[2].nAsset, tx4.vout[2].nNonce, op_true, tx4.witness.vtxoutwit[2].vchRangeproof, unblinded_amount, blind4, asset_out, asset_blinder_out) == 0);

        tx4.vout[3].nValue = CConfidentialValue(tx4.vout[3].nValue.GetAmount() - 1);
        BOOST_CHECK(!VerifyAmounts(inputs, tx4, nullptr, false));
    }

    {
        inputs.clear();
        inputs.push_back(blind_ozz);
        inputs.push_back(other_fzz);

        // Spends 100 blinded bitcoin, 500 of unblinded "other"
        CMutableTransaction tx5;
        tx5.vin.resize(0);
        tx5.vout.resize(0);
        tx5.vin.push_back(CTxIn(COutPoint(ArithToUint256(3), 0)));
        tx5.vin.push_back(CTxIn(COutPoint(ArithToUint256(5), 0)));
        tx5.vout.push_back(CTxOut(bitcoinID, 29, CScript() << OP_TRUE));
        tx5.vout.push_back(CTxOut(bitcoinID, 70, CScript() << OP_TRUE));
        tx5.vout.push_back(CTxOut(otherID, 250, CScript() << OP_TRUE));
        tx5.vout.push_back(CTxOut(otherID, 249, CScript() << OP_TRUE));
        // Fees
        tx5.vout.push_back(CTxOut(bitcoinID, 1, CScript()));
        tx5.vout.push_back(CTxOut(otherID, 1, CScript()));

        // Blinds don't balance
        BOOST_CHECK(!VerifyAmounts(inputs, tx5, nullptr, false));

        // Blinding setup stuff
        std::vector<uint256> input_blinds;
        std::vector<uint256> input_asset_blinds;
        std::vector<CAsset> input_assets;
        std::vector<CAmount> input_amounts;
        std::vector<uint256> output_blinds;
        std::vector<uint256> output_asset_blinds;
        std::vector<CPubKey> output_pubkeys;
        input_blinds.push_back(blind3);
        input_blinds.push_back(uint256()); //
        input_asset_blinds.push_back(asset_blind);
        input_asset_blinds.push_back(uint256());
        input_amounts.push_back(100);
        input_amounts.push_back(500);
        input_assets.push_back(bitcoinID);
        input_assets.push_back(otherID);
        for (unsigned int i = 0; i < 6; i++) {
            output_pubkeys.push_back(pubkey2);
        }

        CMutableTransaction txtemp(tx5);

        // No blinding keys for fees, bails out blinding nothing, still invalid due to imbalance
        BOOST_CHECK(BlindTransaction(input_blinds, input_asset_blinds, input_assets, input_amounts, output_blinds, output_asset_blinds, output_pubkeys, vDummy, vDummy, txtemp) == -1);
        BOOST_CHECK(!VerifyAmounts(inputs, txtemp, nullptr, false));
        // Last will be implied blank keys
        output_pubkeys.resize(4);

        // Blind transaction, verify amounts
        txtemp = tx5;
        BOOST_CHECK(BlindTransaction(input_blinds, input_asset_blinds, input_assets, input_amounts, output_blinds, output_asset_blinds, output_pubkeys, vDummy, vDummy, txtemp) == 4);
        BOOST_CHECK(VerifyAmounts(inputs, txtemp, nullptr, false));

        // Transaction may not have spendable 0-value output
        txtemp.vout.push_back(CTxOut(CAsset(), 0, CScript() << OP_TRUE));
        BOOST_CHECK(!VerifyAmounts(inputs, txtemp, nullptr, false));

        // Create imbalance by removing fees, should still be able to blind
        txtemp = tx5;
        txtemp.vout.resize(5);
        BOOST_CHECK(!VerifyAmounts(inputs, txtemp, nullptr, false));
        txtemp.vout.resize(4);
        BOOST_CHECK(!VerifyAmounts(inputs, txtemp, nullptr, false));
        BOOST_CHECK(BlindTransaction(input_blinds, input_asset_blinds, input_assets, input_amounts, output_blinds, output_asset_blinds, output_pubkeys, vDummy, vDummy, txtemp) == 4);
        BOOST_CHECK(!VerifyAmounts(inputs, txtemp, nullptr, false));

        txtemp = tx5;
        // Remove other input, make surjection proof impossible for 2 "otherID" outputs
        std::vector<uint256> t_input_blinds;
        std::vector<uint256> t_input_asset_blinds;
        std::vector<CAsset> t_input_assets;
        std::vector<CAmount> t_input_amounts;

        t_input_blinds = input_blinds;
        t_input_asset_blinds = input_asset_blinds;
        t_input_assets = input_assets;
        t_input_amounts = input_amounts;
        txtemp.vin.resize(1);
        inputs.resize(1);
        t_input_blinds.resize(1);
        t_input_asset_blinds.resize(1);
        t_input_assets.resize(1);
        t_input_amounts.resize(1);
        BOOST_CHECK(!VerifyAmounts(inputs, txtemp, nullptr, false));
        BOOST_CHECK(BlindTransaction(t_input_blinds, t_input_asset_blinds, t_input_assets, t_input_amounts, output_blinds, output_asset_blinds, output_pubkeys, vDummy, vDummy, txtemp) == 2);
        BOOST_CHECK(!VerifyAmounts(inputs, txtemp, nullptr, false));
    }
}
BOOST_AUTO_TEST_SUITE_END()
