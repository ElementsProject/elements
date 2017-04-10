// Copyright (c) 2017-2017 Blockstream Inc.
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "arith_uint256.h"
#include "blind.h"
#include "uint256.h"
#include "validation.h"

#include "test/test_bitcoin.h"

#include <boost/test/unit_test.hpp>


BOOST_FIXTURE_TEST_SUITE(amount_tests, TestingSetup)

BOOST_AUTO_TEST_CASE(verify_coinbase_test)
{
    // Generate some asset types and feemap
    std::vector<CAsset> types;
    CAmountMap mapFees;
    for (unsigned int i = 1; i < 4; i++) {
        types.emplace_back(GetRandHash());
        mapFees[types.back()] = i;
    }

    // Make coinbase transaction
    CMutableTransaction tx;
    tx.vin.push_back(CTxIn(COutPoint(), CScript(), 0));

    // Blank amount check
    BOOST_CHECK(VerifyCoinbaseAmount(tx, CAmountMap()));

    // Check against non-null fee, surplus is ok
    BOOST_CHECK(VerifyCoinbaseAmount(tx, mapFees));

    // Add non-fee outputs to coinbase
    for (unsigned int i = 1; i < 4; i++) {
        BOOST_CHECK(VerifyCoinbaseAmount(tx, mapFees));
        tx.vout.push_back(CTxOut(types[i-1], i, CScript() << OP_TRUE));
    }
    // All outputs added, should still balance
    BOOST_CHECK(VerifyCoinbaseAmount(tx, mapFees));

    // Adding 0-value unspendable output should not change balance
    tx.vout.push_back(CTxOut(types.back(), 0, CScript() << OP_RETURN));
    BOOST_CHECK(VerifyCoinbaseAmount(tx, mapFees));

    // But you cannot add spendable 0-value output
    tx.vout.push_back(CTxOut(types.back(), 0, CScript() << OP_TRUE));
    BOOST_CHECK(!VerifyCoinbaseAmount(tx, mapFees));
    tx.vout.pop_back();
    BOOST_CHECK(VerifyCoinbaseAmount(tx, mapFees));

    // Adding values outside MAX_MONEY also causes failure
    mapFees[CAsset()] = MAX_MONEY+1;
    tx.vout.push_back(CTxOut(CAsset(), MAX_MONEY+1, CScript() << OP_RETURN));
    BOOST_CHECK(!VerifyCoinbaseAmount(tx, mapFees));
    tx.vout.pop_back();
    mapFees[CAsset()] = 0;
    BOOST_CHECK(VerifyCoinbaseAmount(tx, mapFees));

    // Change the unspendable 0-value output to have asset commitment
    secp256k1_generator gen;
    const unsigned char blind[32] = {0};
    CAsset asset = tx.vout.back().nAsset.GetAsset();

    BlindAsset(tx.vout.back().nAsset, gen, asset, blind);

    BOOST_CHECK(!VerifyCoinbaseAmount(tx, mapFees));
    tx.vout.back().nAsset = types.back();
    BOOST_CHECK(VerifyCoinbaseAmount(tx, mapFees));

    // Change the same output's value to an unblinded commitment to non-zero value (unblinded zero is blank commitment)
    secp256k1_pedersen_commitment commit;
    CreateValueCommitment(tx.vout.back().nValue, commit, blind, gen, 1);
    BOOST_CHECK(!VerifyCoinbaseAmount(tx, mapFees));

    tx.vout.pop_back();
    BOOST_CHECK(VerifyCoinbaseAmount(tx, mapFees));

    // Negative output
    tx.vout.push_back(CTxOut(CAsset(), -1, CScript() << OP_RETURN));
    BOOST_CHECK(!VerifyCoinbaseAmount(tx, mapFees));
    tx.vout.pop_back();

    // Transaction claiming too much fees
    tx.vout.push_back(CTxOut(CAsset(), 1, CScript() << OP_RETURN));
    BOOST_CHECK(!VerifyCoinbaseAmount(tx, mapFees));
    tx.vout.pop_back();
}

BOOST_AUTO_TEST_SUITE_END()
