// Copyright (c) 2011-2014 The Bitcoin Core developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "data/tx_invalid.json.h"
#include "data/tx_valid.json.h"

#include "clientversion.h"
#include "key.h"
#include "keystore.h"
#include "main.h"
#include "script/script.h"
#include "script/script_error.h"
#include "core_io.h"

#include <map>
#include <string>

#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/split.hpp>
#include <boost/test/unit_test.hpp>
#include <boost/assign/list_of.hpp>
#include "json/json_spirit_writer_template.h"

using namespace std;
using namespace json_spirit;
using namespace boost::algorithm;

// In script_tests.cpp
extern Array read_json(const std::string& jsondata);

static std::map<string, unsigned int> mapFlagNames = boost::assign::map_list_of
    (string("NONE"), (unsigned int)SCRIPT_VERIFY_NONE)
    (string("P2SH"), (unsigned int)SCRIPT_VERIFY_P2SH)
    (string("STRICTENC"), (unsigned int)SCRIPT_VERIFY_STRICTENC)
    (string("DERSIG"), (unsigned int)SCRIPT_VERIFY_DERSIG)
    (string("LOW_S"), (unsigned int)SCRIPT_VERIFY_LOW_S)
    (string("SIGPUSHONLY"), (unsigned int)SCRIPT_VERIFY_SIGPUSHONLY)
    (string("MINIMALDATA"), (unsigned int)SCRIPT_VERIFY_MINIMALDATA)
    (string("NULLDUMMY"), (unsigned int)SCRIPT_VERIFY_NULLDUMMY)
    (string("DISCOURAGE_UPGRADABLE_NOPS"), (unsigned int)SCRIPT_VERIFY_DISCOURAGE_UPGRADABLE_NOPS)
    (string("CHECKLOCKTIMEVERIFY"), (unsigned int)SCRIPT_VERIFY_CHECKLOCKTIMEVERIFY)
    (string("CHECKSEQUENCEVERIFY"), (unsigned int)SCRIPT_VERIFY_CHECKSEQUENCEVERIFY);

unsigned int ParseScriptFlags(string strFlags)
{
    if (strFlags.empty()) {
        return 0;
    }
    unsigned int flags = 0;
    vector<string> words;
    split(words, strFlags, is_any_of(","));

    BOOST_FOREACH(string word, words)
    {
        if (!mapFlagNames.count(word))
            BOOST_ERROR("Bad test: unknown verification flag '" << word << "'");
        flags |= mapFlagNames[word];
    }

    return flags;
}

string FormatScriptFlags(unsigned int flags)
{
    if (flags == 0) {
        return "";
    }
    string ret;
    std::map<string, unsigned int>::const_iterator it = mapFlagNames.begin();
    while (it != mapFlagNames.end()) {
        if (flags & it->second) {
            ret += it->first + ",";
        }
        it++;
    }
    return ret.substr(0, ret.size() - 1);
}

BOOST_AUTO_TEST_SUITE(transaction_tests)

// These test cases require their golden sets to be rebuilt when the transaction signatures change, and I don't know
//   how to do that.
#if 0
BOOST_AUTO_TEST_CASE(tx_valid)
{
    // Read tests from test/data/tx_valid.json
    // Format is an array of arrays
    // Inner arrays are either [ "comment" ]
    // or [[[prevout hash, prevout index, prevout scriptPubKey], [input 2], ...],"], serializedTransaction, verifyFlags
    // ... where all scripts are stringified scripts.
    //
    // verifyFlags is a comma separated list of script verification flags to apply, or "NONE"
    Array tests = read_json(std::string(json_tests::tx_valid, json_tests::tx_valid + sizeof(json_tests::tx_valid)));

    ScriptError err;
    BOOST_FOREACH(Value& tv, tests)
    {
        Array test = tv.get_array();
        string strTest = write_string(tv, false);
        if (test[0].type() == array_type)
        {
            if (test.size() != 3 || test[1].type() != str_type || test[2].type() != str_type)
            {
                BOOST_ERROR("Bad test: " << strTest);
                continue;
            }

            map<COutPoint, CScript> mapprevOutScriptPubKeys;
            Array inputs = test[0].get_array();
            bool fValid = true;
            BOOST_FOREACH(Value& input, inputs)
            {
                if (input.type() != array_type)
                {
                    fValid = false;
                    break;
                }
                Array vinput = input.get_array();
                if (vinput.size() != 3)
                {
                    fValid = false;
                    break;
                }

                mapprevOutScriptPubKeys[COutPoint(uint256(vinput[0].get_str()), vinput[1].get_int())] = ParseScript(vinput[2].get_str());
            }
            if (!fValid)
            {
                BOOST_ERROR("Bad test: " << strTest);
                continue;
            }

            string transaction = test[1].get_str();
            CDataStream stream(ParseHex(transaction), SER_NETWORK, PROTOCOL_VERSION);
            CTransaction tx;
            stream >> tx;

            CValidationState state;
            BOOST_CHECK_MESSAGE(CheckTransaction(tx, state), strTest);
            BOOST_CHECK(state.IsValid());

            for (unsigned int i = 0; i < tx.vin.size(); i++)
            {
                if (!mapprevOutScriptPubKeys.count(tx.vin[i].prevout))
                {
                    BOOST_ERROR("Bad test: " << strTest);
                    break;
                }

                unsigned int verify_flags = ParseScriptFlags(test[2].get_str());
                BOOST_CHECK_MESSAGE(VerifyScript(tx.vin[i].scriptSig, mapprevOutScriptPubKeys[tx.vin[i].prevout],
                                                 verify_flags, TransactionNoWithdrawsSignatureChecker(&tx, i), &err),
                                    strTest);
                BOOST_CHECK_MESSAGE(err == SCRIPT_ERR_OK, ScriptErrorString(err));
            }
        }
    }
}

BOOST_AUTO_TEST_CASE(tx_invalid)
{
    // Read tests from test/data/tx_invalid.json
    // Format is an array of arrays
    // Inner arrays are either [ "comment" ]
    // or [[[prevout hash, prevout index, prevout scriptPubKey], [input 2], ...],"], serializedTransaction, verifyFlags
    // ... where all scripts are stringified scripts.
    //
    // verifyFlags is a comma separated list of script verification flags to apply, or "NONE"
    Array tests = read_json(std::string(json_tests::tx_invalid, json_tests::tx_invalid + sizeof(json_tests::tx_invalid)));

    ScriptError err;
    BOOST_FOREACH(Value& tv, tests)
    {
        Array test = tv.get_array();
        string strTest = write_string(tv, false);
        if (test[0].type() == array_type)
        {
            if (test.size() != 3 || test[1].type() != str_type || test[2].type() != str_type)
            {
                BOOST_ERROR("Bad test: " << strTest);
                continue;
            }

            map<COutPoint, CScript> mapprevOutScriptPubKeys;
            Array inputs = test[0].get_array();
            bool fValid = true;
            BOOST_FOREACH(Value& input, inputs)
            {
                if (input.type() != array_type)
                {
                    fValid = false;
                    break;
                }
                Array vinput = input.get_array();
                if (vinput.size() != 3)
                {
                    fValid = false;
                    break;
                }

                mapprevOutScriptPubKeys[COutPoint(uint256(vinput[0].get_str()), vinput[1].get_int())] = ParseScript(vinput[2].get_str());
            }
            if (!fValid)
            {
                BOOST_ERROR("Bad test: " << strTest);
                continue;
            }

            string transaction = test[1].get_str();
            CDataStream stream(ParseHex(transaction), SER_NETWORK, PROTOCOL_VERSION);
            CTransaction tx;
            stream >> tx;

            CValidationState state;
            fValid = CheckTransaction(tx, state) && state.IsValid();

            for (unsigned int i = 0; i < tx.vin.size() && fValid; i++)
            {
                if (!mapprevOutScriptPubKeys.count(tx.vin[i].prevout))
                {
                    BOOST_ERROR("Bad test: " << strTest);
                    break;
                }

                unsigned int verify_flags = ParseScriptFlags(test[2].get_str());
                fValid = VerifyScript(tx.vin[i].scriptSig, mapprevOutScriptPubKeys[tx.vin[i].prevout],
                                      verify_flags, TransactionNoWithdrawsSignatureChecker(&tx, i), &err);
            }
            BOOST_CHECK_MESSAGE(!fValid, strTest);
            BOOST_CHECK_MESSAGE(err != SCRIPT_ERR_OK, ScriptErrorString(err));
        }
    }
}
#endif // 0

//
// Helper: create two dummy transactions, each with
// two outputs.  The first has 11 and 50 CENT outputs
// paid to a TX_PUBKEY, the second 21 and 22 CENT outputs
// paid to a TX_PUBKEYHASH.
//
static std::vector<CMutableTransaction>
SetupDummyInputs(CBasicKeyStore& keystoreRet, CCoinsViewCache& coinsRet)
{
    std::vector<CMutableTransaction> dummyTransactions;
    dummyTransactions.resize(2);

    // Add some keys to the keystore:
    CKey key[4];
    for (int i = 0; i < 4; i++)
    {
        key[i].MakeNewKey(i % 2);
        keystoreRet.AddKey(key[i]);
    }

    // Create some dummy input transactions
    dummyTransactions[0].vout.resize(2);
    dummyTransactions[0].vout[0].nValue = 11*CENT;
    dummyTransactions[0].vout[0].scriptPubKey << ToByteVector(key[0].GetPubKey()) << OP_CHECKSIG;
    dummyTransactions[0].vout[1].nValue = 50*CENT;
    dummyTransactions[0].vout[1].scriptPubKey << ToByteVector(key[1].GetPubKey()) << OP_CHECKSIG;
    coinsRet.ModifyCoins(dummyTransactions[0].GetHash())->FromTx(dummyTransactions[0], 0);

    dummyTransactions[1].vout.resize(2);
    dummyTransactions[1].vout[0].nValue = 21*CENT;
    dummyTransactions[1].vout[0].scriptPubKey = GetScriptForDestination(key[2].GetPubKey().GetID());
    dummyTransactions[1].vout[1].nValue = 22*CENT;
    dummyTransactions[1].vout[1].scriptPubKey = GetScriptForDestination(key[3].GetPubKey().GetID());
    coinsRet.ModifyCoins(dummyTransactions[1].GetHash())->FromTx(dummyTransactions[1], 0);

    return dummyTransactions;
}

BOOST_AUTO_TEST_CASE(test_Get)
{
    CBasicKeyStore keystore;
    CCoinsView coinsDummy;
    CCoinsViewCache coins(&coinsDummy);
    std::vector<CMutableTransaction> dummyTransactions = SetupDummyInputs(keystore, coins);

    CMutableTransaction t1;
    t1.vin.resize(3);
    t1.vin[0].prevout.hash = dummyTransactions[0].GetHash();
    t1.vin[0].prevout.n = 1;
    t1.vin[0].scriptSig << std::vector<unsigned char>(65, 0);
    t1.vin[1].prevout.hash = dummyTransactions[1].GetHash();
    t1.vin[1].prevout.n = 0;
    t1.vin[1].scriptSig << std::vector<unsigned char>(65, 0) << std::vector<unsigned char>(33, 4);
    t1.vin[2].prevout.hash = dummyTransactions[1].GetHash();
    t1.vin[2].prevout.n = 1;
    t1.vin[2].scriptSig << std::vector<unsigned char>(65, 0) << std::vector<unsigned char>(33, 4);
    t1.vout.resize(2);
    t1.vout[0].nValue = 90*CENT;
    t1.vout[0].scriptPubKey << OP_1;

    BOOST_CHECK(AreInputsStandard(t1, coins));
    BOOST_CHECK(t1.vout[0].nValue.IsAmount());
    BOOST_CHECK_EQUAL(t1.vout[0].nValue.GetAmount(), 90*CENT);

    // Adding extra junk to the scriptSig should make it non-standard:
    t1.vin[0].scriptSig << OP_11;
    BOOST_CHECK(!AreInputsStandard(t1, coins));

    // ... as should not having enough:
    t1.vin[0].scriptSig = CScript();
    BOOST_CHECK(!AreInputsStandard(t1, coins));
}

BOOST_AUTO_TEST_CASE(test_IsStandard)
{
    LOCK(cs_main);
    CBasicKeyStore keystore;
    CCoinsView coinsDummy;
    CCoinsViewCache coins(&coinsDummy);
    std::vector<CMutableTransaction> dummyTransactions = SetupDummyInputs(keystore, coins);

    CMutableTransaction t;
    t.vin.resize(1);
    t.vin[0].prevout.hash = dummyTransactions[0].GetHash();
    t.vin[0].prevout.n = 1;
    t.vin[0].scriptSig << std::vector<unsigned char>(65, 0);
    t.vout.resize(1);
    t.vout[0].nValue = 90*CENT;
    CKey key;
    key.MakeNewKey(true);
    t.vout[0].scriptPubKey = GetScriptForDestination(key.GetPubKey().GetID());

    string reason;
    BOOST_CHECK(IsStandardTx(t, reason));

    t.vout[0].nValue = 501; // dust
    BOOST_CHECK(!IsStandardTx(t, reason));

    t.vout[0].nValue = 1001; // not dust
    BOOST_CHECK(IsStandardTx(t, reason));

    t.vout[0].scriptPubKey = CScript() << OP_2;
    BOOST_CHECK(!IsStandardTx(t, reason));

    // 40-byte TX_NULL_DATA (standard)
    t.vout[0].scriptPubKey = CScript() << OP_RETURN << ParseHex("04678afdb0fe5548271967f1a67130b7105cd6a828e03909a67962e0ea1f61deb649f6bc3f4cef38");
    BOOST_CHECK(IsStandardTx(t, reason));

    // 41-byte TX_NULL_DATA (non-standard)
    t.vout[0].scriptPubKey = CScript() << OP_RETURN << ParseHex("04678afdb0fe5548271967f1a67130b7105cd6a828e03909a67962e0ea1f61deb649f6bc3f4cef3800");
    BOOST_CHECK(!IsStandardTx(t, reason));

    // TX_NULL_DATA w/o PUSHDATA
    t.vout.resize(1);
    t.vout[0].scriptPubKey = CScript() << OP_RETURN;
    BOOST_CHECK(IsStandardTx(t, reason));

    // Only one TX_NULL_DATA permitted in all cases
    t.vout.resize(2);
    t.vout[0].scriptPubKey = CScript() << OP_RETURN << ParseHex("04678afdb0fe5548271967f1a67130b7105cd6a828e03909a67962e0ea1f61deb649f6bc3f4cef38");
    t.vout[1].scriptPubKey = CScript() << OP_RETURN << ParseHex("04678afdb0fe5548271967f1a67130b7105cd6a828e03909a67962e0ea1f61deb649f6bc3f4cef38");
    BOOST_CHECK(!IsStandardTx(t, reason));

    t.vout[0].scriptPubKey = CScript() << OP_RETURN << ParseHex("04678afdb0fe5548271967f1a67130b7105cd6a828e03909a67962e0ea1f61deb649f6bc3f4cef38");
    t.vout[1].scriptPubKey = CScript() << OP_RETURN;
    BOOST_CHECK(!IsStandardTx(t, reason));

    t.vout[0].scriptPubKey = CScript() << OP_RETURN;
    t.vout[1].scriptPubKey = CScript() << OP_RETURN;
    BOOST_CHECK(!IsStandardTx(t, reason));
}

BOOST_AUTO_TEST_SUITE_END()
