// Copyright (c) 2017-2017 Blockstream
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "clientversion.h"
#include "chainparams.h"
#include "checkqueue.h"
#include "consensus/validation.h"
#include "core_io.h"
#include "validation.h" // For CheckTransaction
#include "policy/policy.h"
#include "script/script.h"
#include "script/script_error.h"
#include "utilstrencodings.h"
#include "validation.h"
#include "streams.h"
#include "test/test_bitcoin.h"
#include "util.h"

#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/split.hpp>
#include <boost/assign/list_of.hpp>
#include <boost/test/unit_test.hpp>
#include <boost/assign/list_of.hpp>
#include <boost/foreach.hpp>

std::vector<std::vector<unsigned char> > witness_stack = {
    ParseHex("00ca9a3b"),
    ParseHex("e48a1a02a8f799892fda58347c2d794144311d4307dbfd10f77ffe28088c60be"),
    ParseHex("06226e46111a0b59caaf126043eb5bbf28c34f3a5e332a1fc7b2b73cf188910f"),
    ParseHex("0014542a5a8eea9945cc3d7e24468f108b8e0c721a81"),
    ParseHex("020000000365d984d2d0323bbab4807c12c533c014491596929082b1e684205c3fa80397f4010000006b483045022100dfc4741b5dadb6c4c9bd8774d037450e1a281dc2fd73d84115d1d68863d7fc6f02201cfb193bb929ef0e84dfcea5b37bea6484b7a54e79d5a74968a7f3baa79d67880121035b218cb6172451fec3fc467a71938d7e78f425cd76a771da9f193f952ca8c812feffffff6f17f18a671f8e67bdb666e36d8941c1d8ee29b85d9bddbeedbc2973f44fd6bb0000000049483045022100a0848deef222213765ce67f41528e0df6b3877a5f2810d4800759ea8616479ac022058fa148daa1ed7daab46ec0cfe373c17d82d6281cb8e9c7a4a7334136c5e4f0501feffffff9e6a22f9045ec732bad1c0f98d81bd2c9a1b4d4adbfabefb09a9d49e354e80350000000049483045022100ff7c9f9e145c5572d4b21a65a1fbc3331ee3a6757f378554223d963f0f2821d2022048d4c12e7bc4333a2393778645f385f7266176f42e3e86d6af3f0508cc1eed5c01feffffff025892dc01000000001976a914d85a6ba69df7c74e53ec7b99e424c24e2db6d8c988ac00ca9a3b0000000017a914a8105ab6cc3d9aa6ecd9736989d3388c933250e28728030000"),
    ParseHex("0000002088912d3d4e77e8b023382aad412b06a56db195666744eb6d37f9a0c40539380b927fd4b53a3bf94e4df21ae6ea8e407a46df057c43477e2f7b27c67c3751d03e8b31c959ffff7f20010000000200000002b96824c26e89b2fa9989c682412fe3a16372fcdf6c0dce872a7e2d2728c6d69f6e441b8424dfddfcae9954c3a603210ef1336ba8a30e63b4fb0a25c6b8103dcd0105")
};

std::vector<unsigned char> pegin_transaction = ParseHex("020000000001016e441b8424dfddfcae9954c3a603210ef1336ba8a30e63b4fb0a25c6b8103dcd0100004000ffffffff0201e48a1a02a8f799892fda58347c2d794144311d4307dbfd10f77ffe28088c60be01000000003b9aade0001976a914a4c05e4e702cec80df26074843a189cfb05bebdb88ac01e48a1a02a8f799892fda58347c2d794144311d4307dbfd10f77ffe28088c60be010000000000001c200000000002483045022100b2d5f19291a3297f28802a6a2bfef2bc0c440660c55a399bfa89533277bcfdcc022042a003eadd85bcc7fb568f9025d6d869ee5e52084613c859cfae6c929766f75e012103ced1fe72e7e33f37747782a505c94f26c1451e8ceceaef8c75f175f87fdb2e87060400ca9a3b20e48a1a02a8f799892fda58347c2d794144311d4307dbfd10f77ffe28088c60be2006226e46111a0b59caaf126043eb5bbf28c34f3a5e332a1fc7b2b73cf188910f160014542a5a8eea9945cc3d7e24468f108b8e0c721a81fdc401020000000365d984d2d0323bbab4807c12c533c014491596929082b1e684205c3fa80397f4010000006b483045022100dfc4741b5dadb6c4c9bd8774d037450e1a281dc2fd73d84115d1d68863d7fc6f02201cfb193bb929ef0e84dfcea5b37bea6484b7a54e79d5a74968a7f3baa79d67880121035b218cb6172451fec3fc467a71938d7e78f425cd76a771da9f193f952ca8c812feffffff6f17f18a671f8e67bdb666e36d8941c1d8ee29b85d9bddbeedbc2973f44fd6bb0000000049483045022100a0848deef222213765ce67f41528e0df6b3877a5f2810d4800759ea8616479ac022058fa148daa1ed7daab46ec0cfe373c17d82d6281cb8e9c7a4a7334136c5e4f0501feffffff9e6a22f9045ec732bad1c0f98d81bd2c9a1b4d4adbfabefb09a9d49e354e80350000000049483045022100ff7c9f9e145c5572d4b21a65a1fbc3331ee3a6757f378554223d963f0f2821d2022048d4c12e7bc4333a2393778645f385f7266176f42e3e86d6af3f0508cc1eed5c01feffffff025892dc01000000001976a914d85a6ba69df7c74e53ec7b99e424c24e2db6d8c988ac00ca9a3b0000000017a914a8105ab6cc3d9aa6ecd9736989d3388c933250e28728030000970000002088912d3d4e77e8b023382aad412b06a56db195666744eb6d37f9a0c40539380b927fd4b53a3bf94e4df21ae6ea8e407a46df057c43477e2f7b27c67c3751d03e8b31c959ffff7f20010000000200000002b96824c26e89b2fa9989c682412fe3a16372fcdf6c0dce872a7e2d2728c6d69f6e441b8424dfddfcae9954c3a603210ef1336ba8a30e63b4fb0a25c6b8103dcd01050000000000000000");

COutPoint prevout(uint256S("cd3d10b8c6250afbb4630ea3a86b33f10e2103a6c35499aefcdddf24841b446e"), 1);

// Needed for easier parent PoW check, and setting fedpegscript
struct RegtestingSetup : public TestingSetup {
        RegtestingSetup() : TestingSetup(CBaseChainParams::REGTEST, "512103dff4923d778550cc13ce0d887d737553b4b58f4e8e886507fc39f5e447b2186451ae") {}
};

BOOST_FIXTURE_TEST_SUITE(pegin_witness_tests, RegtestingSetup)

BOOST_AUTO_TEST_CASE(witness_valid)
{

    CScriptWitness witness;
    witness.stack = witness_stack;

    BOOST_CHECK(IsValidPeginWitness(witness, prevout));

    // Missing byte on each field to make claim ill-formatted
    // This will break deserialization and other data-matching checks
    for (unsigned int i = 0; i < witness.stack.size(); i++) {
        witness.stack[i].pop_back();
        BOOST_CHECK(!IsValidPeginWitness(witness, prevout));
        witness.stack = witness_stack;
        BOOST_CHECK(IsValidPeginWitness(witness, prevout));
    }

    // Test mismatched but valid nOut to proof
    COutPoint fake_prevout = prevout;
    fake_prevout.n = 0;
    BOOST_CHECK(!IsValidPeginWitness(witness, fake_prevout));

    // Test mistmatched but valid txid
    fake_prevout = prevout;
    fake_prevout.hash = uint256S("2f103ee04a5649eecb932b4da4ca9977f53a12bbe04d9d1eb5ccc0f4a06334");
    BOOST_CHECK(!IsValidPeginWitness(witness, fake_prevout));

    // Ensure that all witness stack sizes are handled
    BOOST_CHECK(IsValidPeginWitness(witness, prevout));
    for (unsigned int i = 0; i < witness.stack.size(); i++) {
        witness.stack.pop_back();
        BOOST_CHECK(!IsValidPeginWitness(witness, prevout));
    }
    witness.stack = witness_stack;

    // Extra element causes failure
    witness.stack.push_back(witness.stack.back());
    BOOST_CHECK(!IsValidPeginWitness(witness, prevout));
    witness.stack = witness_stack;

    // Check validation of peg-in transaction's inputs and balance
    CDataStream ssTx(pegin_transaction, SER_NETWORK, PROTOCOL_VERSION);
    CTransactionRef txRef;
    ssTx >> txRef;
    CTransaction tx(*txRef);

    // Only one(valid) input witness should exist, and should match
    BOOST_CHECK(tx.wit.vtxinwit.size() == 1);
    BOOST_CHECK(tx.wit.vtxinwit[0].m_pegin_witness.stack == witness_stack);
    BOOST_CHECK(tx.vin[0].m_is_pegin);
    // Check that serialization doesn't cause issuance to become non-null
    BOOST_CHECK(tx.vin[0].assetIssuance.IsNull());
    BOOST_CHECK(IsValidPeginWitness(tx.wit.vtxinwit[0].m_pegin_witness, prevout));

    std::set<std::pair<uint256, COutPoint> > setPeginsSpent;
    CValidationState state;
    CCoinsView coinsDummy;
    CCoinsViewCache coins(&coinsDummy);
    BOOST_CHECK(Consensus::CheckTxInputs(tx, state, coins, 0, setPeginsSpent, nullptr, false));
    BOOST_CHECK(setPeginsSpent.size() == 1);
    setPeginsSpent.clear();

    // Strip pegin_witness
    CMutableTransaction mtxn(tx);
    mtxn.wit.vtxinwit[0].m_pegin_witness.SetNull();
    CTransaction tx2(mtxn);
    BOOST_CHECK(!Consensus::CheckTxInputs(tx2, state, coins, 0, setPeginsSpent, nullptr, false));
    BOOST_CHECK(setPeginsSpent.empty());

    // Invalidate peg-in (and spending) authorization by pegin marker.
    // This only checks for peg-in authorization, with the only input marked
    // as m_is_pegin
    CMutableTransaction mtxn2(tx);
    mtxn2.vin[0].m_is_pegin = false;
    CTransaction tx3(mtxn2);
    BOOST_CHECK(!Consensus::CheckTxInputs(tx3, state, coins, 0, setPeginsSpent, nullptr, false));
    BOOST_CHECK(setPeginsSpent.empty());


    // TODO Test mixed pegin/non-pegin input case
    // TODO Test spending authorization in conjunction with valid witness program in pegin auth

}

BOOST_AUTO_TEST_SUITE_END()
