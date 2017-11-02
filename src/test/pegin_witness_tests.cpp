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
    ParseHex("00ca9a3b00000000"),
    ParseHex("e48a1a02a8f799892fda58347c2d794144311d4307dbfd10f77ffe28088c60be"),
    ParseHex("06226e46111a0b59caaf126043eb5bbf28c34f3a5e332a1fc7b2b73cf188910f"),
    ParseHex("001490d2639f54fe5ef68765e6436fdcd026d373f6a2"),
    ParseHex("0200000001ddd30904ddd0876eb39c718615257cb18685dccf1ca729476c01fdb1ac81bc76000000006a473044022060210291ad3cc5ce4dcfde66f9f2e838bd1f99035630902c4e839c6e8a90cb1002205c63da2b84ba624faf3d349d35a637f50b071dfe008ca2bff1cc91be8c77b1c00121029d2bc6d7ca682460e19ffc7a5bb4ec644015e4a4eef2e69706cc25869ddbf0f9feffffff0200ca9a3b0000000017a914a7b4a529506168a41ffb6de37c001fbf50086fbc87802675e8000000001976a9144a51d6e1deaee9a8d1d9e9ff9667af617c5bbb9d88ac65000000"),
    ParseHex("00000020370e2e1744d6a7737760a613785ca4c2e63859bbe496a4debc856474bd0a2a52d9d53f142aaeeacf803cd244bb00d505bbc3ef56868fe12f79c843a4fcd68e898172fb59ffff7f20010000000300000002b10cff03945bc3d0efd5c7228367c2b4b015dc94595e22ef8d09712ffca39df3c63123fe899e560e5b1060cb0cb16555acf166fa060cc4e8bfc22a812bbd3616010d")
};

std::vector<unsigned char> pegin_transaction = ParseHex("020000000101c63123fe899e560e5b1060cb0cb16555acf166fa060cc4e8bfc22a812bbd36160000004000ffffffff0201e48a1a02a8f799892fda58347c2d794144311d4307dbfd10f77ffe28088c60be01000000003b9ab240001976a914e642eae0e083e8d2dfacd626a7aedd07ee454a2688ac01e48a1a02a8f799892fda58347c2d794144311d4307dbfd10f77ffe28088c60be0100000000000017c00000000000000000024830450221009ed9f3ae842b4fef4f47e64699d5ef6b7d647208751fdfe76c884f418a2582330220233a39e6cf24b716809dd6ef4beecc62e2ac8036fd66b03fd48a40a0e279062f0121033e00debbdcbe0f42f855fa64099a8984fba6f60d639a577f35c8bbf60d3d9a27060800ca9a3b0000000020e48a1a02a8f799892fda58347c2d794144311d4307dbfd10f77ffe28088c60be2006226e46111a0b59caaf126043eb5bbf28c34f3a5e332a1fc7b2b73cf188910f16001490d2639f54fe5ef68765e6436fdcd026d373f6a2df0200000001ddd30904ddd0876eb39c718615257cb18685dccf1ca729476c01fdb1ac81bc76000000006a473044022060210291ad3cc5ce4dcfde66f9f2e838bd1f99035630902c4e839c6e8a90cb1002205c63da2b84ba624faf3d349d35a637f50b071dfe008ca2bff1cc91be8c77b1c00121029d2bc6d7ca682460e19ffc7a5bb4ec644015e4a4eef2e69706cc25869ddbf0f9feffffff0200ca9a3b0000000017a914a7b4a529506168a41ffb6de37c001fbf50086fbc87802675e8000000001976a9144a51d6e1deaee9a8d1d9e9ff9667af617c5bbb9d88ac650000009700000020370e2e1744d6a7737760a613785ca4c2e63859bbe496a4debc856474bd0a2a52d9d53f142aaeeacf803cd244bb00d505bbc3ef56868fe12f79c843a4fcd68e898172fb59ffff7f20010000000300000002b10cff03945bc3d0efd5c7228367c2b4b015dc94595e22ef8d09712ffca39df3c63123fe899e560e5b1060cb0cb16555acf166fa060cc4e8bfc22a812bbd3616010d00000000");

COutPoint prevout(uint256S("1636bd2b812ac2bfe8c40c06fa66f1ac5565b10ccb60105b0e569e89fe2331c6"), 0);

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
    fake_prevout.n = 1;
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
