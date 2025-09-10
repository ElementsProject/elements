// Copyright (c) 2017-2017 Blockstream
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <clientversion.h>
#include <chainparams.h>
#include <checkqueue.h>
#include <consensus/tx_verify.h>
#include <consensus/validation.h>
#include <core_io.h>
#include <validation.h> // For CheckTransaction
#include <pegins.h>
#include <policy/policy.h>
#include <script/script.h>
#include <script/script_error.h>
#include <util/strencodings.h>
#include <validation.h>
#include <streams.h>
#include <test/util/setup_common.h>
#include <util/system.h>

#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/split.hpp>
#include <boost/test/unit_test.hpp>

std::vector<std::vector<unsigned char> > witness_stack = {
    ParseHex("00ca9a3b00000000"),
    ParseHex("ef4699c160d014d5ff79636d8a4cb990b9df4ebab649f144d19f5c495c585e47"),
    ParseHex("06226e46111a0b59caaf126043eb5bbf28c34f3a5e332a1fc7b2b73cf188910f"),
    ParseHex("00141eef6361cd1507a303834285d1521d6baf1b19ae"),
    ParseHex("0200000001b399292c8100b8a1b66eb23896f799c1712390d560af0f70e81acd2d17a3b06e0000000049483045022100c3c749623486ea57ea93dfaf78d85590d78c7590a25768fe80f0ea4d6047419002202a0a00a90392b86c53c0fdda908c4591ba28040c16c25734c23b7df3c8b70acd01feffffff0228196bee000000001976a914470dd41542ee1a1bd75f1a838878648c8d65622488ac00ca9a3b0000000017a914cb60b1d7f76ba12b45a116c482c165a74c5d7e388765000000"),
    ParseHex("000000205e3913a320cd2e3a2efa141e47419f54cb9e82320cf8dbc812fc19b9a1b2413a57f5e9fb4fa22de191454a241387f5d10cc794ee0fbf72ae2841baf3129a4eab8133025affff7f20000000000200000002f9d0be670007d38fceece999cb6144658a99c307ccc37f6d8f69129ed0f4545ff321df9790633bc33c67239c4174df8142ee616ee6a2e2788fe4820fe70e9bce0105")
};

std::vector<unsigned char> pegin_transaction = ParseHex("020000000101f321df9790633bc33c67239c4174df8142ee616ee6a2e2788fe4820fe70e9bce0100004000ffffffff0201ef4699c160d014d5ff79636d8a4cb990b9df4ebab649f144d19f5c495c585e4701000000003b9ab2e0001976a914809326f7628dc976fbe63806479a1b8dfcc8c4b988ac01ef4699c160d014d5ff79636d8a4cb990b9df4ebab649f144d19f5c495c585e47010000000000001720000000000000000002483045022100ae17064745d80650a6a5cbcbe15c8c45ba498d1c6f45a7c0f5f32d871b463fc60220799f2836471702c21f7cfe124651727b530ad41f7af4dc213c65f5030a2f6fc4012103a9d3c6c7c161a565a76113632fe13330cf2c0207ba79a76d1154cdc3cb94d940060800ca9a3b0000000020ef4699c160d014d5ff79636d8a4cb990b9df4ebab649f144d19f5c495c585e472006226e46111a0b59caaf126043eb5bbf28c34f3a5e332a1fc7b2b73cf188910f1600141eef6361cd1507a303834285d1521d6baf1b19aebe0200000001b399292c8100b8a1b66eb23896f799c1712390d560af0f70e81acd2d17a3b06e0000000049483045022100c3c749623486ea57ea93dfaf78d85590d78c7590a25768fe80f0ea4d6047419002202a0a00a90392b86c53c0fdda908c4591ba28040c16c25734c23b7df3c8b70acd01feffffff0228196bee000000001976a914470dd41542ee1a1bd75f1a838878648c8d65622488ac00ca9a3b0000000017a914cb60b1d7f76ba12b45a116c482c165a74c5d7e38876500000097000000205e3913a320cd2e3a2efa141e47419f54cb9e82320cf8dbc812fc19b9a1b2413a57f5e9fb4fa22de191454a241387f5d10cc794ee0fbf72ae2841baf3129a4eab8133025affff7f20000000000200000002f9d0be670007d38fceece999cb6144658a99c307ccc37f6d8f69129ed0f4545ff321df9790633bc33c67239c4174df8142ee616ee6a2e2788fe4820fe70e9bce010500000000");

COutPoint prevout(uint256S("ce9b0ee70f82e48f78e2a2e66e61ee4281df74419c23673cc33b639097df21f3"), 1);

const std::string fedpegscript_str = "512103dff4923d778550cc13ce0d887d737553b4b58f4e8e886507fc39f5e447b2186451ae";

// Needed for easier parent PoW check, and setting fedpegscript
struct FedpegSetup : public BasicTestingSetup {
        FedpegSetup() : BasicTestingSetup("custom", fedpegscript_str) {}
};

BOOST_FIXTURE_TEST_SUITE(pegin_witness_tests, FedpegSetup)

BOOST_AUTO_TEST_CASE(witness_valid)
{
    CScriptWitness witness;
    witness.stack = witness_stack;

    std::string err;

    std::vector<unsigned char> fedpegscript_bytes = ParseHex(fedpegscript_str);
    CScript fedpegscript(fedpegscript_bytes.begin(), fedpegscript_bytes.end());
    // Test sample was generated as "legacy" with p2sh-p2wsh fedpegscript
    CScript fedpeg_program(GetScriptForDestination(ScriptHash(GetScriptForDestination(WitnessV0ScriptHash(fedpegscript)))));
    std::vector<std::pair<CScript, CScript>> fedpegscripts;
    // TODO test with additional scripts
    fedpegscripts.push_back(std::make_pair(fedpeg_program, fedpegscript));

    bool valid = IsValidPeginWitness(witness, fedpegscripts, prevout, err, false);
    BOOST_CHECK(err == "");
    BOOST_CHECK(valid);

    // Missing byte on each field to make claim ill-formatted
    // This will break deserialization and other data-matching checks
    for (unsigned int i = 0; i < witness.stack.size(); i++) {
        witness.stack[i].pop_back();
        BOOST_CHECK(!IsValidPeginWitness(witness, fedpegscripts, prevout, err, false));
        witness.stack = witness_stack;
        BOOST_CHECK(IsValidPeginWitness(witness, fedpegscripts, prevout, err, false));
    }

    // Test mismatched but valid nOut to proof
    COutPoint fake_prevout = prevout;
    fake_prevout.n = 0;
    BOOST_CHECK(!IsValidPeginWitness(witness, fedpegscripts, fake_prevout, err, false));

    // Test mismatched but valid txid
    fake_prevout = prevout;
    fake_prevout.hash = uint256S("2f103ee04a5649eecb932b4da4ca9977f53a12bbe04d9d1eb5ccc0f4a06334");
    BOOST_CHECK(!IsValidPeginWitness(witness, fedpegscripts, fake_prevout, err, false));

    // Ensure that all witness stack sizes are handled
    BOOST_CHECK(IsValidPeginWitness(witness, fedpegscripts, prevout, err, false));
    for (unsigned int i = 0; i < witness.stack.size(); i++) {
        witness.stack.pop_back();
        BOOST_CHECK(!IsValidPeginWitness(witness, fedpegscripts, prevout, err, false));
    }
    witness.stack = witness_stack;

    // Extra element causes failure
    witness.stack.push_back(witness.stack.back());
    BOOST_CHECK(!IsValidPeginWitness(witness, fedpegscripts, prevout, err, false));
    witness.stack = witness_stack;

    // Check validation of peg-in transaction's inputs and balance
    CDataStream ssTx(pegin_transaction, SER_NETWORK, PROTOCOL_VERSION);
    CTransactionRef txRef;
    try {
        ssTx >> txRef;
    } catch (...) {
        BOOST_CHECK(false);
        return;
    }
    CTransaction tx(*txRef);

    // Only one(valid) input witness should exist, and should match
    BOOST_CHECK(tx.witness.vtxinwit.size() == 1);
    BOOST_CHECK(tx.witness.vtxinwit[0].m_pegin_witness.stack == witness_stack);
    BOOST_CHECK(tx.vin[0].m_is_pegin);
    // Check that serialization doesn't cause issuance to become non-null
    BOOST_CHECK(tx.vin[0].assetIssuance.IsNull());
    BOOST_CHECK(IsValidPeginWitness(tx.witness.vtxinwit[0].m_pegin_witness, fedpegscripts, prevout, err, false));

    CAmountMap fee_map;

    std::set<std::pair<uint256, COutPoint>> setPeginsSpent;
    TxValidationState state;
    CCoinsView coinsDummy;
    CCoinsViewCache coins(&coinsDummy);
    // Get the latest block index to look up fedpegscripts
    // For these tests, should be genesis-block-hardcoded consensus.fedpegscript
    BOOST_CHECK(Consensus::CheckTxInputs(tx, state, coins, 0, fee_map, setPeginsSpent, NULL, false, true, fedpegscripts));
    BOOST_CHECK(setPeginsSpent.size() == 1);
    setPeginsSpent.clear();

    // Strip pegin_witness
    CMutableTransaction mtxn(tx);
    mtxn.witness.vtxinwit[0].m_pegin_witness.SetNull();
    CTransaction tx2(mtxn);
    BOOST_CHECK(!Consensus::CheckTxInputs(tx2, state, coins, 0, fee_map, setPeginsSpent, NULL, false, true, fedpegscripts));
    BOOST_CHECK(setPeginsSpent.empty());

    // Invalidate peg-in (and spending) authorization by pegin marker.
    // This only checks for peg-in authorization, with the only input marked
    // as m_is_pegin
    CMutableTransaction mtxn2(tx);
    mtxn2.vin[0].m_is_pegin = false;
    CTransaction tx3(mtxn2);
    BOOST_CHECK(!Consensus::CheckTxInputs(tx3, state, coins, 0, fee_map, setPeginsSpent, NULL, false, true, fedpegscripts));
    BOOST_CHECK(setPeginsSpent.empty());


    // TODO Test mixed pegin/non-pegin input case
    // TODO Test spending authorization in conjunction with valid witness program in pegin auth

}

BOOST_AUTO_TEST_SUITE_END()
