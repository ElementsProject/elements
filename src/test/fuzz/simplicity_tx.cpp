// Copyright (c) 2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <span.h>
#include <primitives/transaction.h>
#include <script/sigcache.h>
#include <validation.h>
extern "C" {
#include <simplicity/cmr.h>
#include <simplicity/elements/env.h>
#include <simplicity/elements/exec.h>
}
#include <test/fuzz/FuzzedDataProvider.h>
#include <test/fuzz/fuzz.h>
#include <test/fuzz/util.h>

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

static uint256 GENESIS_HASH;

static CConfidentialAsset INPUT_ASSET_UNCONF{};
static CConfidentialAsset INPUT_ASSET_CONF{};
static CConfidentialValue INPUT_VALUE_UNCONF{};
static CConfidentialValue INPUT_VALUE_CONF{};

const unsigned int VERIFY_FLAGS = SCRIPT_VERIFY_NONE
    | SCRIPT_VERIFY_P2SH
    | SCRIPT_VERIFY_WITNESS
    | SCRIPT_VERIFY_DERSIG
    | SCRIPT_VERIFY_CHECKLOCKTIMEVERIFY
    | SCRIPT_VERIFY_CHECKSEQUENCEVERIFY
    | SCRIPT_VERIFY_TAPROOT
    | SCRIPT_VERIFY_NULLDUMMY
    | SCRIPT_SIGHASH_RANGEPROOF
    | SCRIPT_VERIFY_SIMPLICITY;

void initialize_simplicity_tx()
{
    g_con_elementsmode = true;
    // Copied from init.cpp AppInitMain
    InitSignatureCache();
    InitScriptExecutionCache();
    InitRangeproofCache();
    InitSurjectionproofCache();

    GENESIS_HASH = uint256S("0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206");

    INPUT_VALUE_UNCONF.SetToAmount(12345678);
    INPUT_VALUE_CONF.vchCommitment = {
        0x08,
        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
        0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,
        0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,
        0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38,
    };

    INPUT_ASSET_UNCONF.vchCommitment = INPUT_VALUE_CONF.vchCommitment;
    INPUT_ASSET_UNCONF.vchCommitment[0] = 0x01;
    INPUT_ASSET_CONF.vchCommitment = INPUT_VALUE_CONF.vchCommitment;
    INPUT_ASSET_CONF.vchCommitment[0] = 0x0a;
}

FUZZ_TARGET_INIT(simplicity_tx, initialize_simplicity_tx)
{
    simplicity_err error;

    // 1. (no-op) run through Rust code
    //
    // 2. Construct transaction.
    CMutableTransaction mtx;
    {
        CDataStream txds{buffer, SER_NETWORK, INIT_PROTO_VERSION};
        try {
            txds >> mtx;
        } catch (const std::ios_base::failure&) {
            return;
        }
        mtx.witness.vtxoutwit.resize(mtx.vout.size());

        // If no inputs have witnesses, all the code below should continue to work -- we
        // should be able to call `PrecomputedTransactionData::Init` on a legacy transaction
        // without any trouble. In this case it will set txdata.m_simplicity_tx_data to
        // NULL, and we won't be able to go any further, but there should be no crashes
        // or memory issues.
        if (!mtx.witness.vtxinwit.empty()) {
            mtx.witness.vtxinwit.resize(mtx.vin.size());
            // This is an assertion in the Simplicity interpreter. It is guaranteed
            // to hold for anything on the network since (even if validatepegin is off)
            // pegins are validated for well-formedness long before the script interpreter
            // is invoked. But in this code we just call the interpreter directly without
            // these checks.
            for (unsigned i = 0; i < mtx.vin.size(); i++) {
                if (mtx.vin[i].m_is_pegin && (mtx.witness.vtxinwit[i].m_pegin_witness.stack.size() < 4 || mtx.witness.vtxinwit[i].m_pegin_witness.stack[2].size() != 32)) {
                    return;
                }
            }
        }

        // We use the first vin as a "random oracle" rather than reading more from
        // the fuzzer, because we want our fuzz seeds to have as simple a structure
        // as possible. This means we must reject 0-input transactions, which are
        // invalid on-chain anyway.
        if (mtx.vin.size() == 0) {
            return;
        }
    }
    const auto& random_bytes = mtx.vin[0].prevout.hash;

    // 3. Construct `nIn` and `spent_outs` arrays.
    bool expect_simplicity = false;
    std::vector<CTxOut> spent_outs{};
    unsigned char last_cmr[32] = { 0 };
    for (unsigned int i = 0; i < mtx.vin.size(); i++) {
        // Null asset or value would assert in the interpreter, and are impossible
        // to hit in real transactions. Nonces are not included in the UTXO set and
        // therefore don't matter.
        CConfidentialValue value = i & 1 ? INPUT_VALUE_CONF : INPUT_VALUE_UNCONF;
        CConfidentialAsset asset = i & 2 ? INPUT_ASSET_CONF : INPUT_ASSET_UNCONF;
        CScript scriptPubKey;
        if (i < random_bytes.size()) {
            if (i & 1 && random_bytes.data()[i] & 1) {
                value.vchCommitment[0] ^= 1;
            }
            if (i & 2 && random_bytes.data()[i] & 2) {
                asset.vchCommitment[0] ^= 1;
            }
        }

        // Check for size 4: a Simplicity program will always have a witness, program,
        // CMR, control block and (maybe) annex, in that order. If the annex is present,
        // then checking for size 4 doesn't guarantee that a witness is present, but
        // that is ok at this point. (In fact, it is a useful thing to check.)
        if (i < mtx.witness.vtxinwit.size()) {
            auto& current = mtx.witness.vtxinwit[i].scriptWitness.stack;
            if (current.size() >= 4) {
                size_t top = current.size();
                if (!current[top - 1].empty() && current[top - 1][0] == 0x50) {
                    --top;
                }
                const auto& control = current[top - 1];
                const auto& program = current[top - 3];

                if (control.size() >= TAPROOT_CONTROL_BASE_SIZE && (control[0] & 0xfe) == 0xbe) {
                    // The fuzzer won't be able to produce a valid CMR on its own, so we compute it
                    // and jam it into the witness stack. But we do require the fuzzer give us a
                    // place to put it, so we don't have to resize the stack (and so that actual
                    // valid transactions will work with this code).
                    // Compute CMR and do some sanity checks on it (and the program)
                    std::vector<unsigned char> cmr(32, 0);
                    assert(simplicity_computeCmr(&error, cmr.data(), program.data(), program.size()));
                    if (error == SIMPLICITY_NO_ERROR) {
                        if (memcmp(last_cmr, cmr.data(), sizeof(last_cmr)) == 0) {
                            // If we have already seen this CMR this transaction, try mangling
                            // it to check that this produces a CMR error and not something worse.
                            cmr.data()[1] ^= 1;
                        }
                        memcpy(last_cmr, cmr.data(), sizeof(last_cmr));
                    }

                    const XOnlyPubKey internal{Span{control}.subspan(1, TAPROOT_CONTROL_BASE_SIZE - 1)};

                    const CScript leaf_script{cmr.begin(), cmr.end()};
                    const uint256 tapleaf_hash = ComputeTapleafHash(0xbe, leaf_script);
                    uint256 merkle_root = ComputeTaprootMerkleRoot(control, tapleaf_hash);
                    auto ret = internal.CreateTapTweak(&merkle_root);
                    if (ret.has_value()) {
                        expect_simplicity = (error == SIMPLICITY_NO_ERROR);
                        // Just drop the parity; it needs to match the one in the control block,
                        // but we want to test that logic, so we allow them not to match.
                        const XOnlyPubKey output_key = ret->first;
                        // If we made it here, success (aside from parity maybe)
                        current[top - 2] = std::move(cmr);
                        scriptPubKey = CScript() << OP_1 << ToByteVector(output_key);
                    }
                }
            }
        }
        // For scripts that we're not using, set them to various witness programs to try to
        // trick the interpreter into treating them as taproot or simplicity outputs. It
        // should fail but shouldn't crash or anything.
        //
        // We don't cover all cases, so this may result in the empty scriptpubkey -- this is
        // impossible on-chain but it shouldn't hurt anything.
        if (scriptPubKey.empty()) {
            if (i < random_bytes.size()) {
                switch(random_bytes.data()[i] >> 6) {
                case 0:
                    scriptPubKey << OP_TRUE;
                    break;
                case 1:
                    scriptPubKey << OP_0 << std::vector<unsigned char>(20, 0xab);
                    break;
                case 2:
                    scriptPubKey << OP_0 << std::vector<unsigned char>(32, 0xcd);
                    break;
                case 3:
                    scriptPubKey << OP_1 << std::vector<unsigned char>(32, 0xef);
                    break;
                }
            }
        }

        spent_outs.push_back(CTxOut{asset, value, scriptPubKey});
    }
    assert(spent_outs.size() == mtx.vin.size());

    // 4. Test via scriptcheck
    PrecomputedTransactionData txdata{GENESIS_HASH};
    std::vector<CTxOut> spent_outs_copy{spent_outs};
    txdata.Init(mtx, std::move(spent_outs_copy));
    if (expect_simplicity) {
        // The converse of this is not true -- if !expect_simplicity, it's still possible
        // that we will allocate Simplicity data. The check for whether to do this is very
        // lax: is this a 34-byte scriptPubKey that starts with OP_1 and does it have a
        // nonempty witness.
        assert(txdata.m_simplicity_tx_data_ptr);
        assert(txdata.m_simplicity_tx_data_ptr->m_simplicity_tx_data);
    }

    const CTransaction tx{mtx};
    for (unsigned i = 0; i < tx.vin.size(); i++) {
        CScriptCheck check{txdata.m_spent_outputs[i], tx, i, VERIFY_FLAGS, false /* cache */, &txdata};
        check();
    }
}
