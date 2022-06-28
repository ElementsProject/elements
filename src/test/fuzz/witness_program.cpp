// Copyright (c) 2009-2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <policy/policy.h>
#include <pubkey.h>
#include <secp256k1.h>
#include <secp256k1_schnorrsig.h>
#include <script/interpreter.h>
#include <span.h>
#include <streams.h>

#include <test/fuzz/fuzz.h>

class DummySigChecker : public MutableTransactionSignatureChecker {
    bool CheckECDSASignature(const std::vector<unsigned char>& vchSig, const std::vector<unsigned char>& vchPubKey, const CScript& scriptCode, SigVersion sigversion, unsigned int flags) const override { return !vchSig.empty() && vchSig[0] > 0x80; }

    bool CheckSchnorrSignature(Span<const unsigned char> sig, Span<const unsigned char> pubkey, SigVersion sigversion, const ScriptExecutionData& execdata, ScriptError* serror = nullptr) const override { return !sig.empty() && sig[0] > 0x80; }

public:
    DummySigChecker(const CMutableTransaction* txToIn, unsigned int nInIn, const CConfidentialValue& amountIn, const PrecomputedTransactionData& txdataIn, MissingDataBehavior mdb) : MutableTransactionSignatureChecker{txToIn, nInIn, amountIn, txdataIn, mdb} {}
};

void initialize_witness_program()
{
    static const ECCVerifyHandle verify_handle;
}

FUZZ_TARGET_INIT(witness_program, initialize_witness_program)
{
    CDataStream ds(buffer, SER_NETWORK, INIT_PROTO_VERSION);
    try {
        CMutableTransaction tx;
        unsigned int nIn;
        CConfidentialValue amountIn;
        ds >> tx;
        ds >> nIn;
        ds >> amountIn;

        if (tx.vin.empty() || tx.witness.vtxinwit.size() != tx.vin.size()) {
            return; // if we have no inputs then our script environment doesn't make sense
        }
        nIn %= tx.vin.size();
        PrecomputedTransactionData txdata{};

        CScriptWitness witness;
        int fuzz_control;
        int flags;
        ds >> fuzz_control;
        ds >> witness.stack;
        ds >> flags;

        if ((flags & SCRIPT_VERIFY_CLEANSTACK) != 0) {
            flags |= SCRIPT_VERIFY_P2SH;
            flags |= SCRIPT_VERIFY_WITNESS;
        }
        if ((flags & SCRIPT_VERIFY_WITNESS) != 0) {
            flags |= SCRIPT_VERIFY_P2SH;
        }

        /* segwit v0 */
        std::vector<unsigned char> program;
        ds >> program;

        if (fuzz_control & 1) {
            unsigned char hash_program[32];
            CSHA256().Write(&program[0], program.size()).Finalize(hash_program);
            CScript scriptPubKey = CScript{} << OP_0 << std::vector<unsigned char>(hash_program, hash_program + sizeof(hash_program));
            witness.stack.push_back(program);

            std::vector<CTxOut> spent_outs{};
            for (unsigned int i = 0; i < tx.vin.size(); i++) {
                CConfidentialAsset asset;
                CConfidentialValue value;
                ds >> asset;
                ds >> value;
                if (asset.IsNull() || value.IsNull()) {
                    // this asserts in the interpreter, and are impossible to hit with real transactions
                    return;
                }
                if (i == nIn) {
                    spent_outs.push_back(CTxOut{asset, value, scriptPubKey});
                } else {
                    CScript script;
                    ds >> script;
                    spent_outs.push_back(CTxOut{asset, value, script});
                }
                tx.witness.vtxinwit[i].scriptWitness.stack.push_back(program);
            }
            txdata.Init(tx, std::move(spent_outs));
            DummySigChecker checker{&tx, nIn, amountIn, txdata, MissingDataBehavior::ASSERT_FAIL};

            VerifyScript(/* scriptSig */ CScript{}, scriptPubKey, &witness, flags, checker, /* serror */ NULL);
        /* segwit v1 (taproot) */
        } else {
            /* Generate keys */
            uint256 xonlypk;
            ds >> xonlypk;
            XOnlyPubKey intkey(xonlypk);

            uint256 tapleaf_hash = (CHashWriter(HASHER_TAPLEAF_ELEMENTS) << uint8_t(TAPROOT_LEAF_TAPSCRIPT) << program).GetSHA256();
            auto extkey_parity = intkey.CreateTapTweak(&tapleaf_hash);
            if (!extkey_parity) {
                return;
            }

            /* Serialize keys */
            CScript scriptPubKey = CScript{} << OP_1 << std::vector<unsigned char>(extkey_parity->first.begin(), extkey_parity->first.end());
            witness.stack.push_back(program);

            std::vector<unsigned char> control;
            control.push_back(TAPROOT_LEAF_TAPSCRIPT | extkey_parity->second);
            control.insert(control.end(), intkey.begin(), intkey.end());
            witness.stack.push_back(control);

            std::vector<CTxOut> spent_outs{};
            for (unsigned int i = 0; i < tx.vin.size(); i++) {
                CConfidentialAsset asset;
                CConfidentialValue value;
                ds >> asset;
                ds >> value;
                if (asset.IsNull() || value.IsNull()) {
                    // this asserts in the interpreter, and are impossible to hit with real transactions
                    return;
                }
                if (i == nIn) {
                    spent_outs.push_back(CTxOut{asset, value, scriptPubKey});
                } else {
                    CScript script;
                    ds >> script;
                    spent_outs.push_back(CTxOut{asset, value, script});
                }
                tx.witness.vtxinwit[i].scriptWitness.stack.push_back(program);
                tx.witness.vtxinwit[i].scriptWitness.stack.push_back(control);
            }
            txdata.Init(tx, std::move(spent_outs));
            GenericTransactionSignatureChecker checker{&tx, nIn, amountIn, txdata, MissingDataBehavior::ASSERT_FAIL};

            VerifyScript(/* scriptSig */ CScript{}, scriptPubKey, &witness, flags, checker, /* serror */ NULL);
        }
    } catch (const std::ios_base::failure&) {
        return;
    }
}

