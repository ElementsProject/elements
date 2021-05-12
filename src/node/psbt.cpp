// Copyright (c) 2009-2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <amount.h>
#include <coins.h>
#include <consensus/tx_verify.h>
#include <node/psbt.h>
#include <policy/policy.h>
#include <policy/settings.h>
#include <tinyformat.h>

#include <numeric>

PSBTAnalysis AnalyzePSBT(PartiallySignedTransaction psbtx)
{
    // Go through each input and build status
    PSBTAnalysis result;

    // Elements things
    bool needs_blinded_outputs = false;
    bool has_blinded_outputs = false;

    result.inputs.resize(psbtx.inputs.size());

    for (unsigned int i = 0; i < psbtx.inputs.size(); ++i) {
        PSBTInput& input = psbtx.inputs[i];
        PSBTInputAnalysis& input_analysis = result.inputs[i];

        // We set next role here and ratchet backwards as required
        input_analysis.next = PSBTRole::EXTRACTOR;

        // Check for a UTXO
        CTxOut utxo;
        if (input.GetUTXO(utxo)) {
            if (utxo.nValue.IsExplicit()) {
                if (!MoneyRange(utxo.nValue.GetAmount())) {
                    result.SetInvalid(strprintf("PSBT is not valid. Input %u has invalid value", i));
                    return result;
                }
            } else {
                needs_blinded_outputs = true;
            }
            input_analysis.has_utxo = true;
        } else {
            if (input.non_witness_utxo && *input.prev_out >= input.non_witness_utxo->vout.size()) {
                result.SetInvalid(strprintf("PSBT is not valid. Input %u specifies invalid prevout", i));
                return result;
            }
            input_analysis.has_utxo = false;
            input_analysis.is_final = false;
            input_analysis.next = PSBTRole::UPDATER;
        }

        if (!utxo.IsNull() && utxo.scriptPubKey.IsUnspendable()) {
            result.SetInvalid(strprintf("PSBT is not valid. Input %u spends unspendable output", i));
            return result;
        }

        // Check if it is final
        if (!utxo.IsNull() && !PSBTInputSigned(input)) {
            input_analysis.is_final = false;

            // Figure out what is missing
            SignatureData outdata;
            bool complete = SignPSBTInput(DUMMY_SIGNING_PROVIDER, psbtx, i, 1, &outdata);

            // Things are missing
            if (!complete) {
                input_analysis.missing_pubkeys = outdata.missing_pubkeys;
                input_analysis.missing_redeem_script = outdata.missing_redeem_script;
                input_analysis.missing_witness_script = outdata.missing_witness_script;
                input_analysis.missing_sigs = outdata.missing_sigs;

                // If we are only missing signatures and nothing else, then next is signer
                if (outdata.missing_pubkeys.empty() && outdata.missing_redeem_script.IsNull() && outdata.missing_witness_script.IsNull() && !outdata.missing_sigs.empty()) {
                    input_analysis.next = PSBTRole::SIGNER;
                } else {
                    input_analysis.next = PSBTRole::UPDATER;
                }
            } else {
                input_analysis.next = PSBTRole::FINALIZER;
            }
        } else if (!utxo.IsNull()){
            input_analysis.is_final = true;
        }
    }

    for (const PSBTOutput& output : psbtx.outputs) {
        CTxOut txout = output.GetTxOut();
        if (output.IsBlinded()) {
            has_blinded_outputs = true;
            if (!output.IsFullyBlinded()) {
                result.next = PSBTRole::BLINDER;
            }
        } else {
            // Find the fee output
            if (txout.IsFee()) {
                if (result.fee != nullopt) {
                    result.SetInvalid("There is more than one fee output");
                    return result;
                }
                result.fee = output.amount;
            }
        }
        if (txout.nValue.IsExplicit() && !MoneyRange(txout.nValue.GetAmount())) {
            result.SetInvalid("PSBT is not valid. Output amount invalid");
            return result;
        }
    }

    if (result.fee == nullopt) {
        result.SetInvalid("PSBT missing required fee output");
        return result;
    }

    if (needs_blinded_outputs && !has_blinded_outputs) {
        result.SetInvalid("PSBT has blinded inputs but no blinded outputs. Must have at least one blinded output to balance with the inputs");
        return result;
    }

    // Estimate the size
    CMutableTransaction mtx(psbtx.GetUnsignedTx());
    CCoinsView view_dummy;
    CCoinsViewCache view(&view_dummy);
    bool success = true;

    for (unsigned int i = 0; i < psbtx.inputs.size(); ++i) {
        PSBTInput& input = psbtx.inputs[i];
        Coin newcoin;

        if (!SignPSBTInput(DUMMY_SIGNING_PROVIDER, psbtx, i, 1, nullptr, true) || !input.GetUTXO(newcoin.out)) {
            success = false;
            break;
        } else {
            mtx.vin[i].scriptSig = input.final_script_sig;
            mtx.witness.vtxinwit[i].scriptWitness = input.final_script_witness;
            newcoin.nHeight = 1;
            view.AddCoin(input.GetOutPoint(), std::move(newcoin), true);
        }
    }

    if (success) {
        CTransaction ctx = CTransaction(mtx);
        size_t size = GetVirtualTransactionSize(ctx, GetTransactionSigOpCost(ctx, view, STANDARD_SCRIPT_VERIFY_FLAGS));
        result.estimated_vsize = size;
        // Estimate fee rate
        CFeeRate feerate(*result.fee, size);
        result.estimated_feerate = feerate;
    }

    // Calculate next role for PSBT by grabbing "minimum" PSBTInput next role
    result.next = PSBTRole::EXTRACTOR;
    for (unsigned int i = 0; i < psbtx.inputs.size(); ++i) {
        PSBTInputAnalysis& input_analysis = result.inputs[i];
        result.next = std::min(result.next, input_analysis.next);
    }
    assert(result.next > PSBTRole::CREATOR);

    return result;
}

