// Copyright (c) 2009-2019 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <confidential_validation.h>
#include <pegins.h>
#include <wallet/psbtwallet.h>

TransactionError FillPSBTInputsData(const CWallet* pwallet, PartiallySignedTransaction& psbtx, bool bip32derivs)
{
    LOCK(pwallet->cs_wallet);
    CMutableTransaction& tx = *psbtx.tx;

    // Get all of the previous transactions
    for (unsigned int i = 0; i < tx.vin.size(); ++i) {
        const CTxIn& txin = tx.vin[i];
        PSBTInput& input = psbtx.inputs.at(i);

        if (PSBTInputSigned(input)) {
            continue;
        }

        // Verify input looks sane. This will check that we have at most one uxto, witness or non-witness.
        if (!input.IsSane()) {
            return TransactionError::INVALID_PSBT;
        }

        const uint256& txhash = txin.prevout.hash;
        const auto it = pwallet->mapWallet.find(txhash);
        if (it != pwallet->mapWallet.end()) {
            const CWalletTx& wtx = it->second;
            // If we have no utxo, use the one from the wallet.
            if (!input.non_witness_utxo && input.witness_utxo.IsNull()) {
                // We only need the non_witness_utxo, which is a superset of the witness_utxo.
                //   The signing code will switch to the smaller witness_utxo if this is ok.
                input.non_witness_utxo = wtx.tx;
            }

            // Grab the CA data
            CAmount val_tmp;
            wtx.GetNonIssuanceBlindingData(txin.prevout.n, nullptr, &val_tmp, &input.value_blinding_factor, &input.asset, &input.asset_blinding_factor);
            if (val_tmp != -1) {
                input.value = val_tmp;
            }
        }

        // Get the scriptPubKey to know which SigningProvider to use
        CScript script;
        if (!input.witness_utxo.IsNull()) {
            script = input.witness_utxo.scriptPubKey;
        } else if (input.non_witness_utxo) {
            if (txin.prevout.n >= input.non_witness_utxo->vout.size()) {
                return TransactionError::MISSING_INPUTS;
            }
            script = input.non_witness_utxo->vout[txin.prevout.n].scriptPubKey;
        } else {
            // There's no UTXO so we can just skip this now
            continue;
        }
        SignatureData sigdata;
        input.FillSignatureData(sigdata);
        const SigningProvider* provider = pwallet->GetSigningProvider(script, sigdata);
        if (!provider) {
            continue;
        }

        // Get key origin info for input, if bip32derivs is true. Does not actually sign anything.
        SignPSBTInput(HidingSigningProvider(provider, true /* don't sign */, !bip32derivs), psbtx, i, 1 /* SIGHASH_ALL, ignored */);
    }

    return TransactionError::OK;
}

TransactionError SignPSBT(const CWallet* pwallet, PartiallySignedTransaction& psbtx, bool& complete, int sighash_type, bool sign, bool imbalance_ok, bool bip32derivs)
{
    complete = false;
    // If we're signing, check that the transaction is not still in need of blinding
    if (sign) {
        for (const PSBTOutput& o : psbtx.outputs) {
            if (o.blinding_pubkey.IsValid()) {
                return TransactionError::BLINDING_REQUIRED;
            }
        }
    }

    // Save the original transaction since we need to munge it temporarily, which would violate the PSBT rules
    CTransaction oldtx = CTransaction(*psbtx.tx);

    LOCK(pwallet->cs_wallet);
    CMutableTransaction& tx = *psbtx.tx;
    tx.witness.vtxoutwit.resize(tx.vout.size());

    // Stuff in auxiliary CA blinding data, if we have it
    for (unsigned int i = 0; i < tx.vout.size(); ++i) {
        PSBTOutput& output = psbtx.outputs.at(i);
        CTxOut& out = tx.vout[i];

        if (!output.value_commitment.IsNull()) {
            out.nValue = output.value_commitment;
        }
        if (!output.asset_commitment.IsNull()) {
            out.nAsset = output.asset_commitment;
        }
        if (!output.nonce_commitment.IsNull()) {
            out.nNonce = output.nonce_commitment;
        }

        // The signature can't depend on witness contents, so these are technically not necessary to sign.
        // HOWEVER, as long as we're checking that values balance before signing, they are required.
        CTxOutWitness& outwit = tx.witness.vtxoutwit[i];
        if (!output.range_proof.empty()) {
            outwit.vchRangeproof = output.range_proof;
        }
        if (!output.surjection_proof.empty()) {
            outwit.vchSurjectionproof = output.surjection_proof;
        }
    }

    // Stuff in the peg-in data
    for (unsigned int i = 0; i < tx.vin.size(); ++i) {
        PSBTInput& input = psbtx.inputs[i];
        if (input.value && input.peg_in_tx.which() != 0 && input.txout_proof.which() != 0 && !input.claim_script.empty() && !input.genesis_hash.IsNull()) {
            CScriptWitness pegin_witness;
            if (Params().GetConsensus().ParentChainHasPow()) {
                const Sidechain::Bitcoin::CTransactionRef& btc_peg_in_tx = boost::get<Sidechain::Bitcoin::CTransactionRef>(input.peg_in_tx);
                const Sidechain::Bitcoin::CMerkleBlock& btc_txout_proof = boost::get<Sidechain::Bitcoin::CMerkleBlock>(input.txout_proof);
                pegin_witness = CreatePeginWitness(*input.value, input.asset, input.genesis_hash, input.claim_script, btc_peg_in_tx, btc_txout_proof);
            } else {
                const CTransactionRef& elem_peg_in_tx = boost::get<CTransactionRef>(input.peg_in_tx);
                const CMerkleBlock& elem_txout_proof = boost::get<CMerkleBlock>(input.txout_proof);
                pegin_witness = CreatePeginWitness(*input.value, input.asset, input.genesis_hash, input.claim_script, elem_peg_in_tx, elem_txout_proof);
            }
            tx.vin[i].m_is_pegin = true;
            tx.witness.vtxinwit[i].m_pegin_witness = pegin_witness;
            // Set the witness utxo
            input.witness_utxo = GetPeginOutputFromWitness(tx.witness.vtxinwit[i].m_pegin_witness);
        }
    }

    // This is a convenience/usability check -- it's not invalid to sign an unbalanced transaction, but it's easy to shoot yourself in the foot.
    if (!imbalance_ok) {
        // Get UTXOs for all inputs, to check that amounts balance before signing.
        std::vector<CTxOut> inputs_utxos;
        for (size_t i = 0; i < psbtx.inputs.size(); ++i) {
            PSBTInput& inp = psbtx.inputs[i];
            if (inp.non_witness_utxo) {
                if (inp.non_witness_utxo->GetHash() != tx.vin[i].prevout.hash) {
                    return TransactionError::INVALID_PSBT;
                }
                if (!inp.witness_utxo.IsNull() && inp.non_witness_utxo->vout[tx.vin[i].prevout.n] != inp.witness_utxo) {
                    return TransactionError::INVALID_PSBT;
                }
                inputs_utxos.push_back(inp.non_witness_utxo->vout[tx.vin[i].prevout.n]);
            } else if (!inp.witness_utxo.IsNull()) {
                inputs_utxos.push_back(inp.witness_utxo);
            } else {
                return TransactionError::UTXOS_MISSING_BALANCE_CHECK;
            }
        }

        CTransaction tx_tmp(tx);
        if (!VerifyAmounts(inputs_utxos, tx_tmp, nullptr, false)) {
            return TransactionError::VALUE_IMBALANCE;
        }
    }

    complete = true;
    for (unsigned int i = 0; i < tx.vin.size(); ++i) {
        const CTxIn& txin = psbtx.tx->vin[i];
        PSBTInput& input = psbtx.inputs.at(i);

        // Get the Sighash type
        if (sign && input.sighash_type > 0 && input.sighash_type != sighash_type) {
            complete = false;
            return TransactionError::SIGHASH_MISMATCH;
        }

        // Get the scriptPubKey to know which SigningProvider to use
        CScript script;
        if (!input.witness_utxo.IsNull()) {
            script = input.witness_utxo.scriptPubKey;
        } else if (input.non_witness_utxo) {
            if (txin.prevout.n >= input.non_witness_utxo->vout.size()) {
                return TransactionError::MISSING_INPUTS;
            }
            script = input.non_witness_utxo->vout[txin.prevout.n].scriptPubKey;
        } else {
            // There's no UTXO so we can just skip this now
            complete = false;
            continue;
        }
        SignatureData sigdata;
        input.FillSignatureData(sigdata);
        const SigningProvider* provider = pwallet->GetSigningProvider(script, sigdata);
        if (!provider) {
            complete = false;
            continue;
        }

        // Here we _only_ sign, and do not e.g. fill in key origin data.
        complete &= SignPSBTInput(HidingSigningProvider(provider, !sign, !bip32derivs), psbtx, i, sighash_type);
    }

    // Restore the saved transaction, to remove our temporary munging.
    psbtx.tx = (CMutableTransaction)oldtx;
    return TransactionError::OK;
}

void FillPSBTOutputsData(const CWallet* pwallet, PartiallySignedTransaction& psbtx, bool bip32derivs) {
    LOCK(pwallet->cs_wallet);
    const CMutableTransaction& tx = *psbtx.tx;

    // Fill in the bip32 keypaths and redeemscripts for the outputs so that hardware wallets can identify change
    for (unsigned int i = 0; i < tx.vout.size(); ++i) {
        const CTxOut& out = tx.vout.at(i);
        const SigningProvider* provider = pwallet->GetSigningProvider(out.scriptPubKey);
        PSBTOutput& psbt_out = psbtx.outputs.at(i);

        // Fill a SignatureData with output info
        SignatureData sigdata;
        psbt_out.FillSignatureData(sigdata);

        MutableTransactionSignatureCreator creator(&tx, 0 /* nIn, ignored */, out.nValue, 1 /* sighashtype, ignored */);
        ProduceSignature(HidingSigningProvider(provider, true /* don't sign */, !bip32derivs), creator, out.scriptPubKey, sigdata);
        psbt_out.FromSignatureData(sigdata);
    }
}

TransactionError FillPSBTData(const CWallet* pwallet, PartiallySignedTransaction& psbtx, bool bip32derivs) {
    LOCK(pwallet->cs_wallet);
    TransactionError te;
    te = FillPSBTInputsData(pwallet, psbtx, bip32derivs);
    if (te != TransactionError::OK) {
        return te;
    }
    FillPSBTOutputsData(pwallet, psbtx, bip32derivs);
    return TransactionError::OK;
}

// This function remains for backwards compatibility. It will not succeed in Elements unless everything involved is non-blinded.
TransactionError FillPSBT(const CWallet* pwallet, PartiallySignedTransaction& psbtx, bool& complete, int sighash_type, bool sign, bool bip32derivs)
{
    complete = false;
    TransactionError te;
    te = FillPSBTInputsData(pwallet, psbtx, bip32derivs);
    if (te != TransactionError::OK) {
        return te;
    }
    // For backwards compatibility, do not check if amounts balance before signing in this case.
    te = SignPSBT(pwallet, psbtx, complete, sighash_type, sign, true, bip32derivs);
    if (te != TransactionError::OK) {
        return te;
    }
    FillPSBTOutputsData(pwallet, psbtx, bip32derivs);
    return TransactionError::OK;
}
