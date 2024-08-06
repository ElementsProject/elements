// Copyright (c) 2009-2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <blindpsbt.h>
#include <psbt.h>

#include <chainparams.h>
#include <pegins.h>
#include <primitives/transaction.h>
#include <util/check.h>
#include <util/strencodings.h>


PartiallySignedTransaction::PartiallySignedTransaction(const CMutableTransaction& tx, uint32_t version) : m_version(version)
{
    if (version == 0) {
        this->tx = tx;
    }
    inputs.resize(tx.vin.size(), PSBTInput(GetVersion()));
    outputs.resize(tx.vout.size(), PSBTOutput(GetVersion()));
    SetupFromTx(tx);
}

PartiallySignedTransaction::PartiallySignedTransaction(uint32_t version) :
    m_version(version)
{
    if (GetVersion() >= 2) {
        tx_version = CTransaction::CURRENT_VERSION;
    }
}

bool PartiallySignedTransaction::IsNull() const
{
    return !tx && inputs.empty() && outputs.empty() && unknown.empty();
}

bool PartiallySignedTransaction::Merge(const PartiallySignedTransaction& psbt)
{
    // Prohibited to merge two PSBTs over different transactions
    if (GetUniqueID() != psbt.GetUniqueID()) {
        return false;
    }

    assert(*tx_version == psbt.tx_version);
    for (unsigned int i = 0; i < inputs.size(); ++i) {
        if (!inputs[i].Merge(psbt.inputs[i])) {
            return false;
        }
    }
    for (unsigned int i = 0; i < outputs.size(); ++i) {
        if (!outputs[i].Merge(psbt.outputs[i])) {
            return false;
        }
    }
    for (auto& xpub_pair : psbt.m_xpubs) {
        if (m_xpubs.count(xpub_pair.first) == 0) {
            m_xpubs[xpub_pair.first] = xpub_pair.second;
        } else {
            m_xpubs[xpub_pair.first].insert(xpub_pair.second.begin(), xpub_pair.second.end());
        }
    }
    for (auto& scalar : psbt.m_scalar_offsets) {
        m_scalar_offsets.insert(scalar);
    }
    if (fallback_locktime == std::nullopt && psbt.fallback_locktime != std::nullopt) fallback_locktime = psbt.fallback_locktime;
    if (m_tx_modifiable == std::nullopt && psbt.m_tx_modifiable != std::nullopt) m_tx_modifiable = psbt.m_tx_modifiable;
    unknown.insert(psbt.unknown.begin(), psbt.unknown.end());

    return true;
}

bool PartiallySignedTransaction::ComputeTimeLock(uint32_t& locktime) const
{
    std::optional<uint32_t> time_lock{0};
    std::optional<uint32_t> height_lock{0};
    for (const PSBTInput& input : inputs) {
        if (input.time_locktime != std::nullopt && input.height_locktime == std::nullopt) {
            height_lock.reset(); // Transaction can no longer have a height locktime
            if (time_lock == std::nullopt) {
                return false;
            }
        } else if (input.time_locktime == std::nullopt && input.height_locktime != std::nullopt) {
            time_lock.reset(); // Transaction can no longer have a time locktime
            if (height_lock == std::nullopt) {
                return false;
            }
        }
        if (input.time_locktime && time_lock != std::nullopt) {
            time_lock = std::max(time_lock, input.time_locktime);
        }
        if (input.height_locktime && height_lock != std::nullopt) {
            height_lock = std::max(height_lock, input.height_locktime);
        }
    }
    if (height_lock != std::nullopt && *height_lock > 0) {
        locktime = *height_lock;
        return true;
    }
    if (time_lock != std::nullopt && *time_lock > 0) {
        locktime = *time_lock;
        return true;
    }
    locktime = fallback_locktime.value_or(0);
    return true;
}

CMutableTransaction PartiallySignedTransaction::GetUnsignedTx(bool force_unblinded) const
{
    if (tx != std::nullopt) {
        return *tx;
    }

    CMutableTransaction mtx;
    mtx.nVersion = *tx_version;
    bool locktime_success = ComputeTimeLock(mtx.nLockTime);
    assert(locktime_success);
    uint32_t max_sequence = CTxIn::SEQUENCE_FINAL;
    for (const PSBTInput& input : inputs) {
        CTxIn txin;
        txin.prevout.hash = input.prev_txid;
        txin.prevout.n = *input.prev_out;
        txin.nSequence = input.sequence.value_or(max_sequence);
        txin.assetIssuance.assetBlindingNonce = input.m_issuance_blinding_nonce;
        txin.assetIssuance.assetEntropy = input.m_issuance_asset_entropy;
        // If there is a commitment we should set the value to the commitment unless we are forcing unblinded.
        // If we are forcing unblinded but there is no value, we just use the commitment.
        if (input.m_issuance_value != std::nullopt && (input.m_issuance_value_commitment.IsNull() || force_unblinded)) {
            txin.assetIssuance.nAmount.SetToAmount(*input.m_issuance_value);
        }
        else if(!input.m_issuance_value_commitment.IsNull()) {
            txin.assetIssuance.nAmount = input.m_issuance_value_commitment;
        }
        else {
            txin.assetIssuance.nAmount.SetNull();
        }
        if (input.m_issuance_inflation_keys_amount != std::nullopt && (input.m_issuance_inflation_keys_commitment.IsNull() || force_unblinded)) {
            txin.assetIssuance.nInflationKeys.SetToAmount(*input.m_issuance_inflation_keys_amount);
        }
        else if(!input.m_issuance_inflation_keys_commitment.IsNull()) {
            txin.assetIssuance.nInflationKeys = input.m_issuance_inflation_keys_commitment;
        }
        else {
            txin.assetIssuance.nInflationKeys.SetNull();
        }
        mtx.vin.push_back(txin);
    }
    for (const PSBTOutput& output : outputs) {
        CTxOut txout;
        CTxOutWitness txoutwit;
        txout.scriptPubKey = *output.script;

        bool exp_value = output.m_value_commitment.IsNull() || force_unblinded;
        exp_value = exp_value && output.amount != std::nullopt;
        if (!output.m_value_commitment.IsNull() && output.amount != std::nullopt) {
            exp_value = exp_value && !output.m_blind_value_proof.empty();
            exp_value = exp_value && !output.m_asset_commitment.IsNull();
            exp_value = exp_value && VerifyBlindValueProof(*output.amount, output.m_value_commitment, output.m_blind_value_proof, output.m_asset_commitment);
        }
        if (exp_value) {
            txout.nValue.SetToAmount(*output.amount);
        } else {
            txout.nValue = output.m_value_commitment;
            txoutwit.vchRangeproof = output.m_value_rangeproof;
        }

        bool exp_asset = output.m_asset_commitment.IsNull() || force_unblinded;
        exp_asset = exp_asset && !output.m_asset.IsNull();
        if (!output.m_asset_commitment.IsNull() && !output.m_asset.IsNull()) {
            exp_asset = exp_asset && !output.m_blind_asset_proof.empty();
            exp_asset = exp_asset && !output.m_asset.IsNull();
            exp_asset = exp_asset && VerifyBlindAssetProof(output.m_asset, output.m_blind_asset_proof, output.m_asset_commitment);
        }
        if (exp_asset) {
            txout.nAsset.SetToAsset(CAsset(output.m_asset));
        } else {
            txout.nAsset = output.m_asset_commitment;
            txoutwit.vchSurjectionproof = output.m_asset_surjection_proof;
        }
        if (output.m_ecdh_pubkey.IsValid() && !force_unblinded) {
            txout.nNonce.vchCommitment.insert(txout.nNonce.vchCommitment.end(), output.m_ecdh_pubkey.begin(), output.m_ecdh_pubkey.end());
        }
        mtx.vout.push_back(txout);
        mtx.witness.vtxoutwit.push_back(txoutwit);
    }
    mtx.witness.vtxinwit.resize(inputs.size());
    return mtx;
}

uint256 PartiallySignedTransaction::GetUniqueID() const
{
    if (tx != std::nullopt) {
        return tx->GetHash();
    }

    // Get the unsigned transaction
    CMutableTransaction mtx = GetUnsignedTx(/* force_unblinded */ true);
    // Set the locktime to 0
    mtx.nLockTime = 0;
    // Set the sequence numbers to 0
    for (CTxIn& txin : mtx.vin) {
        txin.nSequence = 0;
    }
    return mtx.GetHash();
}

bool PartiallySignedTransaction::AddInput(PSBTInput& psbtin)
{
    // Check required fields are present and this input is not a duplicate
    if (psbtin.prev_txid.IsNull() ||
        psbtin.prev_out == std::nullopt ||
        std::find_if(inputs.begin(), inputs.end(),
        [psbtin](const PSBTInput& psbt) {
            return psbt.prev_txid == psbtin.prev_txid && psbt.prev_out == psbtin.prev_out;
        }
    ) != inputs.end()) {
        return false;
    }

    if (tx != std::nullopt) {
        // This is a v0 psbt, so do the v0 AddInput
        CTxIn txin(COutPoint(psbtin.prev_txid, *psbtin.prev_out));
        if (std::find(tx->vin.begin(), tx->vin.end(), txin) != tx->vin.end()) {
            return false;
        }
        tx->vin.push_back(txin);
        psbtin.partial_sigs.clear();
        psbtin.final_script_sig.clear();
        psbtin.final_script_witness.SetNull();
        inputs.push_back(psbtin);
        return true;
    }

    // No global tx, must be PSBTv2.
    // Check inputs modifiable flag
    if (m_tx_modifiable == std::nullopt || !m_tx_modifiable->test(0)) {
        return false;
    }

    // Determine if we need to iterate the inputs.
    // For now, we only do this if the new input has a required time lock.
    // The BIP states that we should also do this if m_tx_modifiable's bit 2 is set
    // (Has SIGHASH_SINGLE flag) but since we are only adding inputs at the end of the vector,
    // we don't care about that.
    bool iterate_inputs = psbtin.time_locktime != std::nullopt || psbtin.height_locktime != std::nullopt;
    if (iterate_inputs) {
        uint32_t old_timelock;
        if (!ComputeTimeLock(old_timelock)) {
            return false;
        }

        std::optional<uint32_t> time_lock = psbtin.time_locktime;
        std::optional<uint32_t> height_lock = psbtin.height_locktime;
        bool has_sigs = false;
        for (const PSBTInput& input : inputs) {
            if (input.time_locktime != std::nullopt && input.height_locktime == std::nullopt) {
                height_lock.reset(); // Transaction can no longer have a height locktime
                if (time_lock == std::nullopt) {
                    return false;
                }
            } else if (input.time_locktime == std::nullopt && input.height_locktime != std::nullopt) {
                time_lock.reset(); // Transaction can no longer have a time locktime
                if (height_lock == std::nullopt) {
                    return false;
                }
            }
            if (input.time_locktime && time_lock != std::nullopt) {
                time_lock = std::max(time_lock, input.time_locktime);
            }
            if (input.height_locktime && height_lock != std::nullopt) {
                height_lock = std::max(height_lock, input.height_locktime);
            }
            if (!input.partial_sigs.empty()) {
                has_sigs = true;
            }
        }
        uint32_t new_timelock = fallback_locktime.value_or(0);
        if (height_lock != std::nullopt && *height_lock > 0) {
            new_timelock = *height_lock;
        } else if (time_lock != std::nullopt && *time_lock > 0) {
            new_timelock = *time_lock;
        }
        if (has_sigs && old_timelock != new_timelock) {
            return false;
        }
    }

    // Add the input to the end
    inputs.push_back(psbtin);
    return true;
}

bool PartiallySignedTransaction::AddOutput(const PSBTOutput& psbtout)
{
    if (psbtout.amount == std::nullopt || psbtout.script == std::nullopt) {
        return false;
    }

    if (tx != std::nullopt) {
        // This is a v0 psbt, do the v0 AddOutput
        CTxOut txout(CAsset(), *psbtout.amount, *psbtout.script);
        tx->vout.push_back(txout);
        outputs.push_back(psbtout);
        return true;
    }

    // No global tx, must be PSBTv2
    // Check outputs are modifiable
    if (m_tx_modifiable == std::nullopt || !m_tx_modifiable->test(1)) {
        return false;
    }
    outputs.push_back(psbtout);

    return true;
}

bool PSBTInput::GetUTXO(CTxOut& utxo) const
{
    if (non_witness_utxo) {
        if (*prev_out >= non_witness_utxo->vout.size()) {
            return false;
        }
        utxo = non_witness_utxo->vout[*prev_out];
    } else if (!witness_utxo.IsNull()) {
        utxo = witness_utxo;
    } else if (m_peg_in_value && !m_peg_in_claim_script.empty()) {
        // For Peg-ins, get the UTXO from the peg-in stuff
        utxo = CTxOut(Params().GetConsensus().pegged_asset, CConfidentialValue(*m_peg_in_value), m_peg_in_claim_script);
    } else {
        return false;
    }
    return true;
}

COutPoint PSBTInput::GetOutPoint() const
{
    return COutPoint(prev_txid, *prev_out);
}

bool PartiallySignedTransaction::IsBlinded() const
{
    for (const PSBTOutput& out : outputs) {
        if (out.IsBlinded()) {
            return true;
        }
    }
    return false;
}

bool PartiallySignedTransaction::IsFullyBlinded() const
{
    for (const PSBTOutput& out : outputs) {
        if (out.IsBlinded() && !out.IsFullyBlinded()) {
            return false;
        }
    }
    return true;
}

bool PSBTInput::IsNull() const
{
    return !non_witness_utxo && witness_utxo.IsNull() && partial_sigs.empty() && unknown.empty() && hd_keypaths.empty() && redeem_script.empty() && witness_script.empty();
}

void PSBTInput::FillSignatureData(SignatureData& sigdata) const
{
    if (!final_script_sig.empty()) {
        sigdata.scriptSig = final_script_sig;
        sigdata.complete = true;
    }
    if (!final_script_witness.IsNull()) {
        sigdata.scriptWitness = final_script_witness;
        sigdata.complete = true;
    }
    if (sigdata.complete) {
        return;
    }

    sigdata.signatures.insert(partial_sigs.begin(), partial_sigs.end());
    if (!redeem_script.empty()) {
        sigdata.redeem_script = redeem_script;
    }
    if (!witness_script.empty()) {
        sigdata.witness_script = witness_script;
    }
    for (const auto& key_pair : hd_keypaths) {
        sigdata.misc_pubkeys.emplace(key_pair.first.GetID(), key_pair);
    }
}

void PSBTInput::FromSignatureData(const SignatureData& sigdata)
{
    if (sigdata.complete) {
        partial_sigs.clear();
        hd_keypaths.clear();
        redeem_script.clear();
        witness_script.clear();

        if (!sigdata.scriptSig.empty()) {
            final_script_sig = sigdata.scriptSig;
        }
        if (!sigdata.scriptWitness.IsNull()) {
            final_script_witness = sigdata.scriptWitness;
        }
        return;
    }

    partial_sigs.insert(sigdata.signatures.begin(), sigdata.signatures.end());
    if (redeem_script.empty() && !sigdata.redeem_script.empty()) {
        redeem_script = sigdata.redeem_script;
    }
    if (witness_script.empty() && !sigdata.witness_script.empty()) {
        witness_script = sigdata.witness_script;
    }
    for (const auto& entry : sigdata.misc_pubkeys) {
        hd_keypaths.emplace(entry.second);
    }
}

bool PSBTInput::Merge(const PSBTInput& input)
{
    assert(prev_txid == input.prev_txid);
    assert(*prev_out == *input.prev_out);

    if (!non_witness_utxo && input.non_witness_utxo) non_witness_utxo = input.non_witness_utxo;
    if (witness_utxo.IsNull() && !input.witness_utxo.IsNull()) {
        // TODO: For segwit v1, we will want to clear out the non-witness utxo when setting a witness one. For v0 and non-segwit, this is not safe
        witness_utxo = input.witness_utxo;
    }

    partial_sigs.insert(input.partial_sigs.begin(), input.partial_sigs.end());
    ripemd160_preimages.insert(input.ripemd160_preimages.begin(), input.ripemd160_preimages.end());
    sha256_preimages.insert(input.sha256_preimages.begin(), input.sha256_preimages.end());
    hash160_preimages.insert(input.hash160_preimages.begin(), input.hash160_preimages.end());
    hash256_preimages.insert(input.hash256_preimages.begin(), input.hash256_preimages.end());
    hd_keypaths.insert(input.hd_keypaths.begin(), input.hd_keypaths.end());
    unknown.insert(input.unknown.begin(), input.unknown.end());

    if (redeem_script.empty() && !input.redeem_script.empty()) redeem_script = input.redeem_script;
    if (witness_script.empty() && !input.witness_script.empty()) witness_script = input.witness_script;
    if (final_script_sig.empty() && !input.final_script_sig.empty()) final_script_sig = input.final_script_sig;
    if (final_script_witness.IsNull() && !input.final_script_witness.IsNull()) final_script_witness = input.final_script_witness;
    if (sequence == std::nullopt && input.sequence != std::nullopt) sequence = input.sequence;
    if (time_locktime == std::nullopt && input.time_locktime != std::nullopt) time_locktime = input.time_locktime;
    if (height_locktime == std::nullopt && input.height_locktime != std::nullopt) height_locktime = input.height_locktime;

    if (m_issuance_value == std::nullopt && m_issuance_value_commitment.IsNull() && input.m_issuance_value != std::nullopt) m_issuance_value = input.m_issuance_value;
    if (m_issuance_value_commitment.IsNull() && !input.m_issuance_value_commitment.IsNull()) {
        m_issuance_value_commitment = input.m_issuance_value_commitment;
        m_issuance_value.reset();
    }
    if (m_issuance_rangeproof.empty() && !input.m_issuance_rangeproof.empty()) m_issuance_rangeproof = input.m_issuance_rangeproof;
    if (m_issuance_inflation_keys_rangeproof.empty() && !input.m_issuance_inflation_keys_rangeproof.empty()) m_issuance_inflation_keys_rangeproof = input.m_issuance_inflation_keys_rangeproof;
    if (m_issuance_inflation_keys_amount == std::nullopt && m_issuance_inflation_keys_commitment.IsNull() && input.m_issuance_inflation_keys_amount != std::nullopt) m_issuance_inflation_keys_amount = input.m_issuance_inflation_keys_amount;
    if (m_issuance_inflation_keys_commitment.IsNull() && !input.m_issuance_inflation_keys_commitment.IsNull()) {
        m_issuance_inflation_keys_commitment = input.m_issuance_inflation_keys_commitment;
        m_issuance_inflation_keys_amount.reset();
    }
    if (m_issuance_blinding_nonce.IsNull() && !input.m_issuance_blinding_nonce.IsNull()) m_issuance_blinding_nonce = input.m_issuance_blinding_nonce;
    if (m_issuance_asset_entropy.IsNull() && !input.m_issuance_asset_entropy.IsNull()) m_issuance_asset_entropy = input.m_issuance_asset_entropy;
    if (m_blind_issuance_value_proof.empty() && !input.m_blind_issuance_value_proof.empty()) m_blind_issuance_value_proof = input.m_blind_issuance_value_proof;
    if (m_blind_issuance_inflation_keys_proof.empty() && !input.m_blind_issuance_inflation_keys_proof.empty()) m_blind_issuance_inflation_keys_proof = input.m_blind_issuance_inflation_keys_proof;

    if (m_peg_in_tx.index() == 0 && input.m_peg_in_tx.index() != 0) m_peg_in_tx = input.m_peg_in_tx;
    if (m_peg_in_txout_proof.index() == 0 && input.m_peg_in_txout_proof.index() != 0) m_peg_in_txout_proof = input.m_peg_in_txout_proof;
    if (m_peg_in_claim_script.empty() && !input.m_peg_in_claim_script.empty()) m_peg_in_claim_script = input.m_peg_in_claim_script;
    if (m_peg_in_genesis_hash.IsNull() && !input.m_peg_in_genesis_hash.IsNull()) m_peg_in_genesis_hash = input.m_peg_in_genesis_hash;
    if (m_peg_in_value == std::nullopt && input.m_peg_in_value != std::nullopt) m_peg_in_value = input.m_peg_in_value;
    if (m_peg_in_witness.IsNull() && !input.m_peg_in_witness.IsNull()) m_peg_in_witness = input.m_peg_in_witness;

    if (m_utxo_rangeproof.empty() && !input.m_utxo_rangeproof.empty()) m_utxo_rangeproof = input.m_utxo_rangeproof;

    return true;
}

void PSBTOutput::FillSignatureData(SignatureData& sigdata) const
{
    if (!redeem_script.empty()) {
        sigdata.redeem_script = redeem_script;
    }
    if (!witness_script.empty()) {
        sigdata.witness_script = witness_script;
    }
    for (const auto& key_pair : hd_keypaths) {
        sigdata.misc_pubkeys.emplace(key_pair.first.GetID(), key_pair);
    }
}

void PSBTOutput::FromSignatureData(const SignatureData& sigdata)
{
    if (redeem_script.empty() && !sigdata.redeem_script.empty()) {
        redeem_script = sigdata.redeem_script;
    }
    if (witness_script.empty() && !sigdata.witness_script.empty()) {
        witness_script = sigdata.witness_script;
    }
    for (const auto& entry : sigdata.misc_pubkeys) {
        hd_keypaths.emplace(entry.second);
    }
}

bool PSBTOutput::IsNull() const
{
    return redeem_script.empty() && witness_script.empty() && hd_keypaths.empty() && unknown.empty();
}

bool PSBTOutput::Merge(const PSBTOutput& output)
{
    assert(amount == output.amount);
    assert(script == output.script);
    assert(m_asset == output.m_asset);

    hd_keypaths.insert(output.hd_keypaths.begin(), output.hd_keypaths.end());
    unknown.insert(output.unknown.begin(), output.unknown.end());

    if (redeem_script.empty() && !output.redeem_script.empty()) redeem_script = output.redeem_script;
    if (witness_script.empty() && !output.witness_script.empty()) witness_script = output.witness_script;

    // If this IsBlinded and output IsBlinded, make sure the creator added fields are the same
    if (IsBlinded() && output.IsBlinded()) {
        if (!m_blinding_pubkey.IsValid() || !output.m_blinding_pubkey.IsValid() || !m_blinder_index || !output.m_blinder_index) return false;
        if (m_blinding_pubkey != output.m_blinding_pubkey) return false;
        if (m_blinder_index != output.m_blinder_index) return false;
    }

    // If this IsFullyBlinded and output IsFullyBlinded, just double check them
    if (IsFullyBlinded() && output.IsFullyBlinded()) {
        if (!m_value_commitment.IsNull() && !output.m_value_commitment.IsNull() && (m_value_commitment != output.m_value_commitment)) return false;
        if (!m_asset_commitment.IsNull() && !output.m_asset_commitment.IsNull() && (m_asset_commitment != output.m_asset_commitment)) return false;
        if (!m_value_rangeproof.empty() && !output.m_value_rangeproof.empty() && (m_value_rangeproof != output.m_value_rangeproof)) return false;
        if (!m_asset_surjection_proof.empty() && !output.m_asset_surjection_proof.empty() && (m_asset_surjection_proof != output.m_asset_surjection_proof)) return false;
    }

    // If output IsFullyBlinded and this is not, copy the blinding data and remove the explicits
    if (IsBlinded() && !IsFullyBlinded() && output.IsFullyBlinded()) {
        m_value_commitment = output.m_value_commitment;
        m_asset_commitment = output.m_asset_commitment;
        m_value_rangeproof = output.m_value_rangeproof;
        m_asset_surjection_proof = output.m_asset_surjection_proof;
        m_ecdh_pubkey = output.m_ecdh_pubkey;
        m_blind_value_proof = output.m_blind_value_proof;
        m_blind_asset_proof = output.m_blind_asset_proof;
    }

    return true;
}

CTxOut PSBTOutput::GetTxOut() const
{
    assert(script != std::nullopt);
    assert(amount != std::nullopt || !m_value_commitment.IsNull());
    assert(!m_asset.IsNull() || !m_asset_commitment.IsNull());
    return CTxOut(!m_asset_commitment.IsNull() ? m_asset_commitment : CAsset(m_asset), !m_value_commitment.IsNull() ? m_value_commitment : CConfidentialValue(*amount), *script);
}

bool PSBTOutput::IsBlinded() const
{
    return m_blinding_pubkey.IsValid();
}

bool PSBTOutput::IsPartiallyBlinded() const
{
    return IsBlinded() && (
        !m_value_commitment.IsNull() ||
        !m_asset_commitment.IsNull() ||
        !m_value_rangeproof.empty() ||
        !m_asset_surjection_proof.empty() ||
        m_ecdh_pubkey.IsValid());
}

bool PSBTOutput::IsFullyBlinded() const
{
    return IsBlinded() &&
        !m_value_commitment.IsNull() &&
        !m_asset_commitment.IsNull() &&
        !m_value_rangeproof.empty() &&
        !m_asset_surjection_proof.empty() &&
        m_ecdh_pubkey.IsValid();
}

bool PSBTInputSigned(const PSBTInput& input)
{
    return !input.final_script_sig.empty() || !input.final_script_witness.IsNull();
}

size_t CountPSBTUnsignedInputs(const PartiallySignedTransaction& psbt) {
    size_t count = 0;
    for (const auto& input : psbt.inputs) {
        if (!PSBTInputSigned(input)) {
            count++;
        }
    }

    return count;
}

void UpdatePSBTOutput(const SigningProvider& provider, PartiallySignedTransaction& psbt, int index)
{
    CMutableTransaction tx = psbt.GetUnsignedTx();
    const CTxOut& out = tx.vout.at(index);
    PSBTOutput& psbt_out = psbt.outputs.at(index);

    // Fill a SignatureData with output info
    SignatureData sigdata;
    psbt_out.FillSignatureData(sigdata);

    // Construct a would-be spend of this output, to update sigdata with.
    // Note that ProduceSignature is used to fill in metadata (not actual signatures),
    // so provider does not need to provide any private keys (it can be a HidingSigningProvider).
    MutableTransactionSignatureCreator creator(&tx, /*input_idx=*/0, out.nValue, SIGHASH_ALL);
    ProduceSignature(provider, creator, out.scriptPubKey, sigdata);

    // Put redeem_script, witness_script, key paths, into PSBTOutput.
    psbt_out.FromSignatureData(sigdata);
}

PrecomputedTransactionData PrecomputePSBTData(const PartiallySignedTransaction& psbt)
{
    const CMutableTransaction tx = psbt.GetUnsignedTx();
    bool have_all_spent_outputs = true;
    std::vector<CTxOut> utxos(psbt.inputs.size());
    for (size_t idx = 0; idx < psbt.inputs.size(); ++idx) {
        if (!psbt.inputs[idx].GetUTXO(utxos[idx])) have_all_spent_outputs = false;
    }
    PrecomputedTransactionData txdata{Params().HashGenesisBlock()};
    if (have_all_spent_outputs) {
        txdata.Init(tx, std::move(utxos), true);
    } else {
        txdata.Init(tx, {}, true);
    }
    return txdata;
}

bool SignPSBTInput(const SigningProvider& provider, PartiallySignedTransaction& psbt, int index, const PrecomputedTransactionData* txdata, int sighash,  SignatureData* out_sigdata, bool finalize)
{
    PSBTInput& input = psbt.inputs.at(index);

    // If this input is a peg-in, also make the peg-in witness
    if (input.m_peg_in_tx.index() != 0
        && input.m_peg_in_txout_proof.index() != 0
        && !input.m_peg_in_claim_script.empty()
        && !input.m_peg_in_genesis_hash.IsNull()
        && input.m_peg_in_value != std::nullopt) {
        if (Params().GetConsensus().ParentChainHasPow()) {
            input.m_peg_in_witness = CreatePeginWitness(*input.m_peg_in_value, Params().GetConsensus().pegged_asset, input.m_peg_in_genesis_hash, input.m_peg_in_claim_script, *std::get_if<Sidechain::Bitcoin::CTransactionRef>(&input.m_peg_in_tx), *std::get_if<Sidechain::Bitcoin::CMerkleBlock>(&input.m_peg_in_txout_proof));
        } else {
            input.m_peg_in_witness = CreatePeginWitness(*input.m_peg_in_value, Params().GetConsensus().pegged_asset, input.m_peg_in_genesis_hash, input.m_peg_in_claim_script, *std::get_if<CTransactionRef>(&input.m_peg_in_tx), *std::get_if<CMerkleBlock>(&input.m_peg_in_txout_proof));
        }
    }

    const CMutableTransaction& tx = psbt.GetUnsignedTx();

    if (PSBTInputSigned(input)) {
        return true;
    }

    // Fill SignatureData with input info
    SignatureData sigdata;
    input.FillSignatureData(sigdata);

    // Get UTXO
    bool require_witness_sig = false;
    CTxOut utxo;

    if (input.non_witness_utxo) {
        // If we're taking our information from a non-witness UTXO, verify that it matches the prevout.
        COutPoint prevout = input.GetOutPoint();
        if (prevout.n >= input.non_witness_utxo->vout.size()) {
            return false;
        }
        if (input.non_witness_utxo->GetHash() != prevout.hash) {
            return false;
        }
        utxo = input.non_witness_utxo->vout[prevout.n];
    } else if (!input.witness_utxo.IsNull()) {
        utxo = input.witness_utxo;
        // When we're taking our information from a witness UTXO, we can't verify it is actually data from
        // the output being spent. This is safe in case a witness signature is produced (which includes this
        // information directly in the hash), but not for non-witness signatures. Remember that we require
        // a witness signature in this situation.
        require_witness_sig = true;
    } else if (input.m_peg_in_value && !input.m_peg_in_claim_script.empty()) {
        utxo = CTxOut(Params().GetConsensus().pegged_asset, CConfidentialValue(*input.m_peg_in_value), input.m_peg_in_claim_script);
    } else {
        return false;
    }

    sigdata.witness = false;
    bool sig_complete;
    if (txdata == nullptr) {
        sig_complete = ProduceSignature(provider, DUMMY_SIGNATURE_CREATOR, utxo.scriptPubKey, sigdata);
    } else {
        MutableTransactionSignatureCreator creator(&tx, index, utxo.nValue, txdata, sighash);
        sig_complete = ProduceSignature(provider, creator, utxo.scriptPubKey, sigdata);
    }
    // Verify that a witness signature was produced in case one was required.
    if (require_witness_sig && !sigdata.witness) return false;

    // If we are not finalizing, set sigdata.complete to false to not set the scriptWitness
    if (!finalize && sigdata.complete) sigdata.complete = false;

    input.FromSignatureData(sigdata);

    // If we have a witness signature, put a witness UTXO.
    // TODO: For segwit v1, we should remove the non_witness_utxo
    if (sigdata.witness) {
        input.witness_utxo = utxo;
        // input.non_witness_utxo = nullptr;
    }

    // Fill in the missing info
    if (out_sigdata) {
        out_sigdata->missing_pubkeys = sigdata.missing_pubkeys;
        out_sigdata->missing_sigs = sigdata.missing_sigs;
        out_sigdata->missing_redeem_script = sigdata.missing_redeem_script;
        out_sigdata->missing_witness_script = sigdata.missing_witness_script;
    }

    return sig_complete;
}

bool FinalizePSBT(PartiallySignedTransaction& psbtx)
{
    // Finalize input signatures -- in case we have partial signatures that add up to a complete
    //   signature, but have not combined them yet (e.g. because the combiner that created this
    //   PartiallySignedTransaction did not understand them), this will combine them into a final
    //   script.
    bool complete = true;
    const PrecomputedTransactionData txdata = PrecomputePSBTData(psbtx);
    for (unsigned int i = 0; i < psbtx.inputs.size(); ++i) {
        complete &= SignPSBTInput(DUMMY_SIGNING_PROVIDER, psbtx, i, &txdata, SIGHASH_ALL, nullptr, true);
    }

    return complete;
}

bool FinalizeAndExtractPSBT(PartiallySignedTransaction& psbtx, CMutableTransaction& result)
{
    // It's not safe to extract a PSBT that isn't finalized, and there's no easy way to check
    //   whether a PSBT is finalized without finalizing it, so we just do this.
    if (!FinalizePSBT(psbtx)) {
        return false;
    }

    result = psbtx.GetUnsignedTx();
    for (unsigned int i = 0; i < result.vin.size(); ++i) {
        const PSBTInput& psbt_in = psbtx.inputs[i];
        CTxIn& txin = result.vin[i];
        CTxInWitness& txin_wit = result.witness.vtxinwit[i];

        txin.scriptSig = psbt_in.final_script_sig;
        txin_wit.scriptWitness = psbt_in.final_script_witness;
        txin_wit.vchIssuanceAmountRangeproof = psbt_in.m_issuance_rangeproof;
        txin_wit.vchInflationKeysRangeproof = psbt_in.m_issuance_inflation_keys_rangeproof;

        txin.m_is_pegin = !psbt_in.m_peg_in_witness.IsNull();
        txin_wit.m_pegin_witness = psbt_in.m_peg_in_witness;
    }
    for (unsigned int i = 0; i < result.vout.size(); ++i) {
        const PSBTOutput& psbt_out = psbtx.outputs[i];
        result.witness.vtxoutwit[i].vchSurjectionproof = psbt_out.m_asset_surjection_proof;
        result.witness.vtxoutwit[i].vchRangeproof = psbt_out.m_value_rangeproof;
    }
    return true;
}

TransactionError CombinePSBTs(PartiallySignedTransaction& out, const std::vector<PartiallySignedTransaction>& psbtxs)
{
    out = psbtxs[0]; // Copy the first one

    // Merge
    for (auto it = std::next(psbtxs.begin()); it != psbtxs.end(); ++it) {
        if (!out.Merge(*it)) {
            return TransactionError::PSBT_MISMATCH;
        }
    }
    return TransactionError::OK;
}

std::string PSBTRoleName(PSBTRole role) {
    switch (role) {
    case PSBTRole::CREATOR: return "creator";
    case PSBTRole::UPDATER: return "updater";
    case PSBTRole::BLINDER: return "blinder";
    case PSBTRole::SIGNER: return "signer";
    case PSBTRole::FINALIZER: return "finalizer";
    case PSBTRole::EXTRACTOR: return "extractor";
        // no default case, so the compiler can warn about missing cases
    }
    assert(false);
}

std::string EncodePSBT(const PartiallySignedTransaction& psbt)
{
    CDataStream ssTx(SER_NETWORK, PROTOCOL_VERSION);
    ssTx << psbt;
    return EncodeBase64(ssTx);
}

bool DecodeBase64PSBT(PartiallySignedTransaction& psbt, const std::string& base64_tx, std::string& error)
{
    auto tx_data = DecodeBase64(base64_tx);
    if (!tx_data) {
        error = "invalid base64";
        return false;
    }
    return DecodeRawPSBT(psbt, MakeByteSpan(*tx_data), error);
}

bool DecodeRawPSBT(PartiallySignedTransaction& psbt, Span<const std::byte> tx_data, std::string& error)
{
    CDataStream ss_data(tx_data, SER_NETWORK, PROTOCOL_VERSION);
    try {
        ss_data >> psbt;
        if (!ss_data.empty()) {
            error = "extra data after PSBT";
            return false;
        }
    } catch (const std::exception& e) {
        error = e.what();
        return false;
    }
    return true;
}

uint32_t PartiallySignedTransaction::GetVersion() const
{
    if (m_version != std::nullopt) {
        return *m_version;
    }
    return 0;
}

void PartiallySignedTransaction::SetupFromTx(const CMutableTransaction& tx)
{
    tx_version = tx.nVersion;
    fallback_locktime = tx.nLockTime;

    uint32_t i;
    for (i = 0; i < tx.vin.size(); ++i) {
        PSBTInput& input = inputs.at(i);
        const CTxIn& txin = tx.vin.at(i);

        input.prev_txid = txin.prevout.hash;
        input.prev_out = txin.prevout.n;
        input.sequence = txin.nSequence;

        // Elements things
        if (!txin.assetIssuance.IsNull()) {
            if (txin.assetIssuance.nAmount.IsExplicit()) {
                input.m_issuance_value = txin.assetIssuance.nAmount.GetAmount();
            } else {
                input.m_issuance_value_commitment = txin.assetIssuance.nAmount;
            }

            if (txin.assetIssuance.nInflationKeys.IsExplicit()) {
                input.m_issuance_inflation_keys_amount = txin.assetIssuance.nInflationKeys.GetAmount();
            } else {
                input.m_issuance_inflation_keys_commitment = txin.assetIssuance.nInflationKeys;
            }

            if (!txin.assetIssuance.assetBlindingNonce.IsNull()) {
                input.m_issuance_blinding_nonce = txin.assetIssuance.assetBlindingNonce;
            }
            if (!txin.assetIssuance.assetEntropy.IsNull()) {
                input.m_issuance_asset_entropy = txin.assetIssuance.assetEntropy;
            }
        }
        // Peg-in things
        if (txin.m_is_pegin) {
            CAmount peg_in_value;
            CAsset asset;
            if (DecomposePeginWitness(tx.witness.vtxinwit[i].m_pegin_witness, peg_in_value, asset, input.m_peg_in_genesis_hash, input.m_peg_in_claim_script, input.m_peg_in_tx, input.m_peg_in_txout_proof)) {
                input.m_peg_in_value = peg_in_value;
                assert(asset == Params().GetConsensus().pegged_asset);
            }
        }
    }

    for (i = 0; i < tx.vout.size(); ++i) {
        PSBTOutput& output = outputs.at(i);
        const CTxOut& txout = tx.vout.at(i);

        output.script = txout.scriptPubKey;

        // Elements things
        if (txout.nAsset.IsExplicit()) {
            output.m_asset = txout.nAsset.GetAsset().id;
        } else {
            output.m_asset_commitment = txout.nAsset;
        }

        if (txout.nValue.IsExplicit()) {
            output.amount = txout.nValue.GetAmount();
        } else {
            output.m_value_commitment = txout.nValue;
        }

        // Usually the blinding pubkey is put into the nonce, so pull it out of there
        if (txout.nNonce.IsCommitment()) {
            output.m_blinding_pubkey.Set(txout.nNonce.vchCommitment.begin(), txout.nNonce.vchCommitment.end());
        }
    }
}

void PartiallySignedTransaction::CacheUnsignedTxPieces()
{
    // To make things easier, we split up the global unsigned transaction
    // and use the PSBTv2 fields for PSBTv0.
    if (tx != std::nullopt) {
        SetupFromTx(*tx);
    }
}
