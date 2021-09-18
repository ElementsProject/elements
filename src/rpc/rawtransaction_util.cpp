// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <rpc/rawtransaction_util.h>

#include <block_proof.h>
#include <coins.h>
#include <core_io.h>
#include <key_io.h>
#include <pegins.h>
#include <policy/policy.h>
#include <primitives/transaction.h>
#include <primitives/bitcoin/merkleblock.h>
#include <primitives/bitcoin/transaction.h>
#include <rpc/request.h>
#include <rpc/util.h>
#include <script/sign.h>
#include <script/signingprovider.h>
#include <tinyformat.h>
#include <univalue.h>
#include <util/rbf.h>
#include <util/strencodings.h>
#include <validation.h>

template<typename T_tx>
unsigned int GetPeginTxnOutputIndex(const T_tx& txn, const CScript& witnessProgram, const std::vector<std::pair<CScript, CScript>>& fedpegscripts)
{
    for (const auto & scripts : fedpegscripts) {
        CScript mainchain_script = GetScriptForDestination(WitnessV0ScriptHash(calculate_contract(scripts.second, witnessProgram)));
        if (scripts.first.IsPayToScriptHash()) {
            mainchain_script = GetScriptForDestination(ScriptHash(mainchain_script));
        }
        for (unsigned int nOut = 0; nOut < txn.vout.size(); nOut++) {
            if (txn.vout[nOut].scriptPubKey == mainchain_script) {
                return nOut;
            }
        }
    }
    return txn.vout.size();
}

// Modifies an existing transaction input in-place to be a valid peg-in input, and inserts the witness if deemed valid.
template<typename T_tx_ref, typename T_merkle_block>
static void CreatePegInInputInner(CMutableTransaction& mtx, uint32_t input_idx, T_tx_ref& txBTCRef, T_merkle_block& merkleBlock, const std::set<CScript>& claim_scripts, const std::vector<unsigned char>& txData, const std::vector<unsigned char>& txOutProofData, const CBlockIndex* active_chain_tip)
{
    if ((mtx.vin.size() > input_idx && !mtx.vin[input_idx].scriptSig.empty()) || (mtx.witness.vtxinwit.size() > input_idx && !mtx.witness.vtxinwit[input_idx].IsNull())) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Attempting to add a peg-in to an input that already has a scriptSig or witness");
    }

    CDataStream ssTx(txData, SER_NETWORK, PROTOCOL_VERSION);
    try {
        ssTx >> txBTCRef;
    }
    catch (...) {
        throw JSONRPCError(RPC_TYPE_ERROR, "The included bitcoinTx is malformed. Are you sure that is the whole string?");
    }

    CDataStream ssTxOutProof(txOutProofData, SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS);
    try {
        ssTxOutProof >> merkleBlock;
    }
    catch (...) {
        throw JSONRPCError(RPC_TYPE_ERROR, "The included txoutproof is malformed. Are you sure that is the whole string?");
    }

    if (!ssTxOutProof.empty()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid tx out proof");
    }

    std::vector<uint256> txHashes;
    std::vector<unsigned int> txIndices;
    if (merkleBlock.txn.ExtractMatches(txHashes, txIndices) != merkleBlock.header.hashMerkleRoot)
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid tx out proof");

    if (txHashes.size() != 1 || txHashes[0] != txBTCRef->GetHash())
        throw JSONRPCError(RPC_INVALID_PARAMETER, "The txoutproof must contain bitcoinTx and only bitcoinTx");

    CScript witness_script;
    unsigned int nOut = txBTCRef->vout.size();
    const auto fedpegscripts = GetValidFedpegScripts(active_chain_tip, Params().GetConsensus(), true /* nextblock_validation */);
    for (const CScript& script : claim_scripts) {
        nOut = GetPeginTxnOutputIndex(*txBTCRef, script, fedpegscripts);
        if (nOut != txBTCRef->vout.size()) {
            witness_script = script;
            break;
        }
    }
    if (nOut == txBTCRef->vout.size()) {
        if (claim_scripts.size() == 1) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Given claim_script does not match the given Bitcoin transaction.");
        } else {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Failed to find output in bitcoinTx to the mainchain_address from getpeginaddress");
        }
    }
    CHECK_NONFATAL(witness_script != CScript());

    int version = -1;
    std::vector<unsigned char> witness_program;
    if (!witness_script.IsWitnessProgram(version, witness_program) || version != 0) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Given or recovered script is not a v0 witness program.");
    }

    CAmount value = 0;
    if (!GetAmountFromParentChainPegin(value, *txBTCRef, nOut)) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Amounts to pegin must be explicit and asset must be %s", Params().GetConsensus().parent_pegged_asset.GetHex()));
    }

    // Add/replace input in mtx
    if (mtx.vin.size() <= input_idx) {
        mtx.vin.resize(input_idx + 1);
    }
    mtx.vin[input_idx] = CTxIn(COutPoint(txHashes[0], nOut), CScript(), ~(uint32_t)0);

    // Construct pegin proof
    CScriptWitness pegin_witness = CreatePeginWitness(value, Params().GetConsensus().pegged_asset, Params().ParentGenesisBlockHash(), witness_script, txBTCRef, merkleBlock);

    // Peg-in witness isn't valid, even though the block header is(without depth check)
    // We re-check depth before returning with more descriptive result
    std::string err;
    if (!IsValidPeginWitness(pegin_witness, fedpegscripts, mtx.vin[input_idx].prevout, err, false)) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Constructed peg-in witness is invalid: %s", err));
    }

    // Put input witness in transaction
    mtx.vin[input_idx].m_is_pegin = true;
    CTxInWitness txinwit;
    txinwit.m_pegin_witness = pegin_witness;

    if (mtx.witness.vtxinwit.size() <= input_idx) {
        mtx.witness.vtxinwit.resize(input_idx + 1);
    }
    mtx.witness.vtxinwit[input_idx] = txinwit;
}

void CreatePegInInput(CMutableTransaction& mtx, uint32_t input_idx, CTransactionRef& tx_btc, CMerkleBlock& merkle_block, const std::set<CScript>& claim_scripts, const std::vector<unsigned char>& txData, const std::vector<unsigned char>& txOutProofData, const CBlockIndex* active_chain_tip)
{
    CreatePegInInputInner(mtx, input_idx, tx_btc, merkle_block, claim_scripts, txData, txOutProofData, active_chain_tip);
}
void CreatePegInInput(CMutableTransaction& mtx, uint32_t input_idx, Sidechain::Bitcoin::CTransactionRef& tx_btc, Sidechain::Bitcoin::CMerkleBlock& merkle_block, const std::set<CScript>& claim_scripts, const std::vector<unsigned char>& txData, const std::vector<unsigned char>& txOutProofData, const CBlockIndex* active_chain_tip)
{
    CreatePegInInputInner(mtx, input_idx, tx_btc, merkle_block, claim_scripts, txData, txOutProofData, active_chain_tip);
}

CMutableTransaction ConstructTransaction(const UniValue& inputs_in, const UniValue& outputs_in, const UniValue& locktime, bool rbf, const CBlockIndex* active_chain_tip, std::map<CTxOut, PSBTOutput>* outputs_aux, bool allow_peg_in, bool allow_issuance)
{
    if (outputs_in.isNull()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, output argument must be non-null");
    }

    UniValue inputs;
    if (inputs_in.isNull()) {
        inputs = UniValue::VARR;
    } else {
        inputs = inputs_in.get_array();
    }

    UniValue outputs = outputs_in.get_array();

    CMutableTransaction rawTx;

    if (!locktime.isNull()) {
        int64_t nLockTime = locktime.get_int64();
        if (nLockTime < 0 || nLockTime > LOCKTIME_MAX)
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, locktime out of range");
        rawTx.nLockTime = nLockTime;
    }

    for (unsigned int idx = 0; idx < inputs.size(); idx++) {
        const UniValue& input = inputs[idx];
        const UniValue& o = input.get_obj();

        uint256 txid = ParseHashO(o, "txid");

        const UniValue& vout_v = find_value(o, "vout");
        if (!vout_v.isNum())
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, missing vout key");
        int nOutput = vout_v.get_int();
        if (nOutput < 0)
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, vout cannot be negative");

        uint32_t nSequence;
        if (rbf) {
            nSequence = MAX_BIP125_RBF_SEQUENCE; /* CTxIn::SEQUENCE_FINAL - 2 */
        } else if (rawTx.nLockTime) {
            nSequence = CTxIn::SEQUENCE_FINAL - 1;
        } else {
            nSequence = CTxIn::SEQUENCE_FINAL;
        }

        // set the sequence number if passed in the parameters object
        const UniValue& sequenceObj = find_value(o, "sequence");
        if (sequenceObj.isNum()) {
            int64_t seqNr64 = sequenceObj.get_int64();
            if (seqNr64 < 0 || seqNr64 > CTxIn::SEQUENCE_FINAL) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, sequence number is out of range");
            } else {
                nSequence = (uint32_t)seqNr64;
            }
        }

        CTxIn in(COutPoint(txid, nOutput), CScript(), nSequence);

        // Get issuance stuff if it's there
        const UniValue& blinding_nonce_v = find_value(o, "asset_blinding_nonce");
        const UniValue& entropy_v = find_value(o, "asset_entropy");
        const UniValue& amount_v = find_value(o, "issuance_amount");
        const UniValue& issuance_tokens_v = find_value(o, "issuance_tokens");
        const UniValue& blind_reissuance_v = find_value(o, "blind_reissuance");
        if (!amount_v.isNull() && allow_issuance) {
            if (!amount_v.isNum()) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "issuance_amount is not a number");
            }
            CAmount amt = AmountFromValue(amount_v);
            // issuance_tokens may be null for reissuance
            if (!issuance_tokens_v.isNull()) {
                if (!issuance_tokens_v.isNum()) {
                    throw JSONRPCError(RPC_INVALID_PARAMETER, "issuance_tokens is not a number");
                }
                CAmount num_inflation = AmountFromValue(issuance_tokens_v);
                in.assetIssuance.nInflationKeys.SetToAmount(num_inflation);
            }
            uint256 blinding_nonce;
            if (!blinding_nonce_v.isNull()) {
                blinding_nonce = ParseHashV(blinding_nonce_v, "asset_blinding_nonce");
            }
            uint256 entropy;
            if (!entropy_v.isNull()) {
                entropy = ParseHashV(entropy_v, "asset_entropy");
            }
            in.assetIssuance.nAmount.SetToAmount(amt);
            in.assetIssuance.assetBlindingNonce = blinding_nonce;
            in.assetIssuance.assetEntropy = entropy;
        } else if (!blinding_nonce_v.isNull() || !entropy_v.isNull() || !issuance_tokens_v.isNull() || !blind_reissuance_v.isNull()) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "auxiliary issuance arguments provided without issuance amount");
        }

        // Add to the tx
        rawTx.vin.push_back(in);

        // Get the pegin stuff if it's there
        const UniValue& pegin_tx = find_value(o, "pegin_bitcoin_tx");
        const UniValue& pegin_tx_proof = find_value(o, "pegin_txout_proof");
        const UniValue& pegin_script = find_value(o, "pegin_claim_script");
        if (!pegin_tx.isNull() && !pegin_tx_proof.isNull() && !pegin_script.isNull() && allow_peg_in) {
            if (!IsHex(pegin_script.get_str())) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Given claim_script is not hex.");
            }
            // If given manually, no need for it to be a witness script
            std::vector<unsigned char> claim_script_bytes(ParseHex(pegin_script.get_str()));
            CScript claim_script(claim_script_bytes.begin(), claim_script_bytes.end());
            std::set<CScript> claim_scripts;
            claim_scripts.insert(std::move(claim_script));
            if (Params().GetConsensus().ParentChainHasPow()) {
                Sidechain::Bitcoin::CTransactionRef tx_btc;
                Sidechain::Bitcoin::CMerkleBlock merkle_block;
                CreatePegInInput(rawTx, idx, tx_btc, merkle_block, claim_scripts, ParseHex(pegin_tx.get_str()), ParseHex(pegin_tx_proof.get_str()), active_chain_tip);
                if (!CheckParentProofOfWork(merkle_block.header.GetHash(), merkle_block.header.nBits, Params().GetConsensus())) {
                    throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid tx out proof");
                }
            } else {
                CTransactionRef tx_btc;
                CMerkleBlock merkle_block;
                CreatePegInInput(rawTx, idx, tx_btc, merkle_block, claim_scripts, ParseHex(pegin_tx.get_str()), ParseHex(pegin_tx_proof.get_str()), active_chain_tip);
                if (!CheckProofSignedParent(merkle_block.header, Params().GetConsensus())) {
                    throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid tx out proof");
                }
            }
        } else if (!pegin_tx.isNull() || !pegin_tx_proof.isNull() || !pegin_script.isNull()) {
            if (allow_peg_in) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Some but not all pegin_ arguments provided");
            } else {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "pegin_ arguments provided but this command does not support peg-ins");
            }
        }

    }

    // Keep track of the fee output so we can add it in the very end of the transaction.
    CTxOut fee_out;

    // Duplicate checking
    std::set<CTxDestination> destinations;
    bool has_data{false};

    std::vector<PSBTOutput> psbt_outs;
    for (unsigned int i = 0; i < outputs.size(); ++i) {
        const UniValue& output = outputs[i].get_obj();
        // New PSBTOutput with version 2
        PSBTOutput psbt_out(2);

        // ELEMENTS:
        // Asset defaults to policyAsset
        CTxOut out(::policyAsset, 0, CScript());

        bool is_fee = false;
        for (const std::string& name_ : output.getKeys()) {
            if (name_ == "data") {
                if (has_data) {
                    throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, duplicate key: data");
                }
                has_data = true;
                std::vector<unsigned char> data = ParseHexV(output[name_].getValStr(), "Data");

                out.nValue = 0;
                out.scriptPubKey = CScript() << OP_RETURN << data;
            } else if (name_ == "vdata") {
                // ELEMENTS: support multi-push OP_RETURN
                UniValue vdata = output[name_].get_array();
                CScript datascript = CScript() << OP_RETURN;
                for (size_t i = 0; i < vdata.size(); i++) {
                    std::vector<unsigned char> data = ParseHexV(vdata[i].get_str(), "Data");
                    datascript << data;
                }

                out.nValue = 0;
                out.scriptPubKey = datascript;
            } else if (name_ == "fee") {
                // ELEMENTS: explicit fee outputs
                CAmount nAmount = AmountFromValue(output[name_]);
                out.nValue = nAmount;
                out.scriptPubKey = CScript();
                is_fee = true;
                break;
            } else if (name_ == "burn") {
                CScript datascript = CScript() << OP_RETURN;
                CAmount nAmount = AmountFromValue(output[name_]);
                out.nValue = nAmount;
                out.scriptPubKey = datascript;
            } else if (name_ == "asset") {
                // ELEMENTS: Assets are specified
                out.nAsset = CAsset(ParseHashO(output, name_));
            } else if (name_ == "blinder_index") {
                // For PSET
                psbt_out.m_blinder_index = find_value(output, name_).get_int();
            } else {
                CTxDestination destination = DecodeDestination(name_);
                if (!IsValidDestination(destination)) {
                    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, std::string("Invalid Bitcoin address: ") + name_);
                }

                if (!destinations.insert(destination).second) {
                    throw JSONRPCError(RPC_INVALID_PARAMETER, std::string("Invalid parameter, duplicated address: ") + name_);
                }

                CScript scriptPubKey = GetScriptForDestination(destination);
                CAmount nAmount = AmountFromValue(output[name_]);

                out.nValue = nAmount;
                out.scriptPubKey = scriptPubKey;
                CPubKey blind_pub;
                if (IsBlindDestination(destination)) {
                    blind_pub = GetDestinationBlindingKey(destination);
                    if (!outputs_aux) {
                        // Only use the pubkey-in-nonce hack if the caller is not getting the pubkeys the nice way.
                        out.nNonce.vchCommitment = std::vector<unsigned char>(blind_pub.begin(), blind_pub.end());
                    }
                }
                psbt_out.m_blinding_pubkey = blind_pub;
            }
        }
        if (is_fee) {
            fee_out = out;
        } else {
            rawTx.vout.push_back(out);
            psbt_outs.push_back(psbt_out);
        }
    }

    // Add fee output in the end.
    if (!fee_out.nValue.IsNull() && fee_out.nValue.GetAmount() > 0) {
        rawTx.vout.push_back(fee_out);
        // New PSBTOutput with version 2
        psbt_outs.emplace_back(2);
    }

    if (outputs_aux) {
        for (unsigned int i = 0; i < rawTx.vout.size(); ++i) {
            outputs_aux->insert(std::make_pair(rawTx.vout[i], psbt_outs[i]));
        }
    }

    if (rbf && rawTx.vin.size() > 0 && !SignalsOptInRBF(CTransaction(rawTx))) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter combination: Sequence number(s) contradict replaceable option");
    }

    return rawTx;
}


/** Pushes a JSON object for script verification or signing errors to vErrorsRet. */
static void TxInErrorToJSON(const CTxIn& txin, const CTxInWitness& txinwit, UniValue& vErrorsRet, const std::string& strMessage)
{
    UniValue entry(UniValue::VOBJ);
    entry.pushKV("txid", txin.prevout.hash.ToString());
    entry.pushKV("vout", (uint64_t)txin.prevout.n);
    UniValue witness(UniValue::VARR);
    for (unsigned int i = 0; i < txinwit.scriptWitness.stack.size(); i++) {
        witness.push_back(HexStr(txinwit.scriptWitness.stack[i]));
    }
    entry.pushKV("witness", witness);
    entry.pushKV("scriptSig", HexStr(txin.scriptSig));
    entry.pushKV("sequence", (uint64_t)txin.nSequence);
    entry.pushKV("error", strMessage);
    vErrorsRet.push_back(entry);
}

void ParsePrevouts(const UniValue& prevTxsUnival, FillableSigningProvider* keystore, std::map<COutPoint, Coin>& coins)
{
    if (!prevTxsUnival.isNull()) {
        UniValue prevTxs = prevTxsUnival.get_array();
        for (unsigned int idx = 0; idx < prevTxs.size(); ++idx) {
            const UniValue& p = prevTxs[idx];
            if (!p.isObject()) {
                throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "expected object with {\"txid'\",\"vout\",\"scriptPubKey\"}");
            }

            UniValue prevOut = p.get_obj();

            RPCTypeCheckObj(prevOut,
                {
                    {"txid", UniValueType(UniValue::VSTR)},
                    {"vout", UniValueType(UniValue::VNUM)},
                    {"scriptPubKey", UniValueType(UniValue::VSTR)},
                });

            uint256 txid = ParseHashO(prevOut, "txid");

            int nOut = find_value(prevOut, "vout").get_int();
            if (nOut < 0) {
                throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "vout cannot be negative");
            }

            COutPoint out(txid, nOut);
            std::vector<unsigned char> pkData(ParseHexO(prevOut, "scriptPubKey"));
            CScript scriptPubKey(pkData.begin(), pkData.end());

            {
                auto coin = coins.find(out);
                if (coin != coins.end() && !coin->second.IsSpent() && coin->second.out.scriptPubKey != scriptPubKey) {
                    std::string err("Previous output scriptPubKey mismatch:\n");
                    err = err + ScriptToAsmStr(coin->second.out.scriptPubKey) + "\nvs:\n"+
                        ScriptToAsmStr(scriptPubKey);
                    throw JSONRPCError(RPC_DESERIALIZATION_ERROR, err);
                }
                Coin newcoin;
                newcoin.out.scriptPubKey = scriptPubKey;
                newcoin.out.nValue = CConfidentialValue(MAX_MONEY);
                if (prevOut.exists("amount")) {
                    newcoin.out.nValue = CConfidentialValue(AmountFromValue(find_value(prevOut, "amount")));
                } else if (prevOut.exists("amountcommitment")) {
                    // Segwit sigs require the amount commitment to be sighashed
                    newcoin.out.nValue.vchCommitment = ParseHexO(prevOut, "amountcommitment");
                }
                newcoin.nHeight = 1;
                coins[out] = std::move(newcoin);
            }

            // if redeemScript and private keys were given, add redeemScript to the keystore so it can be signed
            const bool is_p2sh = scriptPubKey.IsPayToScriptHash();
            const bool is_p2wsh = scriptPubKey.IsPayToWitnessScriptHash();
            if (keystore && (is_p2sh || is_p2wsh)) {
                RPCTypeCheckObj(prevOut,
                    {
                        {"redeemScript", UniValueType(UniValue::VSTR)},
                        {"witnessScript", UniValueType(UniValue::VSTR)},
                    }, true);
                UniValue rs = find_value(prevOut, "redeemScript");
                UniValue ws = find_value(prevOut, "witnessScript");
                if (rs.isNull() && ws.isNull()) {
                    throw JSONRPCError(RPC_INVALID_PARAMETER, "Missing redeemScript/witnessScript");
                }

                // work from witnessScript when possible
                std::vector<unsigned char> scriptData(!ws.isNull() ? ParseHexV(ws, "witnessScript") : ParseHexV(rs, "redeemScript"));
                CScript script(scriptData.begin(), scriptData.end());
                keystore->AddCScript(script);
                // Automatically also add the P2WSH wrapped version of the script (to deal with P2SH-P2WSH).
                // This is done for redeemScript only for compatibility, it is encouraged to use the explicit witnessScript field instead.
                CScript witness_output_script{GetScriptForDestination(WitnessV0ScriptHash(script))};
                keystore->AddCScript(witness_output_script);

                if (!ws.isNull() && !rs.isNull()) {
                    // if both witnessScript and redeemScript are provided,
                    // they should either be the same (for backwards compat),
                    // or the redeemScript should be the encoded form of
                    // the witnessScript (ie, for p2sh-p2wsh)
                    if (ws.get_str() != rs.get_str()) {
                        std::vector<unsigned char> redeemScriptData(ParseHexV(rs, "redeemScript"));
                        CScript redeemScript(redeemScriptData.begin(), redeemScriptData.end());
                        if (redeemScript != witness_output_script) {
                            throw JSONRPCError(RPC_INVALID_PARAMETER, "redeemScript does not correspond to witnessScript");
                        }
                    }
                }

                if (is_p2sh) {
                    const CTxDestination p2sh{ScriptHash(script)};
                    const CTxDestination p2sh_p2wsh{ScriptHash(witness_output_script)};
                    if (scriptPubKey == GetScriptForDestination(p2sh)) {
                        // traditional p2sh; arguably an error if
                        // we got here with rs.IsNull(), because
                        // that means the p2sh script was specified
                        // via witnessScript param, but for now
                        // we'll just quietly accept it
                    } else if (scriptPubKey == GetScriptForDestination(p2sh_p2wsh)) {
                        // p2wsh encoded as p2sh; ideally the witness
                        // script was specified in the witnessScript
                        // param, but also support specifying it via
                        // redeemScript param for backwards compat
                        // (in which case ws.IsNull() == true)
                    } else {
                        // otherwise, can't generate scriptPubKey from
                        // either script, so we got unusable parameters
                        throw JSONRPCError(RPC_INVALID_PARAMETER, "redeemScript/witnessScript does not match scriptPubKey");
                    }
                } else if (is_p2wsh) {
                    // plain p2wsh; could throw an error if script
                    // was specified by redeemScript rather than
                    // witnessScript (ie, ws.IsNull() == true), but
                    // accept it for backwards compat
                    const CTxDestination p2wsh{WitnessV0ScriptHash(script)};
                    if (scriptPubKey != GetScriptForDestination(p2wsh)) {
                        throw JSONRPCError(RPC_INVALID_PARAMETER, "redeemScript/witnessScript does not match scriptPubKey");
                    }
                }
            }
        }
    }
}

// ELEMENTS: check whether pegin inputs make sense against the current fedpegscript
bool ValidateTransactionPeginInputs(const CMutableTransaction& mtx, const CBlockIndex* active_chain_tip, std::map<int, std::string>& input_errors)
{
    const auto& fedpegscripts = GetValidFedpegScripts(active_chain_tip, Params().GetConsensus(), true /* nextblock_validation */);
    // Track an immature peg-in that's otherwise valid, give warning
    bool immature_pegin = false;

    for (unsigned int i = 0; i < mtx.vin.size(); i++) {
        const CTxIn& txin = mtx.vin[i];
        std::string err;
        if (txin.m_is_pegin && (mtx.witness.vtxinwit.size() <= i || !IsValidPeginWitness(mtx.witness.vtxinwit[i].m_pegin_witness, fedpegscripts, txin.prevout, err, false))) {
            input_errors[i] = "Peg-in input has invalid proof.";
            continue;
        }
        // Report warning about immature peg-in though
        bool depth_failed = false;
        if(txin.m_is_pegin && !IsValidPeginWitness(mtx.witness.vtxinwit[i].m_pegin_witness, fedpegscripts, txin.prevout, err, true, &depth_failed)) {
            CHECK_NONFATAL(depth_failed);
            immature_pegin = true;
        }
    }
    return immature_pegin;
}

void SignTransaction(CMutableTransaction& mtx, const SigningProvider* keystore, const std::map<COutPoint, Coin>& coins, const UniValue& hashType, UniValue& result, const CBlockIndex* active_chain_tip)
{
    int nHashType = ParseSighashString(hashType);

    // Script verification errors
    std::map<int, std::string> input_errors;

    bool immature_pegin = ValidateTransactionPeginInputs(mtx, active_chain_tip, input_errors);
    bool complete = SignTransaction(mtx, keystore, coins, nHashType, Params().HashGenesisBlock(), input_errors);
    SignTransactionResultToJSON(mtx, complete, coins, input_errors, immature_pegin, result);
}

void SignTransactionResultToJSON(CMutableTransaction& mtx, bool complete, const std::map<COutPoint, Coin>& coins, const std::map<int, std::string>& input_errors, bool immature_pegin, UniValue& result)
{
    // Make errors UniValue
    UniValue vErrors(UniValue::VARR);
    for (const auto& err_pair : input_errors) {
        if (err_pair.second == "Missing amount") {
            // This particular error needs to be an exception for some reason
            throw JSONRPCError(RPC_TYPE_ERROR, strprintf("Missing amount for %s", coins.at(mtx.vin.at(err_pair.first).prevout).out.ToString()));
        }
        TxInErrorToJSON(mtx.vin.at(err_pair.first), mtx.witness.vtxinwit.at(err_pair.first), vErrors, err_pair.second);
    }

    result.pushKV("hex", EncodeHexTx(CTransaction(mtx)));
    result.pushKV("complete", complete);
    if (!vErrors.empty()) {
        if (result.exists("errors")) {
            vErrors.push_backV(result["errors"].getValues());
        }
        result.pushKV("errors", vErrors);
    }
    if (immature_pegin) {
        result.pushKV("warning", "Possibly immature peg-in input(s) detected, signed anyways.");
    }
}

