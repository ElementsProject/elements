// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2019 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <rpc/rawtransaction_util.h>

#include <coins.h>
#include <core_io.h>
#include <key_io.h>
#include <pegins.h>
#include <policy/policy.h>
#include <primitives/transaction.h>
#include <rpc/request.h>
#include <rpc/util.h>
#include <script/sign.h>
#include <script/signingprovider.h>
#include <tinyformat.h>
#include <univalue.h>
#include <util/rbf.h>
#include <util/strencodings.h>

CMutableTransaction ConstructTransaction(const UniValue& inputs_in, const UniValue& outputs_in, const UniValue& locktime, const UniValue& rbf, const UniValue& assets_in)
{
    if (inputs_in.isNull() || outputs_in.isNull())
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, arguments 1 and 2 must be non-null");

    UniValue inputs = inputs_in.get_array();
    const bool outputs_is_obj = outputs_in.isObject();
    UniValue outputs = outputs_is_obj ? outputs_in.get_obj() : outputs_in.get_array();

    CMutableTransaction rawTx;

    if (!locktime.isNull()) {
        int64_t nLockTime = locktime.get_int64();
        if (nLockTime < 0 || nLockTime > LOCKTIME_MAX)
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, locktime out of range");
        rawTx.nLockTime = nLockTime;
    }

    bool rbfOptIn = rbf.isTrue();

    UniValue assets;
    if (!assets_in.isNull()) {
        assets = assets_in.get_obj();
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
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, vout must be positive");

        uint32_t nSequence;
        if (rbfOptIn) {
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

        rawTx.vin.push_back(in);
    }

    if (!outputs_is_obj) {
        // Translate array of key-value pairs into dict
        UniValue outputs_dict = UniValue(UniValue::VOBJ);
        for (size_t i = 0; i < outputs.size(); ++i) {
            const UniValue& output = outputs[i];
            if (!output.isObject()) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, key-value pair not an object as expected");
            }
            if (output.size() != 1) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, key-value pair must contain exactly one key");
            }
            outputs_dict.pushKVs(output);
        }
        outputs = std::move(outputs_dict);
    }
    // Keep track of the fee output so we can add it in the very end of the transaction.
    CTxOut fee_out;

    // Duplicate checking
    std::set<CTxDestination> destinations;
    bool has_data{false};

    for (const std::string& name_ : outputs.getKeys()) {
        // ELEMENTS:
        // Asset defaults to policyAsset
        CAsset asset(::policyAsset);
        if (!assets.isNull()) {
            if (!find_value(assets, name_).isNull()) {
                asset = CAsset(ParseHashO(assets, name_));
            }
        }

        if (name_ == "data") {
            if (has_data) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, duplicate key: data");
            }
            has_data = true;
            std::vector<unsigned char> data = ParseHexV(outputs[name_].getValStr(), "Data");

            CTxOut out(asset, 0, CScript() << OP_RETURN << data);
            rawTx.vout.push_back(out);
        } else if (name_ == "vdata") {
            // ELEMENTS: support multi-push OP_RETURN
            UniValue vdata = outputs[name_].get_array();
            CScript datascript = CScript() << OP_RETURN;
            for (size_t i = 0; i < vdata.size(); i++) {
                std::vector<unsigned char> data = ParseHexV(vdata[i].get_str(), "Data");
                datascript << data;
            }

            CTxOut out(asset, 0, datascript);
            rawTx.vout.push_back(out);
        } else if (name_ == "fee") {
            // ELEMENTS: explicit fee outputs
            CAmount nAmount = AmountFromValue(outputs[name_]);
            fee_out = CTxOut(asset, nAmount, CScript());
        } else if (name_ == "burn") {
            CScript datascript = CScript() << OP_RETURN;
            CAmount nAmount = AmountFromValue(outputs[name_]);
            CTxOut out(asset, nAmount, datascript);
            rawTx.vout.push_back(out);
        } else {
            CTxDestination destination = DecodeDestination(name_);
            if (!IsValidDestination(destination)) {
                throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, std::string("Invalid Bitcoin address: ") + name_);
            }

            if (!destinations.insert(destination).second) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, std::string("Invalid parameter, duplicated address: ") + name_);
            }

            CScript scriptPubKey = GetScriptForDestination(destination);
            CAmount nAmount = AmountFromValue(outputs[name_]);

            CTxOut out(asset, nAmount, scriptPubKey);
            if (IsBlindDestination(destination)) {
                CPubKey blind_pub = GetDestinationBlindingKey(destination);
                out.nNonce.vchCommitment = std::vector<unsigned char>(blind_pub.begin(), blind_pub.end());
            }
            rawTx.vout.push_back(out);
        }
    }

    // Add fee output in the end.
    if (!fee_out.nValue.IsNull() && fee_out.nValue.GetAmount() > 0) {
        rawTx.vout.push_back(fee_out);
    }

    if (!rbf.isNull() && rawTx.vin.size() > 0 && rbfOptIn != SignalsOptInRBF(CTransaction(rawTx))) {
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
        witness.push_back(HexStr(txinwit.scriptWitness.stack[i].begin(), txinwit.scriptWitness.stack[i].end()));
    }
    entry.pushKV("witness", witness);
    entry.pushKV("scriptSig", HexStr(txin.scriptSig.begin(), txin.scriptSig.end()));
    entry.pushKV("sequence", (uint64_t)txin.nSequence);
    entry.pushKV("error", strMessage);
    vErrorsRet.push_back(entry);
}

UniValue SignTransaction(CMutableTransaction& mtx, const UniValue& prevTxsUnival, FillableSigningProvider* keystore, std::map<COutPoint, Coin>& coins, bool is_temp_keystore, const UniValue& hashType)
{
    // Add previous txouts given in the RPC call:
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
                throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "vout must be positive");
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
                    uint256 asset_commit = uint256S(prevOut["amountcommitment"].get_str());
                    newcoin.out.nValue.vchCommitment = std::vector<unsigned char>(asset_commit.begin(), asset_commit.end());
                }
                newcoin.nHeight = 1;
                coins[out] = std::move(newcoin);
            }

            // if redeemScript and private keys were given, add redeemScript to the keystore so it can be signed
            if (is_temp_keystore && (scriptPubKey.IsPayToScriptHash() || scriptPubKey.IsPayToWitnessScriptHash())) {
                RPCTypeCheckObj(prevOut,
                    {
                        {"redeemScript", UniValueType(UniValue::VSTR)},
                        {"witnessScript", UniValueType(UniValue::VSTR)},
                    }, true);
                UniValue rs = find_value(prevOut, "redeemScript");
                if (!rs.isNull()) {
                    std::vector<unsigned char> rsData(ParseHexV(rs, "redeemScript"));
                    CScript redeemScript(rsData.begin(), rsData.end());
                    keystore->AddCScript(redeemScript);
                    // Automatically also add the P2WSH wrapped version of the script (to deal with P2SH-P2WSH).
                    // This is only for compatibility, it is encouraged to use the explicit witnessScript field instead.
                    keystore->AddCScript(GetScriptForWitness(redeemScript));
                }
                UniValue ws = find_value(prevOut, "witnessScript");
                if (!ws.isNull()) {
                    std::vector<unsigned char> wsData(ParseHexV(ws, "witnessScript"));
                    CScript witnessScript(wsData.begin(), wsData.end());
                    keystore->AddCScript(witnessScript);
                    // Automatically also add the P2WSH wrapped version of the script (to deal with P2SH-P2WSH).
                    keystore->AddCScript(GetScriptForWitness(witnessScript));
                }
                if (rs.isNull() && ws.isNull()) {
                    throw JSONRPCError(RPC_INVALID_PARAMETER, "Missing redeemScript/witnessScript");
                }
            }
        }
    }

    int nHashType = ParseSighashString(hashType);

    bool fHashSingle = ((nHashType & ~SIGHASH_ANYONECANPAY) == SIGHASH_SINGLE);

    // Script verification errors
    UniValue vErrors(UniValue::VARR);

    // ELEMENTS:
    // Track an immature peg-in that's otherwise valid, give warning
    bool immature_pegin = false;

    // Use CTransaction for the constant parts of the
    // transaction to avoid rehashing.
    const CTransaction txConst(mtx);
    // Sign what we can, including pegin inputs:
    mtx.witness.vtxinwit.resize(mtx.vin.size());
    for (unsigned int i = 0; i < mtx.vin.size(); i++) {
        CTxIn& txin = mtx.vin[i];
        const CTxInWitness& inWitness = mtx.witness.vtxinwit[i];
        auto coin = coins.find(txin.prevout);

        std::string err;
        if (!txin.m_is_pegin && (coin == coins.end() || coin->second.IsSpent())) {
            TxInErrorToJSON(txin, inWitness, vErrors, "Input not found or already spent");
            continue;
        } else if (txin.m_is_pegin && (txConst.witness.vtxinwit.size() <= i || !IsValidPeginWitness(txConst.witness.vtxinwit[i].m_pegin_witness, txin.prevout, err, false))) {
            TxInErrorToJSON(txin, inWitness, vErrors, "Peg-in input has invalid proof.");
            continue;
        }
        // Report warning about immature peg-in though
        if(txin.m_is_pegin && !IsValidPeginWitness(txConst.witness.vtxinwit[i].m_pegin_witness, txin.prevout, err, true)) {
            assert(err == "Needs more confirmations.");
            immature_pegin = true;
        }

        const CScript& prevPubKey = txin.m_is_pegin ? GetPeginOutputFromWitness(txConst.witness.vtxinwit[i].m_pegin_witness).scriptPubKey : coin->second.out.scriptPubKey;
        const CConfidentialValue& amount = txin.m_is_pegin ? GetPeginOutputFromWitness(txConst.witness.vtxinwit[i].m_pegin_witness).nValue : coin->second.out.nValue;

        SignatureData sigdata = DataFromTransaction(mtx, i, coin->second.out);
        // Only sign SIGHASH_SINGLE if there's a corresponding output:
        if (!fHashSingle || (i < mtx.vout.size())) {
            ProduceSignature(*keystore, MutableTransactionSignatureCreator(&mtx, i, amount, nHashType), prevPubKey, sigdata);
        }

        UpdateTransaction(mtx, i, sigdata);

        // amount must be specified for valid segwit signature
        if (amount.IsExplicit() && amount.GetAmount() == MAX_MONEY && !mtx.witness.vtxinwit[i].scriptWitness.IsNull()) {
            throw JSONRPCError(RPC_TYPE_ERROR, strprintf("Missing amount for %s", coin->second.out.ToString()));
        }

        ScriptError serror = SCRIPT_ERR_OK;
        if (!VerifyScript(txin.scriptSig, prevPubKey, &inWitness.scriptWitness, STANDARD_SCRIPT_VERIFY_FLAGS, TransactionSignatureChecker(&txConst, i, amount), &serror)) {
            if (serror == SCRIPT_ERR_INVALID_STACK_OPERATION) {
                // Unable to sign input and verification failed (possible attempt to partially sign).
                TxInErrorToJSON(txin, inWitness, vErrors, "Unable to sign input, invalid stack size (possibly missing key)");
            } else {
                TxInErrorToJSON(txin, inWitness, vErrors, ScriptErrorString(serror));
            }
        }
    }
    bool fComplete = vErrors.empty();

    UniValue result(UniValue::VOBJ);
    result.pushKV("hex", EncodeHexTx(CTransaction(mtx)));
    result.pushKV("complete", fComplete);
    if (!vErrors.empty()) {
        result.pushKV("errors", vErrors);
    }
    if (immature_pegin) {
        result.pushKV("warning", "Possibly immature peg-in input(s) detected, signed anyways.");
    }

    return result;
}

