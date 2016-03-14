// Copyright (c) 2009-2014 The Bitcoin developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "base58.h"
#include "blind.h"
#include "clientversion.h"
#include "primitives/block.h" // for MAX_BLOCK_SIZE
#include "primitives/transaction.h"
#include "core_io.h"
#include "coins.h"
#include "keystore.h"
#include "merkleblock.h"
#include "script/script.h"
#include "script/sign.h"
#include "streams.h"
#include "ui_interface.h" // for _(...)
#include "univalue/univalue.h"
#include "util.h"
#include "utilstrencodings.h"
#include "utilmoneystr.h"

#include <stdio.h>

#include <boost/algorithm/string.hpp>
#include <boost/assign/list_of.hpp>

using namespace boost::assign;
using namespace std;

static bool fCreateBlank;
static map<string,UniValue> registers;
CClientUIInterface uiInterface;

static bool AppInitRawTx(int argc, char* argv[])
{
    //
    // Parameters
    //
    ParseParameters(argc, argv);

    // Check for -testnet or -regtest parameter (Params() calls are only valid after this clause)
    if (!SelectParamsFromCommandLine()) {
        fprintf(stderr, "Error: Invalid combination of -regtest and -testnet.\n");
        return false;
    }

    fCreateBlank = GetBoolArg("-create", false);

    if (argc<2 || mapArgs.count("-?") || mapArgs.count("-help"))
    {
        // First part of help message is specific to this utility
        std::string strUsage = _("Elements Alpha alpha-tx utility version") + " " + FormatFullVersion() + "\n\n" +
            _("Usage:") + "\n" +
              "  alpha-tx [options] <hex-tx> [commands]  " + _("Update hex-encoded bitcoin transaction") + "\n" +
              "  alpha-tx [options] -create [commands]   " + _("Create hex-encoded bitcoin transaction") + "\n" +
              "\n";

        fprintf(stdout, "%s", strUsage.c_str());

        strUsage = _("Options:") + "\n";
        strUsage += "  -?                      " + _("This help message") + "\n";
        strUsage += "  -create                 " + _("Create new, empty TX.") + "\n";
        strUsage += "  -json                   " + _("Select JSON output") + "\n";
        strUsage += "  -txid                   " + _("Output only the hex-encoded transaction id of the resultant transaction.") + "\n";
        strUsage += "  -regtest                " + _("Enter regression test mode, which uses a special chain in which blocks can be solved instantly.") + "\n";
        strUsage += "  -testnet                " + _("Use the test network") + "\n";
        strUsage += "\n";

        fprintf(stdout, "%s", strUsage.c_str());


        strUsage = _("Commands:") + "\n";
        strUsage += "  delin=N                " + _("Delete input N from TX") + "\n";
        strUsage += "  delout=N               " + _("Delete output N from TX") + "\n";
        strUsage += "  in=TXID:VOUT:VALUE:SEQ[:ASSETID] " + _("Add input to TX") + "\n";
        strUsage += "  blind=B1:B3:B4:...     " + _("Blind transaction outputs") + "\n";
        strUsage += "  locktime=N             " + _("Set TX lock time to N") + "\n";
        strUsage += "  nversion=N             " + _("Set TX version to N") + "\n";
        strUsage += "  outaddr=VALUE:ADDRESS[:ASSETID] " + _("Add address-based output to TX") + "\n";
        strUsage += "  outscript=VALUE:SCRIPT[:ASSETID]" + _("Add raw script output to TX") + "\n";
        strUsage += "  sign=SIGHASH-FLAGS     " + _("Add zero or more signatures to transaction") + "\n";
        strUsage += "      This command requires JSON registers:\n";
        strUsage += "      prevtxs=JSON object\n";
        strUsage += "      privatekeys=JSON object\n";
        strUsage += "      See signrawtransaction docs for format of sighash flags, JSON objects.\n";
        strUsage += "  newasset=1             " + _("Make it a transaction definition transaction. An error will be raised if used after the transaction already has inputs.") + "\n";
        strUsage += "\n";
        fprintf(stdout, "%s", strUsage.c_str());

        strUsage = _("Register Commands:") + "\n";
        strUsage += "  load=NAME:FILENAME     " + _("Load JSON file FILENAME into register NAME") + "\n";
        strUsage += "  set=NAME:JSON-STRING   " + _("Set register NAME to given JSON-STRING") + "\n";
        strUsage += "\n";
        fprintf(stdout, "%s", strUsage.c_str());

        return false;
    }
    return true;
}

static void RegisterSetJson(const string& key, const string& rawJson)
{
    UniValue val;
    if (!val.read(rawJson)) {
        string strErr = "Cannot parse JSON for key " + key;
        throw runtime_error(strErr);
    }

    registers[key] = val;
}

static void RegisterSet(const string& strInput)
{
    // separate NAME:VALUE in string
    size_t pos = strInput.find(':');
    if ((pos == string::npos) ||
        (pos == 0) ||
        (pos == (strInput.size() - 1)))
        throw runtime_error("Register input requires NAME:VALUE");

    string key = strInput.substr(0, pos);
    string valStr = strInput.substr(pos + 1, string::npos);

    RegisterSetJson(key, valStr);
}

static void RegisterLoad(const string& strInput)
{
    // separate NAME:FILENAME in string
    size_t pos = strInput.find(':');
    if ((pos == string::npos) ||
        (pos == 0) ||
        (pos == (strInput.size() - 1)))
        throw runtime_error("Register load requires NAME:FILENAME");

    string key = strInput.substr(0, pos);
    string filename = strInput.substr(pos + 1, string::npos);

    FILE *f = fopen(filename.c_str(), "r");
    if (!f) {
        string strErr = "Cannot open file " + filename;
        throw runtime_error(strErr);
    }

    // load file chunks into one big buffer
    string valStr;
    while ((!feof(f)) && (!ferror(f))) {
        char buf[4096];
        int bread = fread(buf, 1, sizeof(buf), f);
        if (bread <= 0)
            break;

        valStr.insert(valStr.size(), buf, bread);
    }

    if (ferror(f)) {
        string strErr = "Error reading file " + filename;
        throw runtime_error(strErr);
    }

    fclose(f);

    // evaluate as JSON buffer register
    RegisterSetJson(key, valStr);
}

static void MutateTxVersion(CMutableTransaction& tx, const string& cmdVal)
{
    int64_t newVersion = atoi64(cmdVal);
    if (newVersion < 1 || newVersion > CTransaction::CURRENT_VERSION)
        throw runtime_error("Invalid TX version requested");

    tx.nVersion = (int) newVersion;
}

static void MutateTxLocktime(CMutableTransaction& tx, const string& cmdVal)
{
    int64_t newLocktime = atoi64(cmdVal);
    if (newLocktime < 0LL || newLocktime > 0xffffffffLL)
        throw runtime_error("Invalid TX locktime requested");

    tx.nLockTime = (unsigned int) newLocktime;
}

static void MutateTxAddInput(CMutableTransaction& tx, const string& strInput)
{
    // separate TXID:VOUT in string
    size_t pos = strInput.find(':');
    if ((pos == string::npos) ||
        (pos == 0) ||
        (pos == (strInput.size() - 1)))
        throw runtime_error("TX input missing separator");

    // extract and validate TXID
    string strTxid = strInput.substr(0, pos);
    if ((strTxid.size() != 64) || !IsHex(strTxid))
        throw runtime_error("invalid TX input txid");
    uint256 txid(strTxid);

    static const unsigned int minTxOutSz = 9;
    static const unsigned int maxVout = MAX_BLOCK_SIZE / minTxOutSz;

    // Remove txid
    string strVout = strInput.substr(pos + 1, string::npos);

    // extract and validate vout
    int vout = atoi(strVout);
    if ((vout < 0) || (vout > (int)maxVout))
        throw runtime_error("invalid TX input vout");

    // Remove vout
    pos = strVout.find(':', pos + 1);
    strVout = strVout.substr(pos + 1, string::npos);

    // extract and validate VALUE
    pos = strVout.find(':', pos + 1);
    if (pos == string::npos)
        throw runtime_error("TX input missing separator");
    string strValue = strVout.substr(pos + 1, strVout.find(':', pos + 1) - pos - 1);
    CAmount value;
    if (!ParseMoney(strValue, value))
        throw runtime_error("invalid TX output value");

    CAssetID assetID = CAssetID(Params().HashGenesisBlock());
    // extract and validate sequence number
    uint32_t nSequence = ~(uint32_t)0;
    pos = strVout.find(':', pos + 1);
    if (pos != string::npos) {
        if ((pos == 0) || (pos == (strVout.size() - 1)))
            throw runtime_error("empty TX input field");

        string strSeq = strVout.substr(pos + 1, string::npos);
        size_t posAsset = strVout.find(':', pos + 1);
        if (posAsset != string::npos && posAsset != 0 && posAsset != (strVout.size() - 1)) {
            strSeq = strVout.substr(pos + 1, posAsset);
            string strAsset = strVout.substr(posAsset + 1, string::npos);
            assetID = CAssetID(uint256(strAsset));
        }

        strVout.resize(pos);
        int64_t nSeq = atoi64(strSeq);

        // Allow e.g. -1 to be used for 0xffffffff
        if (nSeq < 0)
            nSeq += ((int64_t)std::numeric_limits<uint32_t>::max()) + 1;

        // Range check
        if (nSeq < std::numeric_limits<uint32_t>::min() ||
            nSeq > std::numeric_limits<uint32_t>::max())
        {
            throw runtime_error("invalid TX input sequence");
        }

        nSequence = (uint32_t)nSeq;
    } else {
        throw runtime_error("invalid TX input: sequence missing");
    }

    // append to transaction input list
    CTxIn txin(txid, vout, CScript(), nSequence);
    tx.vin.push_back(txin);
    CAmountMap mTxReward = CTransaction(tx).GetTxRewardMap();
    mTxReward[assetID] += value;
    tx.SetFeesFromTxRewardMap(mTxReward);
}

static void MutateTxAddOutAddr(CMutableTransaction& tx, const string& strInput)
{
    // separate VALUE:ADDRESS in string
    size_t pos = strInput.find(':');
    if ((pos == string::npos) ||
        (pos == 0) ||
        (pos == (strInput.size() - 1)))
        throw runtime_error("TX output missing separator");

    // extract and validate VALUE
    string strValue = strInput.substr(0, pos);
    CAmount value;
    if (!ParseMoney(strValue, value))
        throw runtime_error("invalid TX output value");

    // extract and validate ADDRESS
    string strAddr = strInput.substr(pos + 1, string::npos);
    CAssetID assetID = CAssetID(Params().HashGenesisBlock());
    size_t posAsset = strInput.find(':', pos + 1);
    if (posAsset != string::npos && posAsset != 0 && posAsset != (strInput.size() - 1)) {
        strAddr = strInput.substr(pos + 1, posAsset - pos - 1);
        string strAsset = strInput.substr(posAsset + 1, string::npos);
        assetID = CAssetID(uint256(strAsset));
    }

    CBitcoinAddress addr(strAddr);
    if (!addr.IsValid())
        throw runtime_error("invalid TX output address");

    // build standard output script via GetScriptForDestination()
    CScript scriptPubKey = GetScriptForDestination(addr.Get());

    // construct TxOut, append to transaction output list
    CTxOut txout(value, scriptPubKey, assetID);
    if (addr.IsBlinded()) {
        CPubKey pubkey = addr.GetBlindingKey();
        txout.nValue.vchNonceCommitment = std::vector<unsigned char>(pubkey.begin(), pubkey.end());
    }
    tx.vout.push_back(txout);
    CAmountMap mTxReward = CTransaction(tx).GetTxRewardMap();
    mTxReward[assetID] -= value;
    tx.SetFeesFromTxRewardMap(mTxReward);
}

static void MutateTxBlind(CMutableTransaction& tx, const string& strInput)
{
    std::vector<std::string> input_blinding_factors;
    boost::split(input_blinding_factors, strInput, boost::is_any_of(":"));

    if (input_blinding_factors.size() != tx.vin.size())
        throw runtime_error("One input blinding factor required per transaction input");

    bool fBlindedIns = false;
    bool fBlindedOuts = false;
    std::vector<uint256> input_blinds;
    std::vector<uint256> output_blinds;
    std::vector<CPubKey> output_pubkeys;
    for (size_t nIn = 0; nIn < tx.vin.size(); nIn++) {
        uint256 blind;
        blind.SetHex(input_blinding_factors[nIn]);
        if (blind.size() == 0) {
            input_blinds.push_back(blind);
        } else if (blind.size() == 32) {
            input_blinds.push_back(blind);
            fBlindedIns = true;
        }
    }
    for (size_t nOut = 0; nOut < tx.vout.size(); nOut++) {
        if (!tx.vout[nOut].nValue.IsAmount())
            throw runtime_error("Invalid parameter: transaction outputs must be unblinded");
        if (tx.vout[nOut].nValue.vchNonceCommitment.size() == 0) {
            output_pubkeys.push_back(CPubKey());
        } else {
            CPubKey pubkey(tx.vout[nOut].nValue.vchNonceCommitment);
            if (!pubkey.IsValid()) {
                 throw runtime_error("Invalid parameter: invalid confidentiality public key given");
            }
            output_pubkeys.push_back(pubkey);
            fBlindedOuts = true;
        }
        output_blinds.push_back(uint256());
    }

    if (fBlindedIns && !fBlindedOuts) {
        throw runtime_error("Confidential inputs without confidential outputs");
    }
    BlindOutputs(input_blinds, output_blinds, output_pubkeys, tx);
}

static void MutateTxAddOutScript(CMutableTransaction& tx, const string& strInput)
{
    // separate VALUE:SCRIPT in string
    size_t pos = strInput.find(':');
    if ((pos == string::npos) ||
        (pos == 0))
        throw runtime_error("TX output missing separator");

    // extract and validate VALUE
    string strValue = strInput.substr(0, pos);
    CAmount value;
    if (!ParseMoney(strValue, value))
        throw runtime_error("invalid TX output value");

    // extract and validate script
    string strScript = strInput.substr(pos + 1, string::npos);
    CAssetID assetID = CAssetID(Params().HashGenesisBlock());
    size_t posAsset = strInput.find(':', pos + 1);
    if (posAsset != string::npos && posAsset != 0 && posAsset != (strInput.size() - 1)) {
        strScript = strInput.substr(pos, posAsset);
        string strAsset = strInput.substr(posAsset + 1, string::npos);
        assetID = CAssetID(uint256(strAsset));
    }
    CScript scriptPubKey = ParseScript(strScript); // throws on err

    CAmountMap mTxReward = CTransaction(tx).GetTxRewardMap();
    mTxReward[assetID] -= value;
    tx.SetFeesFromTxRewardMap(mTxReward);
    // construct TxOut, append to transaction output list
    CTxOut txout(value, scriptPubKey, assetID);
    tx.vout.push_back(txout);
}

static void MutateTxDelInput(CMutableTransaction& tx, const string& strInIdx)
{
    // parse requested deletion index
    int inIdx = atoi(strInIdx);
    if (inIdx < 0 || inIdx >= (int)tx.vin.size()) {
        string strErr = "Invalid TX input index '" + strInIdx + "'";
        throw runtime_error(strErr.c_str());
    }
    // TODO: reduce fees (SetFeesFromTxRewardMap)

    // delete input from transaction
    tx.vin.erase(tx.vin.begin() + inIdx);
}

static void MutateTxDelOutput(CMutableTransaction& tx, const string& strOutIdx)
{
    // parse requested deletion index
    int outIdx = atoi(strOutIdx);
    if (outIdx < 0 || outIdx >= (int)tx.vout.size()) {
        string strErr = "Invalid TX output index '" + strOutIdx + "'";
        throw runtime_error(strErr.c_str());
    }

    if (!tx.vout[outIdx].nValue.IsAmount())
        throw runtime_error("Cannot delete confidential outputs");

    CAmountMap mTxReward = CTransaction(tx).GetTxRewardMap();
    CTxOut txOut = tx.vout[outIdx];
    mTxReward[txOut.assetID] -= txOut.nValue.GetAmount();
    tx.SetFeesFromTxRewardMap(mTxReward);
    // delete output from transaction
    tx.vout.erase(tx.vout.begin() + outIdx);
}

static const unsigned int N_SIGHASH_OPTS = 6;
static const struct {
    const char *flagStr;
    int flags;
} sighashOptions[N_SIGHASH_OPTS] = {
    {"ALL", SIGHASH_ALL},
    {"NONE", SIGHASH_NONE},
    {"SINGLE", SIGHASH_SINGLE},
    {"ALL|ANYONECANPAY", SIGHASH_ALL|SIGHASH_ANYONECANPAY},
    {"NONE|ANYONECANPAY", SIGHASH_NONE|SIGHASH_ANYONECANPAY},
    {"SINGLE|ANYONECANPAY", SIGHASH_SINGLE|SIGHASH_ANYONECANPAY},
};

static bool findSighashFlags(int& flags, const string& flagStr)
{
    flags = 0;

    for (unsigned int i = 0; i < N_SIGHASH_OPTS; i++) {
        if (flagStr == sighashOptions[i].flagStr) {
            flags = sighashOptions[i].flags;
            return true;
        }
    }

    return false;
}

uint256 ParseHashUO(map<string,UniValue>& o, string strKey)
{
    if (!o.count(strKey))
        return 0;
    return ParseHashUV(o[strKey], strKey);
}

vector<unsigned char> ParseHexUO(map<string,UniValue>& o, string strKey)
{
    if (!o.count(strKey)) {
        vector<unsigned char> emptyVec;
        return emptyVec;
    }
    return ParseHexUV(o[strKey], strKey);
}

static void MutateTxSign(CMutableTransaction& tx, const string& flagStr)
{
    int nHashType = SIGHASH_ALL;

    if (flagStr.size() > 0)
        if (!findSighashFlags(nHashType, flagStr))
            throw runtime_error("unknown sighash flag/sign option");

    vector<CTransaction> txVariants;
    txVariants.push_back(tx);

    // mergedTx will end up with all the signatures; it
    // starts as a clone of the raw tx:
    CMutableTransaction mergedTx(txVariants[0]);
    bool fComplete = true;
    CCoinsView viewDummy;
    CCoinsViewCache view(&viewDummy);

    if (!registers.count("privatekeys"))
        throw runtime_error("privatekeys register variable must be set.");
    bool fGivenKeys = false;
    CBasicKeyStore tempKeystore;
    UniValue keysObj = registers["privatekeys"];
    fGivenKeys = true;

    for (unsigned int kidx = 0; kidx < keysObj.count(); kidx++) {
        if (!keysObj[kidx].isStr())
            throw runtime_error("privatekey not a string");
        CBitcoinSecret vchSecret;
        bool fGood = vchSecret.SetString(keysObj[kidx].getValStr());
        if (!fGood)
            throw runtime_error("privatekey not valid");

        CKey key = vchSecret.GetKey();
        tempKeystore.AddKey(key);
    }

    // Add previous txouts given in the RPC call:
    if (!registers.count("prevtxs"))
        throw runtime_error("prevtxs register variable must be set.");
    UniValue prevtxsObj = registers["prevtxs"];
    {
        for (unsigned int previdx = 0; previdx < prevtxsObj.count(); previdx++) {
            UniValue prevOut = prevtxsObj[previdx];
            if (!prevOut.isObject())
                throw runtime_error("expected prevtxs internal object");

            map<string,UniValue::VType> types = map_list_of("txid", UniValue::VSTR)("vout",UniValue::VNUM)("value",UniValue::VSTR)("scriptPubKey",UniValue::VSTR);
            if (!prevOut.checkObject(types))
                throw runtime_error("prevtxs internal object typecheck fail");

            uint256 txid = ParseHashUV(prevOut["txid"], "txid");

            int nOut = atoi(prevOut["vout"].getValStr());
            if (nOut < 0)
                throw runtime_error("vout must be positive");

            CTxOutValue value(ParseHexUV(prevOut["value"], "value"), std::vector<unsigned char>());

            vector<unsigned char> pkData(ParseHexUV(prevOut["scriptPubKey"], "scriptPubKey"));
            CScript scriptPubKey(pkData.begin(), pkData.end());

            {
                CCoinsModifier coins = view.ModifyCoins(txid);
                if (coins->IsAvailable(nOut) && coins->vout[nOut].scriptPubKey != scriptPubKey) {
                    string err("Previous output scriptPubKey mismatch:\n");
                    err = err + coins->vout[nOut].scriptPubKey.ToString() + "\nvs:\n"+
                        scriptPubKey.ToString();
                    throw runtime_error(err);
                }
                if ((unsigned int)nOut >= coins->vout.size())
                    coins->vout.resize(nOut+1);
                coins->vout[nOut].scriptPubKey = scriptPubKey;
                coins->vout[nOut].nValue = value;
            }

            // if redeemScript given and private keys given,
            // add redeemScript to the tempKeystore so it can be signed:
            if (fGivenKeys && scriptPubKey.IsPayToScriptHash() &&
                prevOut.exists("redeemScript")) {
                UniValue v = prevOut["redeemScript"];
                vector<unsigned char> rsData(ParseHexUV(v, "redeemScript"));
                CScript redeemScript(rsData.begin(), rsData.end());
                tempKeystore.AddCScript(redeemScript);
            }
        }
    }

    const CKeyStore& keystore = tempKeystore;

    bool fHashSingle = ((nHashType & ~SIGHASH_ANYONECANPAY) == SIGHASH_SINGLE);

    // Sign what we can:
    for (unsigned int i = 0; i < mergedTx.vin.size(); i++) {
        CTxIn& txin = mergedTx.vin[i];
        const CCoins* coins = view.AccessCoins(txin.prevout.hash);
        if (!coins || !coins->IsAvailable(txin.prevout.n)) {
            fComplete = false;
            continue;
        }
        const CScript& prevPubKey = coins->vout[txin.prevout.n].scriptPubKey;

        txin.scriptSig.clear();
        // Only sign SIGHASH_SINGLE if there's a corresponding output:
        if (!fHashSingle || (i < mergedTx.vout.size()))
            SignSignature(keystore, prevPubKey, coins->vout[txin.prevout.n].nValue, mergedTx, i, nHashType);

        // ... and merge in other signatures:
        BOOST_FOREACH(const CTransaction& txv, txVariants) {
            txin.scriptSig = CombineSignatures(prevPubKey, mergedTx, i, coins->vout[txin.prevout.n].nValue, txin.scriptSig, txv.vin[i].scriptSig);
        }
        if (!VerifyScript(txin.scriptSig, prevPubKey, STANDARD_SCRIPT_VERIFY_FLAGS, MutableTransactionNoWithdrawsSignatureChecker(&mergedTx, i, coins->vout[txin.prevout.n].nValue)))
            fComplete = false;
    }

    if (fComplete) {
        // do nothing... for now
        // perhaps store this for later optional JSON output
    }

    tx = mergedTx;
}

static CScript GetScriptFromValue(const UniValue& v, const string& name)
{
    if (v.isObject() && v[name].isStr()) {
        string str = v[name].getValStr();
        try {
            return ParseScript(str);
        } catch (std::exception& e) {}
    }
    throw runtime_error(name+" must be a script");
}

static void MutateTxWithdrawSign(CMutableTransaction& tx, const string& flagStr)
{
    if (!registers.count("withdrawkeys"))
        throw runtime_error("withdrawkeys register variable must be set.");
    UniValue keysObj = registers["withdrawkeys"];

    if (!keysObj.isObject())
        throw runtime_error("withdrawkeysObjs must be an object");
    map<string,UniValue::VType> types = map_list_of("contract",UniValue::VSTR)("txoutproof",UniValue::VSTR)("tx",UniValue::VSTR)("nout",UniValue::VNUM)
                                                   ("secondScriptSig",UniValue::VSTR)("secondScriptPubKey",UniValue::VSTR)("coinbase",UniValue::VSTR);
    if (!keysObj.checkObject(types))
        throw runtime_error("withdrawkeysObjs internal object typecheck fail");

    vector<unsigned char> contractData(ParseHexUV(keysObj["contract"], "contract"));
    vector<unsigned char> txoutproofData(ParseHexUV(keysObj["txoutproof"], "txoutproof"));
    vector<unsigned char> txData(ParseHexUV(keysObj["tx"], "tx"));
    vector<unsigned char> coinbaseTxData(ParseHexUV(keysObj["coinbase"], "coinbase"));
    CScript secondScriptSig(GetScriptFromValue(keysObj, "secondScriptSig"));
    CScript secondScriptPubKey(GetScriptFromValue(keysObj, "secondScriptPubKey"));
    int nOut = atoi(keysObj["nout"].getValStr());

    if (contractData.size() != 40)
        throw runtime_error("contract must be 40 bytes");

    CDataStream ssProof(txoutproofData, SER_NETWORK, PROTOCOL_VERSION);
    CMerkleBlock merkleBlock;
    merkleBlock.header.SetBitcoinBlock();
    ssProof >> merkleBlock;

    CDataStream ssTx(txData, SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_VERSION_MASK_BITCOIN_TX);
    CTransaction txBTC;
    ssTx >> txBTC;

    CDataStream ssCoinbaseTx(coinbaseTxData, SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_VERSION_MASK_BITCOIN_TX);
    CTransaction coinbaseTxBTC;
    ssCoinbaseTx >> coinbaseTxBTC;

    vector<uint256> transactionHashes;
    if (merkleBlock.txn.ExtractMatches(transactionHashes) != merkleBlock.header.hashMerkleRoot ||
            transactionHashes.size() != 2 ||
            transactionHashes[0] != coinbaseTxBTC.GetBitcoinHash() ||
            transactionHashes[1] != txBTC.GetBitcoinHash())
        throw runtime_error("txoutproof is invalid or did not match tx");

    if (nOut < 0 || (unsigned int) nOut >= txBTC.vout.size())
        throw runtime_error("nout must be >= 0, < txout count");

    CScript scriptSig;
    scriptSig << vector<unsigned char>(secondScriptPubKey.begin(), secondScriptPubKey.end()) << vector<unsigned char>(secondScriptSig.begin(), secondScriptSig.end()) << contractData;
    scriptSig.PushWithdraw(txoutproofData);
    scriptSig.PushWithdraw(txData);
    scriptSig << nOut;
    scriptSig.PushWithdraw(coinbaseTxData);

    //TODO: Verify the withdraw proof
    for (unsigned int i = 0; i < tx.vin.size(); i++) {
        tx.vin[i].scriptSig = scriptSig;
    }
}

static void MutateTxAssetDefinition(CMutableTransaction& tx)
{
    if (tx.vin.size() > 0)
        throw runtime_error("Asset definition transaction already has inputs");

    tx.vin.resize(1);
    tx.vin[0].prevout.SetNull();
    tx.vin[0].scriptSig = CScript();
}

class Secp256k1Init
{
public:
    Secp256k1Init() { ECC_Start(); ECC_Blinding_Start(); }
    ~Secp256k1Init() { ECC_Stop(); ECC_Blinding_Stop(); }
};

static void MutateTx(CMutableTransaction& tx, const string& command,
                     const string& commandVal)
{
    boost::scoped_ptr<Secp256k1Init> ecc;

    if (command == "nversion")
        MutateTxVersion(tx, commandVal);
    else if (command == "locktime")
        MutateTxLocktime(tx, commandVal);

    else if (command == "delin")
        MutateTxDelInput(tx, commandVal);
    else if (command == "in")
        MutateTxAddInput(tx, commandVal);

    else if (command == "delout")
        MutateTxDelOutput(tx, commandVal);
    else if (command == "outaddr")
        MutateTxAddOutAddr(tx, commandVal);
    else if (command == "outscript")
        MutateTxAddOutScript(tx, commandVal);

    else if (command == "sign") {
        if (!ecc) { ecc.reset(new Secp256k1Init()); }
        MutateTxSign(tx, commandVal);
    } else if (command == "blind") {
        if (!ecc) { ecc.reset(new Secp256k1Init()); }
        MutateTxBlind(tx, commandVal);
    } else if (command == "withdrawsign")
        MutateTxWithdrawSign(tx, commandVal);
    else if (command == "newasset")
        MutateTxAssetDefinition(tx);

    else if (command == "load")
        RegisterLoad(commandVal);

    else if (command == "set")
        RegisterSet(commandVal);

    else
        throw runtime_error("unknown command");
}

static void OutputTxJSON(const CTransaction& tx)
{
    UniValue entry(UniValue::VOBJ);
    TxToUniv(tx, 0, entry);

    string jsonOutput = entry.write(4);
    fprintf(stdout, "%s\n", jsonOutput.c_str());
}

static void OutputTxHash(const CTransaction& tx)
{
    string strHexHash = tx.GetHash().GetHex(); // the hex-encoded transaction hash (aka the transaction id)

    fprintf(stdout, "%s\n", strHexHash.c_str());
}

static void OutputTxHex(const CTransaction& tx)
{
    string strHex = EncodeHexTx(tx);

    fprintf(stdout, "%s\n", strHex.c_str());
}

static void OutputTx(const CTransaction& tx)
{
    if (GetBoolArg("-json", false))
        OutputTxJSON(tx);
    else if (GetBoolArg("-txid", false))
        OutputTxHash(tx);
    else
        OutputTxHex(tx);
}

static string readStdin()
{
    char buf[4096];
    string ret;

    while (!feof(stdin)) {
        size_t bread = fread(buf, 1, sizeof(buf), stdin);
        ret.append(buf, bread);
        if (bread < sizeof(buf))
            break;
    }

    if (ferror(stdin))
        throw runtime_error("error reading stdin");

    boost::algorithm::trim_right(ret);

    return ret;
}

static int CommandLineRawTx(int argc, char* argv[])
{
    string strPrint;
    int nRet = 0;
    try {
        // Skip switches; Permit common stdin convention "-"
        while (argc > 1 && IsSwitchChar(argv[1][0]) &&
               (argv[1][1] != 0)) {
            argc--;
            argv++;
        }

        CTransaction txDecodeTmp;
        int startArg;

        if (!fCreateBlank) {
            // require at least one param
            if (argc < 2)
                throw runtime_error("too few parameters");

            // param: hex-encoded bitcoin transaction
            string strHexTx(argv[1]);
            if (strHexTx == "-")                 // "-" implies standard input
                strHexTx = readStdin();

            if (!DecodeHexTx(txDecodeTmp, strHexTx))
                throw runtime_error("invalid transaction encoding");

            startArg = 2;
        } else
            startArg = 1;

        CMutableTransaction tx(txDecodeTmp);

        for (int i = startArg; i < argc; i++) {
            string arg = argv[i];
            string key, value;
            size_t eqpos = arg.find('=');
            if (eqpos == string::npos)
                key = arg;
            else {
                key = arg.substr(0, eqpos);
                value = arg.substr(eqpos + 1);
            }

            MutateTx(tx, key, value);
        }

        OutputTx(tx);
    }

    catch (boost::thread_interrupted) {
        throw;
    }
    catch (std::exception& e) {
        strPrint = string("error: ") + e.what();
        nRet = EXIT_FAILURE;
    }
    catch (...) {
        PrintExceptionContinue(NULL, "CommandLineRawTx()");
        throw;
    }

    if (strPrint != "") {
        fprintf((nRet == 0 ? stdout : stderr), "%s\n", strPrint.c_str());
    }
    return nRet;
}

int main(int argc, char* argv[])
{
    SetupEnvironment();

    try {
        if(!AppInitRawTx(argc, argv))
            return EXIT_FAILURE;
    }
    catch (std::exception& e) {
        PrintExceptionContinue(&e, "AppInitRawTx()");
        return EXIT_FAILURE;
    } catch (...) {
        PrintExceptionContinue(NULL, "AppInitRawTx()");
        return EXIT_FAILURE;
    }

    int ret = EXIT_FAILURE;
    try {
        ret = CommandLineRawTx(argc, argv);
    }
    catch (std::exception& e) {
        PrintExceptionContinue(&e, "CommandLineRawTx()");
    } catch (...) {
        PrintExceptionContinue(NULL, "CommandLineRawTx()");
    }
    return ret;
}
