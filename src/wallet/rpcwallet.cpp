// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "core_io.h"
#include "amount.h"
#include "assetsdir.h"
#include "base58.h"
#include "callrpc.h"
#include "chain.h"
#include "consensus/validation.h"
#include "core_io.h"
#include "consensus/validation.h"
#include "crypto/hmac_sha256.h"
#include "global/common.h"
#include "init.h"
#include "validation.h"
#include "issuance.h"
#include "net.h"
#include "policy/policy.h"
#include "policy/rbf.h"
#include "policy/kycfile.h"
#include "primitives/bitcoin/merkleblock.h"
#include "primitives/bitcoin/transaction.h"
#include "rpc/server.h"
#include "script/sign.h"
#include "script/standard.h"
#include "script/registeraddressscript.h"
#include "random.h"
#include "timedata.h"
#include "util.h"
#include "utilmoneystr.h"
#include "wallet.h"
#include "walletdb.h"
#include "merkleblock.h"
#include "chainparams.h"
#include "coincontrol.h"
#include <secp256k1.h>
#include "ethaddress.h"

#include <stdint.h>

#include <boost/assign/list_of.hpp>

using namespace std;

int64_t nWalletUnlockTime;
static CCriticalSection cs_nWalletUnlockTime;

/**
 * Returns asset id corresponding to the given asset expression, which is either an asset label or a hex value.
 * @param  strasset A label string or a hex value corresponding to an asset
 * @return       The asset ID for the given expression
 */
static CAsset GetAssetFromString(const std::string& strasset)
{
    CAsset asset = gAssetsDir.GetAsset(strasset);
    if (asset.IsNull() && strasset.size() == 64 && IsHex(strasset)) {
        asset = CAsset(uint256S(strasset));
    }
    if (asset.IsNull()) {
        throw JSONRPCError(RPC_WALLET_ERROR, strprintf("Unknown label and invalid asset hex: %s", strasset.c_str()));
    }
    return asset;
}

std::string HelpRequiringPassphrase()
{
    return pwalletMain && pwalletMain->IsCrypted()
        ? "\nRequires wallet passphrase to be set with walletpassphrase call."
        : "";
}

bool EnsureWalletIsAvailable(bool avoidException)
{
    if (!pwalletMain)
    {
        if (!avoidException)
            throw JSONRPCError(RPC_METHOD_NOT_FOUND, "Method not found (disabled)");
        else
            return false;
    }
    return true;
}

void EnsureWalletIsUnlocked()
{
    if (pwalletMain->IsLocked())
        throw JSONRPCError(RPC_WALLET_UNLOCK_NEEDED, "Error: Please enter the wallet passphrase with walletpassphrase first.");
}

// Attaches labeled balance reports to UniValue obj with asset filter
// "" displays *all* assets as VOBJ pairs, while named assets must have
// been entered via -assetdir configuration argument and are returned as VNUM.
UniValue PushAssetBalance(CAmountMap& balance, CWallet* wallet, std::string strasset)
{
    UniValue obj(UniValue::VOBJ);
    if (strasset == "") {
        for(std::map<CAsset, CAmount>::const_iterator it = balance.begin(); it != balance.end(); ++it) {
            // Unknown assets
            if (it->first.IsNull())
                continue;
            UniValue pair(UniValue::VOBJ);
            const std::string label = gAssetsDir.GetLabel(it->first);
            if (label != "") {
                obj.push_back(Pair(label, ValueFromAmount(it->second)));
            } else {
                obj.push_back(Pair(it->first.GetHex(), ValueFromAmount(it->second)));
            }
        }
    } else {
        CAsset asset = GetAssetFromString(strasset);
        return ValueFromAmount(balance[asset]);
    }
    return obj;
}

void WalletTxToJSON(const CWalletTx& wtx, UniValue& entry)
{
    int confirms = wtx.GetDepthInMainChain();
    entry.push_back(Pair("confirmations", confirms));
    if (wtx.IsCoinBase())
        entry.push_back(Pair("generated", true));
    if (confirms > 0)
    {
        entry.push_back(Pair("blockhash", wtx.hashBlock.GetHex()));
        entry.push_back(Pair("blockindex", wtx.nIndex));
        entry.push_back(Pair("blocktime", mapBlockIndex[wtx.hashBlock]->GetBlockTime()));
    } else {
        entry.push_back(Pair("trusted", wtx.IsTrusted()));
    }
    uint256 hash = wtx.GetHash();
    entry.push_back(Pair("txid", hash.GetHex()));
    UniValue conflicts(UniValue::VARR);
    BOOST_FOREACH(const uint256& conflict, wtx.GetConflicts())
        conflicts.push_back(conflict.GetHex());
    entry.push_back(Pair("walletconflicts", conflicts));
    entry.push_back(Pair("time", wtx.GetTxTime()));
    entry.push_back(Pair("timereceived", (int64_t)wtx.nTimeReceived));

    // Add opt-in RBF status
    std::string rbfStatus = "no";
    if (confirms <= 0) {
        LOCK(mempool.cs);
        RBFTransactionState rbfState = IsRBFOptIn(wtx, mempool);
        if (rbfState == RBF_TRANSACTIONSTATE_UNKNOWN)
            rbfStatus = "unknown";
        else if (rbfState == RBF_TRANSACTIONSTATE_REPLACEABLE_BIP125)
            rbfStatus = "yes";
    }
    entry.push_back(Pair("bip125-replaceable", rbfStatus));

    // Push transaction comments
    entry.push_back(Pair("comment", wtx.mapValue["comment"]));
    entry.push_back(Pair("to", wtx.mapValue["to"]));

}

string AccountFromValue(const UniValue& value)
{
    string strAccount = value.get_str();
    if (strAccount == "*")
        throw JSONRPCError(RPC_WALLET_INVALID_ACCOUNT_NAME, "Invalid account name");
    return strAccount;
}

UniValue getethaddress(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "getethaddress key\n"
            "1. key         (hex, required) Eth private key\n"
            "\nReturns an eth address from an eth private key.\n"
            "\nResult:\n"
            "\"address\"    (string) The eth address\n"
            "\nExamples:\n"
            + HelpExampleCli("getethaddress", "3ecb44df2159c26e0f995712d4f39b6f6e499b40749b1cf1246c37f9516cb6a4")
            + HelpExampleRpc("getethaddress", "3ecb44df2159c26e0f995712d4f39b6f6e499b40749b1cf1246c37f9516cb6a4")
        );

    std::vector<unsigned char> keyBytes = ParseHex(request.params[0].get_str());
    CKey key;
    key.Set(keyBytes.begin(), keyBytes.end(), false);
    if (!key.IsValid()) throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Private key outside allowed range");

    CPubKey pubkey = key.GetPubKey();
    CEthAddress addr = CEthAddress(pubkey);
    if (addr.IsValid()) {
        return addr.ToString();
    }
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Eth address invalid or key pubkey compressed");
}

UniValue getnewaddress(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() > 1)
        throw runtime_error(
            "getnewaddress ( \"account\" )\n"
            "\nReturns a new Bitcoin address for receiving payments.\n"
            "If 'account' is specified (DEPRECATED), it is added to the address book \n"
            "so payments received with the address will be credited to 'account'.\n"
            "\nArguments:\n"
            "1. \"account\"        (string, optional) DEPRECATED. The account name for the address to be linked to. If not provided, the default account \"\" is used. It can also be set to the empty string \"\" to represent the default account. The account does not need to exist, it will be created if there is no account by the given name.\n"
            "\nResult:\n"
            "\"address\"    (string) The new bitcoin address\n"
            "\nExamples:\n"
            + HelpExampleCli("getnewaddress", "")
            + HelpExampleRpc("getnewaddress", "")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    // Parse the account first so we don't generate a key if there's an error
    string strAccount;
    if (request.params.size() > 0)
        strAccount = AccountFromValue(request.params[0]);

    if (!pwalletMain->IsLocked())
        pwalletMain->TopUpKeyPool();

    // Generate a new key that is added to wallet
    CPubKey newKey;
    if (!pwalletMain->GetKeyFromPool(newKey))
        throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, "Error: Keypool ran out, please call keypoolrefill first");
    CKeyID keyID = newKey.GetID();

    pwalletMain->SetAddressBook(keyID, strAccount, "receive");

    return !pwalletMain->GetDisableCt() ?
        CBitcoinAddress(keyID).AddBlindingKey(pwalletMain->GetBlindingPubKey(GetScriptForDestination(CTxDestination(keyID)))).ToString() :
        CBitcoinAddress(keyID).ToString();
}

UniValue getkycpubkey(const JSONRPCRequest& request){
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() > 1)
        throw runtime_error(
            "getkycpubkey ( \"address\" )\n"
            "\nReturns the kyc public key associated with this wallet, or an address if supplied.\n"
            "\nArguments:\n"
            "1. \"address\"        (string, optional) The address to look up the KYC public key for.\n"
            "\nResult:\n"
            "\"kycpubkey\"    (string) The KYC public key.\n"
            "\nExamples:\n"
            + HelpExampleCli("getkycpubkey", "2dxig5syTVt6SvMjjBFJVGdSj4o8TVsixYK")
            + HelpExampleRpc("getkycpubkey", "2dxig5syTVt6SvMjjBFJVGdSj4o8TVsixYK")
        );

    if(!fWhitelistEncrypt)
        throw JSONRPCError(RPC_MISC_ERROR,
            "Not implemented for unencrypted whitelist");

    LOCK2(cs_main, pwalletMain->cs_wallet);

    CPubKey kycPubKey;

    if(request.params.size()==0){
        kycPubKey=pwalletMain->GetKYCPubKey();
        if(kycPubKey == CPubKey())
            throw JSONRPCError(RPC_WALLET_ERROR, "KYC public key not found");
        UniValue ret(HexStr(kycPubKey.begin(), kycPubKey.end()));
        return ret;
    }

    CBitcoinAddress address(request.params[0].get_str());
    if (!address.IsValid())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid Bitcoin address");

    CTxDestination addr = address.Get();
    if(addr.which() == ((CTxDestination)CNoDestination()).which())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Could not get key ID from Bitcoin address");

    if(!addressWhitelist->LookupKYCKey(addr, kycPubKey))
        throw JSONRPCError(RPC_INVALID_PARAMETER, "KYC public key not found");

    UniValue ret(HexStr(kycPubKey.begin(), kycPubKey.end()));

    return ret;
}

UniValue getavailablekycpubkeys(const JSONRPCRequest& request){
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 0)
        throw runtime_error(
            "getavailablekycpubkeys ( \"address\" )\n"
            "\nReturns the pubkeys available for kycfile encryption.\n"
            "\nArguments: none\n"
             "\nResult:\n"
            "[                     (json array of string)\n"
            "  \"kycpubkey\"         (string) an available kycpbukey\n"
            "  ,...\n"
            "]\n"
            "\nExamples:\n"
            + HelpExampleCli("getavailablekycpubkeys", "\"test\"")
            + HelpExampleRpc("getpavailablekycpubkeys", "\"test\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    CPubKey kycPubKey;

    if(request.params.size()==0){
        kycPubKey=pwalletMain->GetKYCPubKey();
        if(kycPubKey == CPubKey())
            throw JSONRPCError(RPC_WALLET_ERROR, "KYC public key not found");
        UniValue ret(HexStr(kycPubKey.begin(), kycPubKey.end()));
        return ret;
    }

    CBitcoinAddress address(request.params[0].get_str());
    if (!address.IsValid())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid Bitcoin address");

    CTxDestination addr = address.Get();
    if(addr.which() == ((CTxDestination)CNoDestination()).which())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Could not get key ID from Bitcoin address");

    if(!addressWhitelist->LookupKYCKey(addr, kycPubKey))
        throw JSONRPCError(RPC_INVALID_PARAMETER, "KYC public key not found");

    UniValue ret(HexStr(kycPubKey.begin(), kycPubKey.end()));

    return ret;
}

CBitcoinAddress GetAccountAddress(string strAccount, bool bForceNew=false)
{
    CPubKey pubKey;
    if (!pwalletMain->GetAccountPubkey(pubKey, strAccount, bForceNew)) {
        throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, "Error: Keypool ran out, please call keypoolrefill first");
    }

    return !pwalletMain->GetDisableCt() ?
        CBitcoinAddress(pubKey.GetID()).AddBlindingKey(pwalletMain->GetBlindingPubKey(GetScriptForDestination(pubKey.GetID()))).ToString() :
        CBitcoinAddress(pubKey.GetID()).ToString();
}

UniValue getaccountaddress(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "getaccountaddress \"account\"\n"
            "\nDEPRECATED. Returns the current Bitcoin address for receiving payments to this account.\n"
            "\nArguments:\n"
            "1. \"account\"       (string, required) The account name for the address. It can also be set to the empty string \"\" to represent the default account. The account does not need to exist, it will be created and a new address created  if there is no account by the given name.\n"
            "\nResult:\n"
            "\"address\"          (string) The account bitcoin address\n"
            "\nExamples:\n"
            + HelpExampleCli("getaccountaddress", "")
            + HelpExampleCli("getaccountaddress", "\"\"")
            + HelpExampleCli("getaccountaddress", "\"myaccount\"")
            + HelpExampleRpc("getaccountaddress", "\"myaccount\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    // Parse the account first so we don't generate a key if there's an error
    string strAccount = AccountFromValue(request.params[0]);

    UniValue ret(UniValue::VSTR);

    ret = GetAccountAddress(strAccount).ToString();
    return ret;
}


UniValue getrawchangeaddress(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() > 1)
        throw runtime_error(
            "getrawchangeaddress\n"
            "\nReturns a new Bitcoin address, for receiving change.\n"
            "This is for use with raw transactions, NOT normal use.\n"
            "\nResult:\n"
            "\"address\"    (string) The address\n"
            "\nExamples:\n"
            + HelpExampleCli("getrawchangeaddress", "")
            + HelpExampleRpc("getrawchangeaddress", "")
       );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    if (!pwalletMain->IsLocked())
        pwalletMain->TopUpKeyPool();

    CReserveKey reservekey(pwalletMain);
    CPubKey vchPubKey;
    if (!reservekey.GetReservedKey(vchPubKey))
        throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, "Error: Keypool ran out, please call keypoolrefill first");

    reservekey.KeepKey();

    CKeyID keyID = vchPubKey.GetID();

    return !pwalletMain->GetDisableCt() ?
        CBitcoinAddress(keyID).AddBlindingKey(pwalletMain->GetBlindingPubKey(GetScriptForDestination(CTxDestination(keyID)))).ToString() :
        CBitcoinAddress(keyID).ToString();
}


UniValue setaccount(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 1 || request.params.size() > 2)
        throw runtime_error(
            "setaccount \"address\" \"account\"\n"
            "\nDEPRECATED. Sets the account associated with the given address.\n"
            "\nArguments:\n"
            "1. \"address\"         (string, required) The bitcoin address to be associated with an account.\n"
            "2. \"account\"         (string, required) The account to assign the address to.\n"
            "\nExamples:\n"
            + HelpExampleCli("setaccount", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\" \"tabby\"")
            + HelpExampleRpc("setaccount", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\", \"tabby\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    CBitcoinAddress address(request.params[0].get_str());
    if (!address.IsValid())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid Bitcoin address");

    string strAccount;
    if (request.params.size() > 1)
        strAccount = AccountFromValue(request.params[1]);

    // Only add the account if the address is yours.
    if (IsMine(*pwalletMain, address.Get()))
    {
        // Detect when changing the account of an address that is the 'unused current key' of another account:
        if (pwalletMain->mapAddressBook.count(address.Get()))
        {
            string strOldAccount = pwalletMain->mapAddressBook[address.Get()].name;
            if (address == GetAccountAddress(strOldAccount))
                GetAccountAddress(strOldAccount, true);
        }
        pwalletMain->SetAddressBook(address.Get(), strAccount, "receive");
    }
    else
        throw JSONRPCError(RPC_MISC_ERROR, "setaccount can only be used with own address");

    return NullUniValue;
}


UniValue getaccount(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "getaccount \"address\"\n"
            "\nDEPRECATED. Returns the account associated with the given address.\n"
            "\nArguments:\n"
            "1. \"address\"         (string, required) The bitcoin address for account lookup.\n"
            "\nResult:\n"
            "\"accountname\"        (string) the account address\n"
            "\nExamples:\n"
            + HelpExampleCli("getaccount", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\"")
            + HelpExampleRpc("getaccount", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    CBitcoinAddress address(request.params[0].get_str());
    if (!address.IsValid())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid Bitcoin address");

    string strAccount;
    map<CTxDestination, CAddressBookData>::iterator mi = pwalletMain->mapAddressBook.find(address.Get());
    if (mi != pwalletMain->mapAddressBook.end() && !(*mi).second.name.empty())
        strAccount = (*mi).second.name;
    return strAccount;
}


UniValue getaddressesbyaccount(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "getaddressesbyaccount \"account\"\n"
            "\nDEPRECATED. Returns the list of addresses for the given account.\n"
            "\nArguments:\n"
            "1. \"account\"        (string, required) The account name.\n"
            "\nResult:\n"
            "[                     (json array of string)\n"
            "  \"address\"         (string) a bitcoin address associated with the given account\n"
            "  ,...\n"
            "]\n"
            "\nExamples:\n"
            + HelpExampleCli("getaddressesbyaccount", "\"tabby\"")
            + HelpExampleRpc("getaddressesbyaccount", "\"tabby\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    string strAccount = AccountFromValue(request.params[0]);

    // Find all addresses that have the given account
    UniValue ret(UniValue::VARR);
    BOOST_FOREACH(const PAIRTYPE(CTxDestination, CAddressBookData)& item, pwalletMain->mapAddressBook)
    {
        CBitcoinAddress address = item.first;
        if (!pwalletMain->GetDisableCt())
        {
            address.AddBlindingKey(pwalletMain->GetBlindingPubKey(GetScriptForDestination(item.first)));
        }
        const string& strName = item.second.name;
        if (strName == strAccount)
            ret.push_back(address.ToString());
    }
    return ret;
}

static vector<CWalletTx> SendMoney(const CScript& scriptPubKey, CAmount nValue, CAsset asset, bool fSubtractFeeFromAmount,
    const CPubKey &confidentiality_key, CWalletTx& wtxNew, bool fIgnoreBlindFail, bool fSplitTransactions = false,
    CCoinControl* coinControl = NULL)
{
    CAmount curBalance = pwalletMain->GetBalance()[asset];

    // Check amount
    if (nValue < 0)
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid amount");

    if (nValue > curBalance)
        throw JSONRPCError(RPC_WALLET_INSUFFICIENT_FUNDS, "Insufficient funds");

    if (pwalletMain->GetBroadcastTransactions() && !g_connman)
        throw JSONRPCError(RPC_CLIENT_P2P_DISABLED, "Error: Peer-to-peer functionality missing or disabled");

    std::vector<std::vector<CReserveKey>> vChangeKeys;
    // Create and send the transaction
    std::vector<CReserveKey> vChangeKey;
    vChangeKey.reserve(2);
    vChangeKey.emplace_back(pwalletMain);
    if (policyAsset != asset) {
        vChangeKey.emplace_back(pwalletMain);
    }
    vChangeKeys.push_back(vChangeKey);

    CAmount nFeeRequired;
    std::string strError;
    vector<CRecipient> vecSend;
    int nChangePosRet = -1;
    CRecipient recipient = {scriptPubKey, nValue, asset, confidentiality_key, fSubtractFeeFromAmount};
    vecSend.push_back(recipient);

    std::vector<CWalletTx> vecRes = pwalletMain->CreateTransaction(vecSend, wtxNew, vChangeKeys, nFeeRequired, nChangePosRet,
        strError, coinControl, true, NULL, true, NULL, NULL, NULL, CAsset(), fIgnoreBlindFail, fSplitTransactions);

    if (!(vecRes.size() > 0)) {
        if (!fSubtractFeeFromAmount && nValue + nFeeRequired > curBalance)
            strError = strprintf("Error: This transaction requires a transaction fee of at least %s", FormatMoney(nFeeRequired));
        throw JSONRPCError(RPC_WALLET_ERROR, strError);
    }
    wtxNew = vecRes[0];
    for (unsigned int i = 0; i < vecRes.size(); ++i) {
        CValidationState state;
        if (!pwalletMain->CommitTransaction(vecRes[i], vChangeKeys[0], g_connman.get(), state)) {
            strError = strprintf("Error: The transaction was rejected! Reason given: %s %s", state.GetRejectReason(), state.GetDebugMessage());
            throw JSONRPCError(RPC_WALLET_ERROR, strError);
        }
    }
    return vecRes;
}

static vector<CWalletTx> SendMoney(const CTxDestination &address, CAmount nValue, CAsset asset, bool fSubtractFeeFromAmount,
    const CPubKey &confidentiality_key, CWalletTx& wtxNew, bool fIgnoreBlindFail, bool fSplitTransactions, CCoinControl* coinControl = NULL)
{
    return SendMoney(GetScriptForDestination(address), nValue, asset, fSubtractFeeFromAmount, confidentiality_key, wtxNew,
        fIgnoreBlindFail, fSplitTransactions, coinControl);
}

static vector<CWalletTx> SendAnyMoney(const CScript& scriptPubKey, CAmount nValue, const CPubKey &confidentiality_key, CWalletTx& wtxNew,
    bool fIgnoreBlindFail, bool fSplitTransactions = false, int nSortingMethod = 1, CCoinControl* coinControl = NULL)
{
    // Check amount
    if (nValue < 0)
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid amount");

    if (pwalletMain->GetBroadcastTransactions() && !g_connman)
        throw JSONRPCError(RPC_CLIENT_P2P_DISABLED, "Error: Peer-to-peer functionality missing or disabled");

    CAmountMap balanceMap = pwalletMain->GetBalance();
    std::vector<std::pair<CAsset, CAmount>> vecBalanceMap =
        std::vector<std::pair<CAsset, CAmount>>(balanceMap.begin(), balanceMap.end());

    // Default 0 unsorted, 1 descending, 2 ascending
    typedef std::function<bool(std::pair<CAsset, CAmount>, std::pair<CAsset, CAmount>)> Comparator;
    if (nSortingMethod == 1) {
        Comparator compFunc =
            [](std::pair<CAsset, CAmount> left, std::pair<CAsset, CAmount> right) {
                return left.second > right.second;
            };
        std::sort(vecBalanceMap.begin(), vecBalanceMap.end(), compFunc);
    } else if (nSortingMethod == 2) {
        Comparator compFunc =
            [](std::pair<CAsset, CAmount> left, std::pair<CAsset, CAmount> right) {
                return left.second < right.second;
            };
        std::sort(vecBalanceMap.begin(), vecBalanceMap.end(), compFunc);
    }

    CAmount totalBalance = 0;
    for (const auto& it : vecBalanceMap) {
        if (!IsPolicy(it.first)) {
            totalBalance += it.second;
        }
    }
    if (nValue > totalBalance)
        throw JSONRPCError(RPC_WALLET_INSUFFICIENT_FUNDS, "Insufficient funds for sendany");

    // Create and send the transaction
    CAmount nFeeRequired;
    std::string strError;
    int nChangePosRet = -1;

    vector<CRecipient> vecSend;
    CAmount coveredValue = 0;
    bool fOutputsFilled = false;
    for (const auto& it : vecBalanceMap) {
        if (!IsPolicy(it.first)) {
            CTxOut hackDustEstimator = CTxOut(it.first, it.second, CScript());
            if (!hackDustEstimator.IsDust(::minRelayTxFee)) {
                CAmount outputValue = it.second;
                if (nValue <= coveredValue + outputValue) {
                    outputValue = nValue - coveredValue;
                    fOutputsFilled = true;
                }
                CRecipient recipient = {scriptPubKey, outputValue, it.first, confidentiality_key, false};
                vecSend.push_back(recipient);
                coveredValue += outputValue;
                if (fOutputsFilled)
                    break;
            }
        }
    }

    // Create and send the transaction
    std::vector<std::vector<CReserveKey>> vChangeKeys;
    std::vector<CReserveKey> vChangeKey;
    vChangeKey.reserve(vecSend.size() + 1);
    for (unsigned int j = 0; j < vecSend.size() + 1; ++j) {
        vChangeKey.emplace_back(pwalletMain);
    }
    vChangeKeys.push_back(vChangeKey);

    std::vector<CWalletTx> vecRes = pwalletMain->CreateTransaction(vecSend, wtxNew, vChangeKeys, nFeeRequired, nChangePosRet,
        strError, coinControl, true, NULL, true, NULL, NULL, NULL, CAsset(), fIgnoreBlindFail, fSplitTransactions, std::vector<COutput>(), true);
    if (!(vecRes.size() > 0)) {
        if (nValue + nFeeRequired > totalBalance)
            strError = strprintf("Error: This transaction requires a transaction fee of at least %s", FormatMoney(nFeeRequired));
        throw JSONRPCError(RPC_WALLET_ERROR, strError);
    }
    wtxNew = vecRes[0];
    for (unsigned int i = 0; i < vecRes.size(); ++i) {
        CValidationState state;
        if (!pwalletMain->CommitTransaction(vecRes[i], vChangeKeys[i], g_connman.get(), state)) {
            strError = strprintf("Error: The transaction was rejected! Reason given: %s %s", state.GetRejectReason(), state.GetDebugMessage());
            throw JSONRPCError(RPC_WALLET_ERROR, strError);
        }
    }
    return vecRes;
}

static vector<CWalletTx> SendAnyMoney(const CTxDestination &address, CAmount nValue, const CPubKey &confidentiality_key,
    CWalletTx& wtxNew, bool fIgnoreBlindFail, bool fSplitTransactions, int nSortingMethod, CCoinControl* coinControl = NULL)
{
    return SendAnyMoney(GetScriptForDestination(address), nValue, confidentiality_key, wtxNew, fIgnoreBlindFail,
        fSplitTransactions, nSortingMethod, coinControl);
}

static void SendGenerationTransaction(const CScript& assetScriptPubKey, const CPubKey &assetKey, const CScript& tokenScriptPubKey, const CPubKey &tokenKey, CAmount nAmountAsset, CAmount nTokens, bool fBlindIssuances, uint256& entropy, CAsset& reissuanceAsset, CAsset& reissuanceToken, CWalletTx& wtxNew)
{

    CAmount curBalance = pwalletMain->GetBalance()[reissuanceToken];

    if (!reissuanceToken.IsNull() && curBalance <= 0) {
        throw JSONRPCError(RPC_WALLET_INSUFFICIENT_FUNDS, "No available reissuance tokens in wallet.");
    }

    std::vector<std::vector<CReserveKey>> vChangeKeys;
    // Create and send the transaction
    std::vector<CReserveKey> vChangeKey;
    // Need to be careful to not copy CReserveKeys or bad things happen
    // We need 2 change outputs possibly for reissuance case:
    // one for policyAsset, the other for reissuance token
    vChangeKey.reserve(2);
    vChangeKey.emplace_back(pwalletMain);
    if (!reissuanceAsset.IsNull()) {
        vChangeKey.emplace_back(pwalletMain);
    }
    vChangeKeys.push_back(vChangeKey);

    CAmount nFeeRequired;
    std::string strError;
    vector<CRecipient> vecSend;
    int nChangePosRet = -1;
    // Signal outputs to skip "funding" with fixed asset numbers 1, 2, ...
    // We don't know the asset during initial issuance until inputs are chosen
    CRecipient recipient = {assetScriptPubKey, nAmountAsset, CAsset(uint256S("1")), assetKey, false};
    if (assetScriptPubKey.size() > 0) {
        vecSend.push_back(recipient);
    }
    if (tokenScriptPubKey.size() > 0) {
        recipient = {tokenScriptPubKey, nTokens, CAsset(uint256S("2")), tokenKey, false};
        // We need to select the issuance token(s) to spend
        if (!reissuanceToken.IsNull()) {
            recipient.asset = reissuanceToken;
            recipient.nAmount = curBalance; // Or 1?
        }
        vecSend.push_back(recipient);
    }

    std::vector<CWalletTx> vesRes = pwalletMain->CreateTransaction(vecSend, wtxNew, vChangeKeys, nFeeRequired, nChangePosRet, strError, NULL, true, NULL, fBlindIssuances, &entropy, &reissuanceAsset, &reissuanceToken);

    if (!(vesRes.size() > 0)) {
        throw JSONRPCError(RPC_WALLET_ERROR, strError);
    }
    CValidationState state;
    if (!pwalletMain->CommitTransaction(wtxNew, vChangeKeys[0], g_connman.get(), state))
        throw JSONRPCError(RPC_WALLET_ERROR, "Error: The transaction was rejected! This might happen if some of the coins in your wallet were already spent, such as if you used a copy of the wallet and coins were spent in the copy but not marked as spent here.");
}

static void SendOnboardTx(const CScript& script,  CWalletTx& wtxNew){
    if (pwalletMain->GetBroadcastTransactions() && !g_connman)
        throw JSONRPCError(RPC_CLIENT_P2P_DISABLED, "Error: Peer-to-peer functionality missing or disabled");

    CAmount nAmount(0);
    bool fSubtractFeeFromAmount=false, fIgnoreBlindFail=true;
    CPubKey confidentiality_pubkey;


    CCoinControl* coinControl = new CCoinControl();
    //Fee = 0
    coinControl->fOverrideFeeRate=true;
    coinControl->nFeeRate=CFeeRate(0);
    coinControl->fAllowOtherInputs=false;

    int nMinDepth=6;
    int nMaxDepth=9999999;

    vector<COutput> vecOutputs;
    assert(pwalletMain != NULL);
    LOCK2(cs_main, pwalletMain->cs_wallet);
    pwalletMain->AvailableCoins(vecOutputs, true, NULL, true);
    BOOST_FOREACH(const COutput& out, vecOutputs) {
     if ((out.nDepth < nMinDepth) || (out.nDepth > nMaxDepth) |! (out.fSpendable))
            continue;
        CAmount nValue = out.tx->GetOutputValueOut(out.i);
        CAsset assetid = out.tx->GetOutputAsset(out.i);
        if (nValue >= nAmount && assetid == whitelistAsset){
            coinControl->Select(COutPoint(out.tx->GetHash(), out.i));
            const CTxOut& newout = out.tx->tx->vout[out.i];
            std::vector<std::vector<unsigned char> > vSolutions;
            CTxDestination address;
            if (ExtractDestination(newout.scriptPubKey, address)){
                coinControl->destChange=address;
            }
            else{
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Solver failed to retrieve addresses from the output");
            }
            break;
        }
    }

    if(!coinControl->HasSelected()){
         throw JSONRPCError(RPC_INVALID_PARAMETER, "No whitelist asset available");
    }

    SendMoney(script, nAmount, whitelistAsset, fSubtractFeeFromAmount, confidentiality_pubkey, wtxNew, fIgnoreBlindFail, false, coinControl);
}

UniValue onboarduser(const JSONRPCRequest& request){
  if (request.fHelp || request.params.size() != 1)
    throw runtime_error(
            "onboarduser \"filename\" \n"
            "Read in derived keys and tweaked addresses from kyc file (see dumpkycfile) into the address whitelist. Assign a KYC public key to the user if using encrypted whitelist.\n"
            "\nArguments:\n"

            "1. \"filename\"    (string, required) The kyc file name\n"

            "\nExamples:\n"
            + HelpExampleCli("onboarduser", "\"my filename\"")
            + HelpExampleRpc("onboarduser", "\"my filename\"")
            );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    EnsureWalletIsUnlocked();

    CKYCFile file;
    file.read(request.params[0].get_str().c_str());

    CScript script;
    if(!file.getOnboardingScript(script))
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Cannot generate onboarding script");

    CWalletTx wtx;
    SendOnboardTx(script, wtx);
    return wtx.GetHash().GetHex();
}

UniValue blacklistuser(const JSONRPCRequest& request){
  if (request.fHelp || request.params.size() != 1)
    throw runtime_error(
            "blacklistuser \"filename\" \n"
            "Remove addresses in the kyc file from the address whitelist\n"
            "\nArguments:\n"

            "1. \"filename\"    (string, required) The kyc file name\n"

            "\nExamples:\n"
            + HelpExampleCli("blacklistuser", "\"my filename\"")
            + HelpExampleRpc("blacklistuser", "\"my filename\"")
            );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    EnsureWalletIsUnlocked();

    CKYCFile file;
    file.read(request.params[0].get_str().c_str());

    CScript script;
    if(!file.getOnboardingScript(script, true))
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Cannot generate blacklisting script");

    CWalletTx wtx;
    SendOnboardTx(script, wtx);
    return wtx.GetHash().GetHex();
}

static UniValue FinalizeRegisterAddressTx(CRegisterAddressScript* raScript, const CAsset& feeAsset, const CPubKey* pubKey, CWalletTx& wtxNew)
{
    if(fWhitelistEncrypt){
        if(!pubKey)
            throw JSONRPCError(RPC_INVALID_PARAMETER,"KYC pub key is NULL");
    }

    CScript dummyScript;
    raScript->FinalizeUnencrypted(dummyScript);

    // Create a dummy transaction in order to calculate the required fee
    std::vector<std::vector<CReserveKey>> vChangeKeys;
    std::vector<CReserveKey> vChangeKey;
    vChangeKey.reserve(2);
    vChangeKey.emplace_back(pwalletMain);
    vChangeKey.emplace_back(pwalletMain);
    vChangeKeys.push_back(vChangeKey);

    CAmount nFeeRequired = 1;
    std::string strError;
    vector<CRecipient> vecSendDummy;
    int nChangePosRet = -1;
    CRecipient recipientDummy = {dummyScript, CAmount(0), feeAsset, CPubKey(), false};
    vecSendDummy.push_back(recipientDummy);

    CWalletTx wtxDummy;
    std::vector<CWalletTx> vecResDummy = pwalletMain->CreateTransaction(vecSendDummy, wtxDummy, vChangeKeys, nFeeRequired, nChangePosRet,
        strError, NULL, true, NULL, true, NULL, NULL, NULL, CAsset(), true);

    if (!(vecResDummy.size() > 0)) {
        strError = strprintf("Error: failed to create transaction.");
        throw JSONRPCError(RPC_WALLET_ERROR, strError);
    }

    //Now select coins based on the fee required
    assert(pwalletMain != NULL);
    std::vector<COutput> vAvailableCoins;
    pwalletMain->AvailableCoins(vAvailableCoins, true, NULL, true);
    CAmountMap mapValueToSelect, mapValueRet;
    mapValueToSelect[feeAsset] += nFeeRequired;
    std::set<pair<const CWalletTx*,unsigned int> > setCoins;

    if (!pwalletMain->SelectCoins(vAvailableCoins, mapValueToSelect, setCoins, mapValueRet, nullptr, feeAsset))
    {
       strError = strprintf("Error: failed to select coins.");
       throw JSONRPCError(RPC_WALLET_ERROR, strError);
    }

    //Get the bitcoin addresses of the set coins and add the selected coins to a coincontrol list
    std::set<CTxDestination> inputAddrs;
    CTxDestination inputAddr;
    CCoinControl coinControl;
    coinControl.fAllowOtherInputs=false;

    //Create the script using the selected input address to encrypt it
    CKeyID fromKeyID;
    CKey key;

    EnsureWalletIsUnlocked();

    for(auto coin : setCoins) {
        const CWalletTx* pcoin = coin.first;
        unsigned int& icoin=coin.second;
        BOOST_FOREACH(COutput& out, vAvailableCoins){
            if(out.tx == pcoin){
                if((unsigned int)out.i == icoin){
                    const CScript& scriptPubKey = out.tx->tx->vout[out.i].scriptPubKey;
                    if(!ExtractDestination(scriptPubKey, inputAddr)) continue;
                    CBitcoinAddress addr(inputAddr);
                    std::string sAddr = addr.ToString();
                    addr.GetKeyID(fromKeyID);
                    if(!pwalletMain->GetKey(fromKeyID, key)) continue;
                    inputAddrs.insert(inputAddr);
                    COutPoint outPoint(out.tx->GetHash(), out.i);
                    coinControl.Select(outPoint);
                }
            }
        }
    }

    if(inputAddrs.size() == 0)
    {
        throw JSONRPCError(RPC_WALLET_ERROR, "Error: could not retrieve private key for \"fromaddress\" from wallet.");
    }

    CScript script;
    if(fWhitelistEncrypt){
       raScript->Finalize(script, *pubKey, key);
    } else {
       raScript->FinalizeUnencrypted(script);
    }

    vector<CRecipient> vecSend;
    CAmount amount(0);
    CPubKey dummyPubKey;
    CRecipient recipient = {script, amount, feeAsset, dummyPubKey, false};
    vecSend.push_back(recipient);

    CAsset asset;

    std::vector<CWalletTx> vecRes = pwalletMain->CreateTransaction(vecSend, wtxNew, vChangeKeys, nFeeRequired, nChangePosRet,
        strError, &coinControl, true, NULL, true, NULL, NULL, NULL, asset, true);

    //Create the transacrtion again. This time, the script is encrypted.
    if (!(vecRes.size() > 0)) {
        strError = strprintf("Error: failed to create transaction.");
        throw JSONRPCError(RPC_WALLET_ERROR, strError);
    }

    CValidationState state;
    if (!pwalletMain->CommitTransaction(wtxNew, vChangeKeys[0], g_connman.get(), state)) {
        strError = strprintf("Error: The transaction was rejected! Reason given: %s %s", state.GetRejectReason(), state.GetDebugMessage());
        throw JSONRPCError(RPC_WALLET_ERROR, strError);
    }

    return wtxNew.GetHash().GetHex();
}

//Register an P2SH multi address to the
//whitelist via a OP_REGISTERADDRESS transaction.
//Use "asset" to pay the transaction fee.
static void SendAddNextMultiToWhitelistTx(const CAsset& feeAsset, const CPubKey* pubKey,
    const CBitcoinAddress& address, const UniValue& sPubKeys, const uint8_t nMultisig,
    CWalletTx& wtxNew){

    if(fWhitelistEncrypt){
        if(!pubKey)
            throw JSONRPCError(RPC_INVALID_PARAMETER, "KYC pub key is NULL");
        if(!addressWhitelist->find_kyc_whitelisted(pubKey->GetID()))
            throw JSONRPCError(RPC_INVALID_PARAMETER, "KYC public key not whitelisted");
    }

    LOCK2(cs_main, pwalletMain->cs_wallet);
    EnsureWalletIsUnlocked();

    if (pwalletMain->GetBroadcastTransactions() && !g_connman)
        throw JSONRPCError(RPC_CLIENT_P2P_DISABLED, "Error: Peer-to-peer functionality missing or disabled");

    //Get the addresses to be registered, or use the predefined script

    CRegisterAddressScript* raScript = new CRegisterAddressScript(RA_MULTISIG);

    CTxDestination keyid = address.Get();
    if (boost::get<CNoDestination>(&keyid))
        throw JSONRPCError(RPC_INVALID_PARAMETER, std::string(std::string(__func__) +
            ": invalid key id"));

    if (addressWhitelist->is_whitelisted(keyid) || addressWhitelist->is_my_pending(keyid))
        throw JSONRPCError(RPC_INVALID_PARAMETER, "This P2SH address is pending or has been whitelisted already");

    std::vector<CPubKey> pubKeyVec;
    for (unsigned int i = 0; i < sPubKeys.size(); ++i){
        std::string parseStr = sPubKeys[i].get_str();
        std::vector<unsigned char> pubKeyData(ParseHex(parseStr.c_str()));
        CPubKey tpubKey = CPubKey(pubKeyData.begin(), pubKeyData.end());

        if (!tpubKey.IsFullyValid())
            throw JSONRPCError(RPC_INVALID_PARAMETER, std::string(std::string(__func__) +
                ": invalid public key"));

        pubKeyVec.push_back(tpubKey);
    }

    if(!raScript->Append(nMultisig, keyid, pubKeyVec))
        throw JSONRPCError(RPC_INVALID_PARAMETER, "The process of p2sh whitelisting transaction serialization with present parameters has failed");

    addressWhitelist->add_my_pending(keyid);

    try{
        FinalizeRegisterAddressTx(raScript, feeAsset, pubKey, wtxNew);
    } catch(...){
        addressWhitelist->remove_my_pending(keyid);
        throw std::current_exception();
    }
}

//Register an unwhitelisted address from the keypool to the
//whitelist via a OP_REGISTERADDRESS transaction.
//Use "asset" to pay the transaction fee.
static void SendAddNextToWhitelistTx(const CAsset& feeAsset,
    const unsigned int nToRegister, const CPubKey& pubKey,
    CWalletTx& wtxNew){

    if(fWhitelistEncrypt && !addressWhitelist->find_kyc_whitelisted(pubKey.GetID())){
        throw JSONRPCError(RPC_INVALID_PARAMETER, "KYC public key not whitelisted");
    }

    LOCK2(cs_main, pwalletMain->cs_wallet);
    EnsureWalletIsUnlocked();

    // Check the balance of the "from" address
    map<CTxDestination, CAmount> balances = pwalletMain->GetAddressBalances();

    // Check amount
    if (nToRegister <= 0 || nToRegister > 100)
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid naddresses");

    if (pwalletMain->GetBroadcastTransactions() && !g_connman)
        throw JSONRPCError(RPC_CLIENT_P2P_DISABLED, "Error: Peer-to-peer functionality missing or disabled");


    //Get the addresses to be registered, or use the predefined script

    CRegisterAddressScript* raScript = new CRegisterAddressScript(RA_PUBLICKEY);



    CBitcoinAddress addr;
        // get the next registered base58check encoded tweaked public key and add it to the whitelist
    std::set<CKeyID> setKeyPool;

    //Get new addresses to register, topping up the key pool if necessary

    std::set<CKeyID> keysToReg;

    int nReg=0;
    int nWl=0;

    while(keysToReg.size() < nToRegister){
        pwalletMain->TopUpKeyPool(setKeyPool.size()+nToRegister - nReg + nWl);
        pwalletMain->GetAllReserveKeys(setKeyPool);
        for(std::set<CKeyID>::const_iterator it = setKeyPool.begin();
            it != setKeyPool.end(); ++it) {
                const CKeyID &keyid = *it;
                if (addressWhitelist->is_whitelisted(keyid) || addressWhitelist->is_my_pending(keyid)){
                    nWl++;
                    continue;
                }
                addr.Set(keyid);
                    CKey key;
                if (pwalletMain->GetKey(keyid, key)) { // verify exists
                    //keysToReg.push_back(key.GetPubKey());
                    if(keysToReg.insert(keyid).second){
                        if(!raScript->Append(key.GetPubKey()))
                            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Failed to append address to registeraddress script");
                        if(keysToReg.size() == nToRegister)
                            break;
                    }

                }
        }
    }

 //Add to my pending here in case TX fails.
    for(auto& key : keysToReg){
        addressWhitelist->add_my_pending(key);
    }
    try{
        FinalizeRegisterAddressTx(raScript, feeAsset, &pubKey, wtxNew);
    } catch(...){
        for(auto& key : keysToReg){
            addressWhitelist->remove_my_pending(key);
        }
        throw std::current_exception();
    }
}



extern UniValue getrawtransaction(const JSONRPCRequest& request);
extern UniValue signrawtransaction(const JSONRPCRequest& request);
extern UniValue sendrawtransaction(const JSONRPCRequest& request);

UniValue removekycpubkey(const JSONRPCRequest& request){
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "removekycpubkey \"kycpubkey\" \n"
            "\nArguments:\n"

            "1. \"kycpubkey\"    (string, required) The KYC public key to be removed from the list of available kycfile encryption keys\n"

            "\nExamples:\n"
            + HelpExampleCli("removekycpubkey", "\"kycpubkey\"")
            + HelpExampleRpc("removekycpubkey", "\"kycpubkey\"")
            );
    if(fWhitelistEncrypt)
        throw JSONRPCError(RPC_MISC_ERROR, "not implemented for encrypted whitelist");

    LOCK2(cs_main, pwalletMain->cs_wallet);

    EnsureWalletIsUnlocked();

    std::vector<unsigned char> pubKeyData(ParseHex(request.params[0].get_str()));
    CPubKey kycPubKey = CPubKey(pubKeyData.begin(), pubKeyData.end());
    if(!kycPubKey.IsFullyValid())
         throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid public key");

    return RemoveKYCPubKey(kycPubKey);
}


UniValue RemoveKYCPubKey(const CPubKey& kycPubKey){
    COutPoint outPoint;

    if(!addressWhitelist->get_kycpubkey_outpoint(kycPubKey.GetID(), outPoint))
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Could not find kycpubkey registration transaction hash");

    //Spend the whitelist registration transaction to blacklist the kycpubkey
    CMutableTransaction rawTx;
    rawTx.nLockTime=0;
    uint32_t nSequence = (rawTx.nLockTime ? std::numeric_limits<uint32_t>::max() - 1 : std::numeric_limits<uint32_t>::max());

    CTxIn in = CTxIn(outPoint, CScript(), nSequence);
    rawTx.vin.push_back(in);

    // Get the value and asset type of the input transaction
    JSONRPCRequest request2;
    UniValue varr(UniValue::VARR);
    varr.push_back(outPoint.hash.GetHex());
    request2.params = varr;
    UniValue result = getrawtransaction(request2);

    //Get output value
    CMutableTransaction inputTx;
    if (!DecodeHexTx(inputTx, result.get_str()))
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");

    CAmount amountIn=inputTx.vout[outPoint.n].nValue.GetAmount();
    CAsset assetIn=inputTx.vout[outPoint.n].nAsset.GetAsset();

    if (!IsWhitelistAsset(assetIn))
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Input TX asset is not WHITELIST");

    //Construct the change output
    CPubKey vchPubKey;
    CReserveKey changeKey(pwalletMain);
    if (!pwalletMain->IsLocked())
            pwalletMain->TopUpKeyPool();
    if (!changeKey.GetReservedKey(vchPubKey))
        throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, "Error: Keypool ran out, please call keypoolrefill first");

    rawTx.vout.push_back(
            CTxOut(
                assetIn,
                amountIn,
                GetScriptForDestination(vchPubKey.GetID())
            )
        );


    // Sign it
    JSONRPCRequest request3;
    UniValue varr2(UniValue::VARR);
    std::string sHexTx=EncodeHexTx(rawTx);
    varr2.push_back(sHexTx);
    request3.params = varr2;
    UniValue result2 = signrawtransaction(request3);


    // Send it
    JSONRPCRequest request4;
    UniValue varr3(UniValue::VARR);
    varr3.push_back(result2["hex"]);
    request4.params = varr3;
    return sendrawtransaction(request4);
}

UniValue blacklistkycpubkey(const JSONRPCRequest& request){
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "blacklistkycpubkey \"kycpubkey\" \n"
            "\nArguments:\n"

            "1. \"kycpubkey\"    (string, required) The KYC public key to be blacklisted\n"

            "\nExamples:\n"
            + HelpExampleCli("blacklistkycpubkey", "\"kycpubkey\"")
            + HelpExampleRpc("blacklistkycpubkey", "\"kycpubkey\"")
            );
    if(!fWhitelistEncrypt)
        throw JSONRPCError(RPC_MISC_ERROR, "not implemented for unencrypted whitelist");

    LOCK2(cs_main, pwalletMain->cs_wallet);

    EnsureWalletIsUnlocked();

    std::vector<unsigned char> pubKeyData(ParseHex(request.params[0].get_str()));
    CPubKey kycPubKey = CPubKey(pubKeyData.begin(), pubKeyData.end());
    if(!kycPubKey.IsFullyValid())
         throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid public key");



    if(!addressWhitelist->find_kyc_whitelisted(kycPubKey.GetID()))
        throw JSONRPCError(RPC_INVALID_PARAMETER, "kycpubkey is not whitelisted");


    return RemoveKYCPubKey(kycPubKey);
}



UniValue whitelistkycpubkeys(const JSONRPCRequest& request){
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "whitelistkycpubkeys \"kycpubkeys\" \n"
            "\nArguments:\n"

            "1. \"kycpubkeys\" (array, required) The KYC public keys to be whitelisted. If not supplied, one will be selected from the wallet.\n"
            "     [\n"
            "        \"pubkey\", \n"
            "        ...,\n"
            "      ]\n"

            "\nExamples:\n"
            + HelpExampleCli("whitelistkycpubkey", "[\"kycpubkey1\",\"kycpubkey2\"]")
            + HelpExampleRpc("whitelistkycpubkey", "[\"kycpubkey1\",\"kycpubkey2\"]")
            );

    UniValue kycPubKeys(UniValue::VARR);
    kycPubKeys = request.params[0].get_array();
    unsigned int maxNKeys=100;
    if(kycPubKeys.size() > maxNKeys)
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Error: too many keys in input array");

    LOCK2(cs_main, pwalletMain->cs_wallet);

    //Get a suitable whitelist transaction input.
    CTxIn* adminIn = nullptr;
    CMutableTransaction rawTx;
    rawTx.nLockTime=0;

    //1: Find a whitelist unspent tx (look for asset = whitelist in listunspent)
    //2: Get the address from the unspent output info
    //3: validateaddress and extract pubkey from result (admin pubkey)
    //4: extract output value

    int nMinDepth=1;
    CTxDestination adminDest;
    CPubKey adminPubKey;
    CAmount adminValue;
    uint256 adminTxID;

    CAsset wl_asset=Params().GetConsensus().whitelist_asset;

    CAmount amountPerOutput=1;
    CAmount spendAmount=amountPerOutput*kycPubKeys.size();
    CAmount changeAmount = 0;


    vector<COutput> vecOutputs;
    pwalletMain->AvailableCoins(vecOutputs, true, NULL, true);
    BOOST_FOREACH(const COutput& out, vecOutputs) {
        if (out.nDepth < nMinDepth)
            continue;

        adminValue = out.tx->GetOutputValueOut(out.i);
        CAsset assetid = out.tx->GetOutputAsset(out.i);

        //The output must contain some WHITELIST asset
        if (adminValue < 1 || assetid.IsNull())
            continue;

        if (wl_asset != assetid) {
            continue;
        }

        const CScript& scriptPubKey = out.tx->tx->vout[out.i].scriptPubKey;
        if(!ExtractDestination(scriptPubKey, adminDest)) continue;

        CBitcoinAddress address(adminDest);

        isminetype mine = pwalletMain ? IsMine(*pwalletMain, adminDest) : ISMINE_NO;
        if (mine != ISMINE_NO && address.IsBlinded() && address.GetBlindingKey() != pwalletMain->GetBlindingPubKey(GetScriptForDestination(adminDest))) {
            // Note: this will fail to return ismine for deprecated static blinded addresses.
            mine = ISMINE_NO;
        }
        if(!(mine & ISMINE_SPENDABLE)) {
            continue;
        }

        CKeyID keyID;
        const auto& meta = pwalletMain->mapKeyMetadata;

        auto it = address.GetKeyID(keyID) ? meta.find(keyID) : meta.end();
        if (it == meta.end()) {
            it = meta.find(CScriptID(scriptPubKey));
        }
        //Copy the pubkey
        if (it != meta.end()) {
            //Get nsequence
            uint32_t nSequence = (rawTx.nLockTime ? std::numeric_limits<uint32_t>::max() - 1 : std::numeric_limits<uint32_t>::max());
            adminIn = new CTxIn(COutPoint(out.tx->GetHash(), out.i), CScript(), nSequence);
            rawTx.vin.push_back(*adminIn);
            changeAmount=changeAmount+adminValue;
            //Generate a new pubkey if we cannot reuse the input pubkey
            if(!pwalletMain->GetPubKey(keyID, adminPubKey)){
                CReserveKey adminResKey(pwalletMain);
                if (!adminResKey.GetReservedKey(adminPubKey))
                    throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, "Error: Keypool ran out, please call keypoolrefill first");
            }
            //Break if we have enough inputs
            if(changeAmount > spendAmount)
                break;
        }
    }

    if(!adminIn)
        throw JSONRPCError(RPC_WALLET_ERROR, "Error: wallet has no spendable whitelist asset.");


    CPubKey kycPubKey;

    std::vector<CPubKey> pubkeys;
    pubkeys.resize(2);
    pubkeys[0] = adminPubKey;

    for (unsigned int idx = 0; idx < kycPubKeys.size(); idx++){
        const UniValue& item = kycPubKeys[idx];
        std::vector<unsigned char> pubKeyData=ParseHex(item.get_str());

        const CPubKey testKey(pubKeyData.begin(), pubKeyData.end());
        if(!testKey.IsFullyValid())
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid public key");

        //reverse the last 30 bytes so that this key cannot be used to spend the tx
        std::reverse(pubKeyData.begin()+3, pubKeyData.end());
        const CPubKey pubKey(pubKeyData.begin(), pubKeyData.end());

        pubkeys[1] = pubKey;

        //1 of 2 multisig
        rawTx.vout.push_back(
            CTxOut(wl_asset,
                amountPerOutput,
                GetScriptForMultisig(1, pubkeys)
                )
            );
        changeAmount = changeAmount - amountPerOutput;
    }

    rawTx.vout.push_back(
            CTxOut(
                wl_asset,
                changeAmount,
                GetScriptForDestination(adminPubKey.GetID())
            )
        );

    EnsureWalletIsUnlocked();

    // Sign it
    JSONRPCRequest request2;
    UniValue varr(UniValue::VARR);
    varr.push_back(EncodeHexTx(rawTx));
    request2.params = varr;
    UniValue result = signrawtransaction(request2);

    // Send it
    JSONRPCRequest request3;
    varr = UniValue(UniValue::VARR);
    varr.push_back(result["hex"]);
    request3.params = varr;

    return (int)sendrawtransaction(request3).size();
}

UniValue getnunassignedkycpubkeys(const JSONRPCRequest& request){
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 0) {
        throw runtime_error(
            "getunassignedkycpubkey\n"
            "Returns the number of unassigned KYC public keys; really only useful for debugging purposes\n"

            "\nExamples:\n"
            + HelpExampleCli("getnunassignedkycpubkeys", "")
            + HelpExampleRpc("getnunassignedkycpubkeys", "")
        );
    }
    if(!fScanWhitelist && !fRequireWhitelistCheck)
        throw JSONRPCError(RPC_MISC_ERROR, "pkhwhitelist and pkhwhitelist-scan are nor enabled\n");

    return addressWhitelist->n_unassigned_kyc_pubkeys();
}

UniValue topupkycpubkeys(const JSONRPCRequest& request){
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 1) {
        throw runtime_error(
            "topupkycpubkeys \"nkeys\" \n"
            "Create a raw transaction to top up the number of available KYC public keys to \"nkeys\". Max number added per call is capped at 1000.\n"
            "\nArguments:\n"

            "1. \"nkeys\"    (numeric, required) The required key pool size.\n"

            "\nExamples:\n"
            + HelpExampleCli("topupkycpubkeys", "\"nkeys\"")
            + HelpExampleRpc("topupkycpubkeys", "\"nkeys\"")
            );
    }

    LOCK2(cs_main, pwalletMain->cs_wallet);

    int64_t nKeysToAdd=request.params[0].get_int64()-addressWhitelist->n_unassigned_kyc_pubkeys();

    if(nKeysToAdd == 0) return 0;

    int64_t unassignedDiff = CWhiteList::MAX_UNASSIGNED_KYCPUBKEYS-addressWhitelist->n_unassigned_kyc_pubkeys();
    if(nKeysToAdd > unassignedDiff){
        nKeysToAdd = unassignedDiff;
    }

    UniValue kycpubkeys(UniValue::VARR);

    EnsureWalletIsUnlocked();

    UniValue ret(UniValue::VARR);
    UniValue varr(UniValue::VARR);

    unsigned int iMax=nKeysToAdd-1;
    unsigned int nMaxPerTx=100;
    int nAdded=0;
    JSONRPCRequest request2;

    for(unsigned int i=0; i<nKeysToAdd; i++){
        CPubKey kycPubKey = pwalletMain->GenerateNewKey(true);
        std::vector<unsigned char> datavec = ToByteVector(kycPubKey);
        kycpubkeys.push_back(HexStr(datavec.begin(), datavec.end()));
        if(kycpubkeys.size() == nMaxPerTx || (i==iMax && kycpubkeys.size()>0)){
            varr.push_back(kycpubkeys);
            request2.params = varr;
            whitelistkycpubkeys(request2).get_int();
            nAdded += kycpubkeys.size();
            kycpubkeys=UniValue(UniValue::VARR);
            varr=UniValue(UniValue::VARR);
        }

    }
    return nAdded;
}

UniValue sendaddtowhitelisttx(const JSONRPCRequest& request){
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

        if (request.fHelp || request.params.size() <1 || request.params.size() >2 ) {
        throw runtime_error(
            "sendaddtowhitelisttx \"naddresses\"\n"
            "\nRegister the next unwhitelisted address in the keypool via a \"add to whitelist\" transaction.\n"
            + HelpRequiringPassphrase() +
            "\nArguments:\n"
            "1. \"naddresses\"         (numeric or string, required) The number of new addresses to register.\n"
            "2. \"feeasset\"           (string, optional) The asset type to use to pay the transaction fee.\n"
            "\nResult:\n"
            "\"txid\"                  (string) The transaction id.\n"
            "\nExamples:\n"
            + HelpExampleCli("sendaddtowhitelisttx", "10, \"CBT\"")
        );
    }

    if (!fWhitelistEncrypt)
            throw JSONRPCError(RPC_MISC_ERROR, "Not implemented for unencrypted whitelist");


    LOCK2(cs_main, pwalletMain->cs_wallet);
    EnsureWalletIsUnlocked();

    UniValue naddresses = request.params[0];

    std::string sFeeAsset="CBT";
    if(request.params.size() == 2)
        sFeeAsset=request.params[1].get_str();
    CAsset feeasset = GetAssetFromString(sFeeAsset);

    CWalletTx wtx;
    CPubKey kycPubKey=pwalletMain->GetKYCPubKey();
    int naddr=naddresses.get_int();
    SendAddNextToWhitelistTx(feeasset, naddr, kycPubKey, wtx);


    //AuditLogPrintf("%s : sendaddtowhitelisttx %s %s txid:%s\n", getUser(), request.params[0].get_str(),
    //    request.params[1].get_str(), wtx.GetHash().GetHex());

    return wtx.GetHash().GetHex();
}

UniValue sendaddmultitowhitelisttx(const JSONRPCRequest& request){
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 3 || request.params.size() > 4 ) {
        throw runtime_error(
            "sendaddmultitowhitelisttx \"tweakedaddress\" \"basepubkeys\" \"nmultisig\" \"feeasset\"\n"
            "\nRegister the passed p2sh multisig address using \"add to whitelist\" transaction.\n"
            + HelpRequiringPassphrase() +
            "\nArguments:\n"
            "1. \"tweakedaddress\"  (string, required) Base58 tweaked multisig address\n"
            "2. \"basepubkeys\"     (array, required) A json array of ordered hex encoded of the compressed base (un-tweaked) public keys that were used in the multisig\n\n"
            "    [\n"
            "      \"basepubkey\", (string, required) Hex encoded of the compressed base (un-tweaked) public key that was used in the multisig\n\n"
            "      ,...\n"
            "    ]\n"
            "3. \"nmultisig\"     (numeric, required) Number of required signatures for a multisig transaction (n of M)\n"
            "4. \"feeasset\"           (string, optional) The asset type to use to pay the transaction fee.\n"
            "\nResult:\n"
            "\"txid\"                  (string) The transaction id.\n"
            "\nExamples:\n"
            + HelpExampleCli("sendaddmultitowhitelisttx", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\" \"[\\\"16sSauSf5pF2UkUwvKGq4qjNRzBZYqgEL5\\\",\\\"171sgjn4YtPu27adkKGrdDwzRTxnRkBfKV\\\"]\" 1, \"CBT\"")
        );
    }

    if(!fWhitelistEncrypt)
        throw JSONRPCError(RPC_MISC_ERROR, "Not implemented for unencrypted whitelist");

    if (request.params[0].isNull() || request.params[1].isNull() || request.params[2].isNull())
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, required arguments must be non-null");

    LOCK2(cs_main, pwalletMain->cs_wallet);
    EnsureWalletIsUnlocked();

    CBitcoinAddress address(request.params[0].get_str());
    if (!address.IsValid())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid Bitcoin address");

    int nPar2 = request.params[2].get_int();
    if(nPar2 < 1)
        throw JSONRPCError(RPC_INVALID_PARAMETER, "N of multisig can't be less than 1");
    unsigned int nMultisig = nPar2;

    if (nMultisig > MAX_P2SH_SIGOPS || nMultisig == 0)
        throw JSONRPCError(RPC_INVALID_PARAMETER, "N of multisig can't be larger than 255 (1 byte)");

    std::string sFeeAsset="CBT";
    if(request.params.size() == 4)
        sFeeAsset=request.params[3].get_str();
    CAsset feeasset = GetAssetFromString(sFeeAsset);

    CWalletTx wtx;
    CPubKey* kycPubKey = nullptr;
    if(fWhitelistEncrypt){
        kycPubKey = new CPubKey(pwalletMain->GetKYCPubKey());
    }
    SendAddNextMultiToWhitelistTx(feeasset, kycPubKey, address, request.params[1].get_array(), (uint8_t)nMultisig, wtx);
    return wtx.GetHash().GetHex();
}

UniValue sendtoaddress(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 2 || request.params.size() > 8)
        throw runtime_error(
            "sendtoaddress \"bitcoinaddress\" amount ( \"comment\" \"comment-to\" subtractfeefromamount assetlabel ignoreblindfail splitlargetxs)\n"
            "\nSend an amount to a given address.\n"
            + HelpRequiringPassphrase() +
            "\nArguments:\n"
            "1. \"address\"            (string, required) The bitcoin address to send to.\n"
            "2. \"amount\"             (numeric or string, required) The amount in " + CURRENCY_UNIT + " to send. eg 0.1\n"
            "3. \"comment\"            (string, optional) A comment used to store what the transaction is for. \n"
            "                             This is not part of the transaction, just kept in your wallet.\n"
            "4. \"comment_to\"         (string, optional) A comment to store the name of the person or organization \n"
            "                             to which you're sending the transaction. This is not part of the \n"
            "                             transaction, just kept in your wallet.\n"
            "5. subtractfeefromamount  (boolean, optional, default=false) The fee will be deducted from the amount being sent.\n"
            "                             The recipient will receive less bitcoins than you enter in the amount field.\n"
            "6. \"assetlabel\"               (string, optional) Hex asset id or asset label for balance.\n"
            "7. \"ignoreblindfail\"\"   (bool, default=true) Return a transaction even when a blinding attempt fails due to number of blinded inputs/outputs.\n"
            "\nResult:\n"
            "\"txid\"                  (string) The transaction id.\n"
            "\nExamples:\n"
            + HelpExampleCli("sendtoaddress", "\"1M72Sfpbz1BPpXFHz9m3CdqATR44Jvaydd\" 0.1")
            + HelpExampleCli("sendtoaddress", "\"1M72Sfpbz1BPpXFHz9m3CdqATR44Jvaydd\" 0.1 \"donation\" \"seans outpost\"")
            + HelpExampleCli("sendtoaddress", "\"1M72Sfpbz1BPpXFHz9m3CdqATR44Jvaydd\" 0.1 \"\" \"\" true")
            + HelpExampleCli("sendtoaddress", "\"1M72Sfpbz1BPpXFHz9m3CdqATR44Jvaydd\" 0.1 \"\" \"\" true \"my asset\"")
            + HelpExampleRpc("sendtoaddress", "\"1M72Sfpbz1BPpXFHz9m3CdqATR44Jvaydd\", 0.1, \"donation\", \"seans outpost\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    CBitcoinAddress address(request.params[0].get_str());
    if (!address.IsValid())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid Bitcoin address");

    // Amount
    CAmount nAmount = AmountFromValue(request.params[1]);
    if (nAmount <= 0)
        throw JSONRPCError(RPC_TYPE_ERROR, "Invalid amount for send");

    CPubKey confidentiality_pubkey;
    if (address.IsBlinded()) {
        confidentiality_pubkey = address.GetBlindingKey();
    }

    // Wallet comments
    string strComment;
    string strTo;
    if (request.params.size() > 2 && !request.params[2].isNull() && !request.params[2].get_str().empty())
        strComment = request.params[2].get_str();
    if (request.params.size() > 3 && !request.params[3].isNull() && !request.params[3].get_str().empty())
        strTo = request.params[3].get_str();

    bool fSubtractFeeFromAmount = false;
    if (request.params.size() > 4)
        fSubtractFeeFromAmount = request.params[4].get_bool();

    std::string strasset = "CBT";
    if (request.params.size() > 5 && request.params[5].isStr()) {
        strasset = request.params[5].get_str();
    }

    bool fIgnoreBlindFail = true;
    if (request.params.size() > 6)
        fIgnoreBlindFail = request.params[6].get_bool();

    CAsset asset = GetAssetFromString(strasset);

    EnsureWalletIsUnlocked();

    CWalletTx wtx;
    std::vector<CWalletTx> wtxs = SendMoney(address.Get(), nAmount, asset, fSubtractFeeFromAmount,
        confidentiality_pubkey, wtx, fIgnoreBlindFail, false);

    std::string blinds;
    UniValue arr(UniValue::VARR);
    for (const auto &tx : wtxs) {
        if (strComment != "") {
            tx.mapValue["comment"] = strComment;
        }
        if (strTo != "") {
            tx.mapValue["to"] = strTo;
        }
        for (unsigned int i=0; i<tx.tx->vout.size(); i++) {
            blinds += "blind:" + tx.GetOutputBlindingFactor(i).ToString() + "\n";
            blinds += "assetblind:" + tx.GetOutputAssetBlindingFactor(i).ToString() + "\n";
        }
        AuditLogPrintf("%s : sendtoaddress %s %s txid:%s\nblinds:\n%s\n", getUser(), request.params[0].get_str(),
            request.params[1].getValStr(), tx.GetHash().GetHex(), blinds);
        arr.push_back(tx.GetHash().GetHex());
    }
    if (wtxs.size() == 1) {
        return wtxs[0].GetHash().GetHex();
    }
    return arr;
}

UniValue sendanytoaddress(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 2 || request.params.size() > 7)
        throw runtime_error(
            "sendanytoaddress \"bitcoinaddress\" amount ( \"comment\" \"comment-to\" ignoreblindfail splitlargetxs balanceSortType)\n"
            "\nSend an amount to a given address with as many non-policy assets as needed.\n"
            "\nWarning! Only use this RPC in ocean chains in which all non-policy assets are fungible!!\n"
            + HelpRequiringPassphrase() +
            "\nArguments:\n"
            "1. \"address\"            (string, required) The bitcoin address to send to.\n"
            "2. \"amount\"             (numeric or string, required) The amount in " + CURRENCY_UNIT + " to send. eg 0.1\n"
            "3. \"comment\"            (string, optional) A comment used to store what the transaction is for. \n"
            "                             This is not part of the transaction, just kept in your wallet.\n"
            "4. \"comment_to\"         (string, optional) A comment to store the name of the person or organization \n"
            "                             to which you're sending the transaction. This is not part of the \n"
            "                             transaction, just kept in your wallet.\n"
            "5. \"ignoreblindfail\"\"   (bool, default=true) Return a transaction even when a blinding attempt fails due to number of blinded inputs/outputs.\n"
            "6. \"splitlargetxs\"\"   (bool, default=false) Split a transaction that goes over the size limit into smaller transactions.\n"
            "7. \"balanceSortType\"\"   (numeric, default=1) Choose which balances should be used first. 1 - descending, 2 - ascending\n"
            "\nResult:\n"
            "\"txid\"                  (string) The transaction id.\n"
            "\nExamples:\n"
            + HelpExampleCli("sendanytoaddress", "\"1M72Sfpbz1BPpXFHz9m3CdqATR44Jvaydd\" 0.1")
            + HelpExampleCli("sendanytoaddress", "\"1M72Sfpbz1BPpXFHz9m3CdqATR44Jvaydd\" 0.1 \"donation\" \"seans outpost\"")
            + HelpExampleCli("sendanytoaddress", "\"1M72Sfpbz1BPpXFHz9m3CdqATR44Jvaydd\" 0.1 \"\" \"\" true true 2")
            + HelpExampleCli("sendanytoaddress", "\"1M72Sfpbz1BPpXFHz9m3CdqATR44Jvaydd\" 0.1 \"\" \"\" true")
            + HelpExampleRpc("sendanytoaddress", "\"1M72Sfpbz1BPpXFHz9m3CdqATR44Jvaydd\", 0.1, \"donation\", \"seans outpost\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    CBitcoinAddress address(request.params[0].get_str());
    if (!address.IsValid())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid Bitcoin address");

    // Amount
    CAmount nAmount = AmountFromValue(request.params[1]);
    if (nAmount <= 0)
        throw JSONRPCError(RPC_TYPE_ERROR, "Invalid amount for send");

    CPubKey confidentiality_pubkey;
    if (address.IsBlinded()) {
        confidentiality_pubkey = address.GetBlindingKey();
    }

    // Wallet comments
    string strComment;
    string strTo;
    if (request.params.size() > 2 && !request.params[2].isNull() && !request.params[2].get_str().empty())
        strComment = request.params[2].get_str();
    if (request.params.size() > 3 && !request.params[3].isNull() && !request.params[3].get_str().empty())
        strTo = request.params[3].get_str();

    bool fIgnoreBlindFail = true;
    if (request.params.size() > 4)
        fIgnoreBlindFail = request.params[4].get_bool();

    bool fSplitTransactions = false;
    if (request.params.size() > 5)
        fSplitTransactions = request.params[5].get_bool();

    int fSortingType = 1;
    if (request.params.size() > 6)
        fSortingType = request.params[6].get_int();

    if (!(fSortingType == 1 || fSortingType == 2)) {
        throw JSONRPCError(RPC_TYPE_ERROR, "Invalid sendany sorting type.");
    }

    EnsureWalletIsUnlocked();

    CWalletTx wtx;
    vector<CWalletTx> wtxs = SendAnyMoney(address.Get(), nAmount, confidentiality_pubkey,
        wtx, fIgnoreBlindFail, fSplitTransactions, fSortingType);

    std::string blinds;
    UniValue arr(UniValue::VARR);
    for (const auto &tx : wtxs) {
        if (strComment != "") {
            tx.mapValue["comment"] = strComment;
        }
        if (strTo != "") {
            tx.mapValue["to"] = strTo;
        }
        for (unsigned int i=0; i<tx.tx->vout.size(); i++) {
            blinds += "blind:" + tx.GetOutputBlindingFactor(i).ToString() + "\n";
            blinds += "assetblind:" + tx.GetOutputAssetBlindingFactor(i).ToString() + "\n";
        }
        AuditLogPrintf("%s : sendanytoaddress %s %s txid:%s\nblinds:\n%s\n", getUser(), request.params[0].get_str(),
            request.params[1].getValStr(), tx.GetHash().GetHex(), blinds);
        arr.push_back(tx.GetHash().GetHex());
    }
    if (wtxs.size() == 1) {
        return wtxs[0].GetHash().GetHex();
    }
    return arr;
}

UniValue destroyamount(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 1 || request.params.size() > 3)
        throw runtime_error(
            "destroyamount asset amount ( \"comment\" )\n"
            "\nDestroy an amount of a given asset.\n"
            + HelpRequiringPassphrase() +
            "\nArguments:\n"
            "1. \"asset\"       (string, required) Hex asset id or asset label to destroy.\n"
            "2. \"amount\"      (numeric or string, required) The amount to destroy in BTC (8 decimals above the minimal unit).\n"
            "3. \"comment\"     (string, optional) A comment used to store what the transaction is for. \n"
            "                             This is not part of the transaction, just kept in your wallet.\n"
            "\nResult:\n"
            "\"transactionid\"  (string) The transaction id.\n"
            "\nExamples:\n"
            + HelpExampleCli("destroyamount", "\"bitcoin\" 100")
            + HelpExampleCli("destroyamount", "\"bitcoin\" 100 \"destroy assets\"")
            + HelpExampleRpc("destroyamount", "\"bitcoin\" 100 \"destroy assets\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    std::string strasset = request.params[0].get_str();
    CAsset asset = GetAssetFromString(strasset);

    CAmount nAmount = AmountFromValue(request.params[1]);
    if (nAmount <= 0)
        throw JSONRPCError(RPC_TYPE_ERROR, "Invalid amount to destroy");

    CWalletTx wtx;
    if (request.params.size() > 2 && !request.params[2].isNull() && !request.params[2].get_str().empty())
        wtx.mapValue["comment"] = request.params[2].get_str();

    CScript destroyScript(OP_RETURN);
    CPubKey confidentiality_pubkey;

    EnsureWalletIsUnlocked();
    SendMoney(destroyScript, nAmount, asset, false, confidentiality_pubkey, wtx, true);

    std::string blinds;
    for (unsigned int i=0; i<wtx.tx->vout.size(); i++) {
        blinds += "blind:" + wtx.GetOutputBlindingFactor(i).ToString() + "\n";
        blinds += "assetblind:" + wtx.GetOutputAssetBlindingFactor(i).ToString() + "\n";
    }
    AuditLogPrintf("%s : destroyamount %s asset %s id %s txid:%s\nblinds:\n%s\n", getUser(), request.params[1].getValStr(), strasset, asset.GetHex(), wtx.GetHash().GetHex(), blinds);

    return wtx.GetHash().GetHex();
}

UniValue listaddressgroupings(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp)
        throw runtime_error(
            "listaddressgroupings\n"
            "\nLists groups of addresses which have had their common ownership\n"
            "made public by common use as inputs or as the resulting change\n"
            "in past transactions\n"
            "\nResult:\n"
            "[\n"
            "  [\n"
            "    [\n"
            "      \"address\",            (string) The bitcoin address\n"
            "      amount,                 (numeric) The amount in " + CURRENCY_UNIT + "\n"
            "      \"account\"             (string, optional) DEPRECATED. The account\n"
            "    ]\n"
            "    ,...\n"
            "  ]\n"
            "  ,...\n"
            "]\n"
            "\nExamples:\n"
            + HelpExampleCli("listaddressgroupings", "")
            + HelpExampleRpc("listaddressgroupings", "")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    UniValue jsonGroupings(UniValue::VARR);
    map<CTxDestination, CAmount> balances = pwalletMain->GetAddressBalances();
    BOOST_FOREACH(set<CTxDestination> grouping, pwalletMain->GetAddressGroupings())
    {
        UniValue jsonGrouping(UniValue::VARR);
        BOOST_FOREACH(CTxDestination address, grouping)
        {
            UniValue addressInfo(UniValue::VARR);
            CBitcoinAddress addr(address);
            addressInfo.push_back(addr.ToString());
            addressInfo.push_back(ValueFromAmount(balances[address]));
            {
                if (pwalletMain->mapAddressBook.find(addr.Get()) != pwalletMain->mapAddressBook.end())
                    addressInfo.push_back(pwalletMain->mapAddressBook.find(addr.Get())->second.name);
            }
            jsonGrouping.push_back(addressInfo);
        }
        jsonGroupings.push_back(jsonGrouping);
    }
    return jsonGroupings;
}

UniValue signmessage(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 2)
        throw runtime_error(
            "signmessage \"address\" \"message\"\n"
            "\nSign a message with the private key of an address"
            + HelpRequiringPassphrase() + "\n"
            "\nArguments:\n"
            "1. \"address\"         (string, required) The bitcoin address to use for the private key.\n"
            "2. \"message\"         (string, required) The message to create a signature of.\n"
            "\nResult:\n"
            "\"signature\"          (string) The signature of the message encoded in base 64\n"
            "\nExamples:\n"
            "\nUnlock the wallet for 30 seconds\n"
            + HelpExampleCli("walletpassphrase", "\"mypassphrase\" 30") +
            "\nCreate the signature\n"
            + HelpExampleCli("signmessage", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\" \"my message\"") +
            "\nVerify the signature\n"
            + HelpExampleCli("verifymessage", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\" \"signature\" \"my message\"") +
            "\nAs json rpc\n"
            + HelpExampleRpc("signmessage", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\", \"my message\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    EnsureWalletIsUnlocked();

    string strAddress = request.params[0].get_str();
    string strMessage = request.params[1].get_str();

    CBitcoinAddress addr(strAddress);
    if (!addr.IsValid())
        throw JSONRPCError(RPC_TYPE_ERROR, "Invalid address");

    CKeyID keyID;
    if (!addr.GetKeyID(keyID))
        throw JSONRPCError(RPC_TYPE_ERROR, "Address does not refer to key");

    CKey key;
    if (!pwalletMain->GetKey(keyID, key))
        throw JSONRPCError(RPC_WALLET_ERROR, "Private key not available");

    CHashWriter ss(SER_GETHASH, 0);
    ss << strMessageMagic;
    ss << strMessage;

    vector<unsigned char> vchSig;
    if (!key.SignCompact(ss.GetHash(), vchSig))
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Sign failed");

    return EncodeBase64(&vchSig[0], vchSig.size());
}

UniValue encryptmessage(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 2)
        throw runtime_error(
            "signmessage \"address\" \"message\"\n"
            "\nEncrypts a message with the private key of an address"
            + HelpRequiringPassphrase() + "\n"
            "\nArguments:\n"
            "1. \"address\"         (string, required) The bitcoin address to use for the private key.\n"
            "2. \"message\"         (string, required) The message to be encrypted.\n"
            "\nResult:\n"
            "\"encrypted message\"          (string) The encrypted message.\n"
            "\nExamples:\n"
            "\nUnlock the wallet for 30 seconds\n"
            + HelpExampleCli("walletpassphrase", "\"mypassphrase\" 30") +
            "\nEncrypt the message\n"
            + HelpExampleCli("encryptmessage", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\" \"my message\"") +
            "\nDecrypt the message\n"
            + HelpExampleCli("decryptmessage", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\" \"encrypted message\"") +
            "\nAs json rpc\n"
            + HelpExampleRpc("encryptmessage", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\", \"my message\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    EnsureWalletIsUnlocked();

    string strAddress = request.params[0].get_str();
    string strMessage = request.params[1].get_str();

    CBitcoinAddress addr(strAddress);
    if (!addr.IsValid())
        throw JSONRPCError(RPC_TYPE_ERROR, "Invalid address");

    CKeyID keyID;
    if (!addr.GetKeyID(keyID))
        throw JSONRPCError(RPC_TYPE_ERROR, "Address does not refer to key");

    CKey key;
    if (!pwalletMain->GetKey(keyID, key))
        throw JSONRPCError(RPC_WALLET_ERROR, "Private key not available");

    CHashWriter ss(SER_GETHASH, 0);
    ss << strMessage;

    vector<unsigned char> vchSig;
    if (!key.SignCompact(ss.GetHash(), vchSig))
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Sign failed");

    return EncodeBase64(&vchSig[0], vchSig.size());
}

UniValue getreceivedbyaddress(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 1 || request.params.size() > 3)
        throw runtime_error(
            "getreceivedbyaddress \"address\" ( minconf assetlabel )\n"
            "\nReturns the total amount received by the given address in transactions with at least minconf confirmations.\n"
            "\nArguments:\n"
            "1. \"address\"         (string, required) The bitcoin address for transactions.\n"
            "2. minconf             (numeric, optional, default=1) Only include transactions confirmed at least this many times.\n"
            "3. \"assetlabel\"      (string, optional) Hex asset id or asset label for balance.\n"
            "\nResult:\n"
            "amount   (numeric) The total amount in " + CURRENCY_UNIT + " received at this address.\n"
            "\nExamples:\n"
            "\nThe amount from transactions with at least 1 confirmation\n"
            + HelpExampleCli("getreceivedbyaddress", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\"") +
            "\nThe amount including unconfirmed transactions, zero confirmations\n"
            + HelpExampleCli("getreceivedbyaddress", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\" 0") +
            "\nThe amount with at least 6 confirmation, very safe\n"
            + HelpExampleCli("getreceivedbyaddress", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\" 6") +
            "\nAs a json rpc call\n"
            + HelpExampleRpc("getreceivedbyaddress", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\", 6")
       );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    // Bitcoin address
    CBitcoinAddress address = CBitcoinAddress(request.params[0].get_str());
    if (!address.IsValid())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid Bitcoin address");
    CScript scriptPubKey = GetScriptForDestination(address.Get());
    if (!IsMine(*pwalletMain, scriptPubKey))
        return ValueFromAmount(0);

    // Minimum confirmations
    int nMinDepth = 1;
    if (request.params.size() > 1)
        nMinDepth = request.params[1].get_int();

    // Tally
    CAmountMap mapAmount;
    for (map<uint256, CWalletTx>::iterator it = pwalletMain->mapWallet.begin(); it != pwalletMain->mapWallet.end(); ++it)
    {
        const CWalletTx& wtx = (*it).second;
        if (wtx.IsCoinBase() || !CheckFinalTx(*wtx.tx))
            continue;


        for (unsigned int i = 0; i < wtx.tx->vout.size(); i++)
            if (wtx.tx->vout[i].scriptPubKey == scriptPubKey)
                if (wtx.GetDepthInMainChain() >= nMinDepth && wtx.GetOutputValueOut(i) >= 0) {
                    CAmountMap wtxValue;
                    wtxValue[wtx.GetOutputAsset(i)] = wtx.GetOutputValueOut(i);
                    mapAmount += wtxValue;
                }
    }

    std::string asset = "";
    if (request.params.size() > 2 && request.params[2].isStr()) {
        asset = request.params[2].get_str();
    }
    return PushAssetBalance(mapAmount, pwalletMain, asset);
}


UniValue getreceivedbyaccount(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 1 || request.params.size() > 2)
        throw runtime_error(
            "getreceivedbyaccount \"account\" ( minconf )\n"
            "\nDEPRECATED. Returns the total amount received by addresses with <account> in transactions with at least [minconf] confirmations.\n"
            "\nArguments:\n"
            "1. \"account\"      (string, required) The selected account, may be the default account using \"\".\n"
            "2. minconf          (numeric, optional, default=1) Only include transactions confirmed at least this many times.\n"
            "\nResult:\n"
            "amount              (numeric) The total amount in " + CURRENCY_UNIT + " received for this account.\n"
            "\nExamples:\n"
            "\nAmount received by the default account with at least 1 confirmation\n"
            + HelpExampleCli("getreceivedbyaccount", "\"\"") +
            "\nAmount received at the tabby account including unconfirmed amounts with zero confirmations\n"
            + HelpExampleCli("getreceivedbyaccount", "\"tabby\" 0") +
            "\nThe amount with at least 6 confirmation, very safe\n"
            + HelpExampleCli("getreceivedbyaccount", "\"tabby\" 6") +
            "\nAs a json rpc call\n"
            + HelpExampleRpc("getreceivedbyaccount", "\"tabby\", 6")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    // Minimum confirmations
    int nMinDepth = 1;
    if (request.params.size() > 1)
        nMinDepth = request.params[1].get_int();

    // Get the set of pub keys assigned to account
    string strAccount = AccountFromValue(request.params[0]);
    set<CTxDestination> setAddress = pwalletMain->GetAccountAddresses(strAccount);

    // Tally
    CAmountMap mapAmount;
    for (map<uint256, CWalletTx>::iterator it = pwalletMain->mapWallet.begin(); it != pwalletMain->mapWallet.end(); ++it)
    {
        const CWalletTx& wtx = (*it).second;
        if (wtx.IsCoinBase() || !CheckFinalTx(*wtx.tx))
            continue;

        for (unsigned int i = 0; i < wtx.tx->vout.size(); i++)
        {
            CTxDestination address;
            if (ExtractDestination(wtx.tx->vout[i].scriptPubKey, address) && IsMine(*pwalletMain, address) && setAddress.count(address)) {
                if (wtx.GetDepthInMainChain() >= nMinDepth && wtx.GetOutputValueOut(i) >= 0) {
                    CAmountMap wtxValue;
                    wtxValue[wtx.GetOutputAsset(i)] = wtx.GetOutputValueOut(i);
                    mapAmount += wtxValue;
                }
            }
        }
    }

    return PushAssetBalance(mapAmount, pwalletMain, "");
}


UniValue getbalance(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() > 4)
        throw runtime_error(
            "getbalance ( \"account\" minconf include_watchonly \"assetlabel\" )\n"
            "\nIf account is not specified, returns the server's total available balance.\n"
            "If account is specified (DEPRECATED), returns the balance in the account.\n"
            "Note that the account \"\" is not the same as leaving the parameter out.\n"
            "The server total may be different to the balance in the default \"\" account.\n"
            "\nArguments:\n"
            "1. \"account\"         (string, optional) DEPRECATED. The account string may be given as a\n"
            "                     specific account name to find the balance associated with wallet keys in\n"
            "                     a named account, or as the empty string (\"\") to find the balance\n"
            "                     associated with wallet keys not in any named account, or as \"*\" to find\n"
            "                     the balance associated with all wallet keys regardless of account.\n"
            "                     When this option is specified, it calculates the balance in a different\n"
            "                     way than when it is not specified, and which can count spends twice when\n"
            "                     there are conflicting pending transactions (such as those created by\n"
            "                     the bumpfee command), temporarily resulting in low or even negative\n"
            "                     balances. In general, account balance calculation is not considered\n"
            "                     reliable and has resulted in confusing outcomes, so it is recommended to\n"
            "                     avoid passing this argument.\n"
            "2. minconf           (numeric, optional, default=1) Only include transactions confirmed at least this many times.\n"
            "3. include_watchonly (bool, optional, default=false) Also include balance in watch-only addresses (see 'importaddress')\n"
            "4. \"assetlabel\"   (string, optional) Hex asset id or asset label for balance. IF THIS IS USED ALL OTHER ARGUMENTS ARE IGNORED\n"
            "\nResult:\n"

            "amount              (numeric) The total amount in " + CURRENCY_UNIT + " received for this account.\n"
            "\nExamples:\n"
            "\nThe total amount in the wallet\n"
            + HelpExampleCli("getbalance", "") +
            "\nThe total amount in the wallet of the specified asset (leading 3 arguments are ignored)\n"
            + HelpExampleCli("getbalance", "\"*\" 6 false \"b2e15d0d7a0c94e4e2ce0fe6e8691b9e451377f6e46e8045a86f7c4b5d4f0f23\"") +
            "\nAs a json rpc call\n"
            + HelpExampleRpc("getbalance", "\"*\", 6 false \"b2e15d0d7a0c94e4e2ce0fe6e8691b9e451377f6e46e8045a86f7c4b5d4f0f23\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    CAmountMap balance = pwalletMain->GetBalance();

    if (request.params.size() == 0)
        return PushAssetBalance(balance, pwalletMain, "");

    int nMinDepth = 1;
    if (request.params.size() > 1)
        nMinDepth = request.params[1].get_int();
    isminefilter filter = ISMINE_SPENDABLE;
    if(request.params.size() > 2)
        if(request.params[2].get_bool())
            filter = filter | ISMINE_WATCH_ONLY;

    // Asset type ignores accounts. Accounts are scary and deprecated anyways.
    // TODO: Yell at user if args aren't default/blank account
    if (request.params.size() > 3) {
        if (request.params[3].isStr()) {
            std::string assettype = request.params[3].get_str();
            UniValue obj(UniValue::VOBJ);
            return PushAssetBalance(balance, pwalletMain, assettype);
        }
    }

    if (request.params[0].get_str() == "*") {
        // Calculate total balance in a very different way from GetBalance().
        // The biggest difference is that GetBalance() sums up all unspent
        // TxOuts paying to the wallet, while this sums up both spent and
        // unspent TxOuts paying to the wallet, and then subtracts the values of
        // TxIns spending from the wallet. This also has fewer restrictions on
        // which unconfirmed transactions are considered trusted.
        CAmountMap mapBalance;
        for (map<uint256, CWalletTx>::iterator it = pwalletMain->mapWallet.begin(); it != pwalletMain->mapWallet.end(); ++it)
        {
            const CWalletTx& wtx = (*it).second;
            if (!CheckFinalTx(wtx) || wtx.GetBlocksToMaturity() > 0 || wtx.GetDepthInMainChain() < 0)
                continue;

            CAmount allFee;
            string strSentAccount;
            list<COutputEntry> listReceived;
            list<COutputEntry> listSent;
            wtx.GetAmounts(listReceived, listSent, allFee, strSentAccount, filter);
            if (wtx.GetDepthInMainChain() >= nMinDepth)
            {
                for (COutputEntry const &r : listReceived)
                    mapBalance[r.asset] += r.amount;
            }
            for (COutputEntry const &s : listSent)
                mapBalance[s.asset] -= s.amount;
            mapBalance[wtx.tx->GetFee().begin()->first] -= allFee;
            // Tally issuances since there are no corresponding "receives"
            for (unsigned int i = 0; i < wtx.tx->vin.size(); i++) {
                const CTxIn& txin = wtx.tx->vin[i];
                const CAssetIssuance& issuance = txin.assetIssuance;
                if (pwalletMain->IsMine(txin) == ISMINE_NO) {
                    continue;
                }
                CAsset asset;
                CAsset token;
                uint256 entropy;
                if (!issuance.IsNull()) {
                    if (!issuance.IsReissuance()) {
                        GenerateAssetEntropy(entropy, txin.prevout, issuance.assetEntropy);
                        CalculateAsset(asset, entropy);
                        CalculateReissuanceToken(token, entropy, issuance.nAmount.IsCommitment());
                    } else {
                        CalculateAsset(asset, issuance.assetEntropy);
                    }
                }
                if (!issuance.nAmount.IsNull()) {
                    mapBalance[asset] += wtx.GetIssuanceAmount(i, false);
                }
                if (!issuance.nInflationKeys.IsNull()) {
                    mapBalance[token] += wtx.GetIssuanceAmount(i, true);
                }
            }
        }
        return PushAssetBalance(mapBalance, pwalletMain, "");
    }

    string strAccount = AccountFromValue(request.params[0]);

    CAmount nBalance = pwalletMain->GetAccountBalance(strAccount, nMinDepth, filter);

    return ValueFromAmount(nBalance);
}

UniValue getunconfirmedbalance(const JSONRPCRequest &request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() > 1)
        throw runtime_error(
            "getunconfirmedbalance ( asset )\n"
            "\nArguments:\n"
            "1. \"asset\"               (string, optional) Hex asset id or asset label for balance.\n"
            "Returns the server's total unconfirmed balance\n");

    LOCK2(cs_main, pwalletMain->cs_wallet);

    CAmountMap balance = pwalletMain->GetUnconfirmedBalance();

    std::string strasset = "";
    if (request.params.size() > 0) {
        strasset = request.params[0].get_str();
    }

    return PushAssetBalance(balance, pwalletMain, strasset);
}


UniValue movecmd(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 3 || request.params.size() > 5)
        throw runtime_error(
            "move \"fromaccount\" \"toaccount\" amount ( minconf \"comment\" )\n"
            "\nDEPRECATED. Move a specified amount from one account in your wallet to another.\n"
            "\nArguments:\n"
            "1. \"fromaccount\"   (string, required) The name of the account to move funds from. May be the default account using \"\".\n"
            "2. \"toaccount\"     (string, required) The name of the account to move funds to. May be the default account using \"\".\n"
            "3. amount            (numeric) Quantity of " + CURRENCY_UNIT + " to move between accounts.\n"
            "4. (dummy)           (numeric, optional) Ignored. Remains for backward compatibility.\n"
            "5. \"comment\"       (string, optional) An optional comment, stored in the wallet only.\n"
            "\nResult:\n"
            "true|false           (boolean) true if successful.\n"
            "\nExamples:\n"
            "\nMove 0.01 " + CURRENCY_UNIT + " from the default account to the account named tabby\n"
            + HelpExampleCli("move", "\"\" \"tabby\" 0.01") +
            "\nMove 0.01 " + CURRENCY_UNIT + " timotei to akiko with a comment and funds have 6 confirmations\n"
            + HelpExampleCli("move", "\"timotei\" \"akiko\" 0.01 6 \"happy birthday!\"") +
            "\nAs a json rpc call\n"
            + HelpExampleRpc("move", "\"timotei\", \"akiko\", 0.01, 6, \"happy birthday!\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    string strFrom = AccountFromValue(request.params[0]);
    string strTo = AccountFromValue(request.params[1]);
    CAmount nAmount = AmountFromValue(request.params[2]);
    if (nAmount <= 0)
        throw JSONRPCError(RPC_TYPE_ERROR, "Invalid amount for send");
    if (request.params.size() > 3)
        // unused parameter, used to be nMinDepth, keep type-checking it though
        (void)request.params[3].get_int();
    string strComment;
    if (request.params.size() > 4)
        strComment = request.params[4].get_str();

    if (!pwalletMain->AccountMove(strFrom, strTo, nAmount, strComment))
        throw JSONRPCError(RPC_DATABASE_ERROR, "database error");

    return true;
}

UniValue sendmany(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 2 || request.params.size() > 6)
        throw runtime_error(
            "sendmany \"fromaccount\" {\"address\":amount,...} ( minconf \"comment\" [\"address\",...] )\n"
            "\nSend multiple times. Amounts are double-precision floating point numbers."
            + HelpRequiringPassphrase() + "\n"
            "\nArguments:\n"
            "1. \"fromaccount\"         (string, required) DEPRECATED. The account to send the funds from. Should be \"\" for the default account\n"
            "2. \"amounts\"             (string, required) A json object with addresses and amounts\n"
            "    {\n"
            "      \"address\":amount   (numeric or string) The bitcoin address is the key, the numeric amount (can be string) in " + CURRENCY_UNIT + " is the value\n"
            "      ,...\n"
            "    }\n"
            "3. minconf                 (numeric, optional, default=1) Only use the balance confirmed at least this many times.\n"
            "4. \"comment\"             (string, optional) A comment\n"
            "5. subtractfeefrom         (array, optional) A json array with addresses.\n"
            "                           The fee will be equally deducted from the amount of each selected address.\n"
            "                           Those recipients will receive less bitcoins than you enter in their corresponding amount field.\n"
            "                           If no addresses are specified here, the sender pays the fee.\n"
            "    [\n"
            "      \"address\"          (string) Subtract fee from this address\n"
            "      ,...\n"
            "    ]\n"
            "6. \"output_assets\"     (string, optional, default=bitcoin) a json object of assets to addresses\n"
            "   {\n"
            "       \"address\": \"hex\" \n"
            "       \"fee\": \"hex\" \n"
            "       ...\n"
            "   }\n"
            "7. \"ignoreblindfail\"\"   (bool, default=true) Return a transaction even when a blinding attempt fails due to number of blinded inputs/outputs.\n"
            "\nResult:\n"
            "\"txid\"                   (string) The transaction id for the send. Only 1 transaction is created regardless of \n"
            "                                    the number of addresses.\n"
            "\nExamples:\n"
            "\nSend two amounts to two different addresses:\n"
            + HelpExampleCli("sendmany", "\"\" \"{\\\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\\\":0.01,\\\"1353tsE8YMTA4EuV7dgUXGjNFf9KpVvKHz\\\":0.02}\"") +
            "\nSend two amounts to two different addresses setting the confirmation and comment:\n"
            + HelpExampleCli("sendmany", "\"\" \"{\\\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\\\":0.01,\\\"1353tsE8YMTA4EuV7dgUXGjNFf9KpVvKHz\\\":0.02}\" 6 \"testing\"") +
            "\nSend two amounts to two different addresses, subtract fee from amount:\n"
            + HelpExampleCli("sendmany", "\"\" \"{\\\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\\\":0.01,\\\"1353tsE8YMTA4EuV7dgUXGjNFf9KpVvKHz\\\":0.02}\" 1 \"\" \"[\\\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\\\",\\\"1353tsE8YMTA4EuV7dgUXGjNFf9KpVvKHz\\\"]\"") +
            "\nAs a json rpc call\n"
            + HelpExampleRpc("sendmany", "\"\", \"{\\\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\\\":0.01,\\\"1353tsE8YMTA4EuV7dgUXGjNFf9KpVvKHz\\\":0.02}\", 6, \"testing\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    if (pwalletMain->GetBroadcastTransactions() && !g_connman)
        throw JSONRPCError(RPC_CLIENT_P2P_DISABLED, "Error: Peer-to-peer functionality missing or disabled");

    string strAccount = AccountFromValue(request.params[0]);
    UniValue sendTo = request.params[1].get_obj();
    int nMinDepth = 1;
    if (request.params.size() > 2)
        nMinDepth = request.params[2].get_int();

    CWalletTx wtx;
    wtx.strFromAccount = strAccount;
    if (request.params.size() > 3 && !request.params[3].isNull() && !request.params[3].get_str().empty())
        wtx.mapValue["comment"] = request.params[3].get_str();

    UniValue subtractFeeFromAmount(UniValue::VARR);
    if (request.params.size() > 4)
        subtractFeeFromAmount = request.params[4].get_array();

    UniValue assets;
    if (request.params.size() > 5 && !request.params[5].isNull()) {
        if (strAccount != "")
           throw JSONRPCError(RPC_TYPE_ERROR, "Accounts can not be used with assets.");
        assets = request.params[5].get_obj();
    }

    bool fIgnoreBlindFail = true;
    if (request.params.size() > 6) {
        fIgnoreBlindFail = request.params[6].get_bool();
    }

    set<CBitcoinAddress> setAddress;
    vector<CRecipient> vecSend;

    std::string strAudit(getUser());
    strAudit += " : sendmany \n";

    CAmount totalAmount = 0;
    vector<string> keys = sendTo.getKeys();
    BOOST_FOREACH(const string& name_, keys)
    {
        CBitcoinAddress address(name_);

        std::string strasset = "CBT";
        if (!assets.isNull() && assets[name_].isStr()) {
            strasset = assets[name_].get_str();
        }

        CAsset asset = GetAssetFromString(strasset);

        if (!address.IsValid())
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, string("Invalid Bitcoin address: ")+name_);

        if (setAddress.count(address))
            throw JSONRPCError(RPC_INVALID_PARAMETER, string("Invalid parameter, duplicated address: ")+name_);
        setAddress.insert(address);

        CScript scriptPubKey = GetScriptForDestination(address.Get());
        CAmount nAmount = AmountFromValue(sendTo[name_]);
        if (nAmount <= 0)
            throw JSONRPCError(RPC_TYPE_ERROR, "Invalid amount for send");
        totalAmount += nAmount;

        strAudit += name_ + " " + sendTo[name_].getValStr() + "\n";

        CPubKey confidentiality_pubkey;
        if (address.IsBlinded())
            confidentiality_pubkey = address.GetBlindingKey();

        bool fSubtractFeeFromAmount = false;
        for (unsigned int idx = 0; idx < subtractFeeFromAmount.size(); idx++) {
            const UniValue& addr = subtractFeeFromAmount[idx];
            if (addr.get_str() == name_)
                fSubtractFeeFromAmount = true;
        }

        CRecipient recipient = {scriptPubKey, nAmount, asset, confidentiality_pubkey, fSubtractFeeFromAmount};
        vecSend.push_back(recipient);

    }

    // Check if the fee asset is set and pass that to transaction creation
    CAsset feeAsset;
    if (!assets.isNull() && assets["fee"].isStr()) {
        feeAsset = GetAssetFromString(assets["fee"].get_str());
    }

    EnsureWalletIsUnlocked();

    // Check funds
    CAmount nBalance = pwalletMain->GetAccountBalance(strAccount, nMinDepth, ISMINE_SPENDABLE);
    if (totalAmount > nBalance)
        throw JSONRPCError(RPC_WALLET_INSUFFICIENT_FUNDS, "Account has insufficient funds");

    std::vector<std::vector<CReserveKey>> vChangeKeys;
    // Send
    std::vector<CReserveKey> vChangeKey;
    std::set<CAsset> setAssets;
    setAssets.insert(policyAsset);
    for (auto recipient : vecSend) {
        setAssets.insert(recipient.asset);
    }
    vChangeKey.reserve(setAssets.size());
    for (unsigned int i = 0; i < setAssets.size(); i++) {
        vChangeKey.emplace_back(pwalletMain);
    }
    vChangeKeys.push_back(vChangeKey);
    CAmount nFeeRequired = 0;
    int nChangePosRet = -1;
    string strFailReason;

    std::vector<CWalletTx> createResult = pwalletMain->CreateTransaction(vecSend, wtx, vChangeKeys, nFeeRequired, nChangePosRet, strFailReason, NULL, true, NULL, false, NULL, NULL, NULL, feeAsset, fIgnoreBlindFail);

    if (!(createResult.size() > 0))
        throw JSONRPCError(RPC_WALLET_INSUFFICIENT_FUNDS, strFailReason);
    CValidationState state;
    if (!pwalletMain->CommitTransaction(wtx, vChangeKeys[0], g_connman.get(), state)) {
        strFailReason = strprintf("Transaction commit failed:: %s", state.GetRejectReason());
        throw JSONRPCError(RPC_WALLET_ERROR, strFailReason);
    }

    std::string blinds;
    for (unsigned int i=0; i<wtx.tx->vout.size(); i++) {
        blinds += "blind:" + wtx.GetOutputBlindingFactor(i).ToString() + "\n";
        blinds += "assetblind:" + wtx.GetOutputAssetBlindingFactor(i).ToString() + "\n";
    }

    AuditLogPrintf("%s\nblinds:\n%s\n", strAudit, blinds);

    return wtx.GetHash().GetHex();
}

// Defined in rpc/misc.cpp
extern CScript _createmultisig_redeemScript(const UniValue& params);

UniValue addmultisigaddress(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 2 || request.params.size() > 3)
    {
        string msg = "addmultisigaddress nrequired [\"key\",...] ( \"account\" )\n"
            "\nAdd a nrequired-to-sign multisignature address to the wallet.\n"
            "Each key is a Bitcoin address or hex-encoded public key.\n"
            "If 'account' is specified (DEPRECATED), assign address to that account.\n"

            "\nArguments:\n"
            "1. nrequired        (numeric, required) The number of required signatures out of the n keys or addresses.\n"
            "2. \"keys\"         (string, required) A json array of bitcoin addresses or hex-encoded public keys\n"
            "     [\n"
            "       \"address\"  (string) bitcoin address or hex-encoded public key\n"
            "       ...,\n"
            "     ]\n"
            "3. \"account\"      (string, optional) DEPRECATED. An account to assign the addresses to.\n"

            "\nResult:\n"
            "\"address\"         (string) A bitcoin address associated with the keys.\n"

            "\nExamples:\n"
            "\nAdd a multisig address from 2 addresses\n"
            + HelpExampleCli("addmultisigaddress", "2 \"[\\\"16sSauSf5pF2UkUwvKGq4qjNRzBZYqgEL5\\\",\\\"171sgjn4YtPu27adkKGrdDwzRTxnRkBfKV\\\"]\"") +
            "\nAs json rpc call\n"
            + HelpExampleRpc("addmultisigaddress", "2, \"[\\\"16sSauSf5pF2UkUwvKGq4qjNRzBZYqgEL5\\\",\\\"171sgjn4YtPu27adkKGrdDwzRTxnRkBfKV\\\"]\"")
        ;
        throw runtime_error(msg);
    }

    LOCK2(cs_main, pwalletMain->cs_wallet);

    string strAccount;
    if (request.params.size() > 2)
        strAccount = AccountFromValue(request.params[2]);

    // Construct using pay-to-script-hash:
    CScript inner = _createmultisig_redeemScript(request.params);
    CScriptID innerID(inner);
    pwalletMain->AddCScript(inner);

    pwalletMain->SetAddressBook(innerID, strAccount, "send");

    AuditLogPrintf("%s : addmultisigaddress %s\n", getUser(), CBitcoinAddress(innerID).ToString());

    return CBitcoinAddress(innerID).ToString();
}

class Witnessifier : public boost::static_visitor<bool>
{
public:
    CScriptID result;

    bool operator()(const CNoDestination &dest) const { return false; }

    bool operator()(const CKeyID &keyID) {
        CPubKey pubkey;
        if (pwalletMain) {
            CScript basescript = GetScriptForDestination(keyID);
            isminetype typ;
            typ = IsMine(*pwalletMain, basescript, SIGVERSION_WITNESS_V0);
            if (typ != ISMINE_SPENDABLE && typ != ISMINE_WATCH_SOLVABLE)
                return false;
            CScript witscript = GetScriptForWitness(basescript);
            pwalletMain->AddCScript(witscript);
            result = CScriptID(witscript);
            return true;
        }
        return false;
    }

    bool operator()(const CScriptID &scriptID) {
        CScript subscript;
        if (pwalletMain && pwalletMain->GetCScript(scriptID, subscript)) {
            int witnessversion;
            std::vector<unsigned char> witprog;
            if (subscript.IsWitnessProgram(witnessversion, witprog)) {
                result = scriptID;
                return true;
            }
            isminetype typ;
            typ = IsMine(*pwalletMain, subscript, SIGVERSION_WITNESS_V0);
            if (typ != ISMINE_SPENDABLE && typ != ISMINE_WATCH_SOLVABLE)
                return false;
            CScript witscript = GetScriptForWitness(subscript);
            pwalletMain->AddCScript(witscript);
            result = CScriptID(witscript);
            return true;
        }
        return false;
    }
};

UniValue addwitnessaddress(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 1 || request.params.size() > 1)
    {
        string msg = "addwitnessaddress \"address\"\n"
            "\nAdd a witness address for a script (with pubkey or redeemscript known).\n"
            "It returns the witness script.\n"

            "\nArguments:\n"
            "1. \"address\"       (string, required) An address known to the wallet\n"

            "\nResult:\n"
            "\"witnessaddress\",  (string) The value of the new address (P2SH of witness script).\n"
            "}\n"
        ;
        throw runtime_error(msg);
    }

    {
        LOCK(cs_main);
        if (!IsWitnessEnabled(chainActive.Tip(), Params().GetConsensus()) && !GetBoolArg("-walletprematurewitness", false)) {
            throw JSONRPCError(RPC_WALLET_ERROR, "Segregated witness not enabled on network");
        }
    }

    CBitcoinAddress address(request.params[0].get_str());
    if (!address.IsValid())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid Bitcoin address");

    Witnessifier w;
    CTxDestination dest = address.Get();
    bool ret = boost::apply_visitor(w, dest);
    if (!ret) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Public key or redeemscript not known to wallet, or the key is uncompressed");
    }

    pwalletMain->SetAddressBook(w.result, "", "receive");

    AuditLogPrintf("%s : addwitnessaddress %s\n", getUser(), CBitcoinAddress(w.result).ToString());

    return CBitcoinAddress(w.result).ToString();
}

struct tallyitem
{
    CBitcoinAddress address;
    CAmount nAmount;
    CAmountMap mapAmount;
    int nConf;
    vector<uint256> txids;
    bool fIsWatchonly;
    tallyitem()
    {
        nConf = std::numeric_limits<int>::max();
        fIsWatchonly = false;
    }
};

UniValue ListReceived(const UniValue& params, bool fByAccounts)
{
    // Minimum confirmations
    int nMinDepth = 1;
    if (params.size() > 0)
        nMinDepth = params[0].get_int();

    // Whether to include empty accounts
    bool fIncludeEmpty = false;
    if (params.size() > 1)
        fIncludeEmpty = params[1].get_bool();

    isminefilter filter = ISMINE_SPENDABLE;
    if(params.size() > 2)
        if(params[2].get_bool())
            filter = filter | ISMINE_WATCH_ONLY;

    std::string strasset = "";
    if (params.size() > 3 && params[3].isStr()) {
        if (fByAccounts)
            throw JSONRPCError(RPC_WALLET_ERROR, "Accounts are completely disabled for assets.");
        strasset = params[3].get_str();
    }
    CAsset asset;
    if (strasset != "")
        asset = GetAssetFromString(strasset);

    // Tally
    map<CTxDestination, tallyitem> mapTally;
    for (map<uint256, CWalletTx>::iterator it = pwalletMain->mapWallet.begin(); it != pwalletMain->mapWallet.end(); ++it)
    {
        const CWalletTx& wtx = (*it).second;

        if (wtx.IsCoinBase() || !CheckFinalTx(*wtx.tx))
            continue;

        int nDepth = wtx.GetDepthInMainChain();
        if (nDepth < nMinDepth)
            continue;

        for (unsigned int i = 0; i < wtx.tx->vout.size(); i++)
        {
            CTxDestination address;
            if (!ExtractDestination(wtx.tx->vout[i].scriptPubKey, address))
                continue;

            isminefilter mine = IsMine(*pwalletMain, address);
            if(!(mine & filter))
                continue;

            if (wtx.GetOutputValueOut(i) < 0)
                continue;

            if (strasset != "" && wtx.GetOutputAsset(i) != asset)
                continue;

            CBitcoinAddress bitcoinaddress(address);

            tallyitem& item = mapTally[address];
            item.address = bitcoinaddress;
            CAmountMap wtxValue;
            wtxValue[wtx.GetOutputAsset(i)] = wtx.GetOutputValueOut(i);
            item.mapAmount += wtxValue;
            item.nConf = min(item.nConf, nDepth);
            item.txids.push_back(wtx.GetHash());
            if (mine & ISMINE_WATCH_ONLY)
                item.fIsWatchonly = true;
        }
    }

    // Reply
    UniValue ret(UniValue::VARR);
    map<string, tallyitem> mapAccountTally;
    BOOST_FOREACH(const PAIRTYPE(CTxDestination, CAddressBookData)& item, pwalletMain->mapAddressBook)
    {
        const CTxDestination& address = item.first;
        const string& strAccount = item.second.name;
        map<CTxDestination, tallyitem>::iterator it = mapTally.find(address);
        if (it == mapTally.end() && !fIncludeEmpty)
            continue;

        CBitcoinAddress fulladdress = address;
        CAmountMap mapAmount;
        int nConf = std::numeric_limits<int>::max();
        bool fIsWatchonly = false;
        if (it != mapTally.end())
        {
            fulladdress = (*it).second.address;
            mapAmount = (*it).second.mapAmount;
            nConf = (*it).second.nConf;
            fIsWatchonly = (*it).second.fIsWatchonly;
        }

        if (fByAccounts)
        {
            tallyitem& _item = mapAccountTally[strAccount];
            _item.mapAmount += mapAmount;
            _item.nConf = min(_item.nConf, nConf);
            _item.fIsWatchonly = fIsWatchonly;
        }
        else
        {
            UniValue obj(UniValue::VOBJ);
            if(fIsWatchonly)
                obj.push_back(Pair("involvesWatchonly", true));
            if (fulladdress.IsBlinded())
                fulladdress = fulladdress.GetUnblinded();
            obj.push_back(Pair("address",       fulladdress.ToString()));
            obj.push_back(Pair("account",       strAccount));
            obj.push_back(Pair("amount",        PushAssetBalance(mapAmount, pwalletMain, strasset)));
            obj.push_back(Pair("confirmations", (nConf == std::numeric_limits<int>::max() ? 0 : nConf)));
            obj.push_back(Pair("label", strAccount));
            UniValue transactions(UniValue::VARR);
            if (it != mapTally.end())
            {
                BOOST_FOREACH(const uint256& _item, (*it).second.txids)
                {
                    transactions.push_back(_item.GetHex());
                }
            }
            obj.push_back(Pair("txids", transactions));
            ret.push_back(obj);
        }
    }

    if (fByAccounts)
    {
        for (map<string, tallyitem>::iterator it = mapAccountTally.begin(); it != mapAccountTally.end(); ++it)
        {
            CAmountMap mapAmount = (*it).second.mapAmount;
            int nConf = (*it).second.nConf;
            UniValue obj(UniValue::VOBJ);
            if((*it).second.fIsWatchonly)
                obj.push_back(Pair("involvesWatchonly", true));
            obj.push_back(Pair("account",       (*it).first));
            obj.push_back(Pair("amount",        PushAssetBalance(mapAmount, pwalletMain, strasset)));
            obj.push_back(Pair("confirmations", (nConf == std::numeric_limits<int>::max() ? 0 : nConf)));
            ret.push_back(obj);
        }
    }

    return ret;
}

UniValue listreceivedbyaddress(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() > 4)
        throw runtime_error(
            "listreceivedbyaddress ( minconf include_empty include_watchonly, \"assetlabel\" )\n"
            "\nList balances by receiving address.\n"
            "\nArguments:\n"
            "1. minconf           (numeric, optional, default=1) The minimum number of confirmations before payments are included.\n"
            "2. include_empty     (bool, optional, default=false) Whether to include addresses that haven't received any payments.\n"
            "3. include_watchonly (bool, optional, default=false) Whether to include watch-only addresses (see 'importaddress').\n"
            "4.  \"assetlabel\"     (string, optional) The hex asset id or asset label to filter for.\n"
            "\nResult:\n"
            "[\n"
            "  {\n"
            "    \"involvesWatchonly\" : true,        (bool) Only returned if imported addresses were involved in transaction\n"
            "    \"address\" : \"receivingaddress\",  (string) The receiving address\n"
            "    \"account\" : \"accountname\",       (string) DEPRECATED. The account of the receiving address. The default account is \"\".\n"
            "    \"amount\" : x.xxx,                  (numeric) The total amount in " + CURRENCY_UNIT + " received by the address\n"
            "    \"confirmations\" : n,               (numeric) The number of confirmations of the most recent transaction included\n"
            "    \"label\" : \"label\",               (string) A comment for the address/transaction, if any\n"
            "    \"txids\": [\n"
            "       n,                                (numeric) The ids of transactions received with the address \n"
            "       ...\n"
            "    ]\n"
            "  }\n"
            "  ,...\n"
            "]\n"

            "\nExamples:\n"
            + HelpExampleCli("listreceivedbyaddress", "")
            + HelpExampleCli("listreceivedbyaddress", "6 true")
            + HelpExampleRpc("listreceivedbyaddress", "6, true, true")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    return ListReceived(request.params, false);
}

UniValue listreceivedbyaccount(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() > 3)
        throw runtime_error(
            "listreceivedbyaccount ( minconf include_empty include_watchonly)\n"
            "\nDEPRECATED. List balances by account.\n"
            "\nArguments:\n"
            "1. minconf           (numeric, optional, default=1) The minimum number of confirmations before payments are included.\n"
            "2. include_empty     (bool, optional, default=false) Whether to include accounts that haven't received any payments.\n"
            "3. include_watchonly (bool, optional, default=false) Whether to include watch-only addresses (see 'importaddress').\n"

            "\nResult:\n"
            "[\n"
            "  {\n"
            "    \"involvesWatchonly\" : true,   (bool) Only returned if imported addresses were involved in transaction\n"
            "    \"account\" : \"accountname\",  (string) The account name of the receiving account\n"
            "    \"amount\" : x.xxx,             (numeric) The total amount received by addresses with this account\n"
            "    \"confirmations\" : n,          (numeric) The number of confirmations of the most recent transaction included\n"
            "    \"label\" : \"label\"           (string) A comment for the address/transaction, if any\n"
            "  }\n"
            "  ,...\n"
            "]\n"

            "\nExamples:\n"
            + HelpExampleCli("listreceivedbyaccount", "")
            + HelpExampleCli("listreceivedbyaccount", "6 true")
            + HelpExampleRpc("listreceivedbyaccount", "6, true, true")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    return ListReceived(request.params, true);
}

static void MaybePushAddress(UniValue & entry, const CTxDestination &dest, const CPubKey& confidentiality_pubkey)
{
    CBitcoinAddress addr;
    if (addr.Set(dest)) {
        entry.push_back(Pair("address", addr.ToString()));
    }
}

void ListTransactions(const CWalletTx& wtx, const string& strAccount, int nMinDepth, bool fLong, UniValue& ret, const isminefilter& filter)
{
    CAmount nFee;
    string strSentAccount;
    list<COutputEntry> listReceived;
    list<COutputEntry> listSent;

    wtx.GetAmounts(listReceived, listSent, nFee, strSentAccount, filter);

    bool fAllAccounts = (strAccount == string("*"));
    bool involvesWatchonly = wtx.IsFromMe(ISMINE_WATCH_ONLY);

    // Sent
    if ((!listSent.empty() || nFee != 0) && (fAllAccounts || strAccount == strSentAccount))
    {
        BOOST_FOREACH(const COutputEntry& s, listSent)
        {
            UniValue entry(UniValue::VOBJ);
            if(involvesWatchonly || (::IsMine(*pwalletMain, s.destination) & ISMINE_WATCH_ONLY))
                entry.push_back(Pair("involvesWatchonly", true));
            entry.push_back(Pair("account", strSentAccount));
            MaybePushAddress(entry, s.destination, s.confidentiality_pubkey);
            entry.push_back(Pair("category", "send"));
            entry.push_back(Pair("amount", ValueFromAmount(-s.amount)));
            entry.push_back(Pair("amountblinder", s.amountBlindingFactor.GetHex()));
            entry.push_back(Pair("asset", s.asset.GetHex()));
            entry.push_back(Pair("assetblinder", s.assetBlindingFactor.GetHex()));
            if (pwalletMain->mapAddressBook.count(s.destination))
                entry.push_back(Pair("label", pwalletMain->mapAddressBook[s.destination].name));
            entry.push_back(Pair("vout", s.vout));
            entry.push_back(Pair("fee", ValueFromAmount(-nFee)));
            if (fLong)
                WalletTxToJSON(wtx, entry);
            entry.push_back(Pair("abandoned", wtx.isAbandoned()));
            ret.push_back(entry);
        }
    }

    // Received
    if (listReceived.size() > 0 && wtx.GetDepthInMainChain() >= nMinDepth)
    {
        BOOST_FOREACH(const COutputEntry& r, listReceived)
        {
            string account;
            if (pwalletMain->mapAddressBook.count(r.destination))
                account = pwalletMain->mapAddressBook[r.destination].name;
            if (fAllAccounts || (account == strAccount))
            {
                UniValue entry(UniValue::VOBJ);
                if(involvesWatchonly || (::IsMine(*pwalletMain, r.destination) & ISMINE_WATCH_ONLY))
                    entry.push_back(Pair("involvesWatchonly", true));
                entry.push_back(Pair("account", account));
                MaybePushAddress(entry, r.destination, r.confidentiality_pubkey);
                if (wtx.IsCoinBase())
                {
                    if (wtx.GetDepthInMainChain() < 1)
                        entry.push_back(Pair("category", "orphan"));
                    else if (wtx.GetBlocksToMaturity() > 0)
                        entry.push_back(Pair("category", "immature"));
                    else
                        entry.push_back(Pair("category", "generate"));
                }
                else
                {
                    entry.push_back(Pair("category", "receive"));
                }
                entry.push_back(Pair("amount", ValueFromAmount(r.amount)));
                entry.push_back(Pair("amountblinder", r.amountBlindingFactor.GetHex()));
                entry.push_back(Pair("asset", r.asset.GetHex()));
                entry.push_back(Pair("assetblinder", r.assetBlindingFactor.GetHex()));
                if (pwalletMain->mapAddressBook.count(r.destination))
                    entry.push_back(Pair("label", account));
                entry.push_back(Pair("vout", r.vout));
                if (fLong)
                    WalletTxToJSON(wtx, entry);
                ret.push_back(entry);
            }
        }
    }
}

void AcentryToJSON(const CAccountingEntry& acentry, const string& strAccount, UniValue& ret)
{
    bool fAllAccounts = (strAccount == string("*"));

    if (fAllAccounts || acentry.strAccount == strAccount)
    {
        UniValue entry(UniValue::VOBJ);
        entry.push_back(Pair("account", acentry.strAccount));
        entry.push_back(Pair("category", "move"));
        entry.push_back(Pair("time", acentry.nTime));
        entry.push_back(Pair("amount", ValueFromAmount(acentry.nCreditDebit)));
        entry.push_back(Pair("otheraccount", acentry.strOtherAccount));
        entry.push_back(Pair("comment", acentry.strComment));
        ret.push_back(entry);
    }
}

UniValue listtransactions(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() > 4)
        throw runtime_error(
            "listtransactions ( \"account\" count skip include_watchonly)\n"
            "\nReturns up to 'count' most recent transactions skipping the first 'from' transactions for account 'account'.\n"
            "\nArguments:\n"
            "1. \"account\"    (string, optional) DEPRECATED. The account name. Should be \"*\".\n"
            "2. count          (numeric, optional, default=10) The number of transactions to return\n"
            "3. skip           (numeric, optional, default=0) The number of transactions to skip\n"
            "4. include_watchonly (bool, optional, default=false) Include transactions to watch-only addresses (see 'importaddress')\n"
            "\nResult:\n"
            "[\n"
            "  {\n"
            "    \"account\":\"accountname\",       (string) DEPRECATED. The account name associated with the transaction. \n"
            "                                                It will be \"\" for the default account.\n"
            "    \"address\":\"address\",    (string) The bitcoin address of the transaction. Not present for \n"
            "                                                move transactions (category = move).\n"
            "    \"category\":\"send|receive|move\", (string) The transaction category. 'move' is a local (off blockchain)\n"
            "                                                transaction between accounts, and not associated with an address,\n"
            "                                                transaction id or block. 'send' and 'receive' transactions are \n"
            "                                                associated with an address, transaction id and block details\n"
            "    \"amount\": x.xxx,          (numeric) The amount in " + CURRENCY_UNIT + ". This is negative for the 'send' category, and for the\n"
            "                                         'move' category for moves outbound. It is positive for the 'receive' category,\n"
            "    \"asset\"                 (string) The asset id of the amount being moved.)\n"
            "                                         and for the 'move' category for inbound funds.\n"
            "    \"label\": \"label\",       (string) A comment for the address/transaction, if any\n"
            "    \"vout\": n,                (numeric) the vout value\n"
            "    \"fee\": x.xxx,             (numeric) The amount of the fee in " + CURRENCY_UNIT + ". This is negative and only available for the \n"
            "                                         'send' category of transactions.\n"
            "    \"confirmations\": n,       (numeric) The number of confirmations for the transaction. Available for 'send' and \n"
            "                                         'receive' category of transactions. Negative confirmations indicate the\n"
            "                                         transaction conflicts with the block chain\n"
            "    \"trusted\": xxx,           (bool) Whether we consider the outputs of this unconfirmed transaction safe to spend.\n"
            "    \"blockhash\": \"hashvalue\", (string) The block hash containing the transaction. Available for 'send' and 'receive'\n"
            "                                          category of transactions.\n"
            "    \"blockindex\": n,          (numeric) The index of the transaction in the block that includes it. Available for 'send' and 'receive'\n"
            "                                          category of transactions.\n"
            "    \"blocktime\": xxx,         (numeric) The block time in seconds since epoch (1 Jan 1970 GMT).\n"
            "    \"txid\": \"transactionid\", (string) The transaction id. Available for 'send' and 'receive' category of transactions.\n"
            "    \"time\": xxx,              (numeric) The transaction time in seconds since epoch (midnight Jan 1 1970 GMT).\n"
            "    \"timereceived\": xxx,      (numeric) The time received in seconds since epoch (midnight Jan 1 1970 GMT). Available \n"
            "                                          for 'send' and 'receive' category of transactions.\n"
            "    \"comment\": \"...\",       (string) If a comment is associated with the transaction.\n"
            "    \"otheraccount\": \"accountname\",  (string) DEPRECATED. For the 'move' category of transactions, the account the funds came \n"
            "                                          from (for receiving funds, positive amounts), or went to (for sending funds,\n"
            "                                          negative amounts).\n"
            "    \"bip125-replaceable\": \"yes|no|unknown\",  (string) Whether this transaction could be replaced due to BIP125 (replace-by-fee);\n"
            "    \"blindingfactors\": \"...\"  (string) The list of blinding factors for a given transaction in vout order\n"
            "                                                     may be unknown for unconfirmed transactions not in the mempool\n"
            "    \"abandoned\": xxx          (bool) 'true' if the transaction has been abandoned (inputs are respendable). Only available for the \n"
            "                                         'send' category of transactions.\n"
            "  }\n"
            "]\n"

            "\nExamples:\n"
            "\nList the most recent 10 transactions in the systems\n"
            + HelpExampleCli("listtransactions", "") +
            "\nList transactions 100 to 120\n"
            + HelpExampleCli("listtransactions", "\"*\" 20 100") +
            "\nAs a json rpc call\n"
            + HelpExampleRpc("listtransactions", "\"*\", 20, 100")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    string strAccount = "*";
    if (request.params.size() > 0)
        strAccount = request.params[0].get_str();
    int nCount = 10;
    if (request.params.size() > 1)
        nCount = request.params[1].get_int();
    int nFrom = 0;
    if (request.params.size() > 2)
        nFrom = request.params[2].get_int();
    isminefilter filter = ISMINE_SPENDABLE;
    if(request.params.size() > 3)
        if(request.params[3].get_bool())
            filter = filter | ISMINE_WATCH_ONLY;

    if (nCount < 0)
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Negative count");
    if (nFrom < 0)
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Negative from");

    UniValue ret(UniValue::VARR);

    const CWallet::TxItems & txOrdered = pwalletMain->wtxOrdered;

    // iterate backwards until we have nCount items to return:
    for (CWallet::TxItems::const_reverse_iterator it = txOrdered.rbegin(); it != txOrdered.rend(); ++it)
    {
        CWalletTx *const pwtx = (*it).second.first;
        if (pwtx != 0)
            ListTransactions(*pwtx, strAccount, 0, true, ret, filter);
        CAccountingEntry *const pacentry = (*it).second.second;
        if (pacentry != 0)
            AcentryToJSON(*pacentry, strAccount, ret);

        if ((int)ret.size() >= (nCount+nFrom)) break;
    }
    // ret is newest to oldest

    if (nFrom > (int)ret.size())
        nFrom = ret.size();
    if ((nFrom + nCount) > (int)ret.size())
        nCount = ret.size() - nFrom;

    vector<UniValue> arrTmp = ret.getValues();

    vector<UniValue>::iterator first = arrTmp.begin();
    std::advance(first, nFrom);
    vector<UniValue>::iterator last = arrTmp.begin();
    std::advance(last, nFrom+nCount);

    if (last != arrTmp.end()) arrTmp.erase(last, arrTmp.end());
    if (first != arrTmp.begin()) arrTmp.erase(arrTmp.begin(), first);

    std::reverse(arrTmp.begin(), arrTmp.end()); // Return oldest to newest

    ret.clear();
    ret.setArray();
    ret.push_backV(arrTmp);

    return ret;
}

UniValue listaccounts(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() > 2)
        throw runtime_error(
            "listaccounts ( minconf include_watchonly)\n"
            "\nDEPRECATED. Returns Object that has account names as keys, account balances as values.\n"
            "\nArguments:\n"
            "1. minconf             (numeric, optional, default=1) Only include transactions with at least this many confirmations\n"
            "2. include_watchonly   (bool, optional, default=false) Include balances in watch-only addresses (see 'importaddress')\n"
            "\nResult:\n"
            "{                      (json object where keys are account names, and values are numeric balances\n"
            "  \"account\": x.xxx,  (numeric) The property name is the account name, and the value is the total balance for the account.\n"
            "  ...\n"
            "}\n"
            "\nExamples:\n"
            "\nList account balances where there at least 1 confirmation\n"
            + HelpExampleCli("listaccounts", "") +
            "\nList account balances including zero confirmation transactions\n"
            + HelpExampleCli("listaccounts", "0") +
            "\nList account balances for 6 or more confirmations\n"
            + HelpExampleCli("listaccounts", "6") +
            "\nAs json rpc call\n"
            + HelpExampleRpc("listaccounts", "6")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    int nMinDepth = 1;
    if (request.params.size() > 0)
        nMinDepth = request.params[0].get_int();
    isminefilter includeWatchonly = ISMINE_SPENDABLE;
    if(request.params.size() > 1)
        if(request.params[1].get_bool())
            includeWatchonly = includeWatchonly | ISMINE_WATCH_ONLY;

    map<string, CAmount> mapAccountBalances;
    BOOST_FOREACH(const PAIRTYPE(CTxDestination, CAddressBookData)& entry, pwalletMain->mapAddressBook) {
        if (IsMine(*pwalletMain, entry.first) & includeWatchonly) // This address belongs to me
            mapAccountBalances[entry.second.name] = 0;
    }

    for (map<uint256, CWalletTx>::iterator it = pwalletMain->mapWallet.begin(); it != pwalletMain->mapWallet.end(); ++it)
    {
        const CWalletTx& wtx = (*it).second;
        CAmount nFee;
        string strSentAccount;
        list<COutputEntry> listReceived;
        list<COutputEntry> listSent;
        int nDepth = wtx.GetDepthInMainChain();
        if (wtx.GetBlocksToMaturity() > 0 || nDepth < 0)
            continue;
        wtx.GetAmounts(listReceived, listSent, nFee, strSentAccount, includeWatchonly);
        mapAccountBalances[strSentAccount] -= nFee;
        BOOST_FOREACH(const COutputEntry& s, listSent)
            mapAccountBalances[strSentAccount] -= s.amount;
        if (nDepth >= nMinDepth)
        {
            BOOST_FOREACH(const COutputEntry& r, listReceived)
                if (pwalletMain->mapAddressBook.count(r.destination))
                    mapAccountBalances[pwalletMain->mapAddressBook[r.destination].name] += r.amount;
                else
                    mapAccountBalances[""] += r.amount;
        }
    }

    const list<CAccountingEntry> & acentries = pwalletMain->laccentries;
    BOOST_FOREACH(const CAccountingEntry& entry, acentries)
        mapAccountBalances[entry.strAccount] += entry.nCreditDebit;

    UniValue ret(UniValue::VOBJ);
    BOOST_FOREACH(const PAIRTYPE(string, CAmount)& accountBalance, mapAccountBalances) {
        ret.push_back(Pair(accountBalance.first, ValueFromAmount(accountBalance.second)));
    }
    return ret;
}

UniValue listsinceblock(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp)
        throw runtime_error(
            "listsinceblock ( \"blockhash\" target_confirmations include_watchonly)\n"
            "\nGet all transactions in blocks since block [blockhash], or all transactions if omitted\n"
            "\nArguments:\n"
            "1. \"blockhash\"            (string, optional) The block hash to list transactions since\n"
            "2. target_confirmations:    (numeric, optional) The confirmations required, must be 1 or more\n"
            "3. include_watchonly:       (bool, optional, default=false) Include transactions to watch-only addresses (see 'importaddress')"
            "\nResult:\n"
            "{\n"
            "  \"transactions\": [\n"
            "    \"account\":\"accountname\",       (string) DEPRECATED. The account name associated with the transaction. Will be \"\" for the default account.\n"
            "    \"address\":\"address\",    (string) The bitcoin address of the transaction. Not present for move transactions (category = move).\n"
            "    \"category\":\"send|receive\",     (string) The transaction category. 'send' has negative amounts, 'receive' has positive amounts.\n"
            "    \"amount\": x.xxx,          (numeric) The amount in " + CURRENCY_UNIT + ". This is negative for the 'send' category, and for the 'move' category for moves \n"
            "                                          outbound. It is positive for the 'receive' category, and for the 'move' category for inbound funds.\n"
            "    \"vout\" : n,               (numeric) the vout value\n"
            "    \"fee\": x.xxx,             (numeric) The amount of the fee in " + CURRENCY_UNIT + ". This is negative and only available for the 'send' category of transactions.\n"
            "    \"confirmations\": n,       (numeric) The number of confirmations for the transaction. Available for 'send' and 'receive' category of transactions.\n"
            "                                          When it's < 0, it means the transaction conflicted that many blocks ago.\n"
            "    \"blockhash\": \"hashvalue\",     (string) The block hash containing the transaction. Available for 'send' and 'receive' category of transactions.\n"
            "    \"blockindex\": n,          (numeric) The index of the transaction in the block that includes it. Available for 'send' and 'receive' category of transactions.\n"
            "    \"blocktime\": xxx,         (numeric) The block time in seconds since epoch (1 Jan 1970 GMT).\n"
            "    \"txid\": \"transactionid\",  (string) The transaction id. Available for 'send' and 'receive' category of transactions.\n"
            "    \"time\": xxx,              (numeric) The transaction time in seconds since epoch (Jan 1 1970 GMT).\n"
            "    \"timereceived\": xxx,      (numeric) The time received in seconds since epoch (Jan 1 1970 GMT). Available for 'send' and 'receive' category of transactions.\n"
            "    \"bip125-replaceable\": \"yes|no|unknown\",  (string) Whether this transaction could be replaced due to BIP125 (replace-by-fee);\n"
            "                                                   may be unknown for unconfirmed transactions not in the mempool\n"
            "    \"abandoned\": xxx,         (bool) 'true' if the transaction has been abandoned (inputs are respendable). Only available for the 'send' category of transactions.\n"
            "    \"comment\": \"...\",       (string) If a comment is associated with the transaction.\n"
            "    \"label\" : \"label\"       (string) A comment for the address/transaction, if any\n"
            "    \"to\": \"...\",            (string) If a comment to is associated with the transaction.\n"
             "  ],\n"
            "  \"lastblock\": \"lastblockhash\"     (string) The hash of the last block\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("listsinceblock", "")
            + HelpExampleCli("listsinceblock", "\"000000000000000bacf66f7497b7dc45ef753ee9a7d38571037cdb1a57f663ad\" 6")
            + HelpExampleRpc("listsinceblock", "\"000000000000000bacf66f7497b7dc45ef753ee9a7d38571037cdb1a57f663ad\", 6")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    const CBlockIndex *pindex = NULL;
    int target_confirms = 1;
    isminefilter filter = ISMINE_SPENDABLE;

    if (request.params.size() > 0)
    {
        uint256 blockId;

        blockId.SetHex(request.params[0].get_str());
        BlockMap::iterator it = mapBlockIndex.find(blockId);
        if (it != mapBlockIndex.end())
        {
            pindex = it->second;
            if (chainActive[pindex->nHeight] != pindex)
            {
                // the block being asked for is a part of a deactivated chain;
                // we don't want to depend on its perceived height in the block
                // chain, we want to instead use the last common ancestor
                pindex = chainActive.FindFork(pindex);
            }
        }
    }

    if (request.params.size() > 1)
    {
        target_confirms = request.params[1].get_int();

        if (target_confirms < 1)
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter");
    }

    if (request.params.size() > 2 && request.params[2].get_bool())
    {
        filter = filter | ISMINE_WATCH_ONLY;
    }

    int depth = pindex ? (1 + chainActive.Height() - pindex->nHeight) : -1;

    UniValue transactions(UniValue::VARR);

    for (map<uint256, CWalletTx>::iterator it = pwalletMain->mapWallet.begin(); it != pwalletMain->mapWallet.end(); it++)
    {
        CWalletTx tx = (*it).second;

        if (depth == -1 || tx.GetDepthInMainChain() < depth)
            ListTransactions(tx, "*", 0, true, transactions, filter);
    }

    CBlockIndex *pblockLast = chainActive[chainActive.Height() + 1 - target_confirms];
    uint256 lastblock = pblockLast ? pblockLast->GetBlockHash() : uint256();

    UniValue ret(UniValue::VOBJ);
    ret.push_back(Pair("transactions", transactions));
    ret.push_back(Pair("lastblock", lastblock.GetHex()));

    return ret;
}

UniValue gettransaction(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 1 || request.params.size() > 3)
        throw runtime_error(
            "gettransaction \"txid\" ( include_watchonly assetlabel )\n"
            "\nGet detailed information about in-wallet transaction <txid>\n"
            "\nArguments:\n"
            "1. \"txid\"                  (string, required) The transaction id\n"
            "2. \"include_watchonly\"     (bool, optional, default=false) Whether to include watch-only addresses in balance calculation and details[]\n"
            "3. \"assetlabel\"          (string, optional, default=bitcoin) Hex asset id or asset label for balance. \"*\" retrieves all known asset balances.\n"
            "\nResult:\n"
            "{\n"
            "  \"amount\" : x.xxx,        (numeric) The transaction amount in " + CURRENCY_UNIT + "\n"
            "  \"fee\": x.xxx,            (numeric) The amount of the fee in " + CURRENCY_UNIT + ". This is negative and only available for the \n"
            "                              'send' category of transactions.\n"
            "  \"confirmations\" : n,     (numeric) The number of confirmations\n"
            "  \"blockhash\" : \"hash\",  (string) The block hash\n"
            "  \"blockindex\" : xx,       (numeric) The index of the transaction in the block that includes it\n"
            "  \"blocktime\" : ttt,       (numeric) The time in seconds since epoch (1 Jan 1970 GMT)\n"
            "  \"txid\" : \"transactionid\",   (string) The transaction id.\n"
            "  \"time\" : ttt,            (numeric) The transaction time in seconds since epoch (1 Jan 1970 GMT)\n"
            "  \"timereceived\" : ttt,    (numeric) The time received in seconds since epoch (1 Jan 1970 GMT)\n"
            "  \"bip125-replaceable\": \"yes|no|unknown\",  (string) Whether this transaction could be replaced due to BIP125 (replace-by-fee);\n"
            "                                                   may be unknown for unconfirmed transactions not in the mempool\n"
            "  \"details\" : [\n"
            "    {\n"
            "      \"account\" : \"accountname\",      (string) DEPRECATED. The account name involved in the transaction, can be \"\" for the default account.\n"
            "      \"address\" : \"address\",          (string) The bitcoin address involved in the transaction\n"
            "      \"category\" : \"send|receive\",    (string) The category, either 'send' or 'receive'\n"
            "      \"amount\" : x.xxx,                 (numeric) The amount in the asset below\n"
            "      \"amountblinder\": \"hex\"            (string) The blinding factor of the amount.\n"
            "      \"asset\": \"asset\"                (string) The asset id.\n"
            "      \"assetblinder\": \"hex\"             (string) The blinding factor of the asset.\n"
            "      \"label\" : \"label\",              (string) A comment for the address/transaction, if any\n"
            "      \"vout\" : n,                       (numeric) the vout value\n"
            "      \"fee\": x.xxx,                     (numeric) The amount of the fee in " + CURRENCY_UNIT + ". This is negative and only available for the \n"
            "                                           'send' category of transactions.\n"
            "      \"abandoned\": xxx                  (bool) 'true' if the transaction has been abandoned (inputs are respendable). Only available for the \n"
            "                                           'send' category of transactions.\n"
            "    }\n"
            "    ,...\n"
            "  ],\n"
            "  \"hex\" : \"data\"         (string) Raw data for transaction\n"
            "}\n"

            "\nExamples:\n"
            + HelpExampleCli("gettransaction", "\"1075db55d416d3ca199f55b6084e2115b9345e16c5cf302fc80e9d5fbf5d48d\"")
            + HelpExampleCli("gettransaction", "\"1075db55d416d3ca199f55b6084e2115b9345e16c5cf302fc80e9d5fbf5d48d\" true")
            + HelpExampleRpc("gettransaction", "\"1075db55d416d3ca199f55b6084e2115b9345e16c5cf302fc80e9d5fbf5d48d\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    uint256 hash;
    hash.SetHex(request.params[0].get_str());

    isminefilter filter = ISMINE_SPENDABLE;
    if(request.params.size() > 1)
        if(request.params[1].get_bool())
            filter = filter | ISMINE_WATCH_ONLY;

    std::string strasset = "";
    if (request.params.size() > 2) {
        strasset = request.params[2].get_str();
    }

    UniValue entry(UniValue::VOBJ);
    if (!pwalletMain->mapWallet.count(hash))
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid or non-wallet transaction id");
    const CWalletTx& wtx = pwalletMain->mapWallet[hash];

    CAmountMap nCredit = wtx.GetCredit(filter);
    CAmountMap nDebit = wtx.GetDebit(filter);
    assert(wtx.tx->HasValidFee());
    CAmount nFee = (wtx.IsFromMe(filter) ? -wtx.tx->GetFee().begin()->second : 0);
    CAmountMap nNet = nCredit - nDebit;
    nNet[wtx.tx->GetFee().begin()->first] -= nFee;

    entry.push_back(Pair("amount", PushAssetBalance(nNet, pwalletMain, strasset)));
    if (wtx.IsFromMe(filter))
        entry.push_back(Pair("fee", ValueFromAmount(nFee)));

    WalletTxToJSON(wtx, entry);

    UniValue details(UniValue::VARR);
    ListTransactions(wtx, "*", 0, false, details, filter);
    entry.push_back(Pair("details", details));

    string strHex = EncodeHexTx(static_cast<CTransaction>(wtx), RPCSerializationFlags());
    entry.push_back(Pair("hex", strHex));

    return entry;
}

UniValue abandontransaction(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "abandontransaction \"txid\"\n"
            "\nMark in-wallet transaction <txid> as abandoned\n"
            "This will mark this transaction and all its in-wallet descendants as abandoned which will allow\n"
            "for their inputs to be respent.  It can be used to replace \"stuck\" or evicted transactions.\n"
            "It only works on transactions which are not included in a block and are not currently in the mempool.\n"
            "It has no effect on transactions which are already conflicted or abandoned.\n"
            "\nArguments:\n"
            "1. \"txid\"    (string, required) The transaction id\n"
            "\nResult:\n"
            "\nExamples:\n"
            + HelpExampleCli("abandontransaction", "\"1075db55d416d3ca199f55b6084e2115b9345e16c5cf302fc80e9d5fbf5d48d\"")
            + HelpExampleRpc("abandontransaction", "\"1075db55d416d3ca199f55b6084e2115b9345e16c5cf302fc80e9d5fbf5d48d\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    uint256 hash;
    hash.SetHex(request.params[0].get_str());

    if (!pwalletMain->mapWallet.count(hash))
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid or non-wallet transaction id");
    if (!pwalletMain->AbandonTransaction(hash))
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Transaction not eligible for abandonment");

    return NullUniValue;
}


UniValue backupwallet(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "backupwallet \"destination\"\n"
            "\nSafely copies current wallet file to destination, which can be a directory or a path with filename.\n"
            "\nArguments:\n"
            "1. \"destination\"   (string) The destination directory or file\n"
            "\nExamples:\n"
            + HelpExampleCli("backupwallet", "\"backup.dat\"")
            + HelpExampleRpc("backupwallet", "\"backup.dat\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    string strDest = request.params[0].get_str();
    if (!pwalletMain->BackupWallet(strDest))
        throw JSONRPCError(RPC_WALLET_ERROR, "Error: Wallet backup failed!");

    AuditLogPrintf("%s : backupwallet %s\n", getUser(), strDest);

    return NullUniValue;
}


UniValue keypoolrefill(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() > 1)
        throw runtime_error(
            "keypoolrefill ( newsize )\n"
            "\nFills the keypool."
            + HelpRequiringPassphrase() + "\n"
            "\nArguments\n"
            "1. newsize     (numeric, optional, default=100) The new keypool size\n"
            "\nExamples:\n"
            + HelpExampleCli("keypoolrefill", "")
            + HelpExampleRpc("keypoolrefill", "")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    // 0 is interpreted by TopUpKeyPool() as the default keypool size given by -keypool
    unsigned int kpSize = 0;
    if (request.params.size() > 0) {
        if (request.params[0].get_int() < 0)
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, expected valid size.");
        kpSize = (unsigned int)request.params[0].get_int();
    }

    EnsureWalletIsUnlocked();
    pwalletMain->TopUpKeyPool(kpSize);

    if (pwalletMain->GetKeyPoolSize() < kpSize)
        throw JSONRPCError(RPC_WALLET_ERROR, "Error refreshing keypool.");

    return NullUniValue;
}


static void LockWallet(CWallet* pWallet)
{
    LOCK(cs_nWalletUnlockTime);
    nWalletUnlockTime = 0;
    pWallet->Lock();
}

UniValue walletpassphrase(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (pwalletMain->IsCrypted() && (request.fHelp || request.params.size() != 2))
        throw runtime_error(
            "walletpassphrase \"passphrase\" timeout\n"
            "\nStores the wallet decryption key in memory for 'timeout' seconds.\n"
            "This is needed prior to performing transactions related to private keys such as sending bitcoins\n"
            "\nArguments:\n"
            "1. \"passphrase\"     (string, required) The wallet passphrase\n"
            "2. timeout            (numeric, required) The time to keep the decryption key in seconds.\n"
            "\nNote:\n"
            "Issuing the walletpassphrase command while the wallet is already unlocked will set a new unlock\n"
            "time that overrides the old one.\n"
            "\nExamples:\n"
            "\nunlock the wallet for 60 seconds\n"
            + HelpExampleCli("walletpassphrase", "\"my pass phrase\" 60") +
            "\nLock the wallet again (before 60 seconds)\n"
            + HelpExampleCli("walletlock", "") +
            "\nAs json rpc call\n"
            + HelpExampleRpc("walletpassphrase", "\"my pass phrase\", 60")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    if (request.fHelp)
        return true;
    if (!pwalletMain->IsCrypted())
        throw JSONRPCError(RPC_WALLET_WRONG_ENC_STATE, "Error: running with an unencrypted wallet, but walletpassphrase was called.");

    // Note that the walletpassphrase is stored in request.params[0] which is not mlock()ed
    SecureString strWalletPass;
    strWalletPass.reserve(100);
    // TODO: get rid of this .c_str() by implementing SecureString::operator=(std::string)
    // Alternately, find a way to make request.params[0] mlock()'d to begin with.
    strWalletPass = request.params[0].get_str().c_str();

    if (strWalletPass.length() > 0)
    {
        if (!pwalletMain->Unlock(strWalletPass))
            throw JSONRPCError(RPC_WALLET_PASSPHRASE_INCORRECT, "Error: The wallet passphrase entered was incorrect.");
    }
    else
        throw runtime_error(
            "walletpassphrase <passphrase> <timeout>\n"
            "Stores the wallet decryption key in memory for <timeout> seconds.");

    pwalletMain->TopUpKeyPool();

    int64_t nSleepTime = request.params[1].get_int64();
    LOCK(cs_nWalletUnlockTime);
    nWalletUnlockTime = GetTime() + nSleepTime;
    RPCRunLater("lockwallet", boost::bind(LockWallet, pwalletMain), nSleepTime);

    AuditLogPrintf("%s : walletpassphrase\n", getUser());

    return NullUniValue;
}


UniValue walletpassphrasechange(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (pwalletMain->IsCrypted() && (request.fHelp || request.params.size() != 2))
        throw runtime_error(
            "walletpassphrasechange \"oldpassphrase\" \"newpassphrase\"\n"
            "\nChanges the wallet passphrase from 'oldpassphrase' to 'newpassphrase'.\n"
            "\nArguments:\n"
            "1. \"oldpassphrase\"      (string) The current passphrase\n"
            "2. \"newpassphrase\"      (string) The new passphrase\n"
            "\nExamples:\n"
            + HelpExampleCli("walletpassphrasechange", "\"old one\" \"new one\"")
            + HelpExampleRpc("walletpassphrasechange", "\"old one\", \"new one\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    if (request.fHelp)
        return true;
    if (!pwalletMain->IsCrypted())
        throw JSONRPCError(RPC_WALLET_WRONG_ENC_STATE, "Error: running with an unencrypted wallet, but walletpassphrasechange was called.");

    // TODO: get rid of these .c_str() calls by implementing SecureString::operator=(std::string)
    // Alternately, find a way to make request.params[0] mlock()'d to begin with.
    SecureString strOldWalletPass;
    strOldWalletPass.reserve(100);
    strOldWalletPass = request.params[0].get_str().c_str();

    SecureString strNewWalletPass;
    strNewWalletPass.reserve(100);
    strNewWalletPass = request.params[1].get_str().c_str();

    if (strOldWalletPass.length() < 1 || strNewWalletPass.length() < 1)
        throw runtime_error(
            "walletpassphrasechange <oldpassphrase> <newpassphrase>\n"
            "Changes the wallet passphrase from <oldpassphrase> to <newpassphrase>.");

    if (!pwalletMain->ChangeWalletPassphrase(strOldWalletPass, strNewWalletPass))
        throw JSONRPCError(RPC_WALLET_PASSPHRASE_INCORRECT, "Error: The wallet passphrase entered was incorrect.");

    AuditLogPrintf("%s : walletpassphrasechange\n", getUser());

    return NullUniValue;
}


UniValue walletlock(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (pwalletMain->IsCrypted() && (request.fHelp || request.params.size() != 0))
        throw runtime_error(
            "walletlock\n"
            "\nRemoves the wallet encryption key from memory, locking the wallet.\n"
            "After calling this method, you will need to call walletpassphrase again\n"
            "before being able to call any methods which require the wallet to be unlocked.\n"
            "\nExamples:\n"
            "\nSet the passphrase for 2 minutes to perform a transaction\n"
            + HelpExampleCli("walletpassphrase", "\"my pass phrase\" 120") +
            "\nPerform a send (requires passphrase set)\n"
            + HelpExampleCli("sendtoaddress", "\"1M72Sfpbz1BPpXFHz9m3CdqATR44Jvaydd\" 1.0") +
            "\nClear the passphrase since we are done before 2 minutes is up\n"
            + HelpExampleCli("walletlock", "") +
            "\nAs json rpc call\n"
            + HelpExampleRpc("walletlock", "")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    if (request.fHelp)
        return true;
    if (!pwalletMain->IsCrypted())
        throw JSONRPCError(RPC_WALLET_WRONG_ENC_STATE, "Error: running with an unencrypted wallet, but walletlock was called.");

    {
        LOCK(cs_nWalletUnlockTime);
        pwalletMain->Lock();
        nWalletUnlockTime = 0;
    }

    return NullUniValue;
}


UniValue encryptwallet(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (!pwalletMain->IsCrypted() && (request.fHelp || request.params.size() != 1))
        throw runtime_error(
            "encryptwallet \"passphrase\"\n"
            "\nEncrypts the wallet with 'passphrase'. This is for first time encryption.\n"
            "After this, any calls that interact with private keys such as sending or signing \n"
            "will require the passphrase to be set prior the making these calls.\n"
            "Use the walletpassphrase call for this, and then walletlock call.\n"
            "If the wallet is already encrypted, use the walletpassphrasechange call.\n"
            "Note that this will shutdown the server.\n"
            "\nArguments:\n"
            "1. \"passphrase\"    (string) The pass phrase to encrypt the wallet with. It must be at least 1 character, but should be long.\n"
            "\nExamples:\n"
            "\nEncrypt you wallet\n"
            + HelpExampleCli("encryptwallet", "\"my pass phrase\"") +
            "\nNow set the passphrase to use the wallet, such as for signing or sending bitcoin\n"
            + HelpExampleCli("walletpassphrase", "\"my pass phrase\"") +
            "\nNow we can so something like sign\n"
            + HelpExampleCli("signmessage", "\"address\" \"test message\"") +
            "\nNow lock the wallet again by removing the passphrase\n"
            + HelpExampleCli("walletlock", "") +
            "\nAs a json rpc call\n"
            + HelpExampleRpc("encryptwallet", "\"my pass phrase\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    if (request.fHelp)
        return true;
    if (pwalletMain->IsCrypted())
        throw JSONRPCError(RPC_WALLET_WRONG_ENC_STATE, "Error: running with an encrypted wallet, but encryptwallet was called.");

    // TODO: get rid of this .c_str() by implementing SecureString::operator=(std::string)
    // Alternately, find a way to make request.params[0] mlock()'d to begin with.
    SecureString strWalletPass;
    strWalletPass.reserve(100);
    strWalletPass = request.params[0].get_str().c_str();

    if (strWalletPass.length() < 1)
        throw runtime_error(
            "encryptwallet <passphrase>\n"
            "Encrypts the wallet with <passphrase>.");

    if (!pwalletMain->EncryptWallet(strWalletPass))
        throw JSONRPCError(RPC_WALLET_ENCRYPTION_FAILED, "Error: Failed to encrypt the wallet.");

    AuditLogPrintf("%s : encryptwallet\n", getUser());

    // BDB seems to have a bad habit of writing old data into
    // slack space in .dat files; that is bad if the old data is
    // unencrypted private keys. So:
    StartShutdown();
    return "wallet encrypted; Ocean server stopping, restart to run with encrypted wallet. The keypool has been flushed and a new HD seed was generated (if you are using HD). You need to make a new backup.";
}

UniValue lockunspent(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 1 || request.params.size() > 2)
        throw runtime_error(
            "lockunspent unlock ([{\"txid\":\"txid\",\"vout\":n},...])\n"
            "\nUpdates list of temporarily unspendable outputs.\n"
            "Temporarily lock (unlock=false) or unlock (unlock=true) specified transaction outputs.\n"
            "If no transaction outputs are specified when unlocking then all current locked transaction outputs are unlocked.\n"
            "A locked transaction output will not be chosen by automatic coin selection, when spending bitcoins.\n"
            "Locks are stored in memory only. Nodes start with zero locked outputs, and the locked output list\n"
            "is always cleared (by virtue of process exit) when a node stops or fails.\n"
            "Also see the listunspent call\n"
            "\nArguments:\n"
            "1. unlock            (boolean, required) Whether to unlock (true) or lock (false) the specified transactions\n"
            "2. \"transactions\"  (string, optional) A json array of objects. Each object the txid (string) vout (numeric)\n"
            "     [           (json array of json objects)\n"
            "       {\n"
            "         \"txid\":\"id\",    (string) The transaction id\n"
            "         \"vout\": n         (numeric) The output number\n"
            "       }\n"
            "       ,...\n"
            "     ]\n"

            "\nResult:\n"
            "true|false    (boolean) Whether the command was successful or not\n"

            "\nExamples:\n"
            "\nList the unspent transactions\n"
            + HelpExampleCli("listunspent", "") +
            "\nLock an unspent transaction\n"
            + HelpExampleCli("lockunspent", "false \"[{\\\"txid\\\":\\\"a08e6907dbbd3d809776dbfc5d82e371b764ed838b5655e72f463568df1aadf0\\\",\\\"vout\\\":1}]\"") +
            "\nList the locked transactions\n"
            + HelpExampleCli("listlockunspent", "") +
            "\nUnlock the transaction again\n"
            + HelpExampleCli("lockunspent", "true \"[{\\\"txid\\\":\\\"a08e6907dbbd3d809776dbfc5d82e371b764ed838b5655e72f463568df1aadf0\\\",\\\"vout\\\":1}]\"") +
            "\nAs a json rpc call\n"
            + HelpExampleRpc("lockunspent", "false, \"[{\\\"txid\\\":\\\"a08e6907dbbd3d809776dbfc5d82e371b764ed838b5655e72f463568df1aadf0\\\",\\\"vout\\\":1}]\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    if (request.params.size() == 1)
        RPCTypeCheck(request.params, boost::assign::list_of(UniValue::VBOOL));
    else
        RPCTypeCheck(request.params, boost::assign::list_of(UniValue::VBOOL)(UniValue::VARR));

    bool fUnlock = request.params[0].get_bool();

    if (request.params.size() == 1) {
        if (fUnlock)
            pwalletMain->UnlockAllCoins();
        return true;
    }

    UniValue outputs = request.params[1].get_array();
    for (unsigned int idx = 0; idx < outputs.size(); idx++) {
        const UniValue& output = outputs[idx];
        if (!output.isObject())
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, expected object");
        const UniValue& o = output.get_obj();

        RPCTypeCheckObj(o,
            {
                {"txid", UniValueType(UniValue::VSTR)},
                {"vout", UniValueType(UniValue::VNUM)},
            });

        string txid = find_value(o, "txid").get_str();
        if (!IsHex(txid))
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, expected hex txid");

        int nOutput = find_value(o, "vout").get_int();
        if (nOutput < 0)
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, vout must be positive");

        COutPoint outpt(uint256S(txid), nOutput);

        if (fUnlock)
            pwalletMain->UnlockCoin(outpt);
        else
            pwalletMain->LockCoin(outpt);
    }

    return true;
}

UniValue listlockunspent(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() > 0)
        throw runtime_error(
            "listlockunspent\n"
            "\nReturns list of temporarily unspendable outputs.\n"
            "See the lockunspent call to lock and unlock transactions for spending.\n"
            "\nResult:\n"
            "[\n"
            "  {\n"
            "    \"txid\" : \"transactionid\",     (string) The transaction id locked\n"
            "    \"vout\" : n                      (numeric) The vout value\n"
            "  }\n"
            "  ,...\n"
            "]\n"
            "\nExamples:\n"
            "\nList the unspent transactions\n"
            + HelpExampleCli("listunspent", "") +
            "\nLock an unspent transaction\n"
            + HelpExampleCli("lockunspent", "false \"[{\\\"txid\\\":\\\"a08e6907dbbd3d809776dbfc5d82e371b764ed838b5655e72f463568df1aadf0\\\",\\\"vout\\\":1}]\"") +
            "\nList the locked transactions\n"
            + HelpExampleCli("listlockunspent", "") +
            "\nUnlock the transaction again\n"
            + HelpExampleCli("lockunspent", "true \"[{\\\"txid\\\":\\\"a08e6907dbbd3d809776dbfc5d82e371b764ed838b5655e72f463568df1aadf0\\\",\\\"vout\\\":1}]\"") +
            "\nAs a json rpc call\n"
            + HelpExampleRpc("listlockunspent", "")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    vector<COutPoint> vOutpts;
    pwalletMain->ListLockedCoins(vOutpts);

    UniValue ret(UniValue::VARR);

    BOOST_FOREACH(COutPoint &outpt, vOutpts) {
        UniValue o(UniValue::VOBJ);

        o.push_back(Pair("txid", outpt.hash.GetHex()));
        o.push_back(Pair("vout", (int)outpt.n));
        ret.push_back(o);
    }

    return ret;
}

UniValue settxfee(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 1 || request.params.size() > 1)
        throw runtime_error(
            "settxfee amount\n"
            "\nSet the transaction fee per kB. Overwrites the paytxfee parameter.\n"
            "\nArguments:\n"
            "1. amount         (numeric or string, required) The transaction fee in " + CURRENCY_UNIT + "/kB\n"
            "\nResult\n"
            "true|false        (boolean) Returns true if successful\n"
            "\nExamples:\n"
            + HelpExampleCli("settxfee", "0.00001")
            + HelpExampleRpc("settxfee", "0.00001")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    // Amount
    CAmount nAmount = AmountFromValue(request.params[0]);

    payTxFee = CFeeRate(nAmount, 1000);

    AuditLogPrintf("%s : settxfee %s\n", getUser(), request.params[0].getValStr());

    return true;
}

UniValue getwalletinfo(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() > 1)
        throw runtime_error(
            "getwalletinfo ( assetlabel )\n"
            "Returns an object containing various wallet state info.\n"
            "1. \"assetlabel\"               (string, optional) Hex asset id or asset label for balance. \"*\" retrieves all known asset balances.\n"
            "\nResult:\n"
            "{\n"
            "  \"walletversion\": xxxxx,       (numeric) the wallet version\n"
            "  \"balance\": xxxxxxx,           (numeric) the total confirmed balance of the wallet in " + CURRENCY_UNIT + "\n"
            "  \"unconfirmed_balance\": xxx,   (numeric) the total unconfirmed balance of the wallet in " + CURRENCY_UNIT + "\n"
            "  \"immature_balance\": xxxxxx,   (numeric) the total immature balance of the wallet in " + CURRENCY_UNIT + "\n"
            "  \"txcount\": xxxxxxx,           (numeric) the total number of transactions in the wallet\n"
            "  \"keypoololdest\": xxxxxx,      (numeric) the timestamp (seconds since Unix epoch) of the oldest pre-generated key in the key pool\n"
            "  \"keypoolsize\": xxxx,          (numeric) how many new keys are pre-generated\n"
            "  \"unlocked_until\": ttt,        (numeric) the timestamp in seconds since epoch (midnight Jan 1 1970 GMT) that the wallet is unlocked for transfers, or 0 if the wallet is locked\n"
            "  \"paytxfee\": x.xxxx,           (numeric) the transaction fee configuration, set in " + CURRENCY_UNIT + "/kB\n"
            "  \"hdmasterkeyid\": \"<hash160>\" (string) the Hash160 of the HD master pubkey\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("getwalletinfo", "")
            + HelpExampleRpc("getwalletinfo", "")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    UniValue obj(UniValue::VOBJ);
    obj.push_back(Pair("walletversion", pwalletMain->GetVersion()));

    std::string asset = "";
    if (request.params.size() > 0 && request.params[0].isStr()) {
        asset = request.params[0].get_str();
    }
    CAmountMap balance = pwalletMain->GetBalance();
    CAmountMap unBalance = pwalletMain->GetUnconfirmedBalance();
    CAmountMap imBalance = pwalletMain->GetImmatureBalance();
    obj.push_back(Pair("balance", PushAssetBalance(balance, pwalletMain, asset)));
    obj.push_back(Pair("unconfirmed_balance", PushAssetBalance(unBalance, pwalletMain, asset)));
    obj.push_back(Pair("immature_balance",    PushAssetBalance(imBalance, pwalletMain, asset)));
    obj.push_back(Pair("txcount",       (int)pwalletMain->mapWallet.size()));
    obj.push_back(Pair("keypoololdest", pwalletMain->GetOldestKeyPoolTime()));
    obj.push_back(Pair("keypoolsize",   (int)pwalletMain->GetKeyPoolSize()));
    if (pwalletMain->IsCrypted())
        obj.push_back(Pair("unlocked_until", nWalletUnlockTime));
    obj.push_back(Pair("paytxfee",      ValueFromAmount(payTxFee.GetFeePerK())));
    CKeyID masterKeyID = pwalletMain->GetHDChain().masterKeyID;
    if (!masterKeyID.IsNull())
         obj.push_back(Pair("hdmasterkeyid", masterKeyID.GetHex()));
    return obj;
}

UniValue resendwallettransactions(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 0)
        throw runtime_error(
            "resendwallettransactions\n"
            "Immediately re-broadcast unconfirmed wallet transactions to all peers.\n"
            "Intended only for testing; the wallet code periodically re-broadcasts\n"
            "automatically.\n"
            "Returns array of transaction ids that were re-broadcast.\n"
            );

    if (!g_connman)
        throw JSONRPCError(RPC_CLIENT_P2P_DISABLED, "Error: Peer-to-peer functionality missing or disabled");

    LOCK2(cs_main, pwalletMain->cs_wallet);

    std::vector<uint256> txids = pwalletMain->ResendWalletTransactionsBefore(GetTime(), g_connman.get());
    UniValue result(UniValue::VARR);
    BOOST_FOREACH(const uint256& txid, txids)
    {
        result.push_back(txid.ToString());
    }
    return result;
}

UniValue listunspent(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() > 5)
        throw runtime_error(
            "listunspent ( minconf maxconf  [\"addresses\",...] [include_unsafe] asset )\n"
            "\nReturns array of unspent transaction outputs with between minconf and maxconf (inclusive) confirmations of the given asset type, or bitcoin if not provided.\n"
            "Optionally filter to only include txouts paid to specified addresses.\n"
            "\nArguments:\n"
            "1. minconf                 (numeric, optional, default=1) The minimum confirmations to filter\n"
            "2. maxconf                 (numeric, optional, default=9999999) The maximum confirmations to filter\n"
            "3. \"addresses\"             (optional) A json array of bitcoin addresses to filter\n"
            "    [\n"
            "      \"address\"            (string) bitcoin address\n"
            "      ,...\n"
            "    ]\n"
            "4. include_unsafe (bool, optional, default=true) Include outputs that are not safe to spend\n"
            "                  because they come from unconfirmed untrusted transactions or unconfirmed\n"
            "                  replacement transactions (cases where we are less sure that a conflicting\n"
            "                  transaction won't be mined).\n"
            "5.  \"asset\"                 (string, optional, default=all) The hex asset id or label to filter for.\n"
            "[                          (array of json object)\n"
            "  {\n"
            "    \"txid\": \"txid\",        (string) the transaction id \n"
            "    \"vout\": n,             (numeric) the vout value\n"
            "    \"address\": \"address\",  (string) the bitcoin address\n"
            "    \"account\": \"account\",  (string) DEPRECATED. The associated account, or \"\" for the default account\n"
            "    \"scriptPubKey\": \"key\", (string) the script key\n"
            "    \"amount\" : x.xxx,         (numeric) the transaction output amount in " + CURRENCY_UNIT + "\n"
            "    \"asset\": \"hex\"       (string) the asset id for this output\n"
            "    \"assetcommitment\": \"hex\" (string) the asset commitment for this output\n"
            "    \"assetlabel\":\"<assetlabel>\", (string) Asset label for asset type if set.\n"
            "    \"confirmations\": n,    (numeric) The number of confirmations\n"
            "    \"amountcommitment\": \"hex\",     (string) the output's value commitment, if blinded\n"
            "    \"blinder\": \"blind\"     (string) The value blinding factor used for a confidential output\n"
            "    \"assetblinder\": \"blind\"(string) The asset blinding factor used for a confidential output\n"
            "    \"redeemScript\": n      (string) The redeemScript if scriptPubKey is P2SH\n"
            "    \"spendable\": xxx,      (bool) Whether we have the private keys to spend this output\n"
            "    \"solvable\": xxx        (bool) Whether we know how to spend this output, ignoring the lack of keys\n"
            "  }\n"
            "  ,...\n"
            "]\n"

            "\nExamples:\n"
            + HelpExampleCli("listunspent", "")
            + HelpExampleCli("listunspent", "6 9999999 \"[\\\"1PGFqEzfmQch1gKD3ra4k18PNj3tTUUSqg\\\",\\\"1LtvqCaApEdUGFkpKMM4MstjcaL4dKg8SP\\\"]\"")
            + HelpExampleCli("listunspent", "6 9999999 \"[]\" \"myasset\"")
            + HelpExampleRpc("listunspent", "6, 9999999 \"[\\\"1PGFqEzfmQch1gKD3ra4k18PNj3tTUUSqg\\\",\\\"1LtvqCaApEdUGFkpKMM4MstjcaL4dKg8SP\\\"]\"")
        );

    int nMinDepth = 1;
    if (request.params.size() > 0 && !request.params[0].isNull()) {
        RPCTypeCheckArgument(request.params[0], UniValue::VNUM);
        nMinDepth = request.params[0].get_int();
    }

    int nMaxDepth = 9999999;
    if (request.params.size() > 1 && !request.params[1].isNull()) {
        RPCTypeCheckArgument(request.params[1], UniValue::VNUM);
        nMaxDepth = request.params[1].get_int();
    }

    set<CBitcoinAddress> setAddress;
    if (request.params.size() > 2 && !request.params[2].isNull()) {
        RPCTypeCheckArgument(request.params[2], UniValue::VARR);
        UniValue inputs = request.params[2].get_array();
        for (unsigned int idx = 0; idx < inputs.size(); idx++) {
            const UniValue& input = inputs[idx];
            CBitcoinAddress address(input.get_str());
            if (!address.IsValid())
                throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, string("Invalid Bitcoin address: ")+input.get_str());
            if (setAddress.count(address))
                throw JSONRPCError(RPC_INVALID_PARAMETER, string("Invalid parameter, duplicated address: ")+input.get_str());
           setAddress.insert(address);
        }
    }

    bool include_unsafe = true;
    if (request.params.size() > 3 && !request.params[3].isNull()) {
        RPCTypeCheckArgument(request.params[3], UniValue::VBOOL);
        include_unsafe = request.params[3].get_bool();
    }

    std::string assetstr = "";
    if (request.params.size() > 4 && request.params[4].isStr()) {
        assetstr = request.params[4].get_str();
    }
    CAsset asset;
    if (assetstr != "") {
        asset = GetAssetFromString(assetstr);
    }

    UniValue results(UniValue::VARR);
    vector<COutput> vecOutputs;
    assert(pwalletMain != NULL);
    LOCK2(cs_main, pwalletMain->cs_wallet);
    pwalletMain->AvailableCoins(vecOutputs, !include_unsafe, NULL, true);
    BOOST_FOREACH(const COutput& out, vecOutputs) {
        if (out.nDepth < nMinDepth || out.nDepth > nMaxDepth)
            continue;

        CTxDestination address;
        const CScript& scriptPubKey = out.tx->tx->vout[out.i].scriptPubKey;
        bool fValidAddress = ExtractDestination(scriptPubKey, address);

        if (setAddress.size() && (!fValidAddress || !setAddress.count(address)))
            continue;

        CAmount nValue = out.tx->GetOutputValueOut(out.i);
        CAsset assetid = out.tx->GetOutputAsset(out.i);
        if (nValue == -1 || assetid.IsNull())
            continue;

        if (assetstr != "" && asset != assetid) {
            continue;
        }

        UniValue entry(UniValue::VOBJ);
        entry.push_back(Pair("txid", out.tx->GetHash().GetHex()));
        entry.push_back(Pair("vout", out.i));

        if (fValidAddress) {
            CBitcoinAddress addr(address);
            entry.push_back(Pair("address", addr.ToString()));
            if (pwalletMain->mapAddressBook.count(address))
                entry.push_back(Pair("account", pwalletMain->mapAddressBook[address].name));

            if (scriptPubKey.IsPayToScriptHash()) {
                const CScriptID& hash = boost::get<CScriptID>(address);
                CScript redeemScript;
                if (pwalletMain->GetCScript(hash, redeemScript))
                    entry.push_back(Pair("redeemScript", HexStr(redeemScript.begin(), redeemScript.end())));
            }
        }

        entry.push_back(Pair("scriptPubKey", HexStr(scriptPubKey.begin(), scriptPubKey.end())));
        entry.push_back(Pair("amount", ValueFromAmount(nValue)));
        entry.push_back(Pair("asset", assetid.GetHex()));
        if (out.tx->tx->vout[out.i].nAsset.IsCommitment()) {
            entry.push_back(Pair("assetcommitment", HexStr(out.tx->tx->vout[out.i].nAsset.vchCommitment)));
        }
        const std::string label = gAssetsDir.GetLabel(assetid);
        if (label != "") {
            entry.push_back(Pair("assetlabel", label));
        }
        entry.push_back(Pair("confirmations", out.nDepth));
        entry.push_back(Pair("spendable", out.fSpendable));
        entry.push_back(Pair("solvable", out.fSolvable));
        if (out.tx->tx->vout[out.i].nValue.IsCommitment()) {
            entry.push_back(Pair("amountcommitment", HexStr(out.tx->tx->vout[out.i].nValue.vchCommitment)));
        }
        entry.push_back(Pair("blinder",out.tx->GetOutputBlindingFactor(out.i).ToString()));
        entry.push_back(Pair("assetblinder",out.tx->GetOutputAssetBlindingFactor(out.i).ToString()));
        results.push_back(entry);
    }

    return results;
}

UniValue fundrawtransaction(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 1 || request.params.size() > 2)
        throw runtime_error(
                            "fundrawtransaction \"hexstring\" ( options )\n"
                            "\nAdd inputs to a transaction until it has enough in value to meet its out value.\n"
                            "This will not modify existing inputs, and will add change outputs to the json output.\n"
                            "Note that inputs which were signed may need to be resigned after completion since in/outputs have been added.\n"
                            "The inputs added will not be signed, use signrawtransaction for that.\n"
                            "Note that all existing inputs must have their previous output transaction be in the wallet.\n"
                            "Note that all inputs selected must be of standard form and P2SH scripts must be\n"
                            "in the wallet using importaddress or addmultisigaddress (to calculate fees).\n"
                            "You can see whether this is the case by checking the \"solvable\" field in the listunspent output.\n"
                            "Only pay-to-pubkey, multisig, and P2SH versions thereof are currently supported for watch-only\n"
                            "Note: Existing fee outputs will be dropped to aid fee estimation\n"
                            "\nArguments:\n"
                            "1. \"hexstring\"           (string, required) The hex string of the raw transaction\n"
                            "2. options                 (object, optional)\n"
                            "   {\n"
                            "     \"changeAddress\"          (string, optional, default pool address) The bitcoin address to receive the change\n"
                            "     \"changePosition\"    (numeric, optional, default random) The index of the change output (DISABLED)\n"
                            "     \"includeWatching\"        (boolean, optional, default false) Also select inputs which are watch only\n"
                            "     \"lockUnspents\"           (boolean, optional, default false) Lock selected unspent outputs\n"
                            "     \"reserveChangeKey\"       (boolean, optional, default true) Reserves the change output key from the keypool\n"
                            "     \"feeRate\"                (numeric, optional, default not set: makes wallet determine the fee) Set a specific feerate (" + CURRENCY_UNIT + " per KB)\n"
                            "     \"subtractFeeFromOutputs\" (array, optional) A json array of integers.\n"
                            "                              The fee will be equally deducted from the amount of each specified output.\n"
                            "                              The outputs are specified by their zero-based index, before any change output is added.\n"
                            "                              Those recipients will receive less bitcoins than you enter in their corresponding amount field.\n"
                            "                              If no outputs are specified here, the sender pays the fee.\n"
                            "                                  [vout_index,...]\n"
                            "   }\n"
                            "                         for backward compatibility: passing in a true instead of an object will result in {\"includeWatching\":true}\n"
                            "\nResult:\n"
                            "{\n"
                            "  \"hex\":       \"value\", (string)  The resulting raw transaction (hex-encoded string)\n"
                            "  \"fee\":       n,         (numeric) Fee in " + CURRENCY_UNIT + " the resulting transaction pays\n"
                            "}\n"
                            "\nExamples:\n"
                            "\nCreate a transaction with no inputs\n"
                            + HelpExampleCli("createrawtransaction", "\"[]\" \"{\\\"myaddress\\\":0.01}\"") +
                            "\nAdd sufficient unsigned inputs to meet the output value\n"
                            + HelpExampleCli("fundrawtransaction", "\"rawtransactionhex\"") +
                            "\nSign the transaction\n"
                            + HelpExampleCli("signrawtransaction", "\"fundedtransactionhex\"") +
                            "\nSend the transaction\n"
                            + HelpExampleCli("sendrawtransaction", "\"signedtransactionhex\"")
                            );

    RPCTypeCheck(request.params, boost::assign::list_of(UniValue::VSTR));

    CTxDestination changeAddress = CNoDestination();
    int changePosition = -1;
    bool includeWatching = false;
    bool lockUnspents = false;
    bool reserveChangeKey = true;
    CFeeRate feeRate = CFeeRate(0);
    bool overrideEstimatedFeerate = false;
    UniValue subtractFeeFromOutputs;
    set<int> setSubtractFeeFromOutputs;

    if (request.params.size() > 1) {
      if (request.params[1].type() == UniValue::VBOOL) {
        // backward compatibility bool only fallback
        includeWatching = request.params[1].get_bool();
      }
      else {
        RPCTypeCheck(request.params, boost::assign::list_of(UniValue::VSTR)(UniValue::VOBJ));

        UniValue options = request.params[1];

        RPCTypeCheckObj(options,
            {
                {"changeAddress", UniValueType(UniValue::VSTR)},
                {"changePosition", UniValueType(UniValue::VNUM)},
                {"includeWatching", UniValueType(UniValue::VBOOL)},
                {"lockUnspents", UniValueType(UniValue::VBOOL)},
                {"reserveChangeKey", UniValueType(UniValue::VBOOL)},
                {"feeRate", UniValueType()}, // will be checked below
                {"subtractFeeFromOutputs", UniValueType(UniValue::VARR)},
            },
            true, true);

        if (options.exists("changeAddress")) {
            CBitcoinAddress address(options["changeAddress"].get_str());

            if (!address.IsValid())
                throw JSONRPCError(RPC_INVALID_PARAMETER, "changeAddress must be a valid bitcoin address");

            changeAddress = address.Get();
        }

        if (options.exists("changePosition"))
            throw JSONRPCError(RPC_INVALID_PARAMETER, "changePosition argument is disabled");
            //changePosition = options["changePosition"].get_int();

        if (options.exists("includeWatching"))
            includeWatching = options["includeWatching"].get_bool();

        if (options.exists("lockUnspents"))
            lockUnspents = options["lockUnspents"].get_bool();

        if (options.exists("reserveChangeKey"))
            reserveChangeKey = options["reserveChangeKey"].get_bool();

        if (options.exists("feeRate"))
        {
            feeRate = CFeeRate(AmountFromValue(options["feeRate"]));
            overrideEstimatedFeerate = true;
        }

        if (options.exists("subtractFeeFromOutputs"))
            subtractFeeFromOutputs = options["subtractFeeFromOutputs"].get_array();
      }
    }

    // parse hex string from parameter
    CMutableTransaction tx;
    if (!DecodeHexTx(tx, request.params[0].get_str()))
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");

    if (tx.vout.size() == 0)
        throw JSONRPCError(RPC_INVALID_PARAMETER, "TX must have at least one output");

    if (changePosition != -1 && (changePosition < 0 || (unsigned int)changePosition > tx.vout.size()))
        throw JSONRPCError(RPC_INVALID_PARAMETER, "changePosition out of bounds");

    for (unsigned int idx = 0; idx < subtractFeeFromOutputs.size(); idx++) {
        int pos = subtractFeeFromOutputs[idx].get_int();
        if (setSubtractFeeFromOutputs.count(pos))
            throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Invalid parameter, duplicated position: %d", pos));
        if (pos < 0)
            throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Invalid parameter, negative position: %d", pos));
        if (pos >= int(tx.vout.size()))
            throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Invalid parameter, position too large: %d", pos));
        setSubtractFeeFromOutputs.insert(pos);
    }

    CAmount nFeeOut;
    string strFailReason;

    if(!pwalletMain->FundTransaction(tx, nFeeOut, overrideEstimatedFeerate, feeRate, changePosition, strFailReason, includeWatching, lockUnspents, setSubtractFeeFromOutputs, reserveChangeKey, changeAddress))
        throw JSONRPCError(RPC_INTERNAL_ERROR, strFailReason);

    UniValue result(UniValue::VOBJ);
    result.push_back(Pair("hex", EncodeHexTx(tx)));
    result.push_back(Pair("fee", ValueFromAmount(nFeeOut)));

    return result;
}

// Calculate the size of the transaction assuming all signatures are max size
// Use DummySignatureCreator, which inserts 72 byte signatures everywhere.
// TODO: re-use this in CWallet::CreateTransaction (right now
// CreateTransaction uses the constructed dummy-signed tx to do a priority
// calculation, but we should be able to refactor after priority is removed).
// NOTE: this requires that all inputs must be in mapWallet (eg the tx should
// be IsAllFromMe).
int64_t CalculateMaximumSignedTxSize(const CTransaction &tx)
{
    CMutableTransaction txNew(tx);
    std::vector<pair<CWalletTx *, unsigned int>> vCoins;
    // Look up the inputs.  We should have already checked that this transaction
    // IsAllFromMe(ISMINE_SPENDABLE), so every input should already be in our
    // wallet, with a valid index into the vout array.
    for (auto& input : tx.vin) {
        const auto mi = pwalletMain->mapWallet.find(input.prevout.hash);
        assert(mi != pwalletMain->mapWallet.end() && input.prevout.n < mi->second.tx->vout.size());
        vCoins.emplace_back(make_pair(&(mi->second), input.prevout.n));
    }
    if (!pwalletMain->DummySignTx(txNew, vCoins)) {
        // This should never happen, because IsAllFromMe(ISMINE_SPENDABLE)
        // implies that we can sign for every input.
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Transaction contains inputs that cannot be signed");
    }
    return GetVirtualTransactionSize(txNew);
}

UniValue bumpfee(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp)) {
        return NullUniValue;
    }

    if (request.fHelp || request.params.size() < 1 || request.params.size() > 2) {
        throw runtime_error(
            "bumpfee \"txid\" ( options ) \n"
            "\nBumps the fee of an opt-in-RBF transaction T, replacing it with a new transaction B.\n"
            "An opt-in RBF transaction with the given txid must be in the wallet.\n"
            "The command will pay the additional fee by decreasing (or perhaps removing) its change output.\n"
            "If the change output is not big enough to cover the increased fee, the command will currently fail\n"
            "instead of adding new inputs to compensate. (A future implementation could improve this.)\n"
            "The command will fail if the wallet or mempool contains a transaction that spends one of T's outputs.\n"
            "By default, the new fee will be calculated automatically using estimatefee.\n"
            "The user can specify a confirmation target for estimatefee.\n"
            "Alternatively, the user can specify totalFee, or use RPC setpaytxfee to set a higher fee rate.\n"
            "At a minimum, the new fee rate must be high enough to pay an additional new relay fee (incrementalfee\n"
            "returned by getnetworkinfo) to enter the node's mempool.\n"
            "\nArguments:\n"
            "1. txid                  (string, required) The txid to be bumped\n"
            "2. options               (object, optional)\n"
            "   {\n"
            "     \"confTarget\"        (numeric, optional) Confirmation target (in blocks)\n"
            "     \"totalFee\"          (numeric, optional) Total fee (NOT feerate) to pay, in satoshis.\n"
            "                         In rare cases, the actual fee paid might be slightly higher than the specified\n"
            "                         totalFee if the tx change output has to be removed because it is too close to\n"
            "                         the dust threshold.\n"
            "     \"replaceable\"       (boolean, optional, default true) Whether the new transaction should still be\n"
            "                         marked bip-125 replaceable. If true, the sequence numbers in the transaction will\n"
            "                         be left unchanged from the original. If false, any input sequence numbers in the\n"
            "                         original transaction that were less than 0xfffffffe will be increased to 0xfffffffe\n"
            "                         so the new transaction will not be explicitly bip-125 replaceable (though it may\n"
            "                         still be replacable in practice, for example if it has unconfirmed ancestors which\n"
            "                         are replaceable).\n"
            "   }\n"
            "\nResult:\n"
            "{\n"
            "  \"txid\":    \"value\",   (string)  The id of the new transaction\n"
            "  \"origfee\":  n,         (numeric) Fee of the replaced transaction\n"
            "  \"fee\":      n,         (numeric) Fee of the new transaction\n"
            "  \"errors\":  [ str... ] (json array of strings) Errors encountered during processing (may be empty)\n"
            "}\n"
            "\nExamples:\n"
            "\nBump the fee, get the new transaction\'s txid\n" +
            HelpExampleCli("bumpfee", "<txid>"));
    }

    RPCTypeCheck(request.params, boost::assign::list_of(UniValue::VSTR)(UniValue::VOBJ));
    uint256 hash;
    hash.SetHex(request.params[0].get_str());

    // retrieve the original tx from the wallet
    LOCK2(cs_main, pwalletMain->cs_wallet);
    EnsureWalletIsUnlocked();
    if (!pwalletMain->mapWallet.count(hash)) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid or non-wallet transaction id");
    }
    CWalletTx& wtx = pwalletMain->mapWallet[hash];

    if (pwalletMain->HasWalletSpend(hash)) {
        throw JSONRPCError(RPC_MISC_ERROR, "Transaction has descendants in the wallet");
    }

    {
        LOCK(mempool.cs);
        auto it = mempool.mapTx.find(hash);
        if (it != mempool.mapTx.end() && it->GetCountWithDescendants() > 1) {
            throw JSONRPCError(RPC_MISC_ERROR, "Transaction has descendants in the mempool");
        }
    }

    if (wtx.GetDepthInMainChain() != 0) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Transaction has been mined, or is conflicted with a mined transaction");
    }

    if (!SignalsOptInRBF(wtx)) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Transaction is not BIP 125 replaceable");
    }

    if (wtx.mapValue.count("replaced_by_txid")) {
        throw JSONRPCError(RPC_INVALID_REQUEST, strprintf("Cannot bump transaction %s which was already bumped by transaction %s", hash.ToString(), wtx.mapValue.at("replaced_by_txid")));
    }

    // check that original tx consists entirely of our inputs
    // if not, we can't bump the fee, because the wallet has no way of knowing the value of the other inputs (thus the fee)
    if (!pwalletMain->IsAllFromMe(wtx, ISMINE_SPENDABLE)) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Transaction contains inputs that don't belong to this wallet");
    }

    // figure out which output was change
    // if there was no change output or multiple change outputs, fail
    int nOutput = -1;
    for (size_t i = 0; i < wtx.tx->vout.size(); ++i) {
        if (pwalletMain->IsChange(wtx.tx->vout[i])) {
            if (nOutput != -1) {
                throw JSONRPCError(RPC_MISC_ERROR, "Transaction has multiple change outputs");
            }
            nOutput = i;
        }
    }
    if (nOutput == -1) {
        throw JSONRPCError(RPC_MISC_ERROR, "Transaction does not have a change output");
    }

    // Calculate the expected size of the new transaction.
    int64_t txSize = GetVirtualTransactionSize(*(wtx.tx));
    const int64_t maxNewTxSize = CalculateMaximumSignedTxSize(*wtx.tx);

    // optional parameters
    bool specifiedConfirmTarget = false;
    int newConfirmTarget = nTxConfirmTarget;
    CAmount totalFee = 0;
    bool replaceable = true;
    if (request.params.size() > 1) {
        UniValue options = request.params[1];
        RPCTypeCheckObj(options,
            {
                {"confTarget", UniValueType(UniValue::VNUM)},
                {"totalFee", UniValueType(UniValue::VNUM)},
                {"replaceable", UniValueType(UniValue::VBOOL)},
            },
            true, true);

        if (options.exists("confTarget") && options.exists("totalFee")) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "confTarget and totalFee options should not both be set. Please provide either a confirmation target for fee estimation or an explicit total fee for the transaction.");
        } else if (options.exists("confTarget")) {
            specifiedConfirmTarget = true;
            newConfirmTarget = options["confTarget"].get_int();
            if (newConfirmTarget <= 0) { // upper-bound will be checked by estimatefee/smartfee
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid confTarget (cannot be <= 0)");
            }
        } else if (options.exists("totalFee")) {
            totalFee = options["totalFee"].get_int64();
            CAmount requiredFee = CWallet::GetRequiredFee(maxNewTxSize);
            if (totalFee < requiredFee ) {
                throw JSONRPCError(RPC_INVALID_PARAMETER,
                                   strprintf("Insufficient totalFee (cannot be less than required fee %s)",
                                             FormatMoney(requiredFee)));
            }
        }

        if (options.exists("replaceable")) {
            replaceable = options["replaceable"].get_bool();
        }
    }

    // calculate the old fee and fee-rate
    CAmount nOldFee = wtx.tx->GetFee()[Params().GetConsensus().pegged_asset];
    CFeeRate nOldFeeRate(nOldFee, txSize);
    CAmount nNewFee;
    CFeeRate nNewFeeRate;
    // The wallet uses a conservative WALLET_INCREMENTAL_RELAY_FEE value to
    // future proof against changes to network wide policy for incremental relay
    // fee that our node may not be aware of.
    CFeeRate walletIncrementalRelayFee = CFeeRate(WALLET_INCREMENTAL_RELAY_FEE);
    if (::incrementalRelayFee > walletIncrementalRelayFee) {
        walletIncrementalRelayFee = ::incrementalRelayFee;
    }

    if (totalFee > 0) {
        CAmount minTotalFee = nOldFeeRate.GetFee(maxNewTxSize) + ::incrementalRelayFee.GetFee(maxNewTxSize);
        if (totalFee < minTotalFee) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Insufficient totalFee, must be at least %s (oldFee %s + incrementalFee %s)",
                                                                FormatMoney(minTotalFee), FormatMoney(nOldFeeRate.GetFee(maxNewTxSize)), FormatMoney(::incrementalRelayFee.GetFee(maxNewTxSize))));
        }
        nNewFee = totalFee;
        nNewFeeRate = CFeeRate(totalFee, maxNewTxSize);
    } else {
        // if user specified a confirm target then don't consider any global payTxFee
        if (specifiedConfirmTarget) {
            nNewFee = CWallet::GetMinimumFee(maxNewTxSize, newConfirmTarget, mempool, CAmount(0));
        }
        // otherwise use the regular wallet logic to select payTxFee or default confirm target
        else {
            nNewFee = CWallet::GetMinimumFee(maxNewTxSize, newConfirmTarget, mempool);
        }

        nNewFeeRate = CFeeRate(nNewFee, maxNewTxSize);

        // New fee rate must be at least old rate + minimum incremental relay rate
        // walletIncrementalRelayFee.GetFeePerK() should be exact, because it's initialized
        // in that unit (fee per kb).
        // However, nOldFeeRate is a calculated value from the tx fee/size, so
        // add 1 satoshi to the result, because it may have been rounded down.
        if (nNewFeeRate.GetFeePerK() < nOldFeeRate.GetFeePerK() + 1 + walletIncrementalRelayFee.GetFeePerK()) {
            nNewFeeRate = CFeeRate(nOldFeeRate.GetFeePerK() + 1 + walletIncrementalRelayFee.GetFeePerK());
            nNewFee = nNewFeeRate.GetFee(maxNewTxSize);
        }
    }

    // Check that in all cases the new fee doesn't violate maxTxFee
     if (nNewFee > maxTxFee) {
         throw JSONRPCError(RPC_MISC_ERROR,
                            strprintf("Specified or calculated fee %s is too high (cannot be higher than maxTxFee %s)",
                                      FormatMoney(nNewFee), FormatMoney(maxTxFee)));
     }

    // check that fee rate is higher than mempool's minimum fee
    // (no point in bumping fee if we know that the new tx won't be accepted to the mempool)
    // This may occur if the user set TotalFee or paytxfee too low, if fallbackfee is too low, or, perhaps,
    // in a rare situation where the mempool minimum fee increased significantly since the fee estimation just a
    // moment earlier. In this case, we report an error to the user, who may use totalFee to make an adjustment.
    CFeeRate minMempoolFeeRate = mempool.GetMinFee(GetArg("-maxmempool", DEFAULT_MAX_MEMPOOL_SIZE) * 1000000);
    if (nNewFeeRate.GetFeePerK() < minMempoolFeeRate.GetFeePerK()) {
        throw JSONRPCError(RPC_MISC_ERROR, strprintf("New fee rate (%s) is less than the minimum fee rate (%s) to get into the mempool. totalFee value should to be at least %s or settxfee value should be at least %s to add transaction.", FormatMoney(nNewFeeRate.GetFeePerK()), FormatMoney(minMempoolFeeRate.GetFeePerK()), FormatMoney(minMempoolFeeRate.GetFee(maxNewTxSize)), FormatMoney(minMempoolFeeRate.GetFeePerK())));
    }

    // Now modify the output to increase the fee.
    // If the output is not large enough to pay the fee, fail.
    CAmount nDelta = nNewFee - nOldFee;
    assert(nDelta > 0);
    CMutableTransaction tx(*(wtx.tx));
    CTxOut* poutput = &(tx.vout[nOutput]);
    if (poutput->nValue.GetAmount() < nDelta) {
        throw JSONRPCError(RPC_MISC_ERROR, "Change output is too small to bump the fee");
    }

    // If the output would become dust, discard it (converting the dust to fee)
    poutput->nValue = CConfidentialValue(poutput->nValue.GetAmount() - nDelta);
    if (poutput->nValue.GetAmount() <= poutput->GetDustThreshold(::dustRelayFee)) {
        LogPrint("rpc", "Bumping fee and discarding dust output\n");
        nNewFee += poutput->nValue.GetAmount();
        tx.vout.erase(tx.vout.begin() + nOutput);
    }

    // Mark new tx not replaceable, if requested.
    if (!replaceable) {
        for (auto& input : tx.vin) {
            if (input.nSequence < 0xfffffffe) input.nSequence = 0xfffffffe;
        }
    }

    // sign the new tx
    CTransaction txNewConst(tx);
    int nIn = 0;
    for (auto& input : tx.vin) {
        std::map<uint256, CWalletTx>::const_iterator mi = pwalletMain->mapWallet.find(input.prevout.hash);
        assert(mi != pwalletMain->mapWallet.end() && input.prevout.n < mi->second.tx->vout.size());
        const CScript& scriptPubKey = mi->second.tx->vout[input.prevout.n].scriptPubKey;
        const CAmount& amount = mi->second.tx->vout[input.prevout.n].nValue.GetAmount();
        SignatureData sigdata;
        if (!ProduceSignature(TransactionSignatureCreator(pwalletMain, &txNewConst, nIn, amount, SIGHASH_ALL), scriptPubKey, sigdata)) {
            throw JSONRPCError(RPC_WALLET_ERROR, "Can't sign transaction.");
        }
        UpdateTransaction(tx, nIn, sigdata);
        nIn++;
    }

    // commit/broadcast the tx
    std::vector<CReserveKey> vChangeKey;
    CWalletTx wtxBumped(pwalletMain, MakeTransactionRef(std::move(tx)));
    wtxBumped.mapValue = wtx.mapValue;
    wtxBumped.mapValue["replaces_txid"] = hash.ToString();
    wtxBumped.vOrderForm = wtx.vOrderForm;
    wtxBumped.strFromAccount = wtx.strFromAccount;
    wtxBumped.fTimeReceivedIsTxTime = true;
    wtxBumped.fFromMe = true;
    CValidationState state;
    if (!pwalletMain->CommitTransaction(wtxBumped, vChangeKey, g_connman.get(), state)) {
        // NOTE: CommitTransaction never returns false, so this should never happen.
        throw JSONRPCError(RPC_WALLET_ERROR, strprintf("Error: The transaction was rejected! Reason given: %s", state.GetRejectReason()));
    }

    UniValue vErrors(UniValue::VARR);
    if (state.IsInvalid()) {
        // This can happen if the mempool rejected the transaction.  Report
        // what happened in the "errors" response.
        vErrors.push_back(strprintf("Error: The transaction was rejected: %s", FormatStateMessage(state)));
    }

    // mark the original tx as bumped
    if (!pwalletMain->MarkReplaced(wtx.GetHash(), wtxBumped.GetHash())) {
        // TODO: see if JSON-RPC has a standard way of returning a response
        // along with an exception. It would be good to return information about
        // wtxBumped to the caller even if marking the original transaction
        // replaced does not succeed for some reason.
        vErrors.push_back("Error: Created new bumpfee transaction but could not mark the original transaction as replaced.");
    }

    UniValue result(UniValue::VOBJ);
    result.push_back(Pair("txid", wtxBumped.GetHash().GetHex()));
    result.push_back(Pair("origfee", ValueFromAmount(nOldFee)));
    result.push_back(Pair("fee", ValueFromAmount(nNewFee)));
    result.push_back(Pair("errors", vErrors));

    return result;
}

UniValue signblock(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "signblock \"blockhex\"\n"
            "\nSigns a block proposal, checking that it would be accepted first\n"
            "\nArguments:\n"
            "1. \"blockhex\"    (string, required) The hex-encoded block from getnewblockhex\n"
            "\nResult\n"
            " sig      (hex) The signature\n"
            "\nExamples:\n"
            + HelpExampleCli("signblock", "0000002018c6f2f913f9902aeab...5ca501f77be96de63f609010000000000000000015100000000")
        );

    CBlock block;
    if (!DecodeHexBlk(block, request.params[0].get_str()))
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Block decode failed");

    LOCK(cs_main);

    uint256 hash = block.GetHash();
    BlockMap::iterator mi = mapBlockIndex.find(hash);
    if (mi != mapBlockIndex.end())
        throw JSONRPCError(RPC_VERIFY_ERROR, "already have block");

    CBlockIndex* const pindexPrev = chainActive.Tip();
    // TestBlockValidity only supports blocks built on the current Tip
    if (block.hashPrevBlock != pindexPrev->GetBlockHash())
        throw JSONRPCError(RPC_VERIFY_ERROR, "proposal was not based on our best chain");

    CValidationState state;
    if (!TestBlockValidity(state, Params(), block, pindexPrev, false, true) || !state.IsValid()) {
        std::string strRejectReason = state.GetRejectReason();
        if (strRejectReason.empty())
            throw JSONRPCError(RPC_VERIFY_ERROR, state.IsInvalid() ? "Block proposal was invalid" : "Error checking block proposal");
        throw JSONRPCError(RPC_VERIFY_ERROR, strRejectReason);
    }

    block.proof.solution = CScript();
    MaybeGenerateProof(&block, pwalletMain);
    return HexStr(block.proof.solution.begin(), block.proof.solution.end());
}

namespace {
static secp256k1_context *secp256k1_ctx;

class CSecp256k1Init {
public:
    CSecp256k1Init() {
        secp256k1_ctx = secp256k1_context_create(SECP256K1_CONTEXT_VERIFY | SECP256K1_CONTEXT_SIGN);
    }
    ~CSecp256k1Init() {
        secp256k1_context_destroy(secp256k1_ctx);
    }
};
static CSecp256k1Init instance_of_csecp256k1;
}

UniValue getethpeginaddress(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 1)
        throw std::runtime_error(
            "getethpeginaddress key\n"
            "\nReturns information needed for claimethpegin to move coins to the sidechain.\n"
            "The user should send CBT coins from their eth wallet to the eth_mainchain_address returned.\n"
            "The user needs to provide their eth priv key, which is used to generate a claim pubkey that \n"
            "is added to the pegin transaction. The transaction is then signed with the key provided.\n"
            "IMPORTANT: Like getaddress, getethpeginaddress adds new secrets to wallet.dat, necessitating backup on a regular basis.\n"
            "1. key         (hex, required) Eth private key\n"
            "\nResult:\n"
            "\"eth_mainchain_address\"      (string) Mainchain Eth deposit address to send CBT to\n"
            "\"eth_claim_pubkey\"       (string) The claim pubkey in hex required in `claimethpegin` to retrieve pegged-in funds\n"
            "\nExamples:\n"
            + HelpExampleCli("getethpeginaddress", "db21180712a256d6a08cc2115853effa429671041ee8d7e7d7cb36f39bb069a0")
            + HelpExampleRpc("getethpeginaddress", "db21180712a256d6a08cc2115853effa429671041ee8d7e7d7cb36f39bb069a0")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    std::vector<unsigned char> keyBytes = ParseHex(request.params[0].get_str());
    CKey key;
    key.Set(keyBytes.begin(), keyBytes.end(), true);
    if (!key.IsValid()) throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Private key outside allowed range");

    CPubKey pubKey = key.GetPubKey();
    assert(key.VerifyPubKey(pubKey));
    CKeyID vchAddress = pubKey.GetID();
    {
        pwalletMain->MarkDirty();
        pwalletMain->SetAddressBook(vchAddress, "", "receive");

        if (!pwalletMain->HaveKey(vchAddress)) {
            pwalletMain->mapKeyMetadata[vchAddress].nCreateTime = 1;

            if (!pwalletMain->AddKeyPubKey(key, pubKey))
                throw JSONRPCError(RPC_WALLET_ERROR, "Error adding key to wallet");
        }
    }

    std::string destAddressStr = Params().GetConsensus().fedpegAddress.ToString();
    std::string claimPubStr =  HexStr(pubKey.begin(), pubKey.end());
    AuditLogPrintf("%s : getethpeginaddress eth_mainchain_address: %s eth_claim_pubkey: %s\n",
        getUser(), destAddressStr, claimPubStr);

    UniValue fundinginfo(UniValue::VOBJ);
    fundinginfo.pushKV("eth_mainchain_address", destAddressStr);
    fundinginfo.pushKV("eth_claim_pubkey", claimPubStr);
    return fundinginfo;
}

UniValue getpeginaddress(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 0)
        throw std::runtime_error(
            "getpeginaddress\n"
            "\nReturns information needed for claimpegin to move coins to the sidechain.\n"
            "The user should send coins from their Bitcoin wallet to the mainchain_address returned.\n"
            "IMPORTANT: Like getaddress, getpeginaddress adds new secrets to wallet.dat, necessitating backup on a regular basis.\n"

            "\nResult:\n"
            "\"mainchain_address\"           (string) Mainchain Bitcoin deposit address to send bitcoin to\n"
            "\"claim_script\"             (string) The claim script in hex that was committed to. This may be required in `claimpegin` to retrieve pegged-in funds\n"
            "\nExamples:\n"
            + HelpExampleCli("getpeginaddress", "db21180712a256d6a08cc2115853effa429671041ee8d7e7d7cb36f39bb069a0")
            + HelpExampleRpc("getpeginaddress", "db21180712a256d6a08cc2115853effa429671041ee8d7e7d7cb36f39bb069a0")
        );

    //Creates new address for receiving unlocked utxos
    JSONRPCRequest req;
    CBitcoinAddress address(!pwalletMain->GetDisableCt() ?
        CBitcoinAddress(getnewaddress(req).get_str()).GetUnblinded() :
        CBitcoinAddress(getnewaddress(req).get_str()));

    Witnessifier w;
    CTxDestination dest = address.Get();
    bool ret = boost::apply_visitor(w, dest);
    if (!ret) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Public key or redeemscript not known to wallet, or the key is uncompressed");
    }

    pwalletMain->SetAddressBook(w.result, "", "receive");

    CScript destScript = GetScriptForDestination(address.Get());
    CScript witProg = GetScriptForWitness(destScript);

    //Call contracthashtool, get deposit address on mainchain.
    CParentBitcoinAddress destAddr(CScriptID(GetScriptForWitness(
        calculate_contract(Params().GetConsensus().fedpegScript, witProg))));

    AuditLogPrintf("%s : getpeginaddress mainchain_address: %s claim_script: %s\n",
        getUser(), destAddr.ToString(), HexStr(witProg));

    UniValue fundinginfo(UniValue::VOBJ);
    fundinginfo.pushKV("mainchain_address", destAddr.ToString());
    fundinginfo.pushKV("claim_script", HexStr(witProg));
    return fundinginfo;
}

UniValue sendtoethmainchain(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 2 || request.params.size() > 3)
        throw runtime_error(
            "sendtoethmainchain ethmainchainaddress amount ( subtractfeefromamount )\n"
            "\nSends sidechain funds to the given eth mainchain address, through the federated withdraw mechanism\n"
            + HelpRequiringPassphrase() +
            "\nArguments:\n"
            "1. \"address\"        (string, required) The destination address on eth mainchain\n"
            "2. \"amount\"         (numeric, required) The amount being sent to eth mainchain\n"
            "3. \"subtractfeefromamount\"  (boolean, optional, default=false) The fee will be deducted from the amount being pegged-out.\n"
            "\nResult:\n"
            "\"txid\"              (string) Transaction ID of the resulting sidechain transaction\n"
            "\nExamples:\n"
            + HelpExampleCli("sendtoethmainchain", "8e8a0ec05cc3c2b8511aabadeeb821df19ea7564 0.1")
            + HelpExampleRpc("sendtoethmainchain", "8e8a0ec05cc3c2b8511aabadeeb821df19ea7564 0.1")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    EnsureWalletIsUnlocked();

    CEthAddress address(ParseHex(request.params[0].get_str()));
    if (!address.IsValid())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid eth address");

    CAmount nAmount = AmountFromValue(request.params[1]);
    if (nAmount <= 0)
        throw JSONRPCError(RPC_TYPE_ERROR, "Invalid amount for send");

    bool subtract_fee = false;
    if (request.params.size() > 2) {
        subtract_fee = request.params[2].get_bool();
    }

    uint256 genesisBlockHash = Params().ParentGenesisBlockHash();

    // Asset type is implicit, no need to add to script
    CScript scriptPubKey;
    scriptPubKey << OP_RETURN;
    scriptPubKey << std::vector<unsigned char>(genesisBlockHash.begin(), genesisBlockHash.end());
    scriptPubKey << std::vector<unsigned char>(address.begin(), address.end());

    EnsureWalletIsUnlocked();

    CWalletTx wtxNew;
    SendMoney(scriptPubKey, nAmount, Params().GetConsensus().pegged_asset, subtract_fee, CPubKey(), wtxNew, true);

    std::string blinds;
    for (unsigned int i=0; i<wtxNew.tx->vout.size(); i++) {
        blinds += "blind:" + wtxNew.GetOutputBlindingFactor(i).ToString() + "\n";
    }

    AuditLogPrintf("%s : sendtoethmainchain %s\nblinds:\n%s\n", getUser(), wtxNew.tx->GetHash().GetHex(), blinds);

    return wtxNew.GetHash().GetHex();
}

UniValue sendtomainchain(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 2 || request.params.size() > 3)
        throw runtime_error(
            "sendtomainchain mainchainaddress amount ( subtractfeefromamount )\n"
            "\nSends sidechain funds to the given mainchain address, through the federated withdraw mechanism\n"
            + HelpRequiringPassphrase() +
            "\nArguments:\n"
            "1. \"address\"        (string, required) The destination address on Bitcoin mainchain\n"
            "2. \"amount\"         (numeric, required) The amount being sent to Bitcoin mainchain\n"
            "3. \"subtractfeefromamount\"  (boolean, optional, default=false) The fee will be deducted from the amount being pegged-out.\n"
            "\nResult:\n"
            "\"txid\"              (string) Transaction ID of the resulting sidechain transaction\n"
            "\nExamples:\n"
            + HelpExampleCli("sendtomainchain", "\"mgWEy4vBJSHt3mC8C2SEWJQitifb4qeZQq\" 0.1")
            + HelpExampleRpc("sendtomainchain", "\"mgWEy4vBJSHt3mC8C2SEWJQitifb4qeZQq\" 0.1")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    EnsureWalletIsUnlocked();

    CParentBitcoinAddress address(request.params[0].get_str());
    if (!address.IsValid())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid Bitcoin address");

    CAmount nAmount = AmountFromValue(request.params[1]);
    if (nAmount <= 0)
        throw JSONRPCError(RPC_TYPE_ERROR, "Invalid amount for send");

    bool subtract_fee = false;
    if (request.params.size() > 2) {
        subtract_fee = request.params[2].get_bool();
    }

    // Parse Bitcoin address for destination, embed script
    CScript scriptPubKeyMainchain(GetScriptForDestination(address.Get()));

    uint256 genesisBlockHash = Params().ParentGenesisBlockHash();

    // Asset type is implicit, no need to add to script
    CScript scriptPubKey;
    scriptPubKey << OP_RETURN;
    scriptPubKey << std::vector<unsigned char>(genesisBlockHash.begin(), genesisBlockHash.end());
    scriptPubKey << std::vector<unsigned char>(scriptPubKeyMainchain.begin(), scriptPubKeyMainchain.end());

    EnsureWalletIsUnlocked();

    CWalletTx wtxNew;
    SendMoney(scriptPubKey, nAmount, Params().GetConsensus().pegged_asset, subtract_fee, CPubKey(), wtxNew, true);

    std::string blinds;
    for (unsigned int i=0; i<wtxNew.tx->vout.size(); i++) {
        blinds += "blind:" + wtxNew.GetOutputBlindingFactor(i).ToString() + "\n";
    }

    AuditLogPrintf("%s : sendtomainchain %s\nblinds:\n%s\n", getUser(), wtxNew.tx->GetHash().GetHex(), blinds);

    return wtxNew.GetHash().GetHex();
}

unsigned int GetPeginTxnOutputIndex(const Sidechain::Bitcoin::CTransaction& txn, const CScript& witnessProgram)
{
    unsigned int nOut = 0;
    //Call contracthashtool
    CScript mainchain_script = GetScriptForDestination(CScriptID(GetScriptForWitness(calculate_contract(Params().GetConsensus().fedpegScript, witnessProgram))));
    for (; nOut < txn.vout.size(); nOut++)
        if (txn.vout[nOut].scriptPubKey == mainchain_script)
            break;
    return nOut;
}

UniValue getethpegin(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 1)
        throw runtime_error(
            "getethpegin \"txid\"\n"
            " Get eth ERC-20 peg-in transaction via geth rpc connectivity\n"
            "1. \"txid\"        (hex, required) Eth transaction peg-in transaction id\n"
            "Result:\n"
            "{\n"
            "   ...         JSON result of eth_getTransactionReceipt\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("getethpegin", "8b75539cc2b54efe15cd3a0f678545e3f154ca69ba87004d484d10eeb1359cc7")
            + HelpExampleRpc("getethpegin", "8b75539cc2b54efe15cd3a0f678545e3f154ca69ba87004d484d10eeb1359cc7")
        );

    uint256 hash = ParseHashV(request.params[0], "parameter 1");
    return GetEthTransaction(hash);
}

UniValue validateethpegin(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 3)
        throw runtime_error(
            "validateethpegin \"txid\" amount \n"
            " Validate an eth ERC-20 transaction to be used from peg-in to Ocean\n"
            "1. \"txid\"        (hex, required) Eth transaction peg-in transaction id\n"
            "2. \"amount\"      (numeric, required) Eth transaction peg-in amount\n"
            "3. \"claim_pubkey\"    (hex, required) The pubkey generated by getethpeginaddress\n"
            "Result:\n"
            "   valid:      (bool) Pegin is valid or invalid \n"
            "\nExamples:\n"
            + HelpExampleCli("validateethpegin", "8b75539cc2b54efe15cd3a0f678545e3f154ca69ba87004d484d10eeb1359cc7 432.109 03220271a8833566153dbfa52c4ba13d2e56970885e6178a4ce6fa81ecaf38c35a")
            + HelpExampleRpc("validateethpegin", "8b75539cc2b54efe15cd3a0f678545e3f154ca69ba87004d484d10eeb1359cc7 432.109 03220271a8833566153dbfa52c4ba13d2e56970885e6178a4ce6fa81ecaf38c35a")
        );

    uint256 hash = ParseHashV(request.params[0], "txid");
    CAmount nAmount = AmountFromValue(request.params[1]);
    const UniValue tx = GetEthTransaction(hash);

    std::vector<unsigned char> pubkeyBytes(ParseHex(request.params[2].get_str()));
    CPubKey pubKey(pubkeyBytes);
    if (!pubKey.IsFullyValid()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid public key.");
    }
    pubKey.Decompress(); // eth addresses require full pubkey

    std::string strFailReason;
    if (!IsValidEthPegin(tx, nAmount, pubKey, strFailReason) && IsConfirmedEthPegin(tx, strFailReason)) {
        throw JSONRPCError(RPC_TRANSACTION_ERROR, strFailReason);
    }
    return true;
}

UniValue createrawethpegin(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 3)
        throw runtime_error(
            "createrawethpegin \"txid\" amount \n"
            " Create a raw CBT peg-in from an eth ERC-20 transaction\n"
            "1. \"txid\"            (hex, required) Eth transaction peg-in transaction id\n"
            "2. \"amount\"          (numeric, required) Eth transaction peg-in amount\n"
            "3. \"claim_pubkey\"    (hex, required) The claim pubkey generated by getethpeginaddress\n"
            "Result:\n"
            "   transaction:      (string) Raw transaction in hex \n"
            "\nExamples:\n"
            + HelpExampleCli("createrawethpegin", "8b75539cc2b54efe15cd3a0f678545e3f154ca69ba87004d484d10eeb1359cc7 432.109 03220271a8833566153dbfa52c4ba13d2e56970885e6178a4ce6fa81ecaf38c35a")
            + HelpExampleRpc("createrawethpegin", "8b75539cc2b54efe15cd3a0f678545e3f154ca69ba87004d484d10eeb1359cc7 432.109 03220271a8833566153dbfa52c4ba13d2e56970885e6178a4ce6fa81ecaf38c35a")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    CAmount value = AmountFromValue(request.params[1]);
    CDataStream stream(0, 0);
    try {
        stream << value;
    } catch (...) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Amount serialization is invalid.");
    }
    // Need to reinterpret bytes as unsigned chars before adding to witness
    char* buf = stream.data();
    unsigned char* membuf = reinterpret_cast<unsigned char*>(buf);
    std::vector<unsigned char> value_bytes(membuf, membuf + stream.size());

    uint256 genesisBlockHash = Params().ParentGenesisBlockHash();
    uint256 ethHash = ParseHashV(request.params[0], "txid");

    // Pubkey corresponding to the eth address for signing the peg-in
    std::vector<unsigned char> pubkeyBytes(ParseHex(request.params[2].get_str()));
    CPubKey pubKey(pubkeyBytes);
    if (!pubKey.IsFullyValid()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid public key.");
    }

    // Manually construct peg-in transaction, sign it, and send it off.
    // Decrement the output value as much as needed given the total vsize to
    // pay the fees.

    if (!pwalletMain->IsLocked())
        pwalletMain->TopUpKeyPool();

    // Generate a new key that is added to wallet
    CPubKey newKey;
    if (!pwalletMain->GetKeyFromPool(newKey))
        throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, "Error: Keypool ran out, please call keypoolrefill first");
    CKeyID keyID = newKey.GetID();
    pwalletMain->SetAddressBook(keyID, "", "receive");

    // One peg-in input, one wallet output and one fee output
    CMutableTransaction mtx;
    mtx.vin.push_back(CTxIn(COutPoint(ethHash, 0), CScript(), ~(uint32_t)0));
    // mark as peg-in input
    mtx.vin[0].m_is_pegin = true;
    mtx.vout.push_back(CTxOut(Params().GetConsensus().pegged_asset, value, GetScriptForDestination(CBitcoinAddress(keyID).Get())));
    mtx.vout.push_back(CTxOut(Params().GetConsensus().pegged_asset, 0, CScript()));

    // Construct pegin proof
    CScriptWitness pegin_witness;
    std::vector<std::vector<unsigned char> >& stack = pegin_witness.stack;
    stack.push_back(value_bytes);
    stack.push_back(std::vector<unsigned char>(Params().GetConsensus().pegged_asset.begin(), Params().GetConsensus().pegged_asset.end()));
    stack.push_back(std::vector<unsigned char>(genesisBlockHash.begin(), genesisBlockHash.end()));
    stack.push_back(std::vector<unsigned char>(pubKey.begin(), pubKey.end()));
    stack.push_back(std::vector<unsigned char>(ethHash.begin(), ethHash.end()));

    // Check peg-in witness is valid without checking the actual tx
    if (!IsValidEthPeginWitness(pegin_witness, mtx.vin[0].prevout)) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Constructed peg-in witness is invalid.");
    }

    // Put input witness in transaction
    CTxInWitness txinwit;
    txinwit.m_pegin_witness = pegin_witness;
    mtx.wit.vtxinwit.push_back(txinwit);

    // Estimate fee for transaction, decrement fee output(including witness data)
    unsigned int nBytes = GetVirtualTransactionSize(mtx) +
        (1+1+72+1+33/WITNESS_SCALE_FACTOR);
    CAmount nFeeNeeded = CWallet::GetMinimumFee(nBytes, nTxConfirmTarget, mempool);

    mtx.vout[0].nValue = mtx.vout[0].nValue.GetAmount() - nFeeNeeded;
    mtx.vout[1].nValue = mtx.vout[1].nValue.GetAmount() + nFeeNeeded;

    return EncodeHexTx(mtx, RPCSerializationFlags());
}

UniValue claimethpegin(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() != 3)
        throw runtime_error(
            "claimethpegin \"txid\" amount \n"
            "  Claim ERC-20 CBT tokens from eth to Ocean \n"
            "1. \"txid\"            (hex, required) Eth transaction peg-in transaction id\n"
            "2. \"amount\"          (numeric, required) Eth transaction peg-in amount\n"
            "3. \"claim_pubkey\"    (hex, required) The pubkey generated by getethpeginaddress\n"
            "Result:\n"
            "\"txid\"       (string) Txid of the resulting sidechain transaction\n"
            "\nExamples:\n"
            + HelpExampleCli("claimethpegin", "8b75539cc2b54efe15cd3a0f678545e3f154ca69ba87004d484d10eeb1359cc7 432.109 03220271a8833566153dbfa52c4ba13d2e56970885e6178a4ce6fa81ecaf38c35a")
            + HelpExampleRpc("claimethpegin", "8b75539cc2b54efe15cd3a0f678545e3f154ca69ba87004d484d10eeb1359cc7 432.109 03220271a8833566153dbfa52c4ba13d2e56970885e6178a4ce6fa81ecaf38c35a")
        );

    if (GetBoolArg("-validatepegin", DEFAULT_VALIDATE_PEGIN)) {
        if (!validateethpegin(request).getBool()) {
            throw JSONRPCError(RPC_TRANSACTION_ERROR, "Eth pegin invalid");
        }
    }

    // Get raw peg-in transaction
    UniValue ret(createrawethpegin(request));

    // Sign it
    JSONRPCRequest request2;
    UniValue varr(UniValue::VARR);
    varr.push_back(ret);
    request2.params = varr;
    UniValue result = signrawtransaction(request2);

    // Send it
    JSONRPCRequest request3;
    varr = UniValue(UniValue::VARR);
    varr.push_back(result["hex"]);
    request3.params = varr;
    return sendrawtransaction(request3);
}

UniValue createrawpegin(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() < 2 || request.params.size() > 3)
        throw std::runtime_error(
            "createrawpegin bitcoinTx txoutproof ( claim_script )\n"
            "\nCreates a raw transaction to claim coins from the main chain by creating a withdraw transaction with the necessary metadata after the corresponding Bitcoin transaction.\n"
            "Note that this call will not sign the transaction.\n"
            "If a transaction is not relayed it may require manual addition to a functionary mempool in order for it to be mined.\n"
            "\nArguments:\n"
            "1. \"bitcoinTx\"         (string, required) The raw bitcoin transaction (in hex) depositing bitcoin to the mainchain_address generated by getpeginaddress\n"
            "2. \"txoutproof\"        (string, required) A rawtxoutproof (in hex) generated by bitcoind's `gettxoutproof` containing a proof of only bitcoinTx\n"
            "3. \"claim_script\"   (string, optional) The witness program generated by getpeginaddress. Only needed if not in wallet.\n"
            "\nResult:\n"
            "{\n"
            "   \"transaction\"       (string) Raw transaction in hex\n"
            "   \"mature\"            (bool) Whether the peg-in is mature (only included when validating peg-ins)\n"
            "\nExamples:\n"
            + HelpExampleCli("createrawpegin", "\"0200000002b80a99d63ca943d72141750d983a3eeda3a5c5a92aa962884ffb141eb49ffb4f000000006a473044022031ffe1d76decdfbbdb7e2ee6010e865a5134137c261e1921da0348b95a207f9e02203596b065c197e31bcc2f80575154774ac4e80acd7d812c91d93c4ca6a3636f27012102d2130dfbbae9bd27eee126182a39878ac4e117d0850f04db0326981f43447f9efeffffffb80a99d63ca943d72141750d983a3eeda3a5c5a92aa962884ffb141eb49ffb4f010000006b483045022100cf041ce0eb249ae5a6bc33c71c156549c7e5ad877ae39e2e3b9c8f1d81ed35060220472d4e4bcc3b7c8d1b34e467f46d80480959183d743dad73b1ed0e93ec9fd14f012103e73e8b55478ab9c5de22e2a9e73c3e6aca2c2e93cd2bad5dc4436a9a455a5c44feffffff0200e1f5050000000017a914da1745e9b549bd0bfa1a569971c77eba30cd5a4b87e86cbe00000000001976a914a25fe72e7139fd3f61936b228d657b2548b3936a88acc0020000\", \"00000020976e918ed537b0f99028648f2a25c0bd4513644fb84d9cbe1108b4df6b8edf6ba715c424110f0934265bf8c5763d9cc9f1675a0f728b35b9bc5875f6806be3d19cd5b159ffff7f2000000000020000000224eab3da09d99407cb79f0089e3257414c4121cb85a320e1fd0f88678b6b798e0713a8d66544b6f631f9b6d281c71633fb91a67619b189a06bab09794d5554a60105\" \"0014058c769ffc7d12c35cddec87384506f536383f9c\"")
            + HelpExampleRpc("createrawpegin", "\"0200000002b80a99d63ca943d72141750d983a3eeda3a5c5a92aa962884ffb141eb49ffb4f000000006a473044022031ffe1d76decdfbbdb7e2ee6010e865a5134137c261e1921da0348b95a207f9e02203596b065c197e31bcc2f80575154774ac4e80acd7d812c91d93c4ca6a3636f27012102d2130dfbbae9bd27eee126182a39878ac4e117d0850f04db0326981f43447f9efeffffffb80a99d63ca943d72141750d983a3eeda3a5c5a92aa962884ffb141eb49ffb4f010000006b483045022100cf041ce0eb249ae5a6bc33c71c156549c7e5ad877ae39e2e3b9c8f1d81ed35060220472d4e4bcc3b7c8d1b34e467f46d80480959183d743dad73b1ed0e93ec9fd14f012103e73e8b55478ab9c5de22e2a9e73c3e6aca2c2e93cd2bad5dc4436a9a455a5c44feffffff0200e1f5050000000017a914da1745e9b549bd0bfa1a569971c77eba30cd5a4b87e86cbe00000000001976a914a25fe72e7139fd3f61936b228d657b2548b3936a88acc0020000\", \"00000020976e918ed537b0f99028648f2a25c0bd4513644fb84d9cbe1108b4df6b8edf6ba715c424110f0934265bf8c5763d9cc9f1675a0f728b35b9bc5875f6806be3d19cd5b159ffff7f2000000000020000000224eab3da09d99407cb79f0089e3257414c4121cb85a320e1fd0f88678b6b798e0713a8d66544b6f631f9b6d281c71633fb91a67619b189a06bab09794d5554a60105\", \"0014058c769ffc7d12c35cddec87384506f536383f9c\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    if (!IsHex(request.params[0].get_str()) || !IsHex(request.params[1].get_str())) {
        throw JSONRPCError(RPC_TYPE_ERROR, "the first two arguments must be hex strings");
    }

    std::vector<unsigned char> txData = ParseHex(request.params[0].get_str());
    CDataStream ssTx(txData, SER_NETWORK, PROTOCOL_VERSION);
    Sidechain::Bitcoin::CTransactionRef txBTCRef;
    try {
        ssTx >> txBTCRef;
    }
    catch (...) {
        throw JSONRPCError(RPC_TYPE_ERROR, "The included bitcoinTx is malformed. Are you sure that is the whole string?");
    }
    Sidechain::Bitcoin::CTransaction txBTC(*txBTCRef);

    std::vector<unsigned char> txOutProofData = ParseHex(request.params[1].get_str());
    CDataStream ssTxOutProof(txOutProofData, SER_NETWORK, PROTOCOL_VERSION);
    Sidechain::Bitcoin::CMerkleBlock merkleBlock;
    try {
        ssTxOutProof >> merkleBlock;
    }
    catch (...) {
        throw JSONRPCError(RPC_TYPE_ERROR, "The included txoutproof is malformed. Are you sure that is the whole string?");
    }

    if (!ssTxOutProof.empty() || !CheckBitcoinProof(merkleBlock.header.GetHash(), merkleBlock.header.nBits))
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid tx out proof");

    std::vector<uint256> txHashes;
    std::vector<unsigned int> txIndices;
    if (merkleBlock.txn.ExtractMatches(txHashes, txIndices) != merkleBlock.header.hashMerkleRoot)
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid tx out proof");

    if (txHashes.size() != 1 || txHashes[0] != txBTC.GetHash())
        throw JSONRPCError(RPC_INVALID_PARAMETER, "The txoutproof must contain bitcoinTx and only bitcoinTx");

    CScript witnessProgScript;
    unsigned int nOut = txBTC.vout.size();
    if (request.params.size() > 2) {
        // If given manually, no need for it to be a witness script
        std::vector<unsigned char> witnessBytes(ParseHex(request.params[2].get_str()));
        witnessProgScript = CScript(witnessBytes.begin(), witnessBytes.end());
        nOut = GetPeginTxnOutputIndex(txBTC, witnessProgScript);
        if (nOut == txBTC.vout.size()) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Given claim_script does not match the given Bitcoin transaction.");
        }
    }
    else {
        // Look through address book for pegin contract value by extracting the unlderlying witness program from p2sh-p2wpkh
        for (std::map<CTxDestination, CAddressBookData>::const_iterator iter = pwalletMain->mapAddressBook.begin(); iter != pwalletMain->mapAddressBook.end(); ++iter) {
            CBitcoinAddress sidechainAddress(CBitcoinAddress(iter->first));
            CScript witnessProgramScript = GetScriptForWitness(GetScriptForDestination(sidechainAddress.Get()));
            int version;
            std::vector<unsigned char> witnessProgram;
            // Only process witness v0 programs
            if (!witnessProgramScript.IsWitnessProgram(version, witnessProgram) || version != 0) {
                continue;
            }
            nOut = GetPeginTxnOutputIndex(txBTC, witnessProgramScript);
            if (nOut != txBTC.vout.size()) {
                witnessProgScript = witnessProgramScript;
                break;
            }
        }
    }
    if (nOut == txBTC.vout.size()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Failed to find output in bitcoinTx to the mainchain_address from getpeginaddress");
    }
    assert(witnessProgScript != CScript());

    int version = -1;
    std::vector<unsigned char> witnessProgram;
    if (!witnessProgScript.IsWitnessProgram(version, witnessProgram)) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Given or recovered script is not a witness program.");
    }

    CAmount value = txBTC.vout[nOut].nValue;

    CDataStream stream(0, 0);
    try {
        stream << value;
    } catch (...) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Amount serialization is invalid.");
    }
    // Need to reinterpret bytes as unsigned chars before adding to witness
    char* buf = stream.data();
    unsigned char* membuf = reinterpret_cast<unsigned char*>(buf);
    std::vector<unsigned char> value_bytes(membuf, membuf + stream.size());

    uint256 genesisBlockHash = Params().ParentGenesisBlockHash();

    // Manually construct peg-in transaction, sign it, and send it off.
    // Decrement the output value as much as needed given the total vsize to
    // pay the fees.

    if (!pwalletMain->IsLocked())
        pwalletMain->TopUpKeyPool();

    // Generate a new key that is added to wallet
    CPubKey newKey;
    if (!pwalletMain->GetKeyFromPool(newKey))
        throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, "Error: Keypool ran out, please call keypoolrefill first");
    CKeyID keyID = newKey.GetID();

    pwalletMain->SetAddressBook(keyID, "", "receive");

    // One peg-in input, one wallet output and one fee output
    CMutableTransaction mtx;
    mtx.vin.push_back(CTxIn(COutPoint(txHashes[0], nOut), CScript(), ~(uint32_t)0));
    // mark as peg-in input
    mtx.vin[0].m_is_pegin = true;
    mtx.vout.push_back(CTxOut(Params().GetConsensus().pegged_asset, value, GetScriptForDestination(CBitcoinAddress(keyID).Get())));
    mtx.vout.push_back(CTxOut(Params().GetConsensus().pegged_asset, 0, CScript()));

    // Construct pegin proof
    CScriptWitness pegin_witness;
    std::vector<std::vector<unsigned char> >& stack = pegin_witness.stack;
    stack.push_back(value_bytes);
    stack.push_back(std::vector<unsigned char>(Params().GetConsensus().pegged_asset.begin(), Params().GetConsensus().pegged_asset.end()));
    stack.push_back(std::vector<unsigned char>(genesisBlockHash.begin(), genesisBlockHash.end()));
    stack.push_back(std::vector<unsigned char>(witnessProgScript.begin(), witnessProgScript.end()));
    stack.push_back(txData);
    stack.push_back(txOutProofData);

    // Peg-in witness isn't valid, even though the block header is(without depth check)
    // We re-check depth before returning with more descriptive result
    if (!IsValidPeginWitness(pegin_witness, mtx.vin[0].prevout, false)) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Constructed peg-in witness is invalid.");
    }

    // Put input witness in transaction
    CTxInWitness txinwit;
    txinwit.m_pegin_witness = pegin_witness;
    mtx.wit.vtxinwit.push_back(txinwit);

    // Estimate fee for transaction, decrement fee output(including witness data)
    unsigned int nBytes = GetVirtualTransactionSize(mtx) +
        (1+1+72+1+33/WITNESS_SCALE_FACTOR);
    CAmount nFeeNeeded = CWallet::GetMinimumFee(nBytes, nTxConfirmTarget, mempool);

    mtx.vout[0].nValue = mtx.vout[0].nValue.GetAmount() - nFeeNeeded;
    mtx.vout[1].nValue = mtx.vout[1].nValue.GetAmount() + nFeeNeeded;

    UniValue ret(UniValue::VOBJ);

    // Return hex
    std::string strHex = EncodeHexTx(mtx, RPCSerializationFlags());
    ret.push_back(Pair("hex", strHex));

    // Additional block lee-way to avoid bitcoin block races
    if (GetBoolArg("-validatepegin", DEFAULT_VALIDATE_PEGIN)) {
        ret.push_back(Pair("mature", IsConfirmedBitcoinBlock(merkleBlock.header.GetHash(), Params().GetConsensus().pegin_min_depth+2)));
    }

    return ret;
}

UniValue claimpegin(const JSONRPCRequest& request)
{

    if (request.fHelp || request.params.size() < 2 || request.params.size() > 3)
        throw std::runtime_error(
            "claimpegin bitcoinTx txoutproof ( claim_script )\n"
            "\nClaim coins from the main chain by creating a withdraw transaction with the necessary metadata after the corresponding Bitcoin transaction.\n"
            "Note that the transaction will not be relayed unless it is buried at least 102 blocks deep.\n"
            "If a transaction is not relayed it may require manual addition to a functionary mempool in order for it to be mined.\n"
            "\nArguments:\n"
            "1. \"bitcoinTx\"         (string, required) The raw bitcoin transaction (in hex) depositing bitcoin to the mainchain_address generated by getpeginaddress\n"
            "2. \"txoutproof\"        (string, required) A rawtxoutproof (in hex) generated by bitcoind's `gettxoutproof` containing a proof of only bitcoinTx\n"
            "3. \"claim_script\"   (string, optional) The witness program generated by getpeginaddress. Only needed if not in wallet.\n"
            "\nResult:\n"
            "\"txid\"                 (string) Txid of the resulting sidechain transaction\n"
            "\nExamples:\n"
            + HelpExampleCli("claimpegin", "\"0200000002b80a99d63ca943d72141750d983a3eeda3a5c5a92aa962884ffb141eb49ffb4f000000006a473044022031ffe1d76decdfbbdb7e2ee6010e865a5134137c261e1921da0348b95a207f9e02203596b065c197e31bcc2f80575154774ac4e80acd7d812c91d93c4ca6a3636f27012102d2130dfbbae9bd27eee126182a39878ac4e117d0850f04db0326981f43447f9efeffffffb80a99d63ca943d72141750d983a3eeda3a5c5a92aa962884ffb141eb49ffb4f010000006b483045022100cf041ce0eb249ae5a6bc33c71c156549c7e5ad877ae39e2e3b9c8f1d81ed35060220472d4e4bcc3b7c8d1b34e467f46d80480959183d743dad73b1ed0e93ec9fd14f012103e73e8b55478ab9c5de22e2a9e73c3e6aca2c2e93cd2bad5dc4436a9a455a5c44feffffff0200e1f5050000000017a914da1745e9b549bd0bfa1a569971c77eba30cd5a4b87e86cbe00000000001976a914a25fe72e7139fd3f61936b228d657b2548b3936a88acc0020000\", \"00000020976e918ed537b0f99028648f2a25c0bd4513644fb84d9cbe1108b4df6b8edf6ba715c424110f0934265bf8c5763d9cc9f1675a0f728b35b9bc5875f6806be3d19cd5b159ffff7f2000000000020000000224eab3da09d99407cb79f0089e3257414c4121cb85a320e1fd0f88678b6b798e0713a8d66544b6f631f9b6d281c71633fb91a67619b189a06bab09794d5554a60105\" \"0014058c769ffc7d12c35cddec87384506f536383f9c\"")
            + HelpExampleRpc("claimpegin", "\"0200000002b80a99d63ca943d72141750d983a3eeda3a5c5a92aa962884ffb141eb49ffb4f000000006a473044022031ffe1d76decdfbbdb7e2ee6010e865a5134137c261e1921da0348b95a207f9e02203596b065c197e31bcc2f80575154774ac4e80acd7d812c91d93c4ca6a3636f27012102d2130dfbbae9bd27eee126182a39878ac4e117d0850f04db0326981f43447f9efeffffffb80a99d63ca943d72141750d983a3eeda3a5c5a92aa962884ffb141eb49ffb4f010000006b483045022100cf041ce0eb249ae5a6bc33c71c156549c7e5ad877ae39e2e3b9c8f1d81ed35060220472d4e4bcc3b7c8d1b34e467f46d80480959183d743dad73b1ed0e93ec9fd14f012103e73e8b55478ab9c5de22e2a9e73c3e6aca2c2e93cd2bad5dc4436a9a455a5c44feffffff0200e1f5050000000017a914da1745e9b549bd0bfa1a569971c77eba30cd5a4b87e86cbe00000000001976a914a25fe72e7139fd3f61936b228d657b2548b3936a88acc0020000\", \"00000020976e918ed537b0f99028648f2a25c0bd4513644fb84d9cbe1108b4df6b8edf6ba715c424110f0934265bf8c5763d9cc9f1675a0f728b35b9bc5875f6806be3d19cd5b159ffff7f2000000000020000000224eab3da09d99407cb79f0089e3257414c4121cb85a320e1fd0f88678b6b798e0713a8d66544b6f631f9b6d281c71633fb91a67619b189a06bab09794d5554a60105\", \"0014058c769ffc7d12c35cddec87384506f536383f9c\"")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    if (IsInitialBlockDownload()) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Peg-ins cannot be completed during initial sync or reindexing.");
    }

    // Get raw peg-in transaction
    UniValue ret(createrawpegin(request));

    // Make sure it can be propagated and confirmed
    if (!ret["mature"].isNull() && ret["mature"].get_bool() == false) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Peg-in Bitcoin transaction needs more confirmations to be sent.");
    }

    // Sign it
    JSONRPCRequest request2;
    UniValue varr(UniValue::VARR);
    varr.push_back(ret["hex"]);
    request2.params = varr;
    UniValue result = signrawtransaction(request2);

    // Send it
    JSONRPCRequest request3;
    varr = UniValue(UniValue::VARR);
    varr.push_back(result["hex"]);
    request3.params = varr;
    return sendrawtransaction(request3);
}

UniValue createrawissuance(const JSONRPCRequest& request)
{
  if (request.fHelp || request.params.size() !=9)
    throw runtime_error(
            "createrawissuance assetaddress assetamount tokenaddress tokenamount changeaddress feeamount inputtxid vout\n"
            "\nCreate a raw unsigned asset issuance transaction to specified addresses with a policyAsset outpoint as input.\n"
            "\nArguments:\n"
	    "1. \"assetaddress\"          (string, required) Address to send issued asset to.\n"
            "2. \"assetamount\"           (numeric or string, required) Amount of asset to generate.\n"
	    "3. \"tokenaddress\"          (string, required) Address to send reissuance token to.\n"
            "4. \"tokenamount\"           (numeric or string, required) Amount of reissuance tokens to generate. These will allow you to reissue the asset if in wallet using `reissueasset`. These tokens are not consumed during reissuance.\n"
	    "5. \"changeaddress\"         (string, required) Address to return the policyAsset input.\n"
	    "6. \"changeamount\"          (numeric or string, required) Return policyAsset amount.\n"
	    "7. \"changenum\"             (numeric or string, required) Number of change outputs to be generated\n"
            "8. \"inputtxid\"             (string, required) policyAsset input TXID.\n"
	    "9. \"vout\"                  (numeric or string, required) policyAsset TXID output index\n"
            "\nResult:\n"
            "{                        (json object)\n"
            "  \"rawtx\":\"<rawtx>\",   (string) Hex encoded raw unsigned issuance transaction.\n"
            "  \"entropy\":\"<entropy>\" (string) Entropy of the asset type.\n"
            "  \"asset\":\"<asset>\", (string) Asset type for issuance if known.\n"
            "  \"token\":\"<token>\", (string) Token type for issuance.\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("createrawissuance", "\"2dhfx249gZKqMGKtKAgceuCyDiHVEeVZWzU\" 100.0 \"2dp5EWgkc4RyzVvBvAyRAMuJ1hS84BgSBLj\" 1.0 \"2djpn7hq9Jh3jx3sjhPXuhUpJQWHrtXrKLr\" 10.0 1 \"42b7101f4596d39cfb5f5e5ca7b6873474607b04f365590f478261ad74dae717\" 1 ")
            + HelpExampleRpc("createrawissuance", "\"2dhfx249gZKqMGKtKAgceuCyDiHVEeVZWzU\" 100.0 \"2dp5EWgkc4RyzVvBvAyRAMuJ1hS84BgSBLj\" 1.0 \"2djpn7hq9Jh3jx3sjhPXuhUpJQWHrtXrKLr\" 10.0 1 \"42b7101f4596d39cfb5f5e5ca7b6873474607b04f365590f478261ad74dae717\" 1 ")
			);
  //Get the output addresses
  CBitcoinAddress assetAddr(request.params[0].get_str());
  CBitcoinAddress tokenAddr(request.params[2].get_str());
  CBitcoinAddress changeAddr(request.params[4].get_str());

  if (!assetAddr.IsValid())
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid Asset token address");

  if (!tokenAddr.IsValid())
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid Reissuance token address");

  if (!changeAddr.IsValid())
    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid policy asset return address");

  //get the output amounts
  CAmount nAmount = AmountFromValue(request.params[1]);
  CAmount nTokens = AmountFromValue(request.params[3]);
  CAmount nChange = AmountFromValue(request.params[5]);

  if (nAmount == 0 && nTokens == 0) {
    throw JSONRPCError(RPC_TYPE_ERROR, "Issuance must have one non-zero component");
  }

  //get number of change outputs required
  int nChangeOutputs = atoi(request.params[6].get_str());

  bool fBlindIssuances = false;

  //get the input outpoint from RPC
  uint256 prevtxhash;
  prevtxhash.SetHex(request.params[7].get_str());
  uint32_t nout = atoi(request.params[8].get_str());
  COutPoint policyOutpoint(prevtxhash,nout);

  CMutableTransaction rawTx;

  // Calculate entropy, asset and token IDs from the input outpoint
  uint256 entropy;
  CAsset asset;
  CAsset token;
  GenerateAssetEntropy(entropy, policyOutpoint, uint256());
  CalculateAsset(asset, entropy);
  CalculateReissuanceToken(token, entropy, fBlindIssuances);

  //generate the outputs
  CAsset pAsset(issuanceAsset);
  CTxOut txoutAsset(asset,nAmount,GetScriptForDestination(assetAddr.Get()));
  rawTx.vout.push_back(txoutAsset);
  CTxOut txoutToken(token,nTokens,GetScriptForDestination(tokenAddr.Get()));
  rawTx.vout.push_back(txoutToken);
  CTxOut txoutChange(pAsset,nChange,GetScriptForDestination(changeAddr.Get()));
  vector<CTxOut> changeOuts;
  for(int it=0;it<nChangeOutputs;it++) {
    rawTx.vout.push_back(txoutChange);
  }

  //standard sequence number
  uint32_t nSequence = (rawTx.nLockTime ? std::numeric_limits<uint32_t>::max() - 1 : std::numeric_limits<uint32_t>::max());

  //generate input from the provided outpoint
  CTxIn in(policyOutpoint, CScript(), nSequence);

  //push single input to raw transaction
  rawTx.vin.push_back(in);

  //set flags and amounts for asset issuance and reissuance token in the input
  rawTx.vin[0].assetIssuance.nAmount = nAmount;
  rawTx.vin[0].assetIssuance.nInflationKeys = nTokens;

  //return result
  UniValue ret(UniValue::VOBJ);
  ret.push_back(Pair("rawtx", EncodeHexTx(rawTx)));
  ret.push_back(Pair("vin", 0));
  ret.push_back(Pair("entropy", entropy.GetHex()));
  ret.push_back(Pair("asset", asset.GetHex()));
  ret.push_back(Pair("token", token.GetHex()));
  return ret;
}

UniValue issueasset(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 2 || request.params.size() > 3)
        throw runtime_error(
            "issueasset assetamount tokenamount ( blind )\n"
            "\nCreate an asset. Must have funds in wallet to do so. Returns asset hex id.\n"
            "\nArguments:\n"
            "1. \"assetamount\"           (numeric or string, required) Amount of asset to generate.\n"
            "2. \"tokenamount\"           (numeric or string, required) Amount of reissuance tokens to generate. These will allow you to reissue the asset if in wallet using `reissueasset`. These tokens are not consumed during reissuance.\n"
            "3. \"blind\"                 (bool, optional, default=true) Whether to blind the issuances.\n"
            "\nResult:\n"
            "{                        (json object)\n"
            "  \"txid\":\"<txid>\",   (string) Transaction id for issuance.\n"
            "  \"vin\":\"n\",         (numeric) The input position of the issuance in the transaction.\n"
            "  \"entropy\":\"<entropy>\" (string) Entropy of the asset type.\n"
            "  \"asset\":\"<asset>\", (string) Asset type for issuance if known.\n"
            "  \"token\":\"<token>\", (string) Token type for issuance.\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("issueasset", "10 0")
            + HelpExampleRpc("issueasset", "10, 0")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    CAmount nAmount = AmountFromValue(request.params[0]);
    CAmount nTokens = AmountFromValue(request.params[1]);
    if (nAmount == 0 && nTokens == 0) {
        throw JSONRPCError(RPC_TYPE_ERROR, "Issuance must have one non-zero component");
    }

    bool fBlindIssuances = (!pwalletMain->GetDisableCt() && request.params.size() < 3) ||
                        (request.params.size() == 3 && request.params[2].get_bool());

    if (!pwalletMain->IsLocked())
        pwalletMain->TopUpKeyPool();

    // Generate a new key that is added to wallet
    CPubKey newKey;
    CKeyID keyID;
    CBitcoinAddress assetAddr;
    CBitcoinAddress tokenAddr;
    CPubKey assetKey;
    CPubKey tokenKey;

    if (nAmount > 0) {
        if (!pwalletMain->GetKeyFromPool(newKey))
            throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, "Error: Keypool ran out, please call keypoolrefill first");
        keyID = newKey.GetID();
        pwalletMain->SetAddressBook(keyID, "", "receive");
        assetAddr = CBitcoinAddress(keyID);
        assetKey = !pwalletMain->GetDisableCt() ?
            pwalletMain->GetBlindingPubKey(GetScriptForDestination(assetAddr.Get())) : CPubKey();
    }
    if (nTokens > 0) {
        if (!pwalletMain->GetKeyFromPool(newKey))
            throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, "Error: Keypool ran out, please call keypoolrefill first");
        keyID = newKey.GetID();
        pwalletMain->SetAddressBook(keyID, "", "receive");
        tokenAddr = CBitcoinAddress(keyID);
        tokenKey = !pwalletMain->GetDisableCt() ?
            pwalletMain->GetBlindingPubKey(GetScriptForDestination(CTxDestination(keyID))) : CPubKey();
    }

    CWalletTx wtx;
    uint256 dummyentropy;
    CAsset dummyasset;
    SendGenerationTransaction(GetScriptForDestination(assetAddr.Get()), assetKey, GetScriptForDestination(tokenAddr.Get()), tokenKey, nAmount, nTokens, fBlindIssuances, dummyentropy, dummyasset, dummyasset, wtx);

    // Calculate asset type, assumes first vin is used for issuance
    uint256 entropy;
    CAsset asset;
    CAsset token;
    GenerateAssetEntropy(entropy, wtx.tx->vin[0].prevout, uint256());
    CalculateAsset(asset, entropy);
    CalculateReissuanceToken(token, entropy, fBlindIssuances);

    std::string blinds;
    for (unsigned int i=0; i<wtx.tx->vout.size(); i++) {
        blinds += "blind:" + wtx.GetOutputBlindingFactor(i).ToString() + "\n";
        blinds += "assetblind:" + wtx.GetOutputAssetBlindingFactor(i).ToString() + "\n";
    }
    blinds += "issuanceblind:" + wtx.GetIssuanceBlindingFactor(0, false).ToString() + "\n";
    blinds += "tokenblind:" + wtx.GetIssuanceBlindingFactor(0, true).ToString() + "\n";

    AuditLogPrintf("%s : issueasset txid:%s\nblinds:\n%s\n", getUser(), wtx.GetHash().GetHex(), blinds);

    UniValue ret(UniValue::VOBJ);
    ret.push_back(Pair("txid", wtx.tx->GetHash().GetHex()));
    ret.push_back(Pair("vin", 0));
    ret.push_back(Pair("entropy", entropy.GetHex()));
    ret.push_back(Pair("asset", asset.GetHex()));
    ret.push_back(Pair("token", token.GetHex()));
    return ret;
}

UniValue createrawreissuance(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() !=7)
        throw runtime_error(

            "createrawreissuance assetaddress assetamount tokenaddress tokenamount inputtxid vout entropy\n"
            "\nCreate a raw unsigned asset issuance transaction to specified addresses with a policyAsset outpoint as input.\n"
            "\nArguments:\n"
            "1. \"assetaddress\"          (string, required) Address to send re-issued asset to.\n"
            "2. \"assetamount\"           (numeric or string, required) Amount of re-issued asset to generate.\n"
            "3. \"tokenaddress\"          (string, required) Address to return the reissuance token to.\n"
            "4. \"tokenamount\"           (numeric or string, required) Amount of returned re-issuance tokens to generate.\n"
            "5. \"inputtxid\"             (string, required) re-issuance token input TXID.\n"
            "6. \"vout\"                  (numeric or string, required) re-issuance token TXID output index\n"
            "7. \"entropy\"               (string, required) the issuance entropy.\n"
            "\nResult:\n"
            "{                        (json object)\n"
            "  \"hex\":\"<hex>\",   (string) Hex encoded raw unsigned issuance transaction.\n"
            "  \"asset\":\"<asset>\",   (string) Re-issued asset ID\n"
            "  \"token\":\"<token>\",   (string) Re-issuance token ID\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("createrawreissuance", "\"2dhfx249gZKqMGKtKAgceuCyDiHVEeVZWzU\" 0.01 \"2dp5EWgkc4RyzVvBvAyRAMuJ1hS84BgSBLj\" 1.0 \"42b7101f4596d39cfb5f5e5ca7b6873474607b04f365590f478261ad74dae717\" 1 c8213b3ee67b02bcca0148d8581d0f616b822d317d5b26432d2f1f03beda2fa7")
            + HelpExampleRpc("createrawreissuance", "\"2dhfx249gZKqMGKtKAgceuCyDiHVEeVZWzU\" 0.01 \"2dp5EWgkc4RyzVvBvAyRAMuJ1hS84BgSBLj\" 1.0 \"42b7101f4596d39cfb5f5e5ca7b6873474607b04f365590f478261ad74dae717\" 1 c8213b3ee67b02bcca0148d8581d0f616b822d317d5b26432d2f1f03beda2fa7")
            );

    //Get the output addresses
    CBitcoinAddress assetAddr(request.params[0].get_str());
    CBitcoinAddress tokenAddr(request.params[2].get_str());

    if (!assetAddr.IsValid())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid Asset token address");

    if (!tokenAddr.IsValid())
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid Reissuance token address");

    //get the output amounts
    CAmount nAmount = AmountFromValue(request.params[1]);
    CAmount nTokens = AmountFromValue(request.params[3]);

    if (nAmount == 0 || nTokens == 0) {
        throw JSONRPCError(RPC_TYPE_ERROR, "Re-issuance must be non-zero component");
    }

    //get the input outpoint from RPC
    uint256 prevtxhash;
    prevtxhash.SetHex(request.params[4].get_str());
    uint32_t nout = atoi(request.params[5].get_str());
    COutPoint tokenOutpoint(prevtxhash,nout);

    CMutableTransaction rawTx;

    // Calculate asset and token IDs from the input entropy
    uint256 entropy;
    entropy.SetHex(request.params[6].get_str());
    CAsset asset;
    CalculateAsset(asset, entropy);
    CAsset token;
    CalculateReissuanceToken(token, entropy, false);

    //generate the outputs
    CTxOut txoutAsset(asset,nAmount,GetScriptForDestination(assetAddr.Get()));
    rawTx.vout.push_back(txoutAsset);
    CTxOut txoutToken(token,nTokens,GetScriptForDestination(tokenAddr.Get()));
    rawTx.vout.push_back(txoutToken);

    //standard sequence number
    uint32_t nSequence = (rawTx.nLockTime ? std::numeric_limits<uint32_t>::max() - 1 : std::numeric_limits<uint32_t>::max());

    //generate input from the provided outpoint
    CTxIn in(tokenOutpoint, CScript(), nSequence);

    //push single input to raw transaction
    rawTx.vin.push_back(in);

    //set flags and amounts for asset issuance and reissuance token in the input
    rawTx.vin[0].assetIssuance.assetBlindingNonce = CAssetIssuance::UNBLINDED_REISSUANCE_NONCE;
    rawTx.vin[0].assetIssuance.nAmount = nAmount;
    rawTx.vin[0].assetIssuance.assetEntropy = entropy;

    //return result
    UniValue ret(UniValue::VOBJ);
    ret.push_back(Pair("hex", EncodeHexTx(rawTx)));
    ret.push_back(Pair("asset", asset.GetHex()));
    ret.push_back(Pair("token", token.GetHex()));
    return ret;
}

UniValue reissueasset(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 2)
        throw runtime_error(
            "reissueasset asset assetamount\n"
            "\nCreate more of an already issued asset. Must have reissuance token in wallet to do so. Reissuing does not affect your reissuance token balance, only asset.\n"
            "\nArguments:\n"
            "1. \"asset\"                 (string, required) The asset you want to re-issue. The corresponding token must be in your wallet.\n"
            "2. \"assetamount\"           (numeric or string, required) Amount of additional asset to generate.\n"
            "\nResult:\n"
            "{                        (json object)\n"
            "  \"txid\":\"<txid>\",   (string) Transaction id for issuance.\n"
            "  \"vin\":\"n\",         (numeric) The input position of the issuance in the transaction.\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("reissueasset", "<asset> 0")
            + HelpExampleRpc("reissueasset", "<asset>, 0")
        );

    LOCK2(cs_main, pwalletMain->cs_wallet);

    std::string assetstr = request.params[0].get_str();

    CAsset asset = GetAssetFromString(assetstr);

    CAmount nAmount = AmountFromValue(request.params[1]);
    if (nAmount <= 0)
        throw JSONRPCError(RPC_TYPE_ERROR, "Reissuance must create a non-zero amount.");

    if (!pwalletMain->IsLocked())
        pwalletMain->TopUpKeyPool();

    // Find the entropy and reissuance token in wallet
    std::map<uint256, std::pair<CAsset, CAsset> > tokenMap = pwalletMain->GetReissuanceTokenTypes();
    CAsset reissuanceToken;
    uint256 entropy;
    for (const auto& it : tokenMap) {
        if (it.second.second == asset) {
            reissuanceToken = it.second.first;
            entropy = it.first;
        }
        if (it.second.first == asset) {
            throw JSONRPCError(RPC_WALLET_ERROR, "Asset given is a reissuance token type and can not be reissued.");
        }
    }
    if (reissuanceToken.IsNull()) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Asset reissuance token definition could not be found in wallet.");
    }

    CPubKey newKey;
    CKeyID keyID;
    CBitcoinAddress assetAddr;
    CPubKey assetKey;
    CBitcoinAddress tokenAddr;
    CPubKey tokenKey;

    // Add destination for the to-be-created asset
    if (!pwalletMain->GetKeyFromPool(newKey))
        throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, "Error: Keypool ran out, please call keypoolrefill first");
    keyID = newKey.GetID();
    pwalletMain->SetAddressBook(keyID, "", "receive");
    assetAddr = CBitcoinAddress(keyID);
    assetKey = !pwalletMain->GetDisableCt() ?
        pwalletMain->GetBlindingPubKey(GetScriptForDestination(assetAddr.Get())) : CPubKey();

    // Add destination for tokens we are moving
    if (!pwalletMain->GetKeyFromPool(newKey))
        throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, "Error: Keypool ran out, please call keypoolrefill first");
    keyID = newKey.GetID();
    pwalletMain->SetAddressBook(keyID, "", "receive");
    tokenAddr = CBitcoinAddress(keyID);
    tokenKey = !pwalletMain->GetDisableCt() ?
        pwalletMain->GetBlindingPubKey(GetScriptForDestination(CTxDestination(keyID))) : CPubKey();

    // Attempt a send.
    CWalletTx wtx;
    SendGenerationTransaction(GetScriptForDestination(assetAddr.Get()), assetKey, GetScriptForDestination(tokenAddr.Get()), tokenKey, nAmount, -1, !pwalletMain->GetDisableCt(), entropy, asset, reissuanceToken, wtx);

    std::string blinds;
    for (unsigned int i=0; i<wtx.tx->vout.size(); i++) {
        blinds += "blind:" + wtx.GetOutputBlindingFactor(i).ToString() + "\n";
        blinds += "assetblind:" + wtx.GetOutputAssetBlindingFactor(i).ToString() + "\n";
    }

    UniValue obj(UniValue::VOBJ);
    obj.push_back(Pair("txid", wtx.tx->GetHash().GetHex()));
    for (uint64_t i = 0; i < wtx.tx->vin.size(); i++) {
        if (!wtx.tx->vin[i].assetIssuance.IsNull()) {
            obj.push_back(Pair("vin", i));
            blinds += "issuanceblind:" + wtx.GetIssuanceBlindingFactor(i, false).ToString() + "\n";
            break;
        }
    }

    AuditLogPrintf("%s : reissueasset txid:%s\nblinds:\n%s\n", getUser(), wtx.GetHash().GetHex(), blinds);

    return obj;
}

UniValue createrawburn(const JSONRPCRequest& request)
{
    if (request.fHelp || request.params.size() !=4)
        throw runtime_error(
            "createrawissuance txid vout asset amount\n"
            "\nCreate a raw unsigned asset burn transaciton that sends the input amount to an OP_RETURN output.\n"
            "\nArguments:\n"
            "1. \"txid\"          (string, required) TxID to burn.\n"
            "2. \"vin\"           (numeric or string, required) vin to burn.\n"
            "3. \"asset\"          (string, required) asset type of the outpoint\n"
            "4. \"amount\"          (string, required) amount of output\n"
            "\nResult:\n"
            "{                        (json object)\n"
            "  \"hex\":\"<hex>\",   (string) Hex encoded raw unsigned burn transaction.\n"
            "}\n"
            "\nExamples:\n"
            + HelpExampleCli("createrawburn", "\"42b7101f4596d39cfb5f5e5ca7b6873474607b04f365590f478261ad74dae717\" 1 c8213b3ee67b02bcca0148d8581d0f616b822d317d5b26432d2f1f03beda2fa7 0.3234400")
            + HelpExampleRpc("createrawburn", "\"42b7101f4596d39cfb5f5e5ca7b6873474607b04f365590f478261ad74dae717\" 1 c8213b3ee67b02bcca0148d8581d0f616b822d317d5b26432d2f1f03beda2fa7 0.3234400")
            );

    //get the output amounts
    CAmount nAmount = AmountFromValue(request.params[3]);

    //get the input outpoint from RPC
    uint256 prevtxhash;
    prevtxhash.SetHex(request.params[0].get_str());
    uint32_t nout = atoi(request.params[1].get_str());
    COutPoint tokenOutpoint(prevtxhash,nout);

    CMutableTransaction rawTx;

    // Calculate asset and token IDs from the input entropy
    CAsset asset;
    asset.SetHex(request.params[2].get_str());

    CScript destroyScript(OP_RETURN);

    //generate the outputs
    CTxOut txoutAsset(asset,nAmount,destroyScript);
    rawTx.vout.push_back(txoutAsset);

    //standard sequence number
    uint32_t nSequence = (rawTx.nLockTime ? std::numeric_limits<uint32_t>::max() - 1 : std::numeric_limits<uint32_t>::max());

    //generate input from the provided outpoint
    CTxIn in(tokenOutpoint, CScript(), nSequence);

    //push single input to raw transaction
    rawTx.vin.push_back(in);

    //return result
    UniValue ret(UniValue::VOBJ);
    ret.push_back(Pair("hex", EncodeHexTx(rawTx)));
    return ret;
}

UniValue listissuances(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() > 1)
        throw runtime_error(
            "listissuances ( asset ) \n"
            "\nList all issuances known to the wallet for the given asset, or for all issued assets if none provided.\n"
            "\nArguments:\n"
            "1. \"asset\"                 (string, optional) The asset whose issaunces you wish to list.\n"
            "\nResult:\n"
            "[                     (json array of objects)\n"
            "  {\n"
            "    \"txid\":\"<txid>\",   (string) Transaction id for issuance.\n"
            "    \"entropy\":\"<entropy>\" (string) Entropy of the asset type.\n"
            "    \"asset\":\"<asset>\", (string) Asset type for issuance if known.\n"
            "    \"assetlabel\":\"<assetlabel>\", (string) Asset label for issuance if set.\n"
            "    \"token\":\"<token>\", (string) Token type for issuance.\n"
            "    \"vin\":\"n\",         (numeric) The input position of the issuance in the transaction.\n"
            "    \"assetamount\":\"X.XX\",     (numeric) The amount of asset issued. Is -1 if blinded and unknown to wallet.\n"
            "    \"tokenamount\":\"X.XX\",     (numeric) The reissuance token amount issued. Is -1 if blinded and unknown to wallet.\n"
            "    \"isreissuance\":\"<bool>\",  (bool) True if this is a reissuance.\n"
            "    \"assetblinds\":\"<blinder>\" (string) Hex blinding factor for asset amounts.\n"
            "    \"tokenblinds\":\"<blinder>\" (string) Hex blinding factor for token amounts.\n"
            "  }\n"
            "  ,...\n"
            "]\n"
            "\"\"                 (array) List of transaction issuances and information in wallet\n"
            + HelpExampleCli("listissuances", "<asset>")
            + HelpExampleRpc("listissuances", "<asset>")
        );
    RPCTypeCheck(request.params, boost::assign::list_of(UniValue::VSTR));

    LOCK2(cs_main, pwalletMain->cs_wallet);

    std::string assetstr;
    CAsset assetfilter;
    if (request.params.size() > 0) {
        assetstr = request.params[0].get_str();
        if (!IsHex(assetstr) || assetstr.size() != 64)
            throw JSONRPCError(RPC_TYPE_ERROR, "Asset must be a hex string of length 64");
        assetfilter.SetHex(assetstr);
    }

    UniValue issuancelist(UniValue::VARR);
    for (const auto& it : pwalletMain->mapWallet) {
        const CWalletTx* pcoin = &it.second;
        CAsset asset;
        CAsset token;
        uint256 entropy;
        for (uint64_t vinIndex = 0; vinIndex < pcoin->tx->vin.size(); vinIndex++) {
            UniValue item(UniValue::VOBJ);
            const CAssetIssuance& issuance = pcoin->tx->vin[vinIndex].assetIssuance;
            if (issuance.IsNull()) {
                continue;
            }
            if (!issuance.IsReissuance()) {
                GenerateAssetEntropy(entropy, pcoin->tx->vin[vinIndex].prevout, issuance.assetEntropy);
                CalculateAsset(asset, entropy);
                // Null is considered explicit
                CalculateReissuanceToken(token, entropy, issuance.nAmount.IsCommitment());
                item.push_back(Pair("isreissuance", false));
                item.push_back(Pair("token", token.GetHex()));
                CAmount itamount = pcoin->GetIssuanceAmount(vinIndex, true);
                item.push_back(Pair("tokenamount", (itamount == -1 ) ? -1 : ValueFromAmount(itamount)));
                item.push_back(Pair("tokenblinds", pcoin->GetIssuanceBlindingFactor(vinIndex, true).GetHex()));
                item.push_back(Pair("entropy", entropy.GetHex()));
            } else {
                CalculateAsset(asset, issuance.assetEntropy);
                item.push_back(Pair("isreissuance", true));
                item.push_back(Pair("entropy", issuance.assetEntropy.GetHex()));
            }
            item.push_back(Pair("txid", pcoin->tx->GetHash().GetHex()));
            item.push_back(Pair("vin", vinIndex));
            item.push_back(Pair("asset", asset.GetHex()));
            const std::string label = gAssetsDir.GetLabel(asset);
            if (label != "") {
                item.push_back(Pair("assetlabel", label));
            }
            CAmount iaamount = pcoin->GetIssuanceAmount(vinIndex, false);
            item.push_back(Pair("assetamount", (iaamount == -1 ) ? -1 : ValueFromAmount(iaamount)));
            item.push_back(Pair("assetblinds", pcoin->GetIssuanceBlindingFactor(vinIndex, false).GetHex()));
            if (!assetfilter.IsNull() && assetfilter != asset) {
                continue;
            }
            issuancelist.push_back(item);
        }
    }
    return issuancelist;

}

UniValue dumpassetlabels(const JSONRPCRequest& request)
{
    if (!EnsureWalletIsAvailable(request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 0)
        throw runtime_error(
            "dumpassetlabels\n"
            "\nLists all known asset id/label pairs in this wallet. This list can be modified with `-assetdir` configuration argument.\n"
            + HelpExampleCli("generateasset", "\"my asset\" 10" )
            + HelpExampleRpc("generateasset", "\"my asset\" 10" )
        );
    UniValue obj(UniValue::VOBJ);
    for (CAsset as : gAssetsDir.GetKnownAssets()) {
        obj.push_back(Pair(gAssetsDir.GetLabel(as), as.GetHex()));
    }
    return obj;
}

extern UniValue dumpprivkey(const JSONRPCRequest& request); // in rpcdump.cpp
extern UniValue importprivkey(const JSONRPCRequest& request);
extern UniValue importaddress(const JSONRPCRequest& request);
extern UniValue importpubkey(const JSONRPCRequest& request);
extern UniValue dumpwallet(const JSONRPCRequest& request);
extern UniValue dumpderivedkeys(const JSONRPCRequest& request);
extern UniValue dumpkycfile(const JSONRPCRequest& request);
extern UniValue createkycfile(const JSONRPCRequest& request);
extern UniValue readkycfile(const JSONRPCRequest& request);
extern UniValue getderivedkeys(const JSONRPCRequest& request);
extern UniValue validatederivedkeys(const JSONRPCRequest& request);
extern UniValue importwallet(const JSONRPCRequest& request);
extern UniValue importprunedfunds(const JSONRPCRequest& request);
extern UniValue removeprunedfunds(const JSONRPCRequest& request);
extern UniValue importmulti(const JSONRPCRequest& request);
extern UniValue dumpblindingkey(const JSONRPCRequest& request);
extern UniValue dumpissuanceblindingkey(const JSONRPCRequest& request);
extern UniValue importblindingkey(const JSONRPCRequest& request);
extern UniValue importissuanceblindingkey(const JSONRPCRequest& request);

static const CRPCCommand commands[] =
{ //  category              name                        actor (function)           okSafeMode
    //  --------------------- ------------------------    -----------------------    ----------
    { "rawtransactions",    "fundrawtransaction",       &fundrawtransaction,        false,  {"hexstring","options"} },
    { "hidden",             "resendwallettransactions", &resendwallettransactions,  true,   {} },
    { "wallet",             "abandontransaction",       &abandontransaction,        false,  {"txid"} },
    { "wallet",             "addmultisigaddress",       &addmultisigaddress,        true,   {"nrequired","keys","account"} },
    { "wallet",             "addwitnessaddress",        &addwitnessaddress,         true,   {"address"} },
    { "wallet",             "backupwallet",             &backupwallet,              true,   {"destination"} },
    { "wallet",             "createkycfile",            &createkycfile,             true,   {"filename","pubkeylist","multisiglist"} },
    { "wallet",             "dumpblindingkey",          &dumpblindingkey,           true,   {} },
    { "wallet",             "dumpassetlabels",          &dumpassetlabels,           true,   {} },
    { "wallet",             "dumpprivkey",              &dumpprivkey,               true,   {"address"}  },
    { "wallet",             "dumpissuanceblindingkey",  &dumpissuanceblindingkey,   true,   {"txid", "vin"} },
    { "wallet",             "dumpwallet",               &dumpwallet,                true,   {"filename"} },
    { "wallet",             "dumpderivedkeys",          &dumpderivedkeys,           true,   {"filename"} },
    { "wallet",             "dumpkycfile",              &dumpkycfile,               true,   {"filename"} },
    { "wallet",             "readkycfile",              &readkycfile,               true,   {"filename", "outfilename", "onboardpubkey"} },
    { "wallet",             "onboarduser",              &onboarduser,               false,  {"filename"} },
    { "wallet",             "blacklistuser",            &blacklistuser,             false,  {"filename"} },
    { "wallet",             "topupkycpubkeys",          &topupkycpubkeys,           false,  {"nkeys"} },
    { "wallet",             "removekycpubkey",          &removekycpubkey,           false,  {"kycpubkey"} },
    { "wallet",             "blacklistkycpubkey",       &blacklistkycpubkey,        false,  {"kycpubkey"} },
    { "wallet",             "whitelistkycpubkeys",      &whitelistkycpubkeys,       false,  {"kycpubkeys"} },
    { "wallet",             "validatederivedkeys",      &validatederivedkeys,       true,   {"filename"} },
    { "wallet",             "encryptwallet",            &encryptwallet,             true,   {"passphrase"} },
    { "wallet",             "getethpegin",              &getethpegin,               true,   {"txid"}},
    { "wallet",             "validateethpegin",         &validateethpegin,          true,   {"txid", "amount", "claim_pubkey"}},
    { "wallet",             "claimethpegin",            &claimethpegin,             true,   {"txid", "amount", "claim_pubkey"}},
    { "wallet",             "createrawethpegin",        &createrawethpegin,         true,   {"txid", "amount", "claim_pubkey"}},
    { "wallet",             "claimpegin",               &claimpegin,                false,  {"bitcoinT", "txoutproof", "claim_script"} },
    { "wallet",             "createrawpegin",           &createrawpegin,            false,  {"bitcoinT", "txoutproof", "claim_script"} },
    { "wallet",             "getaccountaddress",        &getaccountaddress,         true,   {"account"} },
    { "wallet",             "getaccount",               &getaccount,                true,   {"address"} },
    { "wallet",             "getaddressesbyaccount",    &getaddressesbyaccount,     true,   {"account"} },
    { "wallet",             "getbalance",               &getbalance,                false,  {"account","minconf","include_watchonly"} },
    { "wallet",             "getderivedkeys",           &getderivedkeys,            true,   {} },
    { "wallet",             "getnewaddress",            &getnewaddress,             true,   {"account"} },
    { "wallet",             "getkycpubkey",             &getkycpubkey,              true,   {"address"} },
    { "wallet",             "getrawchangeaddress",      &getrawchangeaddress,       true,   {} },
    { "wallet",             "getethaddress",            &getethaddress,             true,   {"key"} },
    { "wallet",             "getethpeginaddress",       &getethpeginaddress,        false,  {"key"} },
    { "wallet",             "getpeginaddress",          &getpeginaddress,           false,  {} },
    { "wallet",             "getreceivedbyaccount",     &getreceivedbyaccount,      false,  {"account","minconf"} },
    { "wallet",             "getreceivedbyaddress",     &getreceivedbyaddress,      false,  {"address","minconf"} },
    { "wallet",             "gettransaction",           &gettransaction,            false,  {"txid","include_watchonly"} },
    { "wallet",             "getunconfirmedbalance",    &getunconfirmedbalance,     false,  {} },
    { "wallet",             "getwalletinfo",            &getwalletinfo,             false,  {} },
    { "wallet",             "importmulti",              &importmulti,               true,   {"requests","options"} },
    { "wallet",             "importprivkey",            &importprivkey,             true,   {"privkey","label","rescan"} },
    { "wallet",             "importwallet",             &importwallet,              true,   {"filename"} },
    { "wallet",             "importaddress",            &importaddress,             true,   {"address","label","rescan","p2sh"} },
    { "wallet",             "importblindingkey",        &importblindingkey,         true,   {} },
    { "wallet",             "importprunedfunds",        &importprunedfunds,         true,   {"rawtransaction","txoutproof"} },
    { "wallet",             "importpubkey",             &importpubkey,              true,   {"pubkey","label","rescan"} },
    { "wallet",             "importissuanceblindingkey",&importissuanceblindingkey, true,   {"txid", "vin", "blindingkey"} },
    { "wallet",             "keypoolrefill",            &keypoolrefill,             true,   {"newsize"} },
    { "wallet",             "issueasset",               &issueasset,                true,   {"assetamount", "tokenamount", "blind"} },
    { "wallet",             "createrawissuance",        &createrawissuance,         true,   {"assetaddress", "assetamount", "tokenaddress", "tokenamount", "changeaddress", "changeamount", "numchange", "inputtxid", "vout"} },
    { "wallet",             "createrawreissuance",      &createrawreissuance,       true,   {"assetaddress", "assetamount", "tokenaddress", "tokenamount", "inputtxid", "vout", "asset", "entropy", "token"} },
    { "wallet",             "createrawburn",            &createrawburn,             true,   {"txid", "vout", "asset", "amount"} },
    { "wallet",             "listaccounts",             &listaccounts,              false,  {"minconf","include_watchonly"} },
    { "wallet",             "listaddressgroupings",     &listaddressgroupings,      false,  {} },
    { "wallet",             "listlockunspent",          &listlockunspent,           false,  {} },
    { "wallet",             "listissuances",            &listissuances,             false,  {"asset"} },
    { "wallet",             "listreceivedbyaccount",    &listreceivedbyaccount,     false,  {"minconf","include_empty","include_watchonly"} },
    { "wallet",             "listreceivedbyaddress",    &listreceivedbyaddress,     false,  {"minconf","include_empty","include_watchonly"} },
    { "wallet",             "listsinceblock",           &listsinceblock,            false,  {"blockhash","target_confirmations","include_watchonly"} },
    { "wallet",             "listtransactions",         &listtransactions,          false,  {"account","count","skip","include_watchonly"} },
    { "wallet",             "listunspent",              &listunspent,               false,  {"minconf","maxconf","addresses","include_unsafe"} },
    { "wallet",             "lockunspent",              &lockunspent,               true,   {"unlock","transactions"} },
    { "wallet",             "sendmany",                 &sendmany,                  false,  {"fromaccount","amounts","minconf","comment","subtractfeefrom"} },
    { "wallet",             "sendtoaddress",            &sendtoaddress,             false,  {"address","amount","comment","comment_to","subtractfeefromamount"} },
    { "wallet",             "sendanytoaddress",         &sendanytoaddress,          false,  {"address","amount","comment","comment_to","subtractfeefromamount"} },
    { "wallet",             "sendaddtowhitelisttx",     &sendaddtowhitelisttx,      false,  {"naddresses", "feeasset"} },
    { "wallet",             "sendaddmultitowhitelisttx",&sendaddmultitowhitelisttx, false,  {"tweakedaddress", "basepubkeys", "nmultisig", "feeasset"} },
    { "wallet",             "setaccount",               &setaccount,                true,   {"address","account"} },
    { "wallet",             "reissueasset",             &reissueasset,              true,   {"asset", "assetamount"} },
    { "wallet",             "signblock",                &signblock,                 true,   {} },
    { "wallet",             "sendtoethmainchain",       &sendtoethmainchain,        false,  {"address", "amount", "subtractfeefromamount"} },
    { "wallet",             "sendtomainchain",          &sendtomainchain,           false,  {"address", "amount", "subtractfeefromamount"} },
    { "wallet",             "destroyamount",            &destroyamount,             false,  {"asset", "amount", "comment"} },
    { "wallet",             "settxfee",                 &settxfee,                  true,   {"amount"} },
    { "wallet",             "signmessage",              &signmessage,               true,   {"address","message"} },
    { "wallet",             "walletlock",               &walletlock,                true,   {} },
    { "wallet",             "walletpassphrasechange",   &walletpassphrasechange,    true,   {"oldpassphrase","newpassphrase"} },
    { "wallet",             "walletpassphrase",         &walletpassphrase,          true,   {"passphrase","timeout"} },
    { "wallet",             "removeprunedfunds",        &removeprunedfunds,         true,   {"txid"} },
};

void RegisterWalletRPCCommands(CRPCTable &t)
{
    if (GetBoolArg("-disablewallet", false))
        return;

    for (unsigned int vcidx = 0; vcidx < ARRAYLEN(commands); vcidx++)
        t.appendCommand(commands[vcidx].name, &commands[vcidx]);
}
