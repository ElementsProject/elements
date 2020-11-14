// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2019 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <amount.h>
#include <asset.h>
#include <assetsdir.h>
#include <block_proof.h>
#include <consensus/validation.h>
#include <core_io.h>
#include <interfaces/chain.h>
#include <key_io.h>
#include <mainchainrpc.h>
#include <merkleblock.h>
#include <node/context.h>
#include <outputtype.h>
#include <pegins.h>
#include <policy/feerate.h>
#include <policy/fees.h>
#include <policy/policy.h>
#include <policy/rbf.h>
#include <pow.h>
#include <primitives/bitcoin/merkleblock.h>
#include <primitives/bitcoin/transaction.h>
#include <rpc/rawtransaction_util.h>
#include <rpc/server.h>
#include <rpc/util.h>
#include <script/descriptor.h>
#include <script/sign.h>
#include <secp256k1.h>
#include <util/bip32.h>
#include <util/fees.h>
#include <util/moneystr.h>
#include <util/string.h>
#include <util/system.h>
#include <util/url.h>
#include <util/validation.h>
#include <validation.h>
#include <wallet/coincontrol.h>
#include <wallet/feebumper.h>
#include <wallet/fees.h>
#include <wallet/psbtwallet.h>
#include <wallet/rpcwallet.h>
#include <wallet/wallet.h>
#include <wallet/walletdb.h>
#include <wallet/walletutil.h>

#include <stdint.h>

#include <univalue.h>


#include <script/generic.hpp> // signblock
#include <script/descriptor.h> // initpegoutwallet
#include <span.h> // sendtomainchain_pak
#include <blind.h>
#include <issuance.h>

static const std::string WALLET_ENDPOINT_BASE = "/wallet/";

static inline bool GetAvoidReuseFlag(CWallet * const pwallet, const UniValue& param) {
    bool can_avoid_reuse = pwallet->IsWalletFlagSet(WALLET_FLAG_AVOID_REUSE);
    bool avoid_reuse = param.isNull() ? can_avoid_reuse : param.get_bool();

    if (avoid_reuse && !can_avoid_reuse) {
        throw JSONRPCError(RPC_WALLET_ERROR, "wallet does not have the \"avoid reuse\" feature enabled");
    }

    return avoid_reuse;
}


/** Used by RPC commands that have an include_watchonly parameter.
 *  We default to true for watchonly wallets if include_watchonly isn't
 *  explicitly set.
 */
static bool ParseIncludeWatchonly(const UniValue& include_watchonly, const CWallet& pwallet)
{
    if (include_watchonly.isNull()) {
        // if include_watchonly isn't explicitly set, then check if we have a watchonly wallet
        return pwallet.IsWalletFlagSet(WALLET_FLAG_DISABLE_PRIVATE_KEYS);
    }

    // otherwise return whatever include_watchonly was set to
    return include_watchonly.get_bool();
}


/** Checks if a CKey is in the given CWallet compressed or otherwise*/
bool HaveKey(const SigningProvider& wallet, const CKey& key)
{
    CKey key2;
    key2.Set(key.begin(), key.end(), !key.IsCompressed());
    return wallet.HaveKey(key.GetPubKey().GetID()) || wallet.HaveKey(key2.GetPubKey().GetID());
}

bool GetWalletNameFromJSONRPCRequest(const JSONRPCRequest& request, std::string& wallet_name)
{
    if (request.URI.substr(0, WALLET_ENDPOINT_BASE.size()) == WALLET_ENDPOINT_BASE) {
        // wallet endpoint was used
        wallet_name = urlDecode(request.URI.substr(WALLET_ENDPOINT_BASE.size()));
        return true;
    }
    return false;
}

std::shared_ptr<CWallet> GetWalletForJSONRPCRequest(const JSONRPCRequest& request)
{
    std::string wallet_name;
    if (GetWalletNameFromJSONRPCRequest(request, wallet_name)) {
        std::shared_ptr<CWallet> pwallet = GetWallet(wallet_name);
        if (!pwallet) throw JSONRPCError(RPC_WALLET_NOT_FOUND, "Requested wallet does not exist or is not loaded");
        return pwallet;
    }

    std::vector<std::shared_ptr<CWallet>> wallets = GetWallets();
    return wallets.size() == 1 || (request.fHelp && wallets.size() > 0) ? wallets[0] : nullptr;
}

std::string HelpRequiringPassphrase(const CWallet* pwallet)
{
    return pwallet && pwallet->IsCrypted()
        ? "\nRequires wallet passphrase to be set with walletpassphrase call."
        : "";
}

bool EnsureWalletIsAvailable(const CWallet* pwallet, bool avoidException)
{
    if (pwallet) return true;
    if (avoidException) return false;
    if (!HasWallets()) {
        throw JSONRPCError(
            RPC_METHOD_NOT_FOUND, "Method not found (wallet method is disabled because no wallet is loaded)");
    }
    throw JSONRPCError(RPC_WALLET_NOT_SPECIFIED,
        "Wallet file not specified (must request wallet RPC through /wallet/<filename> uri-path).");
}

void EnsureWalletIsUnlocked(const CWallet* pwallet)
{
    if (pwallet->IsLocked()) {
        throw JSONRPCError(RPC_WALLET_UNLOCK_NEEDED, "Error: Please enter the wallet passphrase with walletpassphrase first.");
    }
}

LegacyScriptPubKeyMan& EnsureLegacyScriptPubKeyMan(CWallet& wallet)
{
    LegacyScriptPubKeyMan* spk_man = wallet.GetLegacyScriptPubKeyMan();
    if (!spk_man) {
        throw JSONRPCError(RPC_WALLET_ERROR, "This type of wallet does not support this command");
    }
    return *spk_man;
}

static void WalletTxToJSON(interfaces::Chain& chain, interfaces::Chain::Lock& locked_chain, const CWalletTx& wtx, UniValue& entry)
{
    int confirms = wtx.GetDepthInMainChain();
    entry.pushKV("confirmations", confirms);
    if (wtx.IsCoinBase())
        entry.pushKV("generated", true);
    if (confirms > 0)
    {
        entry.pushKV("blockhash", wtx.m_confirm.hashBlock.GetHex());
        entry.pushKV("blockheight", wtx.m_confirm.block_height);
        entry.pushKV("blockindex", wtx.m_confirm.nIndex);
        int64_t block_time;
        bool found_block = chain.findBlock(wtx.m_confirm.hashBlock, nullptr /* block */, &block_time);
        CHECK_NONFATAL(found_block);
        entry.pushKV("blocktime", block_time);
    } else {
        entry.pushKV("trusted", wtx.IsTrusted(locked_chain));
    }
    uint256 hash = wtx.GetHash();
    entry.pushKV("txid", hash.GetHex());
    UniValue conflicts(UniValue::VARR);
    for (const uint256& conflict : wtx.GetConflicts())
        conflicts.push_back(conflict.GetHex());
    entry.pushKV("walletconflicts", conflicts);
    entry.pushKV("time", wtx.GetTxTime());
    entry.pushKV("timereceived", (int64_t)wtx.nTimeReceived);

    // Add opt-in RBF status
    std::string rbfStatus = "no";
    if (confirms <= 0) {
        RBFTransactionState rbfState = chain.isRBFOptIn(*wtx.tx);
        if (rbfState == RBFTransactionState::UNKNOWN)
            rbfStatus = "unknown";
        else if (rbfState == RBFTransactionState::REPLACEABLE_BIP125)
            rbfStatus = "yes";
    }
    entry.pushKV("bip125-replaceable", rbfStatus);

    for (const std::pair<const std::string, std::string>& item : wtx.mapValue) {
        // Skip blinding data which isn't parseable
        if (item.first != "blindingdata") {
            entry.pushKV(item.first, item.second);
        }
    }
}

static std::string LabelFromValue(const UniValue& value)
{
    std::string label = value.get_str();
    if (label == "*")
        throw JSONRPCError(RPC_WALLET_INVALID_LABEL_NAME, "Invalid label name");
    return label;
}

static UniValue getnewaddress(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"getnewaddress",
                "\nReturns a new address for receiving payments.\n"
                "If 'label' is specified, it is added to the address book \n"
                "so payments received with the address will be associated with 'label'.\n"
                "When the wallet doesn't give blinded addresses by default (-blindedaddresses=0), \n"
                "the address type \"blech32\" can still be used to get a blinded address.\n",
                {
                    {"label", RPCArg::Type::STR, /* default */ "\"\"", "The label name for the address to be linked to. It can also be set to the empty string \"\" to represent the default label. The label does not need to exist, it will be created if there is no label by the given name."},
                    {"address_type", RPCArg::Type::STR, /* default */ "set by -addresstype", "The address type to use. Options are \"legacy\", \"p2sh-segwit\", and \"bech32\". Default is set by -addresstype."},
                },
                RPCResult{
            "\"address\"    (string) The new address\n"
                },
                RPCExamples{
                    HelpExampleCli("getnewaddress", "")
            + HelpExampleRpc("getnewaddress", "")
                },
            }.Check(request);

    LOCK(pwallet->cs_wallet);

    if (!pwallet->CanGetAddresses()) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Error: This wallet has no available keys");
    }

    // Parse the label first so we don't generate a key if there's an error
    std::string label;
    if (!request.params[0].isNull())
        label = LabelFromValue(request.params[0]);

    OutputType output_type = pwallet->m_default_address_type;
    bool force_blind = false;
    if (!request.params[1].isNull()) {
        if (!ParseOutputType(request.params[1].get_str(), output_type)) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, strprintf("Unknown address type '%s'", request.params[1].get_str()));
        }
        // Special case for "blech32" when `-blindedaddresses=0` in the config.
        if (request.params[1].get_str() == "blech32") {
            force_blind = true;
        }
    }

    CTxDestination dest;
    std::string error;
    bool add_blinding_key = force_blind || gArgs.GetBoolArg("-blindedaddresses", g_con_elementsmode);
    if (!pwallet->GetNewDestination(output_type, label, dest, error, add_blinding_key)) {
        throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, error);
    }

    return EncodeDestination(dest);
}

static UniValue getrawchangeaddress(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"getrawchangeaddress",
                "\nReturns a new Bitcoin address, for receiving change.\n"
                "This is for use with raw transactions, NOT normal use.\n",
                {
                    {"address_type", RPCArg::Type::STR, /* default */ "set by -changetype", "The address type to use. Options are \"legacy\", \"p2sh-segwit\", and \"bech32\". Default is set by -changetype."},
                },
                RPCResult{
            "\"address\"    (string) The address\n"
                },
                RPCExamples{
                    HelpExampleCli("getrawchangeaddress", "")
            + HelpExampleRpc("getrawchangeaddress", "")
                },
            }.Check(request);

    LOCK(pwallet->cs_wallet);

    if (!pwallet->CanGetAddresses(true)) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Error: This wallet has no available keys");
    }

    OutputType output_type = pwallet->m_default_change_type != OutputType::CHANGE_AUTO ? pwallet->m_default_change_type : pwallet->m_default_address_type;
    bool force_blind = false;
    if (!request.params[0].isNull()) {
        if (!ParseOutputType(request.params[0].get_str(), output_type)) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, strprintf("Unknown address type '%s'", request.params[0].get_str()));
        }
        // Special case for "blech32" when `-blindedaddresses=0` in the config.
        if (request.params[0].get_str() == "blech32") {
            force_blind = true;
        }
    }

    CTxDestination dest;
    std::string error;
    bool add_blinding_key = force_blind || gArgs.GetBoolArg("-blindedaddresses", g_con_elementsmode);
    if (!pwallet->GetNewChangeDestination(output_type, dest, error, add_blinding_key)) {
        throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, error);
    }
    return EncodeDestination(dest);
}


static UniValue setlabel(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"setlabel",
                "\nSets the label associated with the given address.\n",
                {
                    {"address", RPCArg::Type::STR, RPCArg::Optional::NO, "The address to be associated with a label."},
                    {"label", RPCArg::Type::STR, RPCArg::Optional::NO, "The label to assign to the address."},
                },
                RPCResults{},
                RPCExamples{
                    HelpExampleCli("setlabel", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\" \"tabby\"")
            + HelpExampleRpc("setlabel", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\", \"tabby\"")
                },
            }.Check(request);

    LOCK(pwallet->cs_wallet);

    CTxDestination dest = DecodeDestination(request.params[0].get_str());
    if (!IsValidDestination(dest)) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid Bitcoin address");
    }

    std::string label = LabelFromValue(request.params[1]);

    if (pwallet->IsMine(dest)) {
        pwallet->SetAddressBook(dest, label, "receive");
    } else {
        pwallet->SetAddressBook(dest, label, "send");
    }

    return NullUniValue;
}


static CTransactionRef SendMoney(interfaces::Chain::Lock& locked_chain, CWallet * const pwallet, const CTxDestination &address, CAmount nValue, const CAsset& asset, bool fSubtractFeeFromAmount, const CCoinControl& coin_control, mapValue_t mapValue, bool ignore_blind_fail)
{
    CAmountMap curBalance = pwallet->GetBalance(0, coin_control.m_avoid_address_reuse).m_mine_trusted;

    // Check amount
    if (nValue <= 0)
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid amount");

    if (nValue > curBalance[asset])
        throw JSONRPCError(RPC_WALLET_INSUFFICIENT_FUNDS, "Insufficient funds");

    // Parse Bitcoin address
    CScript scriptPubKey = GetScriptForDestination(address);

    // Create the lower bound number of reserve keys.
    std::vector<COutPoint> vPresetInputs;
    coin_control.ListSelected(vPresetInputs);

    // Create and send the transaction
    CAmount nFeeRequired;
    std::string strError;
    std::vector<CRecipient> vecSend;
    int nChangePosRet = -1;
    CRecipient recipient = {scriptPubKey, nValue, asset, GetDestinationBlindingKey(address), fSubtractFeeFromAmount};
    vecSend.push_back(recipient);
    CTransactionRef tx;
    BlindDetails* blind_details = g_con_elementsmode ? new BlindDetails() : NULL;
    if (blind_details) blind_details->ignore_blind_failure = ignore_blind_fail;
    if (!pwallet->CreateTransaction(locked_chain, vecSend, tx, nFeeRequired, nChangePosRet, strError, coin_control, true, blind_details)) {
        if (!fSubtractFeeFromAmount && nValue + nFeeRequired > curBalance[policyAsset])
            strError = strprintf("Error: This transaction requires a transaction fee of at least %s", FormatMoney(nFeeRequired));
        throw JSONRPCError(RPC_WALLET_ERROR, strError);
    }
    pwallet->CommitTransaction(tx, std::move(mapValue), {} /* orderForm */, blind_details);
    return tx;
}

static UniValue sendtoaddress(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"sendtoaddress",
                "\nSend an amount to a given address." +
                    HelpRequiringPassphrase(pwallet) + "\n",
                {
                    {"address", RPCArg::Type::STR, RPCArg::Optional::NO, "The address to send to."},
                    {"amount", RPCArg::Type::AMOUNT, RPCArg::Optional::NO, "The amount in " + CURRENCY_UNIT + " to send. eg 0.1"},
                    {"comment", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "A comment used to store what the transaction is for.\n"
            "                             This is not part of the transaction, just kept in your wallet."},
                    {"comment_to", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "A comment to store the name of the person or organization\n"
            "                             to which you're sending the transaction. This is not part of the \n"
            "                             transaction, just kept in your wallet."},
                    {"subtractfeefromamount", RPCArg::Type::BOOL, /* default */ "false", "The fee will be deducted from the amount being sent.\n"
            "                             The recipient will receive less bitcoins than you enter in the amount field."},
                    {"replaceable", RPCArg::Type::BOOL, /* default */ "wallet default", "Allow this transaction to be replaced by a transaction with higher fees via BIP 125"},
                    {"conf_target", RPCArg::Type::NUM, /* default */ "wallet default", "Confirmation target (in blocks)"},
                    {"estimate_mode", RPCArg::Type::STR, /* default */ "UNSET", "The fee estimate mode, must be one of:\n"
            "       \"UNSET\"\n"
            "       \"ECONOMICAL\"\n"
            "       \"CONSERVATIVE\""},
                    {"avoid_reuse", RPCArg::Type::BOOL, /* default */ "true", "(only available if avoid_reuse wallet flag is set) Avoid spending from dirty addresses; addresses are considered\n"
            "                             dirty if they have previously been used in a transaction."},
                    {"assetlabel", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "Hex asset id or asset label for balance."},
                    {"ignoreblindfail", RPCArg::Type::BOOL, /* default */ "true", "Return a transaction even when a blinding attempt fails due to number of blinded inputs/outputs."},
                },
                RPCResult{
            "\"txid\"                  (string) The transaction id.\n"
                },
                RPCExamples{
                    HelpExampleCli("sendtoaddress", "\"1M72Sfpbz1BPpXFHz9m3CdqATR44Jvaydd\" 0.1")
                    + HelpExampleCli("sendtoaddress", "\"1M72Sfpbz1BPpXFHz9m3CdqATR44Jvaydd\" 0.1 \"donation\" \"seans outpost\"")
                    + HelpExampleCli("sendtoaddress", "\"1M72Sfpbz1BPpXFHz9m3CdqATR44Jvaydd\" 0.1 \"\" \"\" true")
                    + HelpExampleRpc("sendtoaddress", "\"1M72Sfpbz1BPpXFHz9m3CdqATR44Jvaydd\", 0.1, \"donation\", \"seans outpost\"")
                },
            }.Check(request);

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    CTxDestination dest = DecodeDestination(request.params[0].get_str());
    if (!IsValidDestination(dest)) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid address");
    }

    // Amount
    CAmount nAmount = AmountFromValue(request.params[1]);
    if (nAmount <= 0)
        throw JSONRPCError(RPC_TYPE_ERROR, "Invalid amount for send");

    // Wallet comments
    mapValue_t mapValue;
    if (!request.params[2].isNull() && !request.params[2].get_str().empty())
        mapValue["comment"] = request.params[2].get_str();
    if (!request.params[3].isNull() && !request.params[3].get_str().empty())
        mapValue["to"] = request.params[3].get_str();

    bool fSubtractFeeFromAmount = false;
    if (!request.params[4].isNull()) {
        fSubtractFeeFromAmount = request.params[4].get_bool();
    }

    CCoinControl coin_control;
    if (!request.params[5].isNull()) {
        coin_control.m_signal_bip125_rbf = request.params[5].get_bool();
    }

    if (!request.params[6].isNull()) {
        coin_control.m_confirm_target = ParseConfirmTarget(request.params[6], pwallet->chain().estimateMaxBlocks());
    }

    if (!request.params[7].isNull()) {
        if (!FeeModeFromString(request.params[7].get_str(), coin_control.m_fee_mode)) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid estimate_mode parameter");
        }
    }

    coin_control.m_avoid_address_reuse = GetAvoidReuseFlag(pwallet, request.params[8]);
    // We also enable partial spend avoidance if reuse avoidance is set.
    coin_control.m_avoid_partial_spends |= coin_control.m_avoid_address_reuse;

    std::string strasset = Params().GetConsensus().pegged_asset.GetHex();
    if (request.params.size() > 9 && request.params[9].isStr() && !request.params[9].get_str().empty()) {
        strasset = request.params[9].get_str();
    }
    CAsset asset = GetAssetFromString(strasset);
    if (asset.IsNull() && g_con_elementsmode) {
        throw JSONRPCError(RPC_WALLET_ERROR, strprintf("Unknown label and invalid asset hex: %s", asset.GetHex()));
    }

    bool ignore_blind_fail = true;
    if (request.params.size() > 10) {
        ignore_blind_fail = request.params[10].get_bool();
    }

    EnsureWalletIsUnlocked(pwallet);

    CTransactionRef tx = SendMoney(*locked_chain, pwallet, dest, nAmount, asset, fSubtractFeeFromAmount, coin_control, std::move(mapValue), ignore_blind_fail);
    return tx->GetHash().GetHex();
}

static UniValue listaddressgroupings(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"listaddressgroupings",
                "\nLists groups of addresses which have had their common ownership\n"
                "made public by common use as inputs or as the resulting change\n"
                "in past transactions\n",
                {},
                RPCResult{
            "[\n"
            "  [\n"
            "    [\n"
            "      \"address\",            (string) The address\n"
            "      amount,                 (numeric) The amount in " + CURRENCY_UNIT + "\n"
            "      \"label\"               (string, optional) The label\n"
            "    ]\n"
            "    ,...\n"
            "  ]\n"
            "  ,...\n"
            "]\n"
                },
                RPCExamples{
                    HelpExampleCli("listaddressgroupings", "")
            + HelpExampleRpc("listaddressgroupings", "")
                },
            }.Check(request);

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    UniValue jsonGroupings(UniValue::VARR);
    std::map<CTxDestination, CAmount> balances = pwallet->GetAddressBalances(*locked_chain);
    for (const std::set<CTxDestination>& grouping : pwallet->GetAddressGroupings()) {
        UniValue jsonGrouping(UniValue::VARR);
        for (const CTxDestination& address : grouping)
        {
            UniValue addressInfo(UniValue::VARR);
            addressInfo.push_back(EncodeDestination(address));
            addressInfo.push_back(ValueFromAmount(balances[address]));
            {
                if (pwallet->mapAddressBook.find(address) != pwallet->mapAddressBook.end()) {
                    addressInfo.push_back(pwallet->mapAddressBook.find(address)->second.name);
                }
            }
            jsonGrouping.push_back(addressInfo);
        }
        jsonGroupings.push_back(jsonGrouping);
    }
    return jsonGroupings;
}

static UniValue signmessage(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"signmessage",
                "\nSign a message with the private key of an address" +
                    HelpRequiringPassphrase(pwallet) + "\n",
                {
                    {"address", RPCArg::Type::STR, RPCArg::Optional::NO, "The address to use for the private key."},
                    {"message", RPCArg::Type::STR, RPCArg::Optional::NO, "The message to create a signature of."},
                },
                RPCResult{
            "\"signature\"          (string) The signature of the message encoded in base 64\n"
                },
                RPCExamples{
            "\nUnlock the wallet for 30 seconds\n"
            + HelpExampleCli("walletpassphrase", "\"mypassphrase\" 30") +
            "\nCreate the signature\n"
            + HelpExampleCli("signmessage", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\" \"my message\"") +
            "\nVerify the signature\n"
            + HelpExampleCli("verifymessage", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\" \"signature\" \"my message\"") +
            "\nAs a JSON-RPC call\n"
            + HelpExampleRpc("signmessage", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\", \"my message\"")
                },
            }.Check(request);

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    EnsureWalletIsUnlocked(pwallet);

    std::string strAddress = request.params[0].get_str();
    std::string strMessage = request.params[1].get_str();

    CTxDestination dest = DecodeDestination(strAddress);
    if (!IsValidDestination(dest)) {
        throw JSONRPCError(RPC_TYPE_ERROR, "Invalid address");
    }

    const PKHash *pkhash = boost::get<PKHash>(&dest);
    if (!pkhash) {
        throw JSONRPCError(RPC_TYPE_ERROR, "Address does not refer to key");
    }

    CScript script_pub_key = GetScriptForDestination(*pkhash);
    const SigningProvider* provider = pwallet->GetSigningProvider(script_pub_key);
    if (!provider) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Private key not available");
    }

    CKey key;
    CKeyID keyID(*pkhash);
    if (!provider->GetKey(keyID, key)) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Private key not available");
    }

    CHashWriter ss(SER_GETHASH, 0);
    ss << strMessageMagic;
    ss << strMessage;

    std::vector<unsigned char> vchSig;
    if (!key.SignCompact(ss.GetHash(), vchSig))
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Sign failed");

    return EncodeBase64(vchSig.data(), vchSig.size());
}

static UniValue getreceivedbyaddress(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"getreceivedbyaddress",
                "\nReturns the total amount received by the given address in transactions with at least minconf confirmations.\n",
                {
                    {"address", RPCArg::Type::STR, RPCArg::Optional::NO, "The address for transactions."},
                    {"minconf", RPCArg::Type::NUM, /* default */ "1", "Only include transactions confirmed at least this many times."},
                    {"assetlabel", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "Hex asset id or asset label for balance."},
                },
                RPCResult{
            "amount   (numeric) The total amount in " + CURRENCY_UNIT + " received at this address.\n"
                },
                RPCExamples{
            "\nThe amount from transactions with at least 1 confirmation\n"
            + HelpExampleCli("getreceivedbyaddress", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\"") +
            "\nThe amount including unconfirmed transactions, zero confirmations\n"
            + HelpExampleCli("getreceivedbyaddress", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\" 0") +
            "\nThe amount with at least 6 confirmations\n"
            + HelpExampleCli("getreceivedbyaddress", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\" 6") +
            "\nAs a JSON-RPC call\n"
            + HelpExampleRpc("getreceivedbyaddress", "\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\", 6")
                },
            }.Check(request);

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    // Bitcoin address
    CTxDestination dest = DecodeDestination(request.params[0].get_str());
    if (!IsValidDestination(dest)) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid Bitcoin address");
    }
    CScript scriptPubKey = GetScriptForDestination(dest);
    if (!pwallet->IsMine(scriptPubKey)) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Address not found in wallet");
    }

    // Minimum confirmations
    int nMinDepth = 1;
    if (!request.params[1].isNull())
        nMinDepth = request.params[1].get_int();

    // Tally
    CAmountMap amounts;
    for (auto& pairWtx : pwallet->mapWallet) {
        CWalletTx& wtx = pairWtx.second;
        if (wtx.IsCoinBase() || !locked_chain->checkFinalTx(*wtx.tx)) {
            continue;
        }

        for (unsigned int i = 0; i < wtx.tx->vout.size(); i++) {
            const CTxOut& txout = wtx.tx->vout[i];
            if (txout.scriptPubKey == scriptPubKey) {
                if (wtx.GetDepthInMainChain() >= nMinDepth) {
                    CAmountMap wtxValue;
                    CAmount amt = wtx.GetOutputValueOut(i);
                    if (amt < 0) {
                        continue;
                    }
                    wtxValue[wtx.GetOutputAsset(i)] = amt;
                    amounts += wtxValue;
                }
            }
        }
    }

    std::string asset = "";
    if (request.params.size() > 2 && request.params[2].isStr()) {
        asset = request.params[2].get_str();
    }

    return AmountMapToUniv(amounts, asset);
}


static UniValue getreceivedbylabel(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"getreceivedbylabel",
                "\nReturns the total amount received by addresses with <label> in transactions with at least [minconf] confirmations.\n",
                {
                    {"label", RPCArg::Type::STR, RPCArg::Optional::NO, "The selected label, may be the default label using \"\"."},
                    {"minconf", RPCArg::Type::NUM, /* default */ "1", "Only include transactions confirmed at least this many times."},
                    {"assetlabel", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "Hex asset id or asset label for balance."},
                },
                RPCResult{
            "amount              (numeric) The total amount in " + CURRENCY_UNIT + " received for this label.\n"
                },
                RPCExamples{
            "\nAmount received by the default label with at least 1 confirmation\n"
            + HelpExampleCli("getreceivedbylabel", "\"\"") +
            "\nAmount received at the tabby label including unconfirmed amounts with zero confirmations\n"
            + HelpExampleCli("getreceivedbylabel", "\"tabby\" 0") +
            "\nThe amount with at least 6 confirmations\n"
            + HelpExampleCli("getreceivedbylabel", "\"tabby\" 6") +
            "\nAs a JSON-RPC call\n"
            + HelpExampleRpc("getreceivedbylabel", "\"tabby\", 6")
                },
            }.Check(request);

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    // Minimum confirmations
    int nMinDepth = 1;
    if (!request.params[1].isNull())
        nMinDepth = request.params[1].get_int();

    // Get the set of pub keys assigned to label
    std::string label = LabelFromValue(request.params[0]);
    std::set<CTxDestination> setAddress = pwallet->GetLabelAddresses(label);

    // Tally
    CAmountMap amounts;
    for (auto& pairWtx : pwallet->mapWallet) {
        CWalletTx& wtx = pairWtx.second;
        if (wtx.IsCoinBase() || !locked_chain->checkFinalTx(*wtx.tx)) {
            continue;
        }

        for (unsigned int i = 0; i < wtx.tx->vout.size(); i++) {
            const CTxOut& txout = wtx.tx->vout[i];
            CTxDestination address;
            if (ExtractDestination(txout.scriptPubKey, address) && pwallet->IsMine(address) && setAddress.count(address)) {
                if (wtx.GetDepthInMainChain() >= nMinDepth) {
                    CAmountMap wtxValue;
                    CAmount amt = wtx.GetOutputValueOut(i);
                    if (amt < 0) {
                        continue;
                    }
                    wtxValue[wtx.GetOutputAsset(i)] = amt;
                    amounts += wtxValue;
                }
            }
        }
    }

    std::string asset = "";
    if (request.params.size() > 2 && request.params[2].isStr()) {
        asset = request.params[2].get_str();
    }

    return AmountMapToUniv(amounts, asset);
}


static UniValue getbalance(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"getbalance",
                "\nReturns the total available balance.\n"
                "The available balance is what the wallet considers currently spendable, and is\n"
                "thus affected by options which limit spendability such as -spendzeroconfchange.\n",
                {
                    {"dummy", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "Remains for backward compatibility. Must be excluded or set to \"*\"."},
                    {"minconf", RPCArg::Type::NUM, /* default */ "0", "Only include transactions confirmed at least this many times."},
                    {"include_watchonly", RPCArg::Type::BOOL, /* default */ "true for watch-only wallets, otherwise false", "Also include balance in watch-only addresses (see 'importaddress')"},
                    {"avoid_reuse", RPCArg::Type::BOOL, /* default */ "true", "(only available if avoid_reuse wallet flag is set) Do not include balance in dirty outputs; addresses are considered dirty if they have previously been used in a transaction."},
                    {"assetlabel", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "Hex asset id or asset label for balance."},
                },
                RPCResult{
            "amount              (numeric) The total amount in " + CURRENCY_UNIT + " received for this wallet.\n"
                },
                RPCExamples{
            "\nThe total amount in the wallet with 1 or more confirmations\n"
            + HelpExampleCli("getbalance", "") +
            "\nThe total amount in the wallet at least 6 blocks confirmed\n"
            + HelpExampleCli("getbalance", "\"*\" 6") +
            "\nAs a JSON-RPC call\n"
            + HelpExampleRpc("getbalance", "\"*\", 6")
                },
            }.Check(request);

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    const UniValue& dummy_value = request.params[0];
    if (!dummy_value.isNull() && dummy_value.get_str() != "*") {
        throw JSONRPCError(RPC_METHOD_DEPRECATED, "dummy first argument must be excluded or set to \"*\".");
    }

    int min_depth = 0;
    if (!request.params[1].isNull()) {
        min_depth = request.params[1].get_int();
    }

    bool include_watchonly = ParseIncludeWatchonly(request.params[2], *pwallet);

    bool avoid_reuse = GetAvoidReuseFlag(pwallet, request.params[3]);

    std::string asset = "";
    if (!request.params[4].isNull() && request.params[4].isStr()) {
        asset = request.params[4].get_str();
    }

    const auto bal = pwallet->GetBalance(min_depth, avoid_reuse);

    if (include_watchonly) {
        return AmountMapToUniv(bal.m_mine_trusted + bal.m_watchonly_trusted, asset);
    } else {
        return AmountMapToUniv(bal.m_mine_trusted, asset);
    }
}

static UniValue getunconfirmedbalance(const JSONRPCRequest &request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"getunconfirmedbalance",
                "DEPRECATED\nIdentical to getbalances().mine.untrusted_pending\n",
                {},
                RPCResults{},
                RPCExamples{""},
            }.Check(request);

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    return AmountMapToUniv(pwallet->GetBalance().m_mine_untrusted_pending, "");
}


static UniValue sendmany(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    RPCHelpMan{"sendmany",
                "\nSend multiple times. Amounts are double-precision floating point numbers." +
                    HelpRequiringPassphrase(pwallet) + "\n",
                {
                    {"dummy", RPCArg::Type::STR, RPCArg::Optional::NO, "Must be set to \"\" for backwards compatibility.", "\"\""},
                    {"amounts", RPCArg::Type::OBJ, RPCArg::Optional::NO, "A json object with addresses and amounts",
                        {
                            {"address", RPCArg::Type::AMOUNT, RPCArg::Optional::NO, "The address is the key, the numeric amount (can be string) in " + CURRENCY_UNIT + " is the value"},
                        },
                    },
                    {"minconf", RPCArg::Type::NUM, RPCArg::Optional::OMITTED_NAMED_ARG, "Ignored dummy value"},
                    {"comment", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "A comment"},
                    {"subtractfeefrom", RPCArg::Type::ARR, RPCArg::Optional::OMITTED_NAMED_ARG, "A json array with addresses.\n"
            "                           The fee will be equally deducted from the amount of each selected address.\n"
            "                           Those recipients will receive less bitcoins than you enter in their corresponding amount field.\n"
            "                           If no addresses are specified here, the sender pays the fee.",
                        {
                            {"address", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "Subtract fee from this address"},
                        },
                    },
                    {"replaceable", RPCArg::Type::BOOL, /* default */ "wallet default", "Allow this transaction to be replaced by a transaction with higher fees via BIP 125"},
                    {"conf_target", RPCArg::Type::NUM, /* default */ "wallet default", "Confirmation target (in blocks)"},
                    {"estimate_mode", RPCArg::Type::STR, /* default */ "UNSET", "The fee estimate mode, must be one of:\n"
            "       \"UNSET\"\n"
            "       \"ECONOMICAL\"\n"
            "       \"CONSERVATIVE\""},
                    {"output_assets", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "A json object of addresses to assets.",
                        {
                            {"address", RPCArg::Type::STR, RPCArg::Optional::NO, "A key-value pair where the key is the address used and the value is an asset label or hex asset ID."},
                        },
                    },
                    {"ignoreblindfail", RPCArg::Type::BOOL, /* default */ "true", "Return a transaction even when a blinding attempt fails due to number of blinded inputs/outputs."},
                },
                 RPCResult{
            "\"txid\"                   (string) The transaction id for the send. Only 1 transaction is created regardless of \n"
            "                                    the number of addresses.\n"
                 },
                RPCExamples{
            "\nSend two amounts to two different addresses:\n"
            + HelpExampleCli("sendmany", "\"\" \"{\\\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\\\":0.01,\\\"1353tsE8YMTA4EuV7dgUXGjNFf9KpVvKHz\\\":0.02}\"") +
            "\nSend two amounts to two different addresses setting the confirmation and comment:\n"
            + HelpExampleCli("sendmany", "\"\" \"{\\\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\\\":0.01,\\\"1353tsE8YMTA4EuV7dgUXGjNFf9KpVvKHz\\\":0.02}\" 6 \"testing\"") +
            "\nSend two amounts to two different addresses, subtract fee from amount:\n"
            + HelpExampleCli("sendmany", "\"\" \"{\\\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\\\":0.01,\\\"1353tsE8YMTA4EuV7dgUXGjNFf9KpVvKHz\\\":0.02}\" 1 \"\" \"[\\\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\\\",\\\"1353tsE8YMTA4EuV7dgUXGjNFf9KpVvKHz\\\"]\"") +
            "\nAs a JSON-RPC call\n"
            + HelpExampleRpc("sendmany", "\"\", {\"1D1ZrZNe3JUo7ZycKEYQQiQAWd9y54F4XX\":0.01,\"1353tsE8YMTA4EuV7dgUXGjNFf9KpVvKHz\":0.02}, 6, \"testing\"")
                },
    }.Check(request);

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    if (!request.params[0].isNull() && !request.params[0].get_str().empty()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Dummy value must be set to \"\"");
    }
    UniValue sendTo = request.params[1].get_obj();

    mapValue_t mapValue;
    if (!request.params[3].isNull() && !request.params[3].get_str().empty())
        mapValue["comment"] = request.params[3].get_str();

    UniValue subtractFeeFromAmount(UniValue::VARR);
    if (!request.params[4].isNull())
        subtractFeeFromAmount = request.params[4].get_array();

    CCoinControl coin_control;
    if (!request.params[5].isNull()) {
        coin_control.m_signal_bip125_rbf = request.params[5].get_bool();
    }

    if (!request.params[6].isNull()) {
        coin_control.m_confirm_target = ParseConfirmTarget(request.params[6], pwallet->chain().estimateMaxBlocks());
    }

    if (!request.params[7].isNull()) {
        if (!FeeModeFromString(request.params[7].get_str(), coin_control.m_fee_mode)) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid estimate_mode parameter");
        }
    }

    UniValue assets;
    if (!request.params[8].isNull()) {
        if (!g_con_elementsmode) {
            throw JSONRPCError(RPC_TYPE_ERROR, "Asset argument cannot be given for Bitcoin serialization.");
        }
        assets = request.params[8].get_obj();
    }

    bool ignore_blind_fail = true;
    if (request.params.size() > 9) {
        ignore_blind_fail = request.params[9].get_bool();
    }

    std::set<CTxDestination> destinations;
    std::vector<CRecipient> vecSend;

    std::vector<std::string> keys = sendTo.getKeys();
    for (const std::string& name_ : keys) {
        std::string strasset = Params().GetConsensus().pegged_asset.GetHex();
        if (!assets.isNull() && assets[name_].isStr()) {
            strasset = assets[name_].get_str();
        }
        CAsset asset = GetAssetFromString(strasset);
        if (asset.IsNull() && g_con_elementsmode) {
            throw JSONRPCError(RPC_WALLET_ERROR, strprintf("Unknown label and invalid asset hex: %s", asset.GetHex()));
        }

        CTxDestination dest = DecodeDestination(name_);
        if (!IsValidDestination(dest)) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, std::string("Invalid Bitcoin address: ") + name_);
        }

        if (destinations.count(dest)) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, std::string("Invalid parameter, duplicated address: ") + name_);
        }
        destinations.insert(dest);

        CScript scriptPubKey = GetScriptForDestination(dest);
        CAmount nAmount = AmountFromValue(sendTo[name_]);
        if (nAmount <= 0)
            throw JSONRPCError(RPC_TYPE_ERROR, "Invalid amount for send");

        bool fSubtractFeeFromAmount = false;
        for (unsigned int idx = 0; idx < subtractFeeFromAmount.size(); idx++) {
            const UniValue& addr = subtractFeeFromAmount[idx];
            if (addr.get_str() == name_)
                fSubtractFeeFromAmount = true;
        }

        CRecipient recipient = {scriptPubKey, nAmount, asset, GetDestinationBlindingKey(dest), fSubtractFeeFromAmount};
        vecSend.push_back(recipient);
    }

    EnsureWalletIsUnlocked(pwallet);

    // Shuffle recipient list
    std::shuffle(vecSend.begin(), vecSend.end(), FastRandomContext());

    // Send
    CAmount nFeeRequired = 0;
    int nChangePosRet = -1;
    std::string strFailReason;
    CTransactionRef tx;
    BlindDetails* blind_details = g_con_elementsmode ? new BlindDetails() : NULL;
    if (g_con_elementsmode) {
        blind_details->ignore_blind_failure = ignore_blind_fail;
    }
    bool fCreated = pwallet->CreateTransaction(*locked_chain, vecSend, tx, nFeeRequired, nChangePosRet, strFailReason, coin_control, true, blind_details);
    if (!fCreated) {
        throw JSONRPCError(RPC_WALLET_INSUFFICIENT_FUNDS, strFailReason);
    }

    pwallet->CommitTransaction(tx, std::move(mapValue), {} /* orderForm */, blind_details);
    return tx->GetHash().GetHex();
}

static UniValue addmultisigaddress(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"addmultisigaddress",
                "\nAdd an nrequired-to-sign multisignature address to the wallet. Requires a new wallet backup.\n"
                "Each key is a Bitcoin address or hex-encoded public key.\n"
                "This functionality is only intended for use with non-watchonly addresses.\n"
                "See `importaddress` for watchonly p2sh address support.\n"
                "If 'label' is specified, assign address to that label.\n",
                {
                    {"nrequired", RPCArg::Type::NUM, RPCArg::Optional::NO, "The number of required signatures out of the n keys or addresses."},
                    {"keys", RPCArg::Type::ARR, RPCArg::Optional::NO, "A json array of addresses or hex-encoded public keys",
                        {
                            {"key", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "address or hex-encoded public key"},
                        },
                        },
                    {"label", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "A label to assign the addresses to."},
                    {"address_type", RPCArg::Type::STR, /* default */ "set by -addresstype", "The address type to use. Options are \"legacy\", \"p2sh-segwit\", and \"bech32\"."},
                },
                RPCResult{
            "{\n"
            "  \"address\":\"multisigaddress\",    (string) The value of the new multisig address.\n"
            "  \"redeemScript\":\"script\"         (string) The string value of the hex-encoded redemption script.\n"
            "}\n"
                },
                RPCExamples{
            "\nAdd a multisig address from 2 addresses\n"
            + HelpExampleCli("addmultisigaddress", "2 \"[\\\"16sSauSf5pF2UkUwvKGq4qjNRzBZYqgEL5\\\",\\\"171sgjn4YtPu27adkKGrdDwzRTxnRkBfKV\\\"]\"") +
            "\nAs a JSON-RPC call\n"
            + HelpExampleRpc("addmultisigaddress", "2, \"[\\\"16sSauSf5pF2UkUwvKGq4qjNRzBZYqgEL5\\\",\\\"171sgjn4YtPu27adkKGrdDwzRTxnRkBfKV\\\"]\"")
                },
            }.Check(request);

    LegacyScriptPubKeyMan& spk_man = EnsureLegacyScriptPubKeyMan(*pwallet);

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    std::string label;
    if (!request.params[2].isNull())
        label = LabelFromValue(request.params[2]);

    int required = request.params[0].get_int();

    // Get the public keys
    const UniValue& keys_or_addrs = request.params[1].get_array();
    std::vector<CPubKey> pubkeys;
    for (unsigned int i = 0; i < keys_or_addrs.size(); ++i) {
        if (IsHex(keys_or_addrs[i].get_str()) && (keys_or_addrs[i].get_str().length() == 66 || keys_or_addrs[i].get_str().length() == 130)) {
            pubkeys.push_back(HexToPubKey(keys_or_addrs[i].get_str()));
        } else {
            pubkeys.push_back(AddrToPubKey(spk_man, keys_or_addrs[i].get_str()));
        }
    }

    OutputType output_type = pwallet->m_default_address_type;
    if (!request.params[3].isNull()) {
        if (!ParseOutputType(request.params[3].get_str(), output_type)) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, strprintf("Unknown address type '%s'", request.params[3].get_str()));
        }
    }

    // Construct using pay-to-script-hash:
    CScript inner;
    CTxDestination dest = AddAndGetMultisigDestination(required, pubkeys, output_type, spk_man, inner);
    pwallet->SetAddressBook(dest, label, "send");

    UniValue result(UniValue::VOBJ);
    result.pushKV("address", EncodeDestination(dest));
    result.pushKV("redeemScript", HexStr(inner.begin(), inner.end()));
    return result;
}

class Witnessifier : public boost::static_visitor<bool>
{
public:
    const SigningProvider * const provider;
    CTxDestination result;
    bool already_witness;

    explicit Witnessifier(const SigningProvider *_provider) : provider(_provider), already_witness(false) {}

    bool operator()(const PKHash &keyID) {
        if (provider) {
            CScript basescript = GetScriptForDestination(keyID);
            CScript witscript = GetScriptForWitness(basescript);
            if (!IsSolvable(*provider, witscript)) {
                return false;
            }
            return ExtractDestination(witscript, result);
        }
        return false;
    }

    bool operator()(const ScriptHash &scripthash) {
        CScript subscript;
        if (provider && provider->GetCScript(CScriptID(scripthash), subscript)) {
            int witnessversion;
            std::vector<unsigned char> witprog;
            if (subscript.IsWitnessProgram(witnessversion, witprog)) {
                ExtractDestination(subscript, result);
                already_witness = true;
                return true;
            }
            CScript witscript = GetScriptForWitness(subscript);
            if (!IsSolvable(*provider, witscript)) {
                return false;
            }
            return ExtractDestination(witscript, result);
        }
        return false;
    }

    bool operator()(const WitnessV0KeyHash& id)
    {
        already_witness = true;
        result = id;
        return true;
    }

    bool operator()(const WitnessV0ScriptHash& id)
    {
        already_witness = true;
        result = id;
        return true;
    }

    template<typename T>
    bool operator()(const T& dest) { return false; }
};

struct tallyitem
{
    CAmountMap mapAmount;
    int nConf{std::numeric_limits<int>::max()};
    std::vector<uint256> txids;
    bool fIsWatchonly{false};
    tallyitem()
    {
    }
};

static UniValue ListReceived(interfaces::Chain::Lock& locked_chain, CWallet * const pwallet, const UniValue& params, bool by_label) EXCLUSIVE_LOCKS_REQUIRED(pwallet->cs_wallet)
{
    // Minimum confirmations
    int nMinDepth = 1;
    if (!params[0].isNull())
        nMinDepth = params[0].get_int();

    // Whether to include empty labels
    bool fIncludeEmpty = false;
    if (!params[1].isNull())
        fIncludeEmpty = params[1].get_bool();

    isminefilter filter = ISMINE_SPENDABLE;

    if (ParseIncludeWatchonly(params[2], *pwallet)) {
        filter |= ISMINE_WATCH_ONLY;
    }

    bool has_filtered_address = false;
    CTxDestination filtered_address = CNoDestination();
    if (!by_label && params[3].isStr() && params[3].get_str() != "") {
        if (!IsValidDestinationString(params[3].get_str())) {
            throw JSONRPCError(RPC_WALLET_ERROR, "address_filter parameter was invalid");
        }
        filtered_address = DecodeDestination(params[3].get_str());
        has_filtered_address = true;
    }

    std::string strasset = "";
    if (params.size() > 4 && params[4].isStr()) {
        strasset = params[4].get_str();
    }
    CAsset asset;
    if (!strasset.empty()) {
        asset = GetAssetFromString(strasset);
    }

    // Tally
    std::map<CTxDestination, tallyitem> mapTally;
    for (const std::pair<const uint256, CWalletTx>& pairWtx : pwallet->mapWallet) {
        const CWalletTx& wtx = pairWtx.second;

        if (wtx.IsCoinBase() || !locked_chain.checkFinalTx(*wtx.tx)) {
            continue;
        }

        int nDepth = wtx.GetDepthInMainChain();
        if (nDepth < nMinDepth)
            continue;

        for (size_t index = 0; index < wtx.tx->vout.size(); ++index)
        {
            const CTxOut& txout = wtx.tx->vout[index];

            CTxDestination address;
            if (!ExtractDestination(txout.scriptPubKey, address))
                continue;

            if (has_filtered_address && !(filtered_address == address)) {
                continue;
            }

            isminefilter mine = pwallet->IsMine(address);
            if(!(mine & filter))
                continue;

            CAmount amt = wtx.GetOutputValueOut(index);
            if (amt < 0) {
                continue;
            }

            if (strasset != "" && wtx.GetOutputAsset(index) != asset) {
                continue;
            }

            tallyitem& item = mapTally[address];
            item.mapAmount[wtx.GetOutputAsset(index)] += amt;
            item.nConf = std::min(item.nConf, nDepth);
            item.txids.push_back(wtx.GetHash());
            if (mine & ISMINE_WATCH_ONLY)
                item.fIsWatchonly = true;
        }
    }

    // Reply
    UniValue ret(UniValue::VARR);
    std::map<std::string, tallyitem> label_tally;

    // Create mapAddressBook iterator
    // If we aren't filtering, go from begin() to end()
    auto start = pwallet->mapAddressBook.begin();
    auto end = pwallet->mapAddressBook.end();
    // If we are filtering, find() the applicable entry
    if (has_filtered_address) {
        start = pwallet->mapAddressBook.find(filtered_address);
        if (start != end) {
            end = std::next(start);
        }
    }

    for (auto item_it = start; item_it != end; ++item_it)
    {
        const CTxDestination& address = item_it->first;
        const std::string& label = item_it->second.name;
        auto it = mapTally.find(address);
        if (it == mapTally.end() && !fIncludeEmpty)
            continue;

        CAmountMap mapAmount;
        int nConf = std::numeric_limits<int>::max();
        bool fIsWatchonly = false;
        if (it != mapTally.end())
        {
            mapAmount = (*it).second.mapAmount;
            nConf = (*it).second.nConf;
            fIsWatchonly = (*it).second.fIsWatchonly;
        }

        if (by_label)
        {
            tallyitem& _item = label_tally[label];
            _item.mapAmount += mapAmount;
            _item.nConf = std::min(_item.nConf, nConf);
            _item.fIsWatchonly = fIsWatchonly;
        }
        else
        {
            UniValue obj(UniValue::VOBJ);
            if(fIsWatchonly)
                obj.pushKV("involvesWatchonly", true);
            obj.pushKV("address",       EncodeDestination(address));
            obj.pushKV("amount",        AmountMapToUniv(mapAmount, strasset));
            obj.pushKV("confirmations", (nConf == std::numeric_limits<int>::max() ? 0 : nConf));
            obj.pushKV("label", label);
            UniValue transactions(UniValue::VARR);
            if (it != mapTally.end())
            {
                for (const uint256& _item : (*it).second.txids)
                {
                    transactions.push_back(_item.GetHex());
                }
            }
            obj.pushKV("txids", transactions);
            ret.push_back(obj);
        }
    }

    if (by_label)
    {
        for (const auto& entry : label_tally)
        {
            CAmountMap mapAmount = entry.second.mapAmount;
            int nConf = entry.second.nConf;
            UniValue obj(UniValue::VOBJ);
            if (entry.second.fIsWatchonly)
                obj.pushKV("involvesWatchonly", true);
            obj.pushKV("amount",        AmountMapToUniv(mapAmount, ""));
            obj.pushKV("confirmations", (nConf == std::numeric_limits<int>::max() ? 0 : nConf));
            obj.pushKV("label",         entry.first);
            ret.push_back(obj);
        }
    }

    return ret;
}

static UniValue listreceivedbyaddress(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"listreceivedbyaddress",
                "\nList balances by receiving address.\n",
                {
                    {"minconf", RPCArg::Type::NUM, /* default */ "1", "The minimum number of confirmations before payments are included."},
                    {"include_empty", RPCArg::Type::BOOL, /* default */ "false", "Whether to include addresses that haven't received any payments."},
                    {"include_watchonly", RPCArg::Type::BOOL, /* default */ "true for watch-only wallets, otherwise false", "Whether to include watch-only addresses (see 'importaddress')"},
                    {"address_filter", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "If present, only return information on this address."},
                    {"assetlabel", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "Hex asset id or asset label for balance."},
                },
                RPCResult{
            "[\n"
            "  {\n"
            "    \"involvesWatchonly\" : true,        (bool) Only returns true if imported addresses were involved in transaction.\n"
            "    \"address\" : \"receivingaddress\",  (string) The receiving address\n"
            "    \"amount\" : x.xxx,                  (numeric) The total amount in " + CURRENCY_UNIT + " received by the address\n"
            "    \"confirmations\" : n,               (numeric) The number of confirmations of the most recent transaction included\n"
            "    \"label\" : \"label\",               (string) The label of the receiving address. The default label is \"\".\n"
            "    \"txids\": [\n"
            "       \"txid\",                         (string) The ids of transactions received with the address \n"
            "       ...\n"
            "    ]\n"
            "  }\n"
            "  ,...\n"
            "]\n"
                },
                RPCExamples{
                    HelpExampleCli("listreceivedbyaddress", "")
            + HelpExampleCli("listreceivedbyaddress", "6 true")
            + HelpExampleRpc("listreceivedbyaddress", "6, true, true")
            + HelpExampleRpc("listreceivedbyaddress", "6, true, true, \"1M72Sfpbz1BPpXFHz9m3CdqATR44Jvaydd\"")
                },
            }.Check(request);

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    return ListReceived(*locked_chain, pwallet, request.params, false);
}

static UniValue listreceivedbylabel(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"listreceivedbylabel",
                "\nList received transactions by label.\n",
                {
                    {"minconf", RPCArg::Type::NUM, /* default */ "1", "The minimum number of confirmations before payments are included."},
                    {"include_empty", RPCArg::Type::BOOL, /* default */ "false", "Whether to include labels that haven't received any payments."},
                    {"include_watchonly", RPCArg::Type::BOOL, /* default */ "true for watch-only wallets, otherwise false", "Whether to include watch-only addresses (see 'importaddress')"},
                },
                RPCResult{
            "[\n"
            "  {\n"
            "    \"involvesWatchonly\" : true,   (bool) Only returns true if imported addresses were involved in transaction.\n"
            "    \"amount\" : x.xxx,             (numeric) The total amount received by addresses with this label\n"
            "    \"confirmations\" : n,          (numeric) The number of confirmations of the most recent transaction included\n"
            "    \"label\" : \"label\"           (string) The label of the receiving address. The default label is \"\".\n"
            "  }\n"
            "  ,...\n"
            "]\n"
                },
                RPCExamples{
                    HelpExampleCli("listreceivedbylabel", "")
            + HelpExampleCli("listreceivedbylabel", "6 true")
            + HelpExampleRpc("listreceivedbylabel", "6, true, true")
                },
            }.Check(request);

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    return ListReceived(*locked_chain, pwallet, request.params, true);
}

static void MaybePushAddress(UniValue & entry, const CTxDestination &dest)
{
    if (IsValidDestination(dest)) {
        entry.pushKV("address", EncodeDestination(dest));
    }
}

/**
 * List transactions based on the given criteria.
 *
 * @param  pwallet        The wallet.
 * @param  wtx            The wallet transaction.
 * @param  nMinDepth      The minimum confirmation depth.
 * @param  fLong          Whether to include the JSON version of the transaction.
 * @param  ret            The UniValue into which the result is stored.
 * @param  filter_ismine  The "is mine" filter flags.
 * @param  filter_label   Optional label string to filter incoming transactions.
 */
static void ListTransactions(interfaces::Chain::Lock& locked_chain, CWallet* const pwallet, const CWalletTx& wtx, int nMinDepth, bool fLong, UniValue& ret, const isminefilter& filter_ismine, const std::string* filter_label) EXCLUSIVE_LOCKS_REQUIRED(pwallet->cs_wallet)
{
    CAmount nFee;
    std::list<COutputEntry> listReceived;
    std::list<COutputEntry> listSent;

    wtx.GetAmounts(listReceived, listSent, nFee, filter_ismine);

    bool involvesWatchonly = wtx.IsFromMe(ISMINE_WATCH_ONLY);

    // Sent
    if (!filter_label)
    {
        for (const COutputEntry& s : listSent)
        {
            UniValue entry(UniValue::VOBJ);
            if (involvesWatchonly || (pwallet->IsMine(s.destination) & ISMINE_WATCH_ONLY)) {
                entry.pushKV("involvesWatchonly", true);
            }
            MaybePushAddress(entry, s.destination);
            entry.pushKV("category", "send");
            entry.pushKV("amount", ValueFromAmount(-s.amount));
            if (g_con_elementsmode) {
                entry.pushKV("amountblinder", s.amount_blinding_factor.GetHex());
                entry.pushKV("asset", s.asset.GetHex());
                entry.pushKV("assetblinder", s.asset_blinding_factor.GetHex());
            }
            if (pwallet->mapAddressBook.count(s.destination)) {
                entry.pushKV("label", pwallet->mapAddressBook[s.destination].name);
            }
            entry.pushKV("vout", s.vout);
            entry.pushKV("fee", ValueFromAmount(-nFee));
            if (fLong)
                WalletTxToJSON(pwallet->chain(), locked_chain, wtx, entry);
            entry.pushKV("abandoned", wtx.isAbandoned());
            ret.push_back(entry);
        }
    }

    // Received
    if (listReceived.size() > 0 && wtx.GetDepthInMainChain() >= nMinDepth) {
        for (const COutputEntry& r : listReceived)
        {
            std::string label;
            if (pwallet->mapAddressBook.count(r.destination)) {
                label = pwallet->mapAddressBook[r.destination].name;
            }
            if (filter_label && label != *filter_label) {
                continue;
            }
            UniValue entry(UniValue::VOBJ);
            if (involvesWatchonly || (pwallet->IsMine(r.destination) & ISMINE_WATCH_ONLY)) {
                entry.pushKV("involvesWatchonly", true);
            }
            MaybePushAddress(entry, r.destination);
            if (wtx.IsCoinBase())
            {
                if (wtx.GetDepthInMainChain() < 1)
                    entry.pushKV("category", "orphan");
                else if (wtx.IsImmatureCoinBase())
                    entry.pushKV("category", "immature");
                else
                    entry.pushKV("category", "generate");
            }
            else
            {
                entry.pushKV("category", "receive");
            }
            entry.pushKV("amount", ValueFromAmount(r.amount));
            if (g_con_elementsmode) {
                entry.pushKV("amountblinder", r.amount_blinding_factor.GetHex());
                entry.pushKV("asset", r.asset.GetHex());
                entry.pushKV("assetblinder", r.asset_blinding_factor.GetHex());
            }
            if (pwallet->mapAddressBook.count(r.destination)) {
                entry.pushKV("label", label);
            }
            entry.pushKV("vout", r.vout);
            if (fLong)
                WalletTxToJSON(pwallet->chain(), locked_chain, wtx, entry);
            ret.push_back(entry);
        }
    }
}

static const std::string TransactionDescriptionString()
{
    return "    \"confirmations\": n,                        (numeric) The number of confirmations for the transaction. Negative confirmations means the\n"
           "                                                       transaction conflicted that many blocks ago.\n"
           "    \"generated\": xxx,                          (bool) Only present if transaction only input is a coinbase one.\n"
           "    \"trusted\": xxx,                            (bool) Only present if we consider transaction to be trusted and so safe to spend from.\n"
           "    \"blockhash\": \"hashvalue\",                  (string) The block hash containing the transaction.\n"
           "    \"blockheight\": n,                          (numeric) The block height containing the transaction.\n"
           "    \"blockindex\": n,                           (numeric) The index of the transaction in the block that includes it.\n"
           "    \"blocktime\": xxx,                          (numeric) The block time expressed in " + UNIX_EPOCH_TIME + ".\n"
           "    \"txid\": \"transactionid\",                   (string) The transaction id.\n"
           "    \"walletconflicts\": [                       (array) Conflicting transaction ids.\n"
           "      \"txid\",                                  (string) The transaction id.\n"
           "      ...\n"
           "    ],\n"
           "    \"time\": xxx,                               (numeric) The transaction time expressed in " + UNIX_EPOCH_TIME + ".\n"
           "    \"timereceived\": xxx,                       (numeric) The time received expressed in " + UNIX_EPOCH_TIME + ".\n"
           "    \"comment\": \"...\",                          (string) If a comment is associated with the transaction, only present if not empty.\n"
           "    \"bip125-replaceable\": \"yes|no|unknown\",    (string) Whether this transaction could be replaced due to BIP125 (replace-by-fee);\n"
           "                                                     may be unknown for unconfirmed transactions not in the mempool\n";
}

UniValue listtransactions(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"listtransactions",
                "\nIf a label name is provided, this will return only incoming transactions paying to addresses with the specified label.\n"
                "\nReturns up to 'count' most recent transactions skipping the first 'from' transactions.\n",
                {
                    {"label", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "If set, should be a valid label name to return only incoming transactions\n"
            "              with the specified label, or \"*\" to disable filtering and return all transactions."},
                    {"count", RPCArg::Type::NUM, /* default */ "10", "The number of transactions to return"},
                    {"skip", RPCArg::Type::NUM, /* default */ "0", "The number of transactions to skip"},
                    {"include_watchonly", RPCArg::Type::BOOL, /* default */ "true for watch-only wallets, otherwise false", "Include transactions to watch-only addresses (see 'importaddress')"},
                },
                RPCResult{
            "[\n"
            "  {\n"
            "    \"involvesWatchonly\": xxx, (bool) Only returns true if imported addresses were involved in transaction.\n"
            "    \"address\":\"address\",    (string) The address of the transaction.\n"
            "    \"category\":               (string) The transaction category.\n"
            "                \"send\"                  Transactions sent.\n"
            "                \"receive\"               Non-coinbase transactions received.\n"
            "                \"generate\"              Coinbase transactions received with more than 100 confirmations.\n"
            "                \"immature\"              Coinbase transactions received with 100 or fewer confirmations.\n"
            "                \"orphan\"                Orphaned coinbase transactions received.\n"
            "    \"amount\": x.xxx,          (numeric) The amount in " + CURRENCY_UNIT + ". This is negative for the 'send' category, and is positive\n"
            "                                        for all other categories\n"
            "    \"label\": \"label\",       (string) A comment for the address/transaction, if any\n"
            "    \"vout\": n,                (numeric) the vout value\n"
            "    \"fee\": x.xxx,             (numeric) The amount of the fee in " + CURRENCY_UNIT + ". This is negative and only available for the \n"
            "                                         'send' category of transactions.\n"
            + TransactionDescriptionString()
            + "    \"abandoned\": xxx          (bool) 'true' if the transaction has been abandoned (inputs are respendable). Only available for the \n"
            "                                         'send' category of transactions.\n"
            "  }\n"
            "]\n"
                },
                RPCExamples{
            "\nList the most recent 10 transactions in the systems\n"
            + HelpExampleCli("listtransactions", "") +
            "\nList transactions 100 to 120\n"
            + HelpExampleCli("listtransactions", "\"*\" 20 100") +
            "\nAs a JSON-RPC call\n"
            + HelpExampleRpc("listtransactions", "\"*\", 20, 100")
                },
            }.Check(request);

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    const std::string* filter_label = nullptr;
    if (!request.params[0].isNull() && request.params[0].get_str() != "*") {
        filter_label = &request.params[0].get_str();
        if (filter_label->empty()) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Label argument must be a valid label name or \"*\".");
        }
    }
    int nCount = 10;
    if (!request.params[1].isNull())
        nCount = request.params[1].get_int();
    int nFrom = 0;
    if (!request.params[2].isNull())
        nFrom = request.params[2].get_int();
    isminefilter filter = ISMINE_SPENDABLE;

    if (ParseIncludeWatchonly(request.params[3], *pwallet)) {
        filter |= ISMINE_WATCH_ONLY;
    }

    if (nCount < 0)
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Negative count");
    if (nFrom < 0)
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Negative from");

    UniValue ret(UniValue::VARR);

    {
        auto locked_chain = pwallet->chain().lock();
        LOCK(pwallet->cs_wallet);

        const CWallet::TxItems & txOrdered = pwallet->wtxOrdered;

        // iterate backwards until we have nCount items to return:
        for (CWallet::TxItems::const_reverse_iterator it = txOrdered.rbegin(); it != txOrdered.rend(); ++it)
        {
            CWalletTx *const pwtx = (*it).second;
            ListTransactions(*locked_chain, pwallet, *pwtx, 0, true, ret, filter, filter_label);
            if ((int)ret.size() >= (nCount+nFrom)) break;
        }
    }

    // ret is newest to oldest

    if (nFrom > (int)ret.size())
        nFrom = ret.size();
    if ((nFrom + nCount) > (int)ret.size())
        nCount = ret.size() - nFrom;

    std::vector<UniValue> arrTmp = ret.getValues();

    std::vector<UniValue>::iterator first = arrTmp.begin();
    std::advance(first, nFrom);
    std::vector<UniValue>::iterator last = arrTmp.begin();
    std::advance(last, nFrom+nCount);

    if (last != arrTmp.end()) arrTmp.erase(last, arrTmp.end());
    if (first != arrTmp.begin()) arrTmp.erase(arrTmp.begin(), first);

    std::reverse(arrTmp.begin(), arrTmp.end()); // Return oldest to newest

    ret.clear();
    ret.setArray();
    ret.push_backV(arrTmp);

    return ret;
}

static UniValue listsinceblock(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"listsinceblock",
                "\nGet all transactions in blocks since block [blockhash], or all transactions if omitted.\n"
                "If \"blockhash\" is no longer a part of the main chain, transactions from the fork point onward are included.\n"
                "Additionally, if include_removed is set, transactions affecting the wallet which were removed are returned in the \"removed\" array.\n",
                {
                    {"blockhash", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "If set, the block hash to list transactions since, otherwise list all transactions."},
                    {"target_confirmations", RPCArg::Type::NUM, /* default */ "1", "Return the nth block hash from the main chain. e.g. 1 would mean the best block hash. Note: this is not used as a filter, but only affects [lastblock] in the return value"},
                    {"include_watchonly", RPCArg::Type::BOOL, /* default */ "true for watch-only wallets, otherwise false", "Include transactions to watch-only addresses (see 'importaddress')"},
                    {"include_removed", RPCArg::Type::BOOL, /* default */ "true", "Show transactions that were removed due to a reorg in the \"removed\" array\n"
            "                                                           (not guaranteed to work on pruned nodes)"},
                },
                RPCResult{
            "{\n"
            "  \"transactions\": [\n"
            "    \"involvesWatchonly\": xxx, (bool) Only returns true if imported addresses were involved in transaction.\n"
            "    \"address\":\"address\",    (string) The address of the transaction.\n"
            "    \"category\":               (string) The transaction category.\n"
            "                \"send\"                  Transactions sent.\n"
            "                \"receive\"               Non-coinbase transactions received.\n"
            "                \"generate\"              Coinbase transactions received with more than 100 confirmations.\n"
            "                \"immature\"              Coinbase transactions received with 100 or fewer confirmations.\n"
            "                \"orphan\"                Orphaned coinbase transactions received.\n"
            "    \"amount\": x.xxx,          (numeric) The amount in " + CURRENCY_UNIT + ". This is negative for the 'send' category, and is positive\n"
            "                                         for all other categories\n"
            "    \"vout\" : n,               (numeric) the vout value\n"
            "    \"fee\": x.xxx,             (numeric) The amount of the fee in " + CURRENCY_UNIT + ". This is negative and only available for the 'send' category of transactions.\n"
            + TransactionDescriptionString()
            + "    \"abandoned\": xxx,         (bool) 'true' if the transaction has been abandoned (inputs are respendable). Only available for the 'send' category of transactions.\n"
            "    \"comment\": \"...\",       (string) If a comment is associated with the transaction.\n"
            "    \"label\" : \"label\"       (string) A comment for the address/transaction, if any\n"
            "    \"to\": \"...\",            (string) If a comment to is associated with the transaction.\n"
            "  ],\n"
            "  \"removed\": [\n"
            "    <structure is the same as \"transactions\" above, only present if include_removed=true>\n"
            "    Note: transactions that were re-added in the active chain will appear as-is in this array, and may thus have a positive confirmation count.\n"
            "  ],\n"
            "  \"lastblock\": \"lastblockhash\"     (string) The hash of the block (target_confirmations-1) from the best block on the main chain. This is typically used to feed back into listsinceblock the next time you call it. So you would generally use a target_confirmations of say 6, so you will be continually re-notified of transactions until they've reached 6 confirmations plus any new ones\n"
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("listsinceblock", "")
            + HelpExampleCli("listsinceblock", "\"000000000000000bacf66f7497b7dc45ef753ee9a7d38571037cdb1a57f663ad\" 6")
            + HelpExampleRpc("listsinceblock", "\"000000000000000bacf66f7497b7dc45ef753ee9a7d38571037cdb1a57f663ad\", 6")
                },
            }.Check(request);

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    // The way the 'height' is initialized is just a workaround for the gcc bug #47679 since version 4.6.0.
    Optional<int> height = MakeOptional(false, int()); // Height of the specified block or the common ancestor, if the block provided was in a deactivated chain.
    Optional<int> altheight; // Height of the specified block, even if it's in a deactivated chain.
    int target_confirms = 1;
    isminefilter filter = ISMINE_SPENDABLE;

    uint256 blockId;
    if (!request.params[0].isNull() && !request.params[0].get_str().empty()) {
        blockId = ParseHashV(request.params[0], "blockhash");
        height = locked_chain->findFork(blockId, &altheight);
        if (!height) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Block not found");
        }
    }

    if (!request.params[1].isNull()) {
        target_confirms = request.params[1].get_int();

        if (target_confirms < 1) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter");
        }
    }

    if (ParseIncludeWatchonly(request.params[2], *pwallet)) {
        filter |= ISMINE_WATCH_ONLY;
    }

    bool include_removed = (request.params[3].isNull() || request.params[3].get_bool());

    const Optional<int> tip_height = locked_chain->getHeight();
    int depth = tip_height && height ? (1 + *tip_height - *height) : -1;

    UniValue transactions(UniValue::VARR);

    for (const std::pair<const uint256, CWalletTx>& pairWtx : pwallet->mapWallet) {
        CWalletTx tx = pairWtx.second;

        if (depth == -1 || abs(tx.GetDepthInMainChain()) < depth) {
            ListTransactions(*locked_chain, pwallet, tx, 0, true, transactions, filter, nullptr /* filter_label */);
        }
    }

    // when a reorg'd block is requested, we also list any relevant transactions
    // in the blocks of the chain that was detached
    UniValue removed(UniValue::VARR);
    while (include_removed && altheight && *altheight > *height) {
        CBlock block;
        if (!pwallet->chain().findBlock(blockId, &block) || block.IsNull()) {
            throw JSONRPCError(RPC_INTERNAL_ERROR, "Can't read block from disk");
        }
        for (const CTransactionRef& tx : block.vtx) {
            auto it = pwallet->mapWallet.find(tx->GetHash());
            if (it != pwallet->mapWallet.end()) {
                // We want all transactions regardless of confirmation count to appear here,
                // even negative confirmation ones, hence the big negative.
                ListTransactions(*locked_chain, pwallet, it->second, -100000000, true, removed, filter, nullptr /* filter_label */);
            }
        }
        blockId = block.hashPrevBlock;
        --*altheight;
    }

    int last_height = tip_height ? *tip_height + 1 - target_confirms : -1;
    uint256 lastblock = last_height >= 0 ? locked_chain->getBlockHash(last_height) : uint256();

    UniValue ret(UniValue::VOBJ);
    ret.pushKV("transactions", transactions);
    if (include_removed) ret.pushKV("removed", removed);
    ret.pushKV("lastblock", lastblock.GetHex());

    return ret;
}

static UniValue gettransaction(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"gettransaction",
                "\nGet detailed information about in-wallet transaction <txid>\n",
                {
                    {"txid", RPCArg::Type::STR, RPCArg::Optional::NO, "The transaction id"},
                    {"include_watchonly", RPCArg::Type::BOOL, /* default */ "true for watch-only wallets, otherwise false",
                            "Whether to include watch-only addresses in balance calculation and details[]"},
                    {"verbose", RPCArg::Type::BOOL, /* default */ "false",
                            "Whether to include a `decoded` field containing the decoded transaction (equivalent to RPC decoderawtransaction)"},
                    {"assetlabel", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "Hex asset id or asset label for balance."},
                },
                RPCResult{
            "{\n"
            "    \"amount\" : x.xxx,        (numeric) The transaction amount in " + CURRENCY_UNIT + "\n"
            "    \"fee\": x.xxx,            (numeric) The amount of the fee in " + CURRENCY_UNIT + ". This is negative and only available for the \n"
            "                              'send' category of transactions.\n"
            + TransactionDescriptionString()
            + "    \"details\" : [\n"
            "      {\n"
            "        \"involvesWatchonly\": xxx,         (bool) Only returns true if imported addresses were involved in transaction.\n"
            "        \"address\" : \"address\",          (string) The address involved in the transaction\n"
            "        \"category\" :                      (string) The transaction category.\n"
            "                     \"send\"                  Transactions sent.\n"
            "                     \"receive\"               Non-coinbase transactions received.\n"
            "                     \"generate\"              Coinbase transactions received with more than 100 confirmations.\n"
            "                     \"immature\"              Coinbase transactions received with 100 or fewer confirmations.\n"
            "                     \"orphan\"                Orphaned coinbase transactions received.\n"
            "        \"amount\" : x.xxx,                 (numeric) The amount in " + CURRENCY_UNIT + "\n"
            "        \"label\" : \"label\",              (string) A comment for the address/transaction, if any\n"
            "        \"vout\" : n,                       (numeric) the vout value\n"
            "        \"fee\": x.xxx,                     (numeric) The amount of the fee in " + CURRENCY_UNIT + ". This is negative and only available for the \n"
            "                                           'send' category of transactions.\n"
            "        \"abandoned\": xxx                  (bool) 'true' if the transaction has been abandoned (inputs are respendable). Only available for the \n"
            "                                           'send' category of transactions.\n"
            "      }\n"
            "      ,...\n"
            "    ],\n"
            "    \"hex\" : \"data\"         (string) Raw data for transaction\n"
            "    \"decoded\" : transaction         (json object) Optional, the decoded transaction (only present when `verbose` is passed), equivalent to the\n"
            "                                                  RPC decoderawtransaction method, or the RPC getrawtransaction method when `verbose` is passed.\n"
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("gettransaction", "\"1075db55d416d3ca199f55b6084e2115b9345e16c5cf302fc80e9d5fbf5d48d\"")
            + HelpExampleCli("gettransaction", "\"1075db55d416d3ca199f55b6084e2115b9345e16c5cf302fc80e9d5fbf5d48d\" true")
            + HelpExampleCli("gettransaction", "\"1075db55d416d3ca199f55b6084e2115b9345e16c5cf302fc80e9d5fbf5d48d\" false true")
            + HelpExampleRpc("gettransaction", "\"1075db55d416d3ca199f55b6084e2115b9345e16c5cf302fc80e9d5fbf5d48d\"")
                },
            }.Check(request);

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    uint256 hash(ParseHashV(request.params[0], "txid"));

    isminefilter filter = ISMINE_SPENDABLE;

    if (ParseIncludeWatchonly(request.params[1], *pwallet)) {
        filter |= ISMINE_WATCH_ONLY;
    }

    bool verbose = request.params[2].isNull() ? false : request.params[2].get_bool();

    std::string asset = "";
    if (request.params[3].isStr() && !request.params[3].get_str().empty()) {
        asset = request.params[3].get_str();
    }

    UniValue entry(UniValue::VOBJ);
    auto it = pwallet->mapWallet.find(hash);
    if (it == pwallet->mapWallet.end()) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid or non-wallet transaction id");
    }
    const CWalletTx& wtx = it->second;

    CAmountMap nCredit = wtx.GetCredit(filter);
    CAmountMap nDebit = wtx.GetDebit(filter);
    CAmountMap nNet = nCredit - nDebit;
    assert(HasValidFee(*wtx.tx));
    CAmountMap nFee = wtx.IsFromMe(filter) ? CAmountMap() - GetFeeMap(*wtx.tx) : CAmountMap();
    if (!g_con_elementsmode) {
        CAmount total_out = 0;
        for (const auto& output : wtx.tx->vout) {
            total_out += output.nValue.GetAmount();
        }
        nFee = CAmountMap();
        nFee[::policyAsset] = wtx.IsFromMe(filter) ? total_out - nDebit[::policyAsset] : 0;
    }

    entry.pushKV("amount", AmountMapToUniv(nNet - nFee, asset));
    if (wtx.IsFromMe(filter))
        entry.pushKV("fee", AmountMapToUniv(nFee, ""));

    WalletTxToJSON(pwallet->chain(), *locked_chain, wtx, entry);

    UniValue details(UniValue::VARR);
    ListTransactions(*locked_chain, pwallet, wtx, 0, false, details, filter, nullptr /* filter_label */);
    entry.pushKV("details", details);

    std::string strHex = EncodeHexTx(*wtx.tx, pwallet->chain().rpcSerializationFlags());
    entry.pushKV("hex", strHex);

    if (verbose) {
        UniValue decoded(UniValue::VOBJ);
        TxToUniv(*wtx.tx, uint256(), decoded, false);
        entry.pushKV("decoded", decoded);
    }

    return entry;
}

static UniValue abandontransaction(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"abandontransaction",
                "\nMark in-wallet transaction <txid> as abandoned\n"
                "This will mark this transaction and all its in-wallet descendants as abandoned which will allow\n"
                "for their inputs to be respent.  It can be used to replace \"stuck\" or evicted transactions.\n"
                "It only works on transactions which are not included in a block and are not currently in the mempool.\n"
                "It has no effect on transactions which are already abandoned.\n",
                {
                    {"txid", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The transaction id"},
                },
                RPCResults{},
                RPCExamples{
                    HelpExampleCli("abandontransaction", "\"1075db55d416d3ca199f55b6084e2115b9345e16c5cf302fc80e9d5fbf5d48d\"")
            + HelpExampleRpc("abandontransaction", "\"1075db55d416d3ca199f55b6084e2115b9345e16c5cf302fc80e9d5fbf5d48d\"")
                },
            }.Check(request);

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    uint256 hash(ParseHashV(request.params[0], "txid"));

    if (!pwallet->mapWallet.count(hash)) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid or non-wallet transaction id");
    }
    if (!pwallet->AbandonTransaction(hash)) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Transaction not eligible for abandonment");
    }

    return NullUniValue;
}


static UniValue backupwallet(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"backupwallet",
                "\nSafely copies current wallet file to destination, which can be a directory or a path with filename.\n",
                {
                    {"destination", RPCArg::Type::STR, RPCArg::Optional::NO, "The destination directory or file"},
                },
                RPCResults{},
                RPCExamples{
                    HelpExampleCli("backupwallet", "\"backup.dat\"")
            + HelpExampleRpc("backupwallet", "\"backup.dat\"")
                },
            }.Check(request);

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    std::string strDest = request.params[0].get_str();
    if (!pwallet->BackupWallet(strDest)) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Error: Wallet backup failed!");
    }

    return NullUniValue;
}


static UniValue keypoolrefill(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"keypoolrefill",
                "\nFills the keypool."+
                    HelpRequiringPassphrase(pwallet) + "\n",
                {
                    {"newsize", RPCArg::Type::NUM, /* default */ "100", "The new keypool size"},
                },
                RPCResults{},
                RPCExamples{
                    HelpExampleCli("keypoolrefill", "")
            + HelpExampleRpc("keypoolrefill", "")
                },
            }.Check(request);

    if (pwallet->IsWalletFlagSet(WALLET_FLAG_DISABLE_PRIVATE_KEYS)) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Error: Private keys are disabled for this wallet");
    }

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    // 0 is interpreted by TopUpKeyPool() as the default keypool size given by -keypool
    unsigned int kpSize = 0;
    if (!request.params[0].isNull()) {
        if (request.params[0].get_int() < 0)
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, expected valid size.");
        kpSize = (unsigned int)request.params[0].get_int();
    }

    EnsureWalletIsUnlocked(pwallet);
    pwallet->TopUpKeyPool(kpSize);

    if (pwallet->GetKeyPoolSize() < kpSize) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Error refreshing keypool.");
    }

    return NullUniValue;
}


static UniValue walletpassphrase(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"walletpassphrase",
                "\nStores the wallet decryption key in memory for 'timeout' seconds.\n"
                "This is needed prior to performing transactions related to private keys such as sending bitcoins\n"
            "\nNote:\n"
            "Issuing the walletpassphrase command while the wallet is already unlocked will set a new unlock\n"
            "time that overrides the old one.\n",
                {
                    {"passphrase", RPCArg::Type::STR, RPCArg::Optional::NO, "The wallet passphrase"},
                    {"timeout", RPCArg::Type::NUM, RPCArg::Optional::NO, "The time to keep the decryption key in seconds; capped at 100000000 (~3 years)."},
                },
                RPCResults{},
                RPCExamples{
            "\nUnlock the wallet for 60 seconds\n"
            + HelpExampleCli("walletpassphrase", "\"my pass phrase\" 60") +
            "\nLock the wallet again (before 60 seconds)\n"
            + HelpExampleCli("walletlock", "") +
            "\nAs a JSON-RPC call\n"
            + HelpExampleRpc("walletpassphrase", "\"my pass phrase\", 60")
                },
            }.Check(request);

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    if (!pwallet->IsCrypted()) {
        throw JSONRPCError(RPC_WALLET_WRONG_ENC_STATE, "Error: running with an unencrypted wallet, but walletpassphrase was called.");
    }

    // Note that the walletpassphrase is stored in request.params[0] which is not mlock()ed
    SecureString strWalletPass;
    strWalletPass.reserve(100);
    // TODO: get rid of this .c_str() by implementing SecureString::operator=(std::string)
    // Alternately, find a way to make request.params[0] mlock()'d to begin with.
    strWalletPass = request.params[0].get_str().c_str();

    // Get the timeout
    int64_t nSleepTime = request.params[1].get_int64();
    // Timeout cannot be negative, otherwise it will relock immediately
    if (nSleepTime < 0) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Timeout cannot be negative.");
    }
    // Clamp timeout
    constexpr int64_t MAX_SLEEP_TIME = 100000000; // larger values trigger a macos/libevent bug?
    if (nSleepTime > MAX_SLEEP_TIME) {
        nSleepTime = MAX_SLEEP_TIME;
    }

    if (strWalletPass.empty()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "passphrase can not be empty");
    }

    if (!pwallet->Unlock(strWalletPass)) {
        throw JSONRPCError(RPC_WALLET_PASSPHRASE_INCORRECT, "Error: The wallet passphrase entered was incorrect.");
    }

    pwallet->TopUpKeyPool();

    pwallet->nRelockTime = GetTime() + nSleepTime;

    // Keep a weak pointer to the wallet so that it is possible to unload the
    // wallet before the following callback is called. If a valid shared pointer
    // is acquired in the callback then the wallet is still loaded.
    std::weak_ptr<CWallet> weak_wallet = wallet;
    pwallet->chain().rpcRunLater(strprintf("lockwallet(%s)", pwallet->GetName()), [weak_wallet] {
        if (auto shared_wallet = weak_wallet.lock()) {
            LOCK(shared_wallet->cs_wallet);
            shared_wallet->Lock();
            shared_wallet->nRelockTime = 0;
        }
    }, nSleepTime);

    return NullUniValue;
}


static UniValue walletpassphrasechange(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"walletpassphrasechange",
                "\nChanges the wallet passphrase from 'oldpassphrase' to 'newpassphrase'.\n",
                {
                    {"oldpassphrase", RPCArg::Type::STR, RPCArg::Optional::NO, "The current passphrase"},
                    {"newpassphrase", RPCArg::Type::STR, RPCArg::Optional::NO, "The new passphrase"},
                },
                RPCResults{},
                RPCExamples{
                    HelpExampleCli("walletpassphrasechange", "\"old one\" \"new one\"")
            + HelpExampleRpc("walletpassphrasechange", "\"old one\", \"new one\"")
                },
            }.Check(request);

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    if (!pwallet->IsCrypted()) {
        throw JSONRPCError(RPC_WALLET_WRONG_ENC_STATE, "Error: running with an unencrypted wallet, but walletpassphrasechange was called.");
    }

    // TODO: get rid of these .c_str() calls by implementing SecureString::operator=(std::string)
    // Alternately, find a way to make request.params[0] mlock()'d to begin with.
    SecureString strOldWalletPass;
    strOldWalletPass.reserve(100);
    strOldWalletPass = request.params[0].get_str().c_str();

    SecureString strNewWalletPass;
    strNewWalletPass.reserve(100);
    strNewWalletPass = request.params[1].get_str().c_str();

    if (strOldWalletPass.empty() || strNewWalletPass.empty()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "passphrase can not be empty");
    }

    if (!pwallet->ChangeWalletPassphrase(strOldWalletPass, strNewWalletPass)) {
        throw JSONRPCError(RPC_WALLET_PASSPHRASE_INCORRECT, "Error: The wallet passphrase entered was incorrect.");
    }

    return NullUniValue;
}


static UniValue walletlock(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"walletlock",
                "\nRemoves the wallet encryption key from memory, locking the wallet.\n"
                "After calling this method, you will need to call walletpassphrase again\n"
                "before being able to call any methods which require the wallet to be unlocked.\n",
                {},
                RPCResults{},
                RPCExamples{
            "\nSet the passphrase for 2 minutes to perform a transaction\n"
            + HelpExampleCli("walletpassphrase", "\"my pass phrase\" 120") +
            "\nPerform a send (requires passphrase set)\n"
            + HelpExampleCli("sendtoaddress", "\"1M72Sfpbz1BPpXFHz9m3CdqATR44Jvaydd\" 1.0") +
            "\nClear the passphrase since we are done before 2 minutes is up\n"
            + HelpExampleCli("walletlock", "") +
            "\nAs a JSON-RPC call\n"
            + HelpExampleRpc("walletlock", "")
                },
            }.Check(request);

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    if (!pwallet->IsCrypted()) {
        throw JSONRPCError(RPC_WALLET_WRONG_ENC_STATE, "Error: running with an unencrypted wallet, but walletlock was called.");
    }

    pwallet->Lock();
    pwallet->nRelockTime = 0;

    return NullUniValue;
}


static UniValue encryptwallet(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"encryptwallet",
                "\nEncrypts the wallet with 'passphrase'. This is for first time encryption.\n"
                "After this, any calls that interact with private keys such as sending or signing \n"
                "will require the passphrase to be set prior the making these calls.\n"
                "Use the walletpassphrase call for this, and then walletlock call.\n"
                "If the wallet is already encrypted, use the walletpassphrasechange call.\n",
                {
                    {"passphrase", RPCArg::Type::STR, RPCArg::Optional::NO, "The pass phrase to encrypt the wallet with. It must be at least 1 character, but should be long."},
                },
                RPCResults{},
                RPCExamples{
            "\nEncrypt your wallet\n"
            + HelpExampleCli("encryptwallet", "\"my pass phrase\"") +
            "\nNow set the passphrase to use the wallet, such as for signing or sending bitcoin\n"
            + HelpExampleCli("walletpassphrase", "\"my pass phrase\"") +
            "\nNow we can do something like sign\n"
            + HelpExampleCli("signmessage", "\"address\" \"test message\"") +
            "\nNow lock the wallet again by removing the passphrase\n"
            + HelpExampleCli("walletlock", "") +
            "\nAs a JSON-RPC call\n"
            + HelpExampleRpc("encryptwallet", "\"my pass phrase\"")
                },
            }.Check(request);

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    if (pwallet->IsWalletFlagSet(WALLET_FLAG_DISABLE_PRIVATE_KEYS)) {
        throw JSONRPCError(RPC_WALLET_ENCRYPTION_FAILED, "Error: wallet does not contain private keys, nothing to encrypt.");
    }

    if (pwallet->IsCrypted()) {
        throw JSONRPCError(RPC_WALLET_WRONG_ENC_STATE, "Error: running with an encrypted wallet, but encryptwallet was called.");
    }

    // TODO: get rid of this .c_str() by implementing SecureString::operator=(std::string)
    // Alternately, find a way to make request.params[0] mlock()'d to begin with.
    SecureString strWalletPass;
    strWalletPass.reserve(100);
    strWalletPass = request.params[0].get_str().c_str();

    if (strWalletPass.empty()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "passphrase can not be empty");
    }

    if (!pwallet->EncryptWallet(strWalletPass)) {
        throw JSONRPCError(RPC_WALLET_ENCRYPTION_FAILED, "Error: Failed to encrypt the wallet.");
    }

    return "wallet encrypted; The keypool has been flushed and a new HD seed was generated (if you are using HD). You need to make a new backup.";
}

static UniValue lockunspent(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"lockunspent",
                "\nUpdates list of temporarily unspendable outputs.\n"
                "Temporarily lock (unlock=false) or unlock (unlock=true) specified transaction outputs.\n"
                "If no transaction outputs are specified when unlocking then all current locked transaction outputs are unlocked.\n"
                "A locked transaction output will not be chosen by automatic coin selection, when spending bitcoins.\n"
                "Locks are stored in memory only. Nodes start with zero locked outputs, and the locked output list\n"
                "is always cleared (by virtue of process exit) when a node stops or fails.\n"
                "Also see the listunspent call\n",
                {
                    {"unlock", RPCArg::Type::BOOL, RPCArg::Optional::NO, "Whether to unlock (true) or lock (false) the specified transactions"},
                    {"transactions", RPCArg::Type::ARR, /* default */ "empty array", "A json array of objects. Each object the txid (string) vout (numeric).",
                        {
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                                {
                                    {"txid", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The transaction id"},
                                    {"vout", RPCArg::Type::NUM, RPCArg::Optional::NO, "The output number"},
                                },
                            },
                        },
                    },
                },
                RPCResult{
            "true|false    (boolean) Whether the command was successful or not\n"
                },
                RPCExamples{
            "\nList the unspent transactions\n"
            + HelpExampleCli("listunspent", "") +
            "\nLock an unspent transaction\n"
            + HelpExampleCli("lockunspent", "false \"[{\\\"txid\\\":\\\"a08e6907dbbd3d809776dbfc5d82e371b764ed838b5655e72f463568df1aadf0\\\",\\\"vout\\\":1}]\"") +
            "\nList the locked transactions\n"
            + HelpExampleCli("listlockunspent", "") +
            "\nUnlock the transaction again\n"
            + HelpExampleCli("lockunspent", "true \"[{\\\"txid\\\":\\\"a08e6907dbbd3d809776dbfc5d82e371b764ed838b5655e72f463568df1aadf0\\\",\\\"vout\\\":1}]\"") +
            "\nAs a JSON-RPC call\n"
            + HelpExampleRpc("lockunspent", "false, \"[{\\\"txid\\\":\\\"a08e6907dbbd3d809776dbfc5d82e371b764ed838b5655e72f463568df1aadf0\\\",\\\"vout\\\":1}]\"")
                },
            }.Check(request);

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    RPCTypeCheckArgument(request.params[0], UniValue::VBOOL);

    bool fUnlock = request.params[0].get_bool();

    if (request.params[1].isNull()) {
        if (fUnlock)
            pwallet->UnlockAllCoins();
        return true;
    }

    RPCTypeCheckArgument(request.params[1], UniValue::VARR);

    const UniValue& output_params = request.params[1];

    // Create and validate the COutPoints first.

    std::vector<COutPoint> outputs;
    outputs.reserve(output_params.size());

    for (unsigned int idx = 0; idx < output_params.size(); idx++) {
        const UniValue& o = output_params[idx].get_obj();

        RPCTypeCheckObj(o,
            {
                {"txid", UniValueType(UniValue::VSTR)},
                {"vout", UniValueType(UniValue::VNUM)},
            });

        const uint256 txid(ParseHashO(o, "txid"));
        const int nOutput = find_value(o, "vout").get_int();
        if (nOutput < 0) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, vout must be positive");
        }

        const COutPoint outpt(txid, nOutput);

        const auto it = pwallet->mapWallet.find(outpt.hash);
        if (it == pwallet->mapWallet.end()) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, unknown transaction");
        }

        const CWalletTx& trans = it->second;

        if (outpt.n >= trans.tx->vout.size()) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, vout index out of bounds");
        }

        if (pwallet->IsSpent(outpt.hash, outpt.n)) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, expected unspent output");
        }

        const bool is_locked = pwallet->IsLockedCoin(outpt.hash, outpt.n);

        if (fUnlock && !is_locked) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, expected locked output");
        }

        if (!fUnlock && is_locked) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter, output already locked");
        }

        outputs.push_back(outpt);
    }

    // Atomically set (un)locked status for the outputs.
    for (const COutPoint& outpt : outputs) {
        if (fUnlock) pwallet->UnlockCoin(outpt);
        else pwallet->LockCoin(outpt);
    }

    return true;
}

static UniValue listlockunspent(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"listlockunspent",
                "\nReturns list of temporarily unspendable outputs.\n"
                "See the lockunspent call to lock and unlock transactions for spending.\n",
                {},
                RPCResult{
            "[\n"
            "  {\n"
            "    \"txid\" : \"transactionid\",     (string) The transaction id locked\n"
            "    \"vout\" : n                      (numeric) The vout value\n"
            "  }\n"
            "  ,...\n"
            "]\n"
                },
                RPCExamples{
            "\nList the unspent transactions\n"
            + HelpExampleCli("listunspent", "") +
            "\nLock an unspent transaction\n"
            + HelpExampleCli("lockunspent", "false \"[{\\\"txid\\\":\\\"a08e6907dbbd3d809776dbfc5d82e371b764ed838b5655e72f463568df1aadf0\\\",\\\"vout\\\":1}]\"") +
            "\nList the locked transactions\n"
            + HelpExampleCli("listlockunspent", "") +
            "\nUnlock the transaction again\n"
            + HelpExampleCli("lockunspent", "true \"[{\\\"txid\\\":\\\"a08e6907dbbd3d809776dbfc5d82e371b764ed838b5655e72f463568df1aadf0\\\",\\\"vout\\\":1}]\"") +
            "\nAs a JSON-RPC call\n"
            + HelpExampleRpc("listlockunspent", "")
                },
            }.Check(request);

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    std::vector<COutPoint> vOutpts;
    pwallet->ListLockedCoins(vOutpts);

    UniValue ret(UniValue::VARR);

    for (const COutPoint& outpt : vOutpts) {
        UniValue o(UniValue::VOBJ);

        o.pushKV("txid", outpt.hash.GetHex());
        o.pushKV("vout", (int)outpt.n);
        ret.push_back(o);
    }

    return ret;
}

static UniValue settxfee(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"settxfee",
                "\nSet the transaction fee per kB for this wallet. Overrides the global -paytxfee command line parameter.\n",
                {
                    {"amount", RPCArg::Type::AMOUNT, RPCArg::Optional::NO, "The transaction fee in " + CURRENCY_UNIT + "/kB"},
                },
                RPCResult{
            "true|false        (boolean) Returns true if successful\n"
                },
                RPCExamples{
                    HelpExampleCli("settxfee", "0.00001")
            + HelpExampleRpc("settxfee", "0.00001")
                },
            }.Check(request);

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    CAmount nAmount = AmountFromValue(request.params[0]);
    CFeeRate tx_fee_rate(nAmount, 1000);
    if (tx_fee_rate == CFeeRate(0)) {
        // automatic selection
    } else if (tx_fee_rate < pwallet->chain().relayMinFee()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("txfee cannot be less than min relay tx fee (%s)", pwallet->chain().relayMinFee().ToString()));
    } else if (tx_fee_rate < pwallet->m_min_fee) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("txfee cannot be less than wallet min fee (%s)", pwallet->m_min_fee.ToString()));
    }

    pwallet->m_pay_tx_fee = tx_fee_rate;
    return true;
}

static UniValue getbalances(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const rpc_wallet = GetWalletForJSONRPCRequest(request);
    if (!EnsureWalletIsAvailable(rpc_wallet.get(), request.fHelp)) {
        return NullUniValue;
    }
    CWallet& wallet = *rpc_wallet;

    RPCHelpMan{
        "getbalances",
        "Returns an object with all balances in " + CURRENCY_UNIT + ".\n",
        {},
        RPCResult{
            "{\n"
            "    \"mine\": {                        (object) balances from outputs that the wallet can sign\n"
            "      \"trusted\": xxx                 (numeric) trusted balance (outputs created by the wallet or confirmed outputs)\n"
            "      \"untrusted_pending\": xxx       (numeric) untrusted pending balance (outputs created by others that are in the mempool)\n"
            "      \"immature\": xxx                (numeric) balance from immature coinbase outputs\n"
            "      \"used\": xxx                    (numeric) (only present if avoid_reuse is set) balance from coins sent to addresses that were previously spent from (potentially privacy violating)\n"
            "    },\n"
            "    \"watchonly\": {                   (object) watchonly balances (not present if wallet does not watch anything)\n"
            "      \"trusted\": xxx                 (numeric) trusted balance (outputs created by the wallet or confirmed outputs)\n"
            "      \"untrusted_pending\": xxx       (numeric) untrusted pending balance (outputs created by others that are in the mempool)\n"
            "      \"immature\": xxx                (numeric) balance from immature coinbase outputs\n"
            "    },\n"
            "}\n"},
        RPCExamples{
            HelpExampleCli("getbalances", "") +
            HelpExampleRpc("getbalances", "")},
    }.Check(request);

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    wallet.BlockUntilSyncedToCurrentChain();

    auto locked_chain = wallet.chain().lock();
    LOCK(wallet.cs_wallet);

    UniValue obj(UniValue::VOBJ);

    const auto bal = wallet.GetBalance();
    UniValue balances{UniValue::VOBJ};
    {
        UniValue balances_mine{UniValue::VOBJ};
        balances_mine.pushKV("trusted", AmountMapToUniv(bal.m_mine_trusted, ""));
        balances_mine.pushKV("untrusted_pending", AmountMapToUniv(bal.m_mine_untrusted_pending, ""));
        balances_mine.pushKV("immature", AmountMapToUniv(bal.m_mine_immature, ""));
        if (wallet.IsWalletFlagSet(WALLET_FLAG_AVOID_REUSE)) {
            // If the AVOID_REUSE flag is set, bal has been set to just the un-reused address balance. Get
            // the total balance, and then subtract bal to get the reused address balance.
            const auto full_bal = wallet.GetBalance(0, false);
            balances_mine.pushKV("used", AmountMapToUniv(full_bal.m_mine_trusted + full_bal.m_mine_untrusted_pending - bal.m_mine_trusted - bal.m_mine_untrusted_pending, ""));
        }
        balances.pushKV("mine", balances_mine);
    }
    auto spk_man = wallet.GetLegacyScriptPubKeyMan();
    if (spk_man && spk_man->HaveWatchOnly()) {
        UniValue balances_watchonly{UniValue::VOBJ};
        balances_watchonly.pushKV("trusted", AmountMapToUniv(bal.m_watchonly_trusted, ""));
        balances_watchonly.pushKV("untrusted_pending", AmountMapToUniv(bal.m_watchonly_untrusted_pending, ""));
        balances_watchonly.pushKV("immature", AmountMapToUniv(bal.m_watchonly_immature, ""));
        balances.pushKV("watchonly", balances_watchonly);
    }
    return balances;
}

static UniValue getwalletinfo(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    RPCHelpMan{"getwalletinfo",
                "Returns an object containing various wallet state info.\n",
                {},
                RPCResult{
            "{\n"
            "  \"walletname\": xxxxx,               (string) the wallet name\n"
            "  \"walletversion\": xxxxx,            (numeric) the wallet version\n"
            "  \"balance\": xxxxxxx,                (numeric) DEPRECATED. Identical to getbalances().mine.trusted\n"
            "  \"unconfirmed_balance\": xxx,        (numeric) DEPRECATED. Identical to getbalances().mine.untrusted_pending\n"
            "  \"immature_balance\": xxxxxx,        (numeric) DEPRECATED. Identical to getbalances().mine.immature\n"
            "  \"txcount\": xxxxxxx,                (numeric) the total number of transactions in the wallet\n"
            "  \"keypoololdest\": xxxxxx,           (numeric) the " + UNIX_EPOCH_TIME + " of the oldest pre-generated key in the key pool\n"
            "  \"keypoolsize\": xxxx,               (numeric) how many new keys are pre-generated (only counts external keys)\n"
            "  \"keypoolsize_hd_internal\": xxxx,   (numeric) how many new keys are pre-generated for internal use (used for change outputs, only appears if the wallet is using this feature, otherwise external keys are used)\n"
            "  \"unlocked_until\": ttt,             (numeric) the " + UNIX_EPOCH_TIME + " until which the wallet is unlocked for transfers, or 0 if the wallet is locked\n"
            "  \"paytxfee\": x.xxxx,                (numeric) the transaction fee configuration, set in " + CURRENCY_UNIT + "/kB\n"
            "  \"hdseedid\": \"<hash160>\"            (string, optional) the Hash160 of the HD seed (only present when HD is enabled)\n"
            "  \"private_keys_enabled\": true|false (boolean) false if privatekeys are disabled for this wallet (enforced watch-only wallet)\n"
            "  \"avoid_reuse\": true|false          (boolean) whether this wallet tracks clean/dirty coins in terms of reuse\n"
            "  \"scanning\":                        (json object) current scanning details, or false if no scan is in progress\n"
            "    {\n"
            "      \"duration\" : xxxx              (numeric) elapsed seconds since scan start\n"
            "      \"progress\" : x.xxxx,           (numeric) scanning progress percentage [0.0, 1.0]\n"
            "    }\n"
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("getwalletinfo", "")
            + HelpExampleRpc("getwalletinfo", "")
                },
    }.Check(request);

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    UniValue obj(UniValue::VOBJ);

    size_t kpExternalSize = pwallet->KeypoolCountExternalKeys();
    const auto bal = pwallet->GetBalance();
    obj.pushKV("walletname", pwallet->GetName());
    obj.pushKV("walletversion", pwallet->GetVersion());
    obj.pushKV("balance", AmountMapToUniv(bal.m_mine_trusted, ""));
    obj.pushKV("unconfirmed_balance", AmountMapToUniv(bal.m_mine_untrusted_pending, ""));
    obj.pushKV("immature_balance", AmountMapToUniv(bal.m_mine_immature,  ""));
    obj.pushKV("txcount",       (int)pwallet->mapWallet.size());
    obj.pushKV("keypoololdest", pwallet->GetOldestKeyPoolTime());
    obj.pushKV("keypoolsize", (int64_t)kpExternalSize);

    LegacyScriptPubKeyMan* spk_man = pwallet->GetLegacyScriptPubKeyMan();
    if (spk_man) {
        CKeyID seed_id = spk_man->GetHDChain().seed_id;
        if (!seed_id.IsNull()) {
            obj.pushKV("hdseedid", seed_id.GetHex());
        }
    }

    if (pwallet->CanSupportFeature(FEATURE_HD_SPLIT)) {
        obj.pushKV("keypoolsize_hd_internal",   (int64_t)(pwallet->GetKeyPoolSize() - kpExternalSize));
    }
    if (pwallet->IsCrypted()) {
        obj.pushKV("unlocked_until", pwallet->nRelockTime);
    }
    obj.pushKV("paytxfee", ValueFromAmount(pwallet->m_pay_tx_fee.GetFeePerK()));
    obj.pushKV("private_keys_enabled", !pwallet->IsWalletFlagSet(WALLET_FLAG_DISABLE_PRIVATE_KEYS));
    obj.pushKV("avoid_reuse", pwallet->IsWalletFlagSet(WALLET_FLAG_AVOID_REUSE));
    if (pwallet->IsScanning()) {
        UniValue scanning(UniValue::VOBJ);
        scanning.pushKV("duration", pwallet->ScanningDuration() / 1000);
        scanning.pushKV("progress", pwallet->ScanningProgress());
        obj.pushKV("scanning", scanning);
    } else {
        obj.pushKV("scanning", false);
    }
    return obj;
}

static UniValue listwalletdir(const JSONRPCRequest& request)
{
            RPCHelpMan{"listwalletdir",
                "Returns a list of wallets in the wallet directory.\n",
                {},
                RPCResult{
            "{\n"
            "  \"wallets\" : [                (json array of objects)\n"
            "    {\n"
            "      \"name\" : \"name\"          (string) The wallet name\n"
            "    }\n"
            "    ,...\n"
            "  ]\n"
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("listwalletdir", "")
            + HelpExampleRpc("listwalletdir", "")
                },
            }.Check(request);

    UniValue wallets(UniValue::VARR);
    for (const auto& path : ListWalletDir()) {
        UniValue wallet(UniValue::VOBJ);
        wallet.pushKV("name", path.string());
        wallets.push_back(wallet);
    }

    UniValue result(UniValue::VOBJ);
    result.pushKV("wallets", wallets);
    return result;
}

static UniValue listwallets(const JSONRPCRequest& request)
{
            RPCHelpMan{"listwallets",
                "Returns a list of currently loaded wallets.\n"
                "For full information on the wallet, use \"getwalletinfo\"\n",
                {},
                RPCResult{
            "[                         (json array of strings)\n"
            "  \"walletname\"            (string) the wallet name\n"
            "   ...\n"
            "]\n"
                },
                RPCExamples{
                    HelpExampleCli("listwallets", "")
            + HelpExampleRpc("listwallets", "")
                },
            }.Check(request);

    UniValue obj(UniValue::VARR);

    for (const std::shared_ptr<CWallet>& wallet : GetWallets()) {
        if (!EnsureWalletIsAvailable(wallet.get(), request.fHelp)) {
            return NullUniValue;
        }

        LOCK(wallet->cs_wallet);

        obj.push_back(wallet->GetName());
    }

    return obj;
}

static UniValue loadwallet(const JSONRPCRequest& request)
{
            RPCHelpMan{"loadwallet",
                "\nLoads a wallet from a wallet file or directory."
                "\nNote that all wallet command-line options used when starting the daemon will be"
                "\napplied to the new wallet (eg -zapwallettxes, upgradewallet, rescan, etc).\n",
                {
                    {"filename", RPCArg::Type::STR, RPCArg::Optional::NO, "The wallet directory or .dat file."},
                },
                RPCResult{
            "{\n"
            "  \"name\" :    <wallet_name>,        (string) The wallet name if loaded successfully.\n"
            "  \"warning\" : <warning>,            (string) Warning message if wallet was not loaded cleanly.\n"
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("loadwallet", "\"test.dat\"")
            + HelpExampleRpc("loadwallet", "\"test.dat\"")
                },
            }.Check(request);

    WalletLocation location(request.params[0].get_str());

    if (!location.Exists()) {
        throw JSONRPCError(RPC_WALLET_NOT_FOUND, "Wallet " + location.GetName() + " not found.");
    } else if (fs::is_directory(location.GetPath())) {
        // The given filename is a directory. Check that there's a wallet.dat file.
        fs::path wallet_dat_file = location.GetPath() / "wallet.dat";
        if (fs::symlink_status(wallet_dat_file).type() == fs::file_not_found) {
            throw JSONRPCError(RPC_WALLET_NOT_FOUND, "Directory " + location.GetName() + " does not contain a wallet.dat file.");
        }
    }

    std::string error;
    std::vector<std::string> warning;
    std::shared_ptr<CWallet> const wallet = LoadWallet(*g_rpc_chain, location, error, warning);
    if (!wallet) throw JSONRPCError(RPC_WALLET_ERROR, error);

    UniValue obj(UniValue::VOBJ);
    obj.pushKV("name", wallet->GetName());
    obj.pushKV("warning", Join(warning, "\n"));

    return obj;
}

static UniValue setwalletflag(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            std::string flags = "";
            for (auto& it : WALLET_FLAG_MAP)
                if (it.second & MUTABLE_WALLET_FLAGS)
                    flags += (flags == "" ? "" : ", ") + it.first;
            RPCHelpMan{"setwalletflag",
                "\nChange the state of the given wallet flag for a wallet.\n",
                {
                    {"flag", RPCArg::Type::STR, RPCArg::Optional::NO, "The name of the flag to change. Current available flags: " + flags},
                    {"value", RPCArg::Type::BOOL, /* default */ "true", "The new state."},
                },
                RPCResult{
            "{\n"
            "    \"flag_name\": string   (string) The name of the flag that was modified\n"
            "    \"flag_state\": bool    (bool) The new state of the flag\n"
            "    \"warnings\": string    (string) Any warnings associated with the change\n"
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("setwalletflag", "avoid_reuse")
                  + HelpExampleRpc("setwalletflag", "\"avoid_reuse\"")
                },
            }.Check(request);

    std::string flag_str = request.params[0].get_str();
    bool value = request.params[1].isNull() || request.params[1].get_bool();

    if (!WALLET_FLAG_MAP.count(flag_str)) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Unknown wallet flag: %s", flag_str));
    }

    auto flag = WALLET_FLAG_MAP.at(flag_str);

    if (!(flag & MUTABLE_WALLET_FLAGS)) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Wallet flag is immutable: %s", flag_str));
    }

    UniValue res(UniValue::VOBJ);

    if (pwallet->IsWalletFlagSet(flag) == value) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Wallet flag is already set to %s: %s", value ? "true" : "false", flag_str));
    }

    res.pushKV("flag_name", flag_str);
    res.pushKV("flag_state", value);

    if (value) {
        pwallet->SetWalletFlag(flag);
    } else {
        pwallet->UnsetWalletFlag(flag);
    }

    if (flag && value && WALLET_FLAG_CAVEATS.count(flag)) {
        res.pushKV("warnings", WALLET_FLAG_CAVEATS.at(flag));
    }

    return res;
}

static UniValue createwallet(const JSONRPCRequest& request)
{
    RPCHelpMan{
        "createwallet",
        "\nCreates and loads a new wallet.\n",
        {
            {"wallet_name", RPCArg::Type::STR, RPCArg::Optional::NO, "The name for the new wallet. If this is a path, the wallet will be created at the path location."},
            {"disable_private_keys", RPCArg::Type::BOOL, /* default */ "false", "Disable the possibility of private keys (only watchonlys are possible in this mode)."},
            {"blank", RPCArg::Type::BOOL, /* default */ "false", "Create a blank wallet. A blank wallet has no keys or HD seed. One can be set using sethdseed."},
            {"passphrase", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "Encrypt the wallet with this passphrase."},
            {"avoid_reuse", RPCArg::Type::BOOL, /* default */ "false", "Keep track of coin reuse, and treat dirty and clean coins differently with privacy considerations in mind."},
        },
        RPCResult{
            "{\n"
            "  \"name\" :    <wallet_name>,        (string) The wallet name if created successfully. If the wallet was created using a full path, the wallet_name will be the full path.\n"
            "  \"warning\" : <warning>,            (string) Warning message if wallet was not loaded cleanly.\n"
            "}\n"
        },
        RPCExamples{
            HelpExampleCli("createwallet", "\"testwallet\"")
            + HelpExampleRpc("createwallet", "\"testwallet\"")
        },
    }.Check(request);

    uint64_t flags = 0;
    if (!request.params[1].isNull() && request.params[1].get_bool()) {
        flags |= WALLET_FLAG_DISABLE_PRIVATE_KEYS;
    }

    if (!request.params[2].isNull() && request.params[2].get_bool()) {
        flags |= WALLET_FLAG_BLANK_WALLET;
    }
    SecureString passphrase;
    passphrase.reserve(100);
    std::vector<std::string> warnings;
    if (!request.params[3].isNull()) {
        passphrase = request.params[3].get_str().c_str();
        if (passphrase.empty()) {
            // Empty string means unencrypted
            warnings.emplace_back("Empty string given as passphrase, wallet will not be encrypted.");
        }
    }

    if (!request.params[4].isNull() && request.params[4].get_bool()) {
        flags |= WALLET_FLAG_AVOID_REUSE;
    }

    std::string error;
    std::shared_ptr<CWallet> wallet;
    WalletCreationStatus status = CreateWallet(*g_rpc_chain, passphrase, flags, request.params[0].get_str(), error, warnings, wallet);
    switch (status) {
        case WalletCreationStatus::CREATION_FAILED:
            throw JSONRPCError(RPC_WALLET_ERROR, error);
        case WalletCreationStatus::ENCRYPTION_FAILED:
            throw JSONRPCError(RPC_WALLET_ENCRYPTION_FAILED, error);
        case WalletCreationStatus::SUCCESS:
            break;
        // no default case, so the compiler can warn about missing cases
    }

    UniValue obj(UniValue::VOBJ);
    obj.pushKV("name", wallet->GetName());
    obj.pushKV("warning", Join(warnings, "\n"));

    return obj;
}

static UniValue unloadwallet(const JSONRPCRequest& request)
{
            RPCHelpMan{"unloadwallet",
                "Unloads the wallet referenced by the request endpoint otherwise unloads the wallet specified in the argument.\n"
                "Specifying the wallet name on a wallet endpoint is invalid.",
                {
                    {"wallet_name", RPCArg::Type::STR, /* default */ "the wallet name from the RPC request", "The name of the wallet to unload."},
                },
                RPCResults{},
                RPCExamples{
                    HelpExampleCli("unloadwallet", "wallet_name")
            + HelpExampleRpc("unloadwallet", "wallet_name")
                },
            }.Check(request);

    std::string wallet_name;
    if (GetWalletNameFromJSONRPCRequest(request, wallet_name)) {
        if (!request.params[0].isNull()) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Cannot unload the requested wallet");
        }
    } else {
        wallet_name = request.params[0].get_str();
    }

    std::shared_ptr<CWallet> wallet = GetWallet(wallet_name);
    if (!wallet) {
        throw JSONRPCError(RPC_WALLET_NOT_FOUND, "Requested wallet does not exist or is not loaded");
    }

    // Release the "main" shared pointer and prevent further notifications.
    // Note that any attempt to load the same wallet would fail until the wallet
    // is destroyed (see CheckUniqueFileid).
    if (!RemoveWallet(wallet)) {
        throw JSONRPCError(RPC_MISC_ERROR, "Requested wallet already unloaded");
    }

    UnloadWallet(std::move(wallet));

    return NullUniValue;
}

static UniValue listunspent(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    RPCHelpMan{
                "listunspent",
                "\nReturns array of unspent transaction outputs\n"
                "with between minconf and maxconf (inclusive) confirmations.\n"
                "Optionally filter to only include txouts paid to specified addresses.\n",
                {
                    {"minconf", RPCArg::Type::NUM, /* default */ "1", "The minimum confirmations to filter"},
                    {"maxconf", RPCArg::Type::NUM, /* default */ "9999999", "The maximum confirmations to filter"},
                    {"addresses", RPCArg::Type::ARR, /* default */ "empty array", "A json array of addresses to filter",
                        {
                            {"address", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "address"},
                        },
                    },
                    {"include_unsafe", RPCArg::Type::BOOL, /* default */ "true", "Include outputs that are not safe to spend\n"
            "                  See description of \"safe\" attribute below."},
                    {"query_options", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED_NAMED_ARG, "JSON with query options",
                        {
                            {"minimumAmount", RPCArg::Type::AMOUNT, /* default */ "0", "Minimum value of each UTXO in " + CURRENCY_UNIT + ""},
                            {"maximumAmount", RPCArg::Type::AMOUNT, /* default */ "unlimited", "Maximum value of each UTXO in " + CURRENCY_UNIT + ""},
                            {"maximumCount", RPCArg::Type::NUM, /* default */ "unlimited", "Maximum number of UTXOs"},
                            {"minimumSumAmount", RPCArg::Type::AMOUNT, /* default */ "unlimited", "Minimum sum value of all UTXOs in " + CURRENCY_UNIT + ""},
                            {"asset", RPCArg::Type::STR, /* default */ "", "Asset to filter outputs for."},
                        },
                        "query_options"},
                },
                RPCResult{
            "[                   (array of json object)\n"
            "  {\n"
            "    \"txid\" : \"txid\",          (string) the transaction id \n"
            "    \"vout\" : n,               (numeric) the vout value\n"
            "    \"address\" : \"address\",    (string) the address\n"
            "    \"label\" : \"label\",        (string) The associated label, or \"\" for the default label\n"
            "    \"scriptPubKey\" : \"key\",   (string) the script key\n"
            "    \"amount\" : x.xxx,         (numeric) the transaction output amount in " + CURRENCY_UNIT + "\n"
            "    \"amountcommitment\" : \"hex\", (string) the transaction output commitment in hex\n"
            "    \"asset\" : \"hex\",          (string) the transaction output asset in hex\n"
            "    \"assetcommitment\" : \"hex\", (string) the transaction output asset commitment in hex\n"
            "    \"amountblinder\" : \"hex\",  (string) the transaction output amount blinding factor in hex\n"
            "    \"assetblinder\" : \"hex\",   (string) the transaction output asset blinding factor in hex\n"
            "    \"confirmations\" : n,      (numeric) The number of confirmations\n"
            "    \"redeemScript\" : \"script\" (string) The redeemScript if scriptPubKey is P2SH\n"
            "    \"witnessScript\" : \"script\" (string) witnessScript if the scriptPubKey is P2WSH or P2SH-P2WSH\n"
            "    \"spendable\" : xxx,        (bool) Whether we have the private keys to spend this output\n"
            "    \"solvable\" : xxx,         (bool) Whether we know how to spend this output, ignoring the lack of keys\n"
            "    \"reused\" : xxx,           (bool) (only present if avoid_reuse is set) Whether this output is reused/dirty (sent to an address that was previously spent from)\n"
            "    \"desc\" : xxx,             (string, only when solvable) A descriptor for spending this output\n"
            "    \"safe\" : xxx              (bool) Whether this output is considered safe to spend. Unconfirmed transactions\n"
            "                              from outside keys and unconfirmed replacement transactions are considered unsafe\n"
            "                              and are not eligible for spending by fundrawtransaction and sendtoaddress.\n"
            "  }\n"
            "  ,...\n"
            "]\n"
                },
                RPCExamples{
                    HelpExampleCli("listunspent", "")
            + HelpExampleCli("listunspent", "6 9999999 \"[\\\"1PGFqEzfmQch1gKD3ra4k18PNj3tTUUSqg\\\",\\\"1LtvqCaApEdUGFkpKMM4MstjcaL4dKg8SP\\\"]\"")
            + HelpExampleRpc("listunspent", "6, 9999999 \"[\\\"1PGFqEzfmQch1gKD3ra4k18PNj3tTUUSqg\\\",\\\"1LtvqCaApEdUGFkpKMM4MstjcaL4dKg8SP\\\"]\"")
            + HelpExampleCli("listunspent", "6 9999999 '[]' true '{ \"minimumAmount\": 0.005 }'")
            + HelpExampleRpc("listunspent", "6, 9999999, [] , true, { \"minimumAmount\": 0.005 } ")
                },
            }.Check(request);

    int nMinDepth = 1;
    if (!request.params[0].isNull()) {
        RPCTypeCheckArgument(request.params[0], UniValue::VNUM);
        nMinDepth = request.params[0].get_int();
    }

    int nMaxDepth = 9999999;
    if (!request.params[1].isNull()) {
        RPCTypeCheckArgument(request.params[1], UniValue::VNUM);
        nMaxDepth = request.params[1].get_int();
    }

    std::set<CTxDestination> destinations;
    if (!request.params[2].isNull()) {
        RPCTypeCheckArgument(request.params[2], UniValue::VARR);
        UniValue inputs = request.params[2].get_array();
        for (unsigned int idx = 0; idx < inputs.size(); idx++) {
            const UniValue& input = inputs[idx];
            CTxDestination dest = DecodeDestination(input.get_str());
            if (!IsValidDestination(dest)) {
                throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, std::string("Invalid Bitcoin address: ") + input.get_str());
            }
            if (!destinations.insert(dest).second) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, std::string("Invalid parameter, duplicated address: ") + input.get_str());
            }
        }
    }

    bool include_unsafe = true;
    if (!request.params[3].isNull()) {
        RPCTypeCheckArgument(request.params[3], UniValue::VBOOL);
        include_unsafe = request.params[3].get_bool();
    }

    CAmount nMinimumAmount = 0;
    CAmount nMaximumAmount = MAX_MONEY;
    CAmount nMinimumSumAmount = MAX_MONEY;
    uint64_t nMaximumCount = 0;
    std::string asset_str;

    if (!request.params[4].isNull()) {
        const UniValue& options = request.params[4].get_obj();

        if (options.exists("minimumAmount"))
            nMinimumAmount = AmountFromValue(options["minimumAmount"]);

        if (options.exists("maximumAmount"))
            nMaximumAmount = AmountFromValue(options["maximumAmount"]);

        if (options.exists("minimumSumAmount"))
            nMinimumSumAmount = AmountFromValue(options["minimumSumAmount"]);

        if (options.exists("maximumCount"))
            nMaximumCount = options["maximumCount"].get_int64();

        if (options.exists("asset"))
            asset_str = options["asset"].get_str();
    }

    CAsset asset_filter;
    if (!asset_str.empty()) {
        asset_filter = GetAssetFromString(asset_str);
    }

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    UniValue results(UniValue::VARR);
    std::vector<COutput> vecOutputs;
    {
        CCoinControl cctl;
        cctl.m_avoid_address_reuse = false;
        cctl.m_min_depth = nMinDepth;
        cctl.m_max_depth = nMaxDepth;
        auto locked_chain = pwallet->chain().lock();
        LOCK(pwallet->cs_wallet);
        pwallet->AvailableCoins(*locked_chain, vecOutputs, !include_unsafe, &cctl, nMinimumAmount, nMaximumAmount, nMinimumSumAmount, nMaximumCount, asset_filter.IsNull() ? nullptr : &asset_filter);
    }

    LOCK(pwallet->cs_wallet);

    const bool avoid_reuse = pwallet->IsWalletFlagSet(WALLET_FLAG_AVOID_REUSE);

    for (const COutput& out : vecOutputs) {
        CTxDestination address;
        const CTxOut& tx_out = out.tx->tx->vout[out.i];
        const CScript& scriptPubKey = out.tx->tx->vout[out.i].scriptPubKey;
        bool fValidAddress = ExtractDestination(scriptPubKey, address);
        bool reused = avoid_reuse && pwallet->IsUsedDestination(out.tx->GetHash(), out.i);

        if (destinations.size() && (!fValidAddress || !destinations.count(address)))
            continue;

        // Elements
        CAmount amount = out.tx->GetOutputValueOut(out.i);
        CAsset assetid = out.tx->GetOutputAsset(out.i);
        // Only list known outputs that match optional filter
        if (g_con_elementsmode && (amount < 0 || assetid.IsNull())) {
            wallet->WalletLogPrintf("Unable to unblind output: %s:%d\n", out.tx->tx->GetHash().GetHex(), out.i);
            continue;
        }
        if (!asset_str.empty() && asset_filter != assetid) {
            continue;
        }
        //////////

        UniValue entry(UniValue::VOBJ);
        entry.pushKV("txid", out.tx->GetHash().GetHex());
        entry.pushKV("vout", out.i);

        if (fValidAddress) {
            entry.pushKV("address", EncodeDestination(address));

            auto i = pwallet->mapAddressBook.find(address);
            if (i != pwallet->mapAddressBook.end()) {
                entry.pushKV("label", i->second.name);
            }

            const SigningProvider* provider = pwallet->GetSigningProvider(scriptPubKey);
            if (provider) {
                if (scriptPubKey.IsPayToScriptHash()) {
                    const CScriptID& hash = CScriptID(boost::get<ScriptHash>(address));
                    CScript redeemScript;
                    if (provider->GetCScript(hash, redeemScript)) {
                        entry.pushKV("redeemScript", HexStr(redeemScript.begin(), redeemScript.end()));
                        // Now check if the redeemScript is actually a P2WSH script
                        CTxDestination witness_destination;
                        if (redeemScript.IsPayToWitnessScriptHash()) {
                            bool extracted = ExtractDestination(redeemScript, witness_destination);
                            CHECK_NONFATAL(extracted);
                            // Also return the witness script
                            const WitnessV0ScriptHash& whash = boost::get<WitnessV0ScriptHash>(witness_destination);
                            CScriptID id;
                            CRIPEMD160().Write(whash.begin(), whash.size()).Finalize(id.begin());
                            CScript witnessScript;
                            if (provider->GetCScript(id, witnessScript)) {
                                entry.pushKV("witnessScript", HexStr(witnessScript.begin(), witnessScript.end()));
                            }
                        }
                    }
                } else if (scriptPubKey.IsPayToWitnessScriptHash()) {
                    const WitnessV0ScriptHash& whash = boost::get<WitnessV0ScriptHash>(address);
                    CScriptID id;
                    CRIPEMD160().Write(whash.begin(), whash.size()).Finalize(id.begin());
                    CScript witnessScript;
                    if (provider->GetCScript(id, witnessScript)) {
                        entry.pushKV("witnessScript", HexStr(witnessScript.begin(), witnessScript.end()));
                    }
                }
            }
        }

        entry.pushKV("scriptPubKey", HexStr(scriptPubKey.begin(), scriptPubKey.end()));
        entry.pushKV("amount", ValueFromAmount(amount));
        if (g_con_elementsmode) {
            if (tx_out.nAsset.IsCommitment()) {
                entry.pushKV("assetcommitment", HexStr(tx_out.nAsset.vchCommitment));
            }
            entry.pushKV("asset", assetid.GetHex());
            if (tx_out.nValue.IsCommitment()) {
                entry.pushKV("amountcommitment", HexStr(tx_out.nValue.vchCommitment));
            }
            entry.pushKV("amountblinder", out.tx->GetOutputAmountBlindingFactor(out.i).ToString());
            entry.pushKV("assetblinder", out.tx->GetOutputAssetBlindingFactor(out.i).ToString());
        }
        entry.pushKV("confirmations", out.nDepth);
        entry.pushKV("spendable", out.fSpendable);
        entry.pushKV("solvable", out.fSolvable);
        if (out.fSolvable) {
            const SigningProvider* provider = pwallet->GetSigningProvider(scriptPubKey);
            if (provider) {
                auto descriptor = InferDescriptor(scriptPubKey, *provider);
                entry.pushKV("desc", descriptor->ToString());
            }
        }
        if (avoid_reuse) entry.pushKV("reused", reused);
        entry.pushKV("safe", out.fSafe);
        results.push_back(entry);
    }

    return results;
}

void FundTransaction(CWallet* const pwallet, CMutableTransaction& tx, CAmount& fee_out, int& change_position, UniValue options, const UniValue& solving_data)
{
    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    CCoinControl coinControl;
    change_position = -1;
    bool lockUnspents = false;
    UniValue subtractFeeFromOutputs;
    std::set<int> setSubtractFeeFromOutputs;

    if (!options.isNull()) {
      if (options.type() == UniValue::VBOOL) {
        // backward compatibility bool only fallback
        coinControl.fAllowWatchOnly = options.get_bool();
      }
      else {
        RPCTypeCheckArgument(options, UniValue::VOBJ);

        RPCTypeCheckObj(options,
            {
                {"changeAddress", UniValueType()}, // will be checked below
                {"changePosition", UniValueType(UniValue::VNUM)},
                {"change_type", UniValueType(UniValue::VSTR)},
                {"includeWatching", UniValueType(UniValue::VBOOL)},
                {"lockUnspents", UniValueType(UniValue::VBOOL)},
                {"feeRate", UniValueType()}, // will be checked below
                {"subtractFeeFromOutputs", UniValueType(UniValue::VARR)},
                {"replaceable", UniValueType(UniValue::VBOOL)},
                {"conf_target", UniValueType(UniValue::VNUM)},
                {"estimate_mode", UniValueType(UniValue::VSTR)},
            },
            true, true);

        if (options.exists("changeAddress")) {
            std::map<CAsset, CTxDestination> destinations;

            if (options["changeAddress"].isStr()) {
                // Single destination for default asset (policyAsset).
                CTxDestination dest = DecodeDestination(options["changeAddress"].get_str());
                if (!IsValidDestination(dest)) {
                    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "changeAddress must be a valid address");
                }
                destinations[::policyAsset] = dest;
            } else if (options["changeAddress"].isObject()) {
                // Map of assets to destinations.
                std::map<std::string, UniValue> kvMap;
                options["changeAddress"].getObjMap(kvMap);

                for (const auto& kv : kvMap) {
                    CAsset asset = GetAssetFromString(kv.first);
                    if (asset.IsNull()) {
                        throw JSONRPCError(RPC_INVALID_PARAMETER, "changeAddress key must be a valid asset label or hex");
                    }

                    CTxDestination dest = DecodeDestination(kv.second.get_str());
                    if (!IsValidDestination(dest)) {
                        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "changeAddress must be a valid address");
                    }

                    destinations[asset] = dest;
                }
            } else {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "changeAddress must be either a map or a string");
            }

            coinControl.destChange = destinations;
        }

        if (options.exists("changePosition"))
            change_position = options["changePosition"].get_int();

        if (options.exists("change_type")) {
            if (options.exists("changeAddress")) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Cannot specify both changeAddress and address_type options");
            }
            coinControl.m_change_type = pwallet->m_default_change_type;
            if (!ParseOutputType(options["change_type"].get_str(), *coinControl.m_change_type)) {
                throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, strprintf("Unknown change type '%s'", options["change_type"].get_str()));
            }
        }

        coinControl.fAllowWatchOnly = ParseIncludeWatchonly(options["includeWatching"], *pwallet);

        if (options.exists("lockUnspents"))
            lockUnspents = options["lockUnspents"].get_bool();

        if (options.exists("feeRate"))
        {
            coinControl.m_feerate = CFeeRate(AmountFromValue(options["feeRate"]));
            coinControl.fOverrideFeeRate = true;
        }

        if (options.exists("subtractFeeFromOutputs"))
            subtractFeeFromOutputs = options["subtractFeeFromOutputs"].get_array();

        if (options.exists("replaceable")) {
            coinControl.m_signal_bip125_rbf = options["replaceable"].get_bool();
        }
        if (options.exists("conf_target")) {
            if (options.exists("feeRate")) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Cannot specify both conf_target and feeRate");
            }
            coinControl.m_confirm_target = ParseConfirmTarget(options["conf_target"], pwallet->chain().estimateMaxBlocks());
        }
        if (options.exists("estimate_mode")) {
            if (options.exists("feeRate")) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Cannot specify both estimate_mode and feeRate");
            }
            if (!FeeModeFromString(options["estimate_mode"].get_str(), coinControl.m_fee_mode)) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid estimate_mode parameter");
            }
        }
      }
    } else {
        // if options is null and not a bool
        coinControl.fAllowWatchOnly = ParseIncludeWatchonly(NullUniValue, *pwallet);
    }

    if (!solving_data.isNull()) {
        if (solving_data.exists("pubkeys")) {
            UniValue pubkey_strs = solving_data["pubkeys"].get_array();
            for (unsigned int i = 0; i < pubkey_strs.size(); ++i) {
                std::vector<unsigned char> data(ParseHex(pubkey_strs[i].get_str()));
                CPubKey pubkey(data.begin(), data.end());
                if (!pubkey.IsFullyValid()) {
                    throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, strprintf("%s is not a valid public key", pubkey_strs[i].get_str()));
                }
                coinControl.m_external_provider.pubkeys.emplace(pubkey.GetID(), pubkey);
                // Add witnes script for pubkeys
                CScript wit_script = GetScriptForDestination(WitnessV0KeyHash(pubkey.GetID()));
                coinControl.m_external_provider.scripts.emplace(CScriptID(wit_script), wit_script);
            }
        }

        if (solving_data.exists("scripts")) {
            UniValue script_strs = solving_data["scripts"].get_array();
            for (unsigned int i = 0; i < script_strs.size(); ++i) {
                CScript script = ParseScript(script_strs[i].get_str());
                coinControl.m_external_provider.scripts.emplace(CScriptID(script), script);
            }
        }

        if (solving_data.exists("descriptors")) {
            UniValue desc_strs = solving_data["descriptors"].get_array();
            for (unsigned int i = 0; i < desc_strs.size(); ++i) {
                FlatSigningProvider desc_out;
                std::string error;
                std::unique_ptr<Descriptor> desc = Parse(desc_strs[i].get_str(), desc_out, error, true);
                coinControl.m_external_provider = Merge(coinControl.m_external_provider, desc_out);
            }
        }
    }

    if (tx.vout.size() == 0)
        throw JSONRPCError(RPC_INVALID_PARAMETER, "TX must have at least one output");

    if (change_position != -1 && (change_position < 0 || (unsigned int)change_position > tx.vout.size()))
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

    // Check any existing inputs for peg-in data and add to external txouts if so
    // Fetch specified UTXOs from the UTXO set
    const auto& fedpegscripts = GetValidFedpegScripts(::ChainActive().Tip(), Params().GetConsensus(), true /* nextblock_validation */);
    std::map<COutPoint, Coin> coins;
    for (unsigned int i = 0; i < tx.vin.size(); ++i ) {
        const CTxIn& txin = tx.vin[i];
        coins[txin.prevout]; // Create empty map entry keyed by prevout.
        if (txin.m_is_pegin) {
            std::string err;
            if (tx.witness.vtxinwit.size() != tx.vin.size() || !IsValidPeginWitness(tx.witness.vtxinwit[i].m_pegin_witness, fedpegscripts, txin.prevout, err, false)) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Transaction contains invalid peg-in input: %s", err));
            }
            CScriptWitness& pegin_witness = tx.witness.vtxinwit[i].m_pegin_witness;
            CTxOut txout = GetPeginOutputFromWitness(pegin_witness);
            coinControl.SelectExternal(txin.prevout, txout);
        }
    }
    CCoinsView viewDummy;
    CCoinsViewCache view(&viewDummy);
    {
        LOCK2(cs_main, mempool.cs);
        CCoinsViewCache& chain_view = ::ChainstateActive().CoinsTip();
        CCoinsViewMemPool mempool_view(&chain_view, mempool);
        for (auto& coin : coins) {
            if (!mempool_view.GetCoin(coin.first, coin.second)) {
                // Either the coin is not in the CCoinsViewCache or is spent. Clear it.
                coin.second.Clear();
            }
        }
    }
    for (const auto& coin : coins) {
        if (!coin.second.out.IsNull()) {
            coinControl.SelectExternal(coin.first, coin.second.out);
        }
    }

    std::string strFailReason;

    if (!pwallet->FundTransaction(tx, fee_out, change_position, strFailReason, lockUnspents, setSubtractFeeFromOutputs, coinControl)) {
        throw JSONRPCError(RPC_WALLET_ERROR, strFailReason);
    }
}

static UniValue fundrawtransaction(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    RPCHelpMan{"fundrawtransaction",
                "\nAdd inputs to a transaction until it has enough in value to meet its out value.\n"
                "This will not modify existing inputs, and will add at most one change output to the outputs.\n"
                "No existing outputs will be modified unless \"subtractFeeFromOutputs\" is specified.\n"
                "Note that inputs which were signed may need to be resigned after completion since in/outputs have been added.\n"
                "The inputs added will not be signed, use signrawtransactionwithkey\n"
                " or signrawtransactionwithwallet for that.\n"
                "Note that all existing inputs must have their previous output transaction be in the wallet.\n"
                "Note that all inputs selected must be of standard form and P2SH scripts must be\n"
                "in the wallet using importaddress or addmultisigaddress (to calculate fees).\n"
                "You can see whether this is the case by checking the \"solvable\" field in the listunspent output.\n"
                "Only pay-to-pubkey, multisig, and P2SH versions thereof are currently supported for watch-only\n",
                {
                    {"hexstring", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The hex string of the raw transaction"},
                    {"options", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED_NAMED_ARG, "for backward compatibility: passing in a true instead of an object will result in {\"includeWatching\":true}",
                        {
                            {"changeAddress", RPCArg::Type::STR, /* default */ "pool address", "The address to receive the change"},
                            {"changePosition", RPCArg::Type::NUM, /* default */ "random", "The index of the change output"},
                            {"change_type", RPCArg::Type::STR, /* default */ "set by -changetype", "The output type to use. Only valid if changeAddress is not specified. Options are \"legacy\", \"p2sh-segwit\", and \"bech32\"."},
                            {"includeWatching", RPCArg::Type::BOOL, /* default */ "true for watch-only wallets, otherwise false", "Also select inputs which are watch only.\n"
                                                          "Only solvable inputs can be used. Watch-only destinations are solvable if the public key and/or output script was imported,\n"
                                                          "e.g. with 'importpubkey' or 'importmulti' with the 'pubkeys' or 'desc' field."},
                            {"lockUnspents", RPCArg::Type::BOOL, /* default */ "false", "Lock selected unspent outputs"},
                            {"feeRate", RPCArg::Type::AMOUNT, /* default */ "not set: makes wallet determine the fee", "Set a specific fee rate in " + CURRENCY_UNIT + "/kB"},
                            {"subtractFeeFromOutputs", RPCArg::Type::ARR, /* default */ "empty array", "A json array of integers.\n"
                            "                              The fee will be equally deducted from the amount of each specified output.\n"
                            "                              Those recipients will receive less bitcoins than you enter in their corresponding amount field.\n"
                            "                              If no outputs are specified here, the sender pays the fee.",
                                {
                                    {"vout_index", RPCArg::Type::NUM, RPCArg::Optional::OMITTED, "The zero-based output index, before a change output is added."},
                                },
                            },
                            {"replaceable", RPCArg::Type::BOOL, /* default */ "wallet default", "Marks this transaction as BIP125 replaceable.\n"
                            "                              Allows this transaction to be replaced by a transaction with higher fees"},
                            {"conf_target", RPCArg::Type::NUM, /* default */ "wallet default", "Confirmation target (in blocks)"},
                            {"estimate_mode", RPCArg::Type::STR, /* default */ "UNSET", "The fee estimate mode, must be one of:\n"
                            "         \"UNSET\"\n"
                            "         \"ECONOMICAL\"\n"
                            "         \"CONSERVATIVE\""},
                        },
                        "options"},
                    {"iswitness", RPCArg::Type::BOOL, /* default */ "depends on heuristic tests", "Whether the transaction hex is a serialized witness transaction.\n"
                        "If iswitness is not present, heuristic tests will be used in decoding.\n"
                        "If true, only witness deserialization will be tried.\n"
                        "If false, only non-witness deserialization will be tried.\n"
                        "This boolean should reflect whether the transaction has inputs\n"
                        "(e.g. fully valid, or on-chain transactions), if known by the caller."
                    },
                    {"solving_data", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED_NAMED_ARG, "Keys and scripts needed for producing a final transaction with a dummy signature. Used for fee estimation during coin selection.\n",
                        {
                            {"pubkeys", RPCArg::Type::ARR, /* default */ "empty array", "A json array of public keys.\n",
                                {
                                    {"pubkey", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "A public key"},
                                },
                            },
                            {"scripts", RPCArg::Type::ARR, /* default */ "empty array", "A json array of scripts.\n",
                                {
                                    {"script", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "A script"},
                                },
                            },
                            {"descriptors", RPCArg::Type::ARR, /* default */ "empty array", "A json array of descriptors.\n",
                                {
                                    {"descriptor", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "A descriptor"},
                                },
                            }
                        }
                    },
                },
                RPCResult{
                            "{\n"
                            "  \"hex\":       \"value\", (string)  The resulting raw transaction (hex-encoded string)\n"
                            "  \"fee\":       n,         (numeric) Fee in " + CURRENCY_UNIT + " the resulting transaction pays\n"
                            "  \"changepos\": n          (numeric) The position of the added change output, or -1\n"
                            "}\n"
                                },
                                RPCExamples{
                            "\nCreate a transaction with no inputs\n"
                            + HelpExampleCli("createrawtransaction", "\"[]\" \"{\\\"myaddress\\\":0.01}\"") +
                            "\nAdd sufficient unsigned inputs to meet the output value\n"
                            + HelpExampleCli("fundrawtransaction", "\"rawtransactionhex\"") +
                            "\nSign the transaction\n"
                            + HelpExampleCli("signrawtransactionwithwallet", "\"fundedtransactionhex\"") +
                            "\nSend the transaction\n"
                            + HelpExampleCli("sendrawtransaction", "\"signedtransactionhex\"")
                                },
    }.Check(request);

    RPCTypeCheck(request.params, {UniValue::VSTR, UniValueType(), UniValue::VBOOL});

    // parse hex string from parameter
    CMutableTransaction tx;
    bool try_witness = request.params[2].isNull() ? true : request.params[2].get_bool();
    bool try_no_witness = request.params[2].isNull() ? true : !request.params[2].get_bool();
    if (!DecodeHexTx(tx, request.params[0].get_str(), try_no_witness, try_witness)) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    }

    CAmount fee;
    int change_position;
    FundTransaction(pwallet, tx, fee, change_position, request.params[1], request.params[3]);

    UniValue result(UniValue::VOBJ);
    result.pushKV("hex", EncodeHexTx(CTransaction(tx)));
    result.pushKV("fee", ValueFromAmount(fee));
    result.pushKV("changepos", change_position);

    return result;
}

UniValue signrawtransactionwithwallet(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"signrawtransactionwithwallet",
                "\nSign inputs for raw transaction (serialized, hex-encoded).\n"
                "The second optional argument (may be null) is an array of previous transaction outputs that\n"
                "this transaction depends on but may not yet be in the block chain." +
                    HelpRequiringPassphrase(pwallet) + "\n",
                {
                    {"hexstring", RPCArg::Type::STR, RPCArg::Optional::NO, "The transaction hex string"},
                    {"prevtxs", RPCArg::Type::ARR, RPCArg::Optional::OMITTED_NAMED_ARG, "A json array of previous dependent transaction outputs",
                        {
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                                {
                                    {"txid", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The transaction id"},
                                    {"vout", RPCArg::Type::NUM, RPCArg::Optional::NO, "The output number"},
                                    {"scriptPubKey", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "script key"},
                                    {"redeemScript", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "(required for P2SH) redeem script"},
                                    {"witnessScript", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "(required for P2WSH or P2SH-P2WSH) witness script"},
                                    {"amount", RPCArg::Type::AMOUNT, RPCArg::Optional::OMITTED, "The amount spent (required if non-confidential segwit output)"},
                                    {"amountcommitment", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "The amount commitment spent (required if confidential segwit output)"},
                                },
                            },
                        },
                    },
                    {"sighashtype", RPCArg::Type::STR, /* default */ "ALL", "The signature hash type. Must be one of\n"
            "       \"ALL\"\n"
            "       \"NONE\"\n"
            "       \"SINGLE\"\n"
            "       \"ALL|ANYONECANPAY\"\n"
            "       \"NONE|ANYONECANPAY\"\n"
            "       \"SINGLE|ANYONECANPAY\""},
                },
                RPCResult{
            "{\n"
            "  \"hex\" : \"value\",                  (string) The hex-encoded raw transaction with signature(s)\n"
            "  \"complete\" : true|false,          (boolean) If the transaction has a complete set of signatures\n"
            "  \"errors\" : [                      (json array of objects) Script verification errors (if there are any)\n"
            "    {\n"
            "      \"txid\" : \"hash\",              (string) The hash of the referenced, previous transaction\n"
            "      \"vout\" : n,                   (numeric) The index of the output to spent and used as input\n"
            "      \"scriptSig\" : \"hex\",          (string) The hex-encoded signature script\n"
            "      \"sequence\" : n,               (numeric) Script sequence number\n"
            "      \"error\" : \"text\"              (string) Verification or signing error related to the input\n"
            "    }\n"
            "    ,...\n"
            "  ]\n"
            "  \"warning\" : \"text\"            (string) Warning that a peg-in input signed may be immature. This could mean lack of connectivity to or misconfiguration of the daemon."
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("signrawtransactionwithwallet", "\"myhex\"")
            + HelpExampleRpc("signrawtransactionwithwallet", "\"myhex\"")
                },
            }.Check(request);

    RPCTypeCheck(request.params, {UniValue::VSTR, UniValue::VARR, UniValue::VSTR}, true);

    CMutableTransaction mtx;
    if (!DecodeHexTx(mtx, request.params[0].get_str(), true)) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    }

    // Sign the transaction
    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);
    EnsureWalletIsUnlocked(pwallet);

    // Fetch previous transactions (inputs):
    const auto& fedpegscripts = GetValidFedpegScripts(::ChainActive().Tip(), Params().GetConsensus(), true /* nextblock_validation */);
    std::set<const SigningProvider*> providers;
    std::map<COutPoint, Coin> coins;
    for (unsigned int i = 0; i < mtx.vin.size(); ++i) {
        const CTxIn& txin = mtx.vin[i];
        coins[txin.prevout]; // Create empty map entry keyed by prevout.
        // ELEMENTS: for pegins we directly look up the provider by
        //  extracting the scriptPubKey from the pegin witness
        if (txin.m_is_pegin) {
            std::string err;
            if (mtx.witness.vtxinwit.size() == mtx.vin.size() && IsValidPeginWitness(mtx.witness.vtxinwit[i].m_pegin_witness, fedpegscripts, txin.prevout, err, false)) {
                CTxOut pegin_output = GetPeginOutputFromWitness(mtx.witness.vtxinwit[i].m_pegin_witness);
                const SigningProvider* provider = pwallet->GetSigningProvider(pegin_output.scriptPubKey);
                if (provider) {
                    providers.insert(std::move(provider));
                }
            }
        }
    }
    pwallet->chain().findCoins(coins);

    // Parse the prevtxs array
    ParsePrevouts(request.params[1], nullptr, coins);

    for (const std::pair<COutPoint, Coin> coin_pair : coins) {
        const SigningProvider* provider = pwallet->GetSigningProvider(coin_pair.second.out.scriptPubKey);
        if (provider) {
            providers.insert(std::move(provider));
        }
    }
    if (providers.size() == 0) {
        // When there are no available providers, use DUMMY_SIGNING_PROVIDER so we can check if the tx is complete
        providers.insert(&DUMMY_SIGNING_PROVIDER);
    }

    UniValue result(UniValue::VOBJ);
    for (const SigningProvider* provider : providers) {
        SignTransaction(mtx, provider, coins, request.params[2], result);
    }
     return result;
}

static UniValue bumpfee(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();


    if (!EnsureWalletIsAvailable(pwallet, request.fHelp))
        return NullUniValue;

            RPCHelpMan{"bumpfee",
                "\nBumps the fee of an opt-in-RBF transaction T, replacing it with a new transaction B.\n"
                "An opt-in RBF transaction with the given txid must be in the wallet.\n"
                "The command will pay the additional fee by reducing change outputs or adding inputs when necessary. It may add a new change output if one does not already exist.\n"
                "If `totalFee` (DEPRECATED) is given, adding inputs is not supported, so there must be a single change output that is big enough or it will fail.\n"
                "All inputs in the original transaction will be included in the replacement transaction.\n"
                "The command will fail if the wallet or mempool contains a transaction that spends one of T's outputs.\n"
                "By default, the new fee will be calculated automatically using estimatesmartfee.\n"
                "The user can specify a confirmation target for estimatesmartfee.\n"
                "Alternatively, the user can specify totalFee (DEPRECATED), or fee_rate (" + CURRENCY_UNIT + " per kB) for the new transaction .\n"
                "At a minimum, the new fee rate must be high enough to pay an additional new relay fee (incrementalfee\n"
                "returned by getnetworkinfo) to enter the node's mempool.\n",
                {
                    {"txid", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The txid to be bumped"},
                    {"options", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED_NAMED_ARG, "",
                        {
                            {"confTarget", RPCArg::Type::NUM, /* default */ "wallet default", "Confirmation target (in blocks)"},
                            {"totalFee", RPCArg::Type::NUM, /* default */ "fallback to 'confTarget'", "Total fee (NOT feerate) to pay, in satoshis. (DEPRECATED)\n"
            "                         In rare cases, the actual fee paid might be slightly higher than the specified\n"
            "                         totalFee if the tx change output has to be removed because it is too close to\n"
            "                         the dust threshold."},
                            {"fee_rate", RPCArg::Type::NUM, /* default */ "fallback to 'confTarget'", "FeeRate (NOT total fee) to pay, in " + CURRENCY_UNIT + " per kB\n"
            "                         Specify a fee rate instead of relying on the built-in fee estimator.\n"
            "                         Must be at least 0.0001 BTC per kB higher than the current transaction fee rate.\n"},
                            {"replaceable", RPCArg::Type::BOOL, /* default */ "true", "Whether the new transaction should still be\n"
            "                         marked bip-125 replaceable. If true, the sequence numbers in the transaction will\n"
            "                         be left unchanged from the original. If false, any input sequence numbers in the\n"
            "                         original transaction that were less than 0xfffffffe will be increased to 0xfffffffe\n"
            "                         so the new transaction will not be explicitly bip-125 replaceable (though it may\n"
            "                         still be replaceable in practice, for example if it has unconfirmed ancestors which\n"
            "                         are replaceable)."},
                            {"estimate_mode", RPCArg::Type::STR, /* default */ "UNSET", "The fee estimate mode, must be one of:\n"
            "         \"UNSET\"\n"
            "         \"ECONOMICAL\"\n"
            "         \"CONSERVATIVE\""},
                        },
                        "options"},
                },
                RPCResult{
            "{\n"
            "  \"psbt\":    \"psbt\",    (string) The base64-encoded unsigned PSBT of the new transaction. Only returned when wallet private keys are disabled.\n"
            "  \"txid\":    \"value\",   (string) The id of the new transaction. Only returned when wallet private keys are enabled.\n"
            "  \"origfee\":  n,        (numeric) The fee of the replaced transaction.\n"
            "  \"fee\":      n,        (numeric) The fee of the new transaction.\n"
            "  \"errors\":  [ str... ] (json array of strings) Errors encountered during processing (may be empty).\n"
            "}\n"
                },
                RPCExamples{
            "\nBump the fee, get the new transaction\'s txid\n" +
                    HelpExampleCli("bumpfee", "<txid>")
                },
            }.Check(request);

    RPCTypeCheck(request.params, {UniValue::VSTR, UniValue::VOBJ});
    uint256 hash(ParseHashV(request.params[0], "txid"));

    CCoinControl coin_control;
    coin_control.fAllowWatchOnly = pwallet->IsWalletFlagSet(WALLET_FLAG_DISABLE_PRIVATE_KEYS);
    // optional parameters
    CAmount totalFee = 0;
    coin_control.m_signal_bip125_rbf = true;

    if (!request.params[1].isNull()) {
        UniValue options = request.params[1];
        RPCTypeCheckObj(options,
            {
                {"confTarget", UniValueType(UniValue::VNUM)},
                {"totalFee", UniValueType(UniValue::VNUM)},
                {"fee_rate", UniValueType(UniValue::VNUM)},
                {"replaceable", UniValueType(UniValue::VBOOL)},
                {"estimate_mode", UniValueType(UniValue::VSTR)},
            },
            true, true);
        if (options.exists("confTarget") && (options.exists("totalFee") || options.exists("fee_rate"))) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "confTarget can't be set with totalFee or fee_rate. Please provide either a confirmation target in blocks for automatic fee estimation, or an explicit fee rate.");
        } else if (options.exists("fee_rate") && options.exists("totalFee")) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "fee_rate can't be set along with totalFee.");
        } else if (options.exists("confTarget")) { // TODO: alias this to conf_target
            coin_control.m_confirm_target = ParseConfirmTarget(options["confTarget"], pwallet->chain().estimateMaxBlocks());
        } else if (options.exists("totalFee")) {
            if (!pwallet->chain().rpcEnableDeprecated("totalFee")) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "totalFee argument has been deprecated and will be removed in 0.20. Please use -deprecatedrpc=totalFee to continue using this argument until removal.");
            }
            totalFee = options["totalFee"].get_int64();
            if (totalFee <= 0) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Invalid totalFee %s (must be greater than 0)", FormatMoney(totalFee)));
            }
        } else if (options.exists("fee_rate")) {
            CFeeRate fee_rate(AmountFromValue(options["fee_rate"]));
            if (fee_rate <= CFeeRate(0)) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Invalid fee_rate %s (must be greater than 0)", fee_rate.ToString()));
            }
            coin_control.m_feerate = fee_rate;
        }

        if (options.exists("replaceable")) {
            coin_control.m_signal_bip125_rbf = options["replaceable"].get_bool();
        }
        if (options.exists("estimate_mode")) {
            if (!FeeModeFromString(options["estimate_mode"].get_str(), coin_control.m_fee_mode)) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid estimate_mode parameter");
            }
        }
    }

    // Make sure the results are valid at least up to the most recent block
    // the user could have gotten from another RPC command prior to now
    pwallet->BlockUntilSyncedToCurrentChain();

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);
    EnsureWalletIsUnlocked(pwallet);


    std::vector<std::string> errors;
    CAmount old_fee;
    CAmount new_fee;
    CMutableTransaction mtx;
    feebumper::Result res;
    if (totalFee > 0) {
        // Targeting total fee bump. Requires a change output of sufficient size.
        res = feebumper::CreateTotalBumpTransaction(pwallet, hash, coin_control, totalFee, errors, old_fee, new_fee, mtx);
    } else {
        // Targeting feerate bump.
        res = feebumper::CreateRateBumpTransaction(*pwallet, hash, coin_control, errors, old_fee, new_fee, mtx);
    }
    if (res != feebumper::Result::OK) {
        switch(res) {
            case feebumper::Result::INVALID_ADDRESS_OR_KEY:
                throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, errors[0]);
                break;
            case feebumper::Result::INVALID_REQUEST:
                throw JSONRPCError(RPC_INVALID_REQUEST, errors[0]);
                break;
            case feebumper::Result::INVALID_PARAMETER:
                throw JSONRPCError(RPC_INVALID_PARAMETER, errors[0]);
                break;
            case feebumper::Result::WALLET_ERROR:
                throw JSONRPCError(RPC_WALLET_ERROR, errors[0]);
                break;
            default:
                throw JSONRPCError(RPC_MISC_ERROR, errors[0]);
                break;
        }
    }

    UniValue result(UniValue::VOBJ);

    // If wallet private keys are enabled, return the new transaction id,
    // otherwise return the base64-encoded unsigned PSBT of the new transaction.
    if (!pwallet->IsWalletFlagSet(WALLET_FLAG_DISABLE_PRIVATE_KEYS)) {
        if (!feebumper::SignTransaction(*pwallet, mtx)) {
            throw JSONRPCError(RPC_WALLET_ERROR, "Can't sign transaction.");
        }

        uint256 txid;
        if (feebumper::CommitTransaction(*pwallet, hash, std::move(mtx), errors, txid) != feebumper::Result::OK) {
            throw JSONRPCError(RPC_WALLET_ERROR, errors[0]);
        }

        result.pushKV("txid", txid.GetHex());
    } else {
        PartiallySignedTransaction psbtx(mtx);
        bool complete = false;
        const TransactionError err = FillPSBT(pwallet, psbtx, complete, SIGHASH_ALL, false /* sign */, true /* bip32derivs */);
        CHECK_NONFATAL(err == TransactionError::OK);
        CHECK_NONFATAL(!complete);
        CDataStream ssTx(SER_NETWORK, PROTOCOL_VERSION);
        ssTx << psbtx;
        result.pushKV("psbt", EncodeBase64(ssTx.str()));
    }

    result.pushKV("origfee", ValueFromAmount(old_fee));
    result.pushKV("fee", ValueFromAmount(new_fee));
    UniValue result_errors(UniValue::VARR);
    for (const std::string& error : errors) {
        result_errors.push_back(error);
    }
    result.pushKV("errors", result_errors);

    return result;
}

UniValue rescanblockchain(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"rescanblockchain",
                "\nRescan the local blockchain for wallet related transactions.\n"
                "Note: Use \"getwalletinfo\" to query the scanning progress.\n",
                {
                    {"start_height", RPCArg::Type::NUM, /* default */ "0", "block height where the rescan should start"},
                    {"stop_height", RPCArg::Type::NUM, RPCArg::Optional::OMITTED_NAMED_ARG, "the last block height that should be scanned. If none is provided it will rescan up to the tip at return time of this call."},
                },
                RPCResult{
            "{\n"
            "  \"start_height\"     (numeric) The block height where the rescan started (the requested height or 0)\n"
            "  \"stop_height\"      (numeric) The height of the last rescanned block. May be null in rare cases if there was a reorg and the call didn't scan any blocks because they were already scanned in the background.\n"
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("rescanblockchain", "100000 120000")
            + HelpExampleRpc("rescanblockchain", "100000, 120000")
                },
            }.Check(request);

    WalletRescanReserver reserver(pwallet);
    if (!reserver.reserve()) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Wallet is currently rescanning. Abort existing rescan or wait.");
    }

    int start_height = 0;
    uint256 start_block, stop_block;
    {
        auto locked_chain = pwallet->chain().lock();
        Optional<int> tip_height = locked_chain->getHeight();

        if (!request.params[0].isNull()) {
            start_height = request.params[0].get_int();
            if (start_height < 0 || !tip_height || start_height > *tip_height) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid start_height");
            }
        }

        Optional<int> stop_height;
        if (!request.params[1].isNull()) {
            stop_height = request.params[1].get_int();
            if (*stop_height < 0 || !tip_height || *stop_height > *tip_height) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid stop_height");
            }
            else if (*stop_height < start_height) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, "stop_height must be greater than start_height");
            }
        }

        // We can't rescan beyond non-pruned blocks, stop and throw an error
        if (locked_chain->findPruned(start_height, stop_height)) {
            throw JSONRPCError(RPC_MISC_ERROR, "Can't rescan beyond pruned data. Use RPC call getblockchaininfo to determine your pruned height.");
        }

        if (tip_height) {
            start_block = locked_chain->getBlockHash(start_height);
            // If called with a stop_height, set the stop_height here to
            // trigger a rescan to that height.
            // If called without a stop height, leave stop_height as null here
            // so rescan continues to the tip (even if the tip advances during
            // rescan).
            if (stop_height) {
                stop_block = locked_chain->getBlockHash(*stop_height);
            }
        }
    }

    CWallet::ScanResult result =
        pwallet->ScanForWalletTransactions(start_block, stop_block, reserver, true /* fUpdate */);
    switch (result.status) {
    case CWallet::ScanResult::SUCCESS:
        break;
    case CWallet::ScanResult::FAILURE:
        throw JSONRPCError(RPC_MISC_ERROR, "Rescan failed. Potentially corrupted data files.");
    case CWallet::ScanResult::USER_ABORT:
        throw JSONRPCError(RPC_MISC_ERROR, "Rescan aborted.");
        // no default case, so the compiler can warn about missing cases
    }
    UniValue response(UniValue::VOBJ);
    response.pushKV("start_height", start_height);
    response.pushKV("stop_height", result.last_scanned_height ? *result.last_scanned_height : UniValue());
    return response;
}

class DescribeWalletAddressVisitor : public boost::static_visitor<UniValue>
{
public:
    const SigningProvider * const provider;

    void ProcessSubScript(const CScript& subscript, UniValue& obj) const
    {
        // Always present: script type and redeemscript
        std::vector<std::vector<unsigned char>> solutions_data;
        txnouttype which_type = Solver(subscript, solutions_data);
        obj.pushKV("script", GetTxnOutputType(which_type));
        obj.pushKV("hex", HexStr(subscript.begin(), subscript.end()));

        CTxDestination embedded;
        if (ExtractDestination(subscript, embedded)) {
            // Only when the script corresponds to an address.
            UniValue subobj(UniValue::VOBJ);
            UniValue detail = DescribeAddress(embedded);
            subobj.pushKVs(detail);
            UniValue wallet_detail = boost::apply_visitor(*this, embedded);
            subobj.pushKVs(wallet_detail);
            subobj.pushKV("address", EncodeDestination(embedded));
            subobj.pushKV("scriptPubKey", HexStr(subscript.begin(), subscript.end()));
            // Always report the pubkey at the top level, so that `getnewaddress()['pubkey']` always works.
            if (subobj.exists("pubkey")) obj.pushKV("pubkey", subobj["pubkey"]);
            obj.pushKV("embedded", std::move(subobj));
        } else if (which_type == TX_MULTISIG) {
            // Also report some information on multisig scripts (which do not have a corresponding address).
            // TODO: abstract out the common functionality between this logic and ExtractDestinations.
            obj.pushKV("sigsrequired", solutions_data[0][0]);
            UniValue pubkeys(UniValue::VARR);
            for (size_t i = 1; i < solutions_data.size() - 1; ++i) {
                CPubKey key(solutions_data[i].begin(), solutions_data[i].end());
                pubkeys.push_back(HexStr(key.begin(), key.end()));
            }
            obj.pushKV("pubkeys", std::move(pubkeys));
        }
    }

    explicit DescribeWalletAddressVisitor(const SigningProvider* _provider) : provider(_provider) {}

    UniValue operator()(const CNoDestination& dest) const { return UniValue(UniValue::VOBJ); }

    UniValue operator()(const PKHash& pkhash) const
    {
        CKeyID keyID(pkhash);
        UniValue obj(UniValue::VOBJ);
        CPubKey vchPubKey;
        if (provider && provider->GetPubKey(keyID, vchPubKey)) {
            obj.pushKV("pubkey", HexStr(vchPubKey));
            obj.pushKV("iscompressed", vchPubKey.IsCompressed());
        }
        return obj;
    }

    UniValue operator()(const ScriptHash& scripthash) const
    {
        CScriptID scriptID(scripthash);
        UniValue obj(UniValue::VOBJ);
        CScript subscript;
        if (provider && provider->GetCScript(scriptID, subscript)) {
            ProcessSubScript(subscript, obj);
        }
        return obj;
    }

    UniValue operator()(const WitnessV0KeyHash& id) const
    {
        UniValue obj(UniValue::VOBJ);
        CPubKey pubkey;
        if (provider && provider->GetPubKey(CKeyID(id), pubkey)) {
            obj.pushKV("pubkey", HexStr(pubkey));
        }
        return obj;
    }

    UniValue operator()(const WitnessV0ScriptHash& id) const
    {
        UniValue obj(UniValue::VOBJ);
        CScript subscript;
        CRIPEMD160 hasher;
        uint160 hash;
        hasher.Write(id.begin(), 32).Finalize(hash.begin());
        if (provider && provider->GetCScript(CScriptID(hash), subscript)) {
            ProcessSubScript(subscript, obj);
        }
        return obj;
    }

    UniValue operator()(const WitnessUnknown& id) const { return UniValue(UniValue::VOBJ); }
    UniValue operator()(const NullData& id) const { return NullUniValue; }
};

static UniValue DescribeWalletAddress(CWallet* pwallet, const CTxDestination& dest)
{
    UniValue ret(UniValue::VOBJ);
    UniValue detail = DescribeAddress(dest);
    CScript script = GetScriptForDestination(dest);
    const SigningProvider* provider = nullptr;
    if (pwallet) {
        provider = pwallet->GetSigningProvider(script);
    }
    ret.pushKVs(detail);
    ret.pushKVs(boost::apply_visitor(DescribeWalletAddressVisitor(provider), dest));
    return ret;
}

class DescribeWalletBlindAddressVisitor : public boost::static_visitor<UniValue>
{
public:
    CWallet * const pwallet;
    isminetype mine;

    explicit DescribeWalletBlindAddressVisitor(CWallet* _pwallet, isminetype mine_in) : pwallet(_pwallet), mine(mine_in) {}

    UniValue operator()(const CNoDestination& dest) const { return UniValue(UniValue::VOBJ); }

    UniValue operator()(const PKHash& pkhash) const
    {
        UniValue obj(UniValue::VOBJ);
        if (!IsBlindDestination(pkhash) && mine != ISMINE_NO) {
            CPubKey blind_pub = pwallet->GetBlindingPubKey(GetScriptForDestination(pkhash));
            PKHash dest(pkhash);
            dest.blinding_pubkey = blind_pub;
            obj.pushKV("confidential", EncodeDestination(dest));
        } else {
            obj.pushKV("confidential", EncodeDestination(pkhash));
        }
        return obj;
    }

    UniValue operator()(const ScriptHash& scripthash) const
    {
        UniValue obj(UniValue::VOBJ);
        if (!IsBlindDestination(scripthash) && mine != ISMINE_NO) {
            CPubKey blind_pub = pwallet->GetBlindingPubKey(GetScriptForDestination(scripthash));
            ScriptHash dest(scripthash);
            dest.blinding_pubkey = blind_pub;
            obj.pushKV("confidential", EncodeDestination(dest));
        } else {
            obj.pushKV("confidential", EncodeDestination(scripthash));
        }
        return obj;
    }

    UniValue operator()(const WitnessV0KeyHash& id) const
    {
        UniValue obj(UniValue::VOBJ);
        if (!IsBlindDestination(id) && mine != ISMINE_NO) {
            CPubKey blind_pub = pwallet->GetBlindingPubKey(GetScriptForDestination(id));
            WitnessV0KeyHash dest(id);
            dest.blinding_pubkey = blind_pub;
            obj.pushKV("confidential", EncodeDestination(dest));
        } else {
            obj.pushKV("confidential", EncodeDestination(id));
        }
        return obj;
    }

    UniValue operator()(const WitnessV0ScriptHash& id) const
    {
        UniValue obj(UniValue::VOBJ);
        if (!IsBlindDestination(id) && mine != ISMINE_NO) {
            CPubKey blind_pub = pwallet->GetBlindingPubKey(GetScriptForDestination(id));
            WitnessV0ScriptHash dest(id);
            dest.blinding_pubkey = blind_pub;
            obj.pushKV("confidential", EncodeDestination(dest));
        } else {
            obj.pushKV("confidential", EncodeDestination(id));
        }
        return obj;
    }

    UniValue operator()(const WitnessUnknown& id) const { return UniValue(UniValue::VOBJ); }
    UniValue operator()(const NullData& id) const { return NullUniValue; }
};

static UniValue DescribeWalletBlindAddress(CWallet* pwallet, const CTxDestination& dest, isminetype mine)
{
    UniValue ret(UniValue::VOBJ);
    ret.pushKVs(boost::apply_visitor(DescribeWalletBlindAddressVisitor(pwallet, mine), dest));
    return ret;
}

/** Convert CAddressBookData to JSON record.  */
static UniValue AddressBookDataToJSON(const CAddressBookData& data, const bool verbose)
{
    UniValue ret(UniValue::VOBJ);
    if (verbose) {
        ret.pushKV("name", data.name);
    }
    ret.pushKV("purpose", data.purpose);
    return ret;
}

UniValue getaddressinfo(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    const std::string example_address = "\"bc1q09vm5lfy0j5reeulh4x5752q25uqqvz34hufdl\"";

            RPCHelpMan{"getaddressinfo",
                "\nReturn information about the given address.\n"
                "Some of the information will only be present if the address is in the active wallet.\n",
                {
                    {"address", RPCArg::Type::STR, RPCArg::Optional::NO, "The address for which to get information."},
                },
                RPCResult{
            "{\n"
            "  \"address\" : \"address\",              (string) The address validated.\n"
            "  \"scriptPubKey\" : \"hex\",             (string) The hex-encoded scriptPubKey generated by the address.\n"
            "  \"ismine\" : true|false,              (boolean) If the address is yours.\n"
            "  \"iswatchonly\" : true|false,         (boolean) If the address is watchonly.\n"
            "  \"solvable\" : true|false,            (boolean) If we know how to spend coins sent to this address, ignoring the possible lack of private keys.\n"
            "  \"desc\" : \"desc\",                    (string, optional) A descriptor for spending coins sent to this address (only when solvable).\n"
            "  \"isscript\" : true|false,            (boolean) If the key is a script.\n"
            "  \"ischange\" : true|false,            (boolean) If the address was used for change output.\n"
            "  \"iswitness\" : true|false,           (boolean) If the address is a witness address.\n"
            "  \"witness_version\" : version         (numeric, optional) The version number of the witness program.\n"
            "  \"witness_program\" : \"hex\"           (string, optional) The hex value of the witness program.\n"
            "  \"script\" : \"type\"                   (string, optional) The output script type. Only if isscript is true and the redeemscript is known. Possible\n"
            "                                                         types: nonstandard, pubkey, pubkeyhash, scripthash, multisig, nulldata, witness_v0_keyhash,\n"
            "                                                         witness_v0_scripthash, witness_unknown.\n"
            "  \"hex\" : \"hex\",                      (string, optional) The redeemscript for the p2sh address.\n"
            "  \"pubkeys\"                           (array, optional) Array of pubkeys associated with the known redeemscript (only if script is multisig).\n"
            "    [\n"
            "      \"pubkey\" (string)\n"
            "      ,...\n"
            "    ]\n"
            "  \"sigsrequired\" : xxxxx              (numeric, optional) The number of signatures required to spend multisig output (only if script is multisig).\n"
            "  \"pubkey\" : \"publickeyhex\",          (string, optional) The hex value of the raw public key for single-key addresses (possibly embedded in P2SH or P2WSH).\n"
            "  \"embedded\" : {...},                 (object, optional) Information about the address embedded in P2SH or P2WSH, if relevant and known. Includes all\n"
            "                                                         getaddressinfo output fields for the embedded address, excluding metadata (timestamp, hdkeypath,\n"
            "                                                         hdseedid) and relation to the wallet (ismine, iswatchonly).\n"
            "  \"iscompressed\" : true|false,        (boolean, optional) If the pubkey is compressed.\n"
            "  \"confidential_key\" : \"hex\",         (string) The hex value of the raw blinding public key for that address, if any. \"\" if none.\n"
            "  \"unconfidential\" : \"address\",       (string) The address without confidentiality key.\n"
            "  \"confidential\" : \"address\",         (string) The address with wallet-stored confidentiality key if known. Only displayed for non-confidential address inputs.\n"
            "  \"label\" :  \"label\"                  (string) The label associated with the address. Defaults to \"\". Equivalent to the label name in the labels array below.\n"
            "  \"timestamp\" : timestamp,            (number, optional) The creation time of the key, if available, expressed in " + UNIX_EPOCH_TIME + ".\n"
            "  \"hdkeypath\" : \"keypath\"             (string, optional) The HD keypath, if the key is HD and available.\n"
            "  \"hdseedid\" : \"<hash160>\"            (string, optional) The Hash160 of the HD seed.\n"
            "  \"hdmasterfingerprint\" : \"<hash160>\" (string, optional) The fingerprint of the master key.\n"
            "  \"labels\"                            (json object) An array of labels associated with the address. Currently limited to one label but returned\n"
            "                                               as an array to keep the API stable if multiple labels are enabled in the future.\n"
            "    [\n"
            "      \"label name\" (string) The label name. Defaults to \"\". Equivalent to the label field above.\n\n"
            "      DEPRECATED, will be removed in 0.21. To re-enable, launch bitcoind with `-deprecatedrpc=labelspurpose`:\n"
            "      { (json object of label data)\n"
            "        \"name\" : \"label name\" (string) The label name. Defaults to \"\". Equivalent to the label field above.\n"
            "        \"purpose\" : \"purpose\" (string) The purpose of the associated address (send or receive).\n"
            "      }\n"
            "    ]\n"
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("getaddressinfo", example_address) +
                    HelpExampleRpc("getaddressinfo", example_address)
                },
            }.Check(request);

    LOCK(pwallet->cs_wallet);

    UniValue ret(UniValue::VOBJ);
    CTxDestination dest = DecodeDestination(request.params[0].get_str());
    // Make sure the destination is valid
    if (!IsValidDestination(dest)) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid address");
    }

    std::string currentAddress = EncodeDestination(dest);
    ret.pushKV("address", currentAddress);

    CScript scriptPubKey = GetScriptForDestination(dest);
    ret.pushKV("scriptPubKey", HexStr(scriptPubKey.begin(), scriptPubKey.end()));

    const SigningProvider* provider = pwallet->GetSigningProvider(scriptPubKey);

    isminetype mine = pwallet->IsMine(dest);
    // Elements: Addresses we can not unblind outputs for aren't spendable
    if (IsBlindDestination(dest) &&
            GetDestinationBlindingKey(dest) != pwallet->GetBlindingPubKey(GetScriptForDestination(dest))) {
        mine = ISMINE_NO;
    }
    ret.pushKV("ismine", bool(mine & ISMINE_SPENDABLE));

    bool solvable = provider && IsSolvable(*provider, scriptPubKey);
    ret.pushKV("solvable", solvable);

    if (solvable) {
       ret.pushKV("desc", InferDescriptor(scriptPubKey, *provider)->ToString());
    }

    ret.pushKV("iswatchonly", bool(mine & ISMINE_WATCH_ONLY));

    UniValue detail = DescribeWalletAddress(pwallet, dest);
    ret.pushKVs(detail);
    // Elements blinding info
    UniValue blind_detail = DescribeWalletBlindAddress(pwallet, dest, mine);
    ret.pushKVs(blind_detail);
    blind_detail = DescribeBlindAddress(dest);
    ret.pushKVs(blind_detail);

    // Return label field if existing. Currently only one label can be
    // associated with an address, so the label should be equivalent to the
    // value of the name key/value pair in the labels array below.
    if (pwallet->mapAddressBook.count(dest)) {
        ret.pushKV("label", pwallet->mapAddressBook[dest].name);
    }

    ret.pushKV("ischange", pwallet->IsChange(scriptPubKey));

    ScriptPubKeyMan* spk_man = pwallet->GetScriptPubKeyMan(scriptPubKey);
    if (spk_man) {
        if (const CKeyMetadata* meta = spk_man->GetMetadata(dest)) {
            ret.pushKV("timestamp", meta->nCreateTime);
            if (meta->has_key_origin) {
                ret.pushKV("hdkeypath", WriteHDKeypath(meta->key_origin.path));
                ret.pushKV("hdseedid", meta->hd_seed_id.GetHex());
                ret.pushKV("hdmasterfingerprint", HexStr(meta->key_origin.fingerprint, meta->key_origin.fingerprint + 4));
            }
        }
    }

    // Return a `labels` array containing the label associated with the address,
    // equivalent to the `label` field above. Currently only one label can be
    // associated with an address, but we return an array so the API remains
    // stable if we allow multiple labels to be associated with an address in
    // the future.
    //
    // DEPRECATED: The previous behavior of returning an array containing a JSON
    // object of `name` and `purpose` key/value pairs has been deprecated.
    UniValue labels(UniValue::VARR);
    std::map<CTxDestination, CAddressBookData>::iterator mi = pwallet->mapAddressBook.find(dest);
    if (mi != pwallet->mapAddressBook.end()) {
        if (pwallet->chain().rpcEnableDeprecated("labelspurpose")) {
            labels.push_back(AddressBookDataToJSON(mi->second, true));
        } else {
            labels.push_back(mi->second.name);
        }
    }
    ret.pushKV("labels", std::move(labels));

    return ret;
}

static UniValue getaddressesbylabel(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"getaddressesbylabel",
                "\nReturns the list of addresses assigned the specified label.\n",
                {
                    {"label", RPCArg::Type::STR, RPCArg::Optional::NO, "The label."},
                },
                RPCResult{
            "{ (json object with addresses as keys)\n"
            "  \"address\": { (json object with information about address)\n"
            "    \"purpose\": \"string\" (string)  Purpose of address (\"send\" for sending address, \"receive\" for receiving address)\n"
            "  },...\n"
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("getaddressesbylabel", "\"tabby\"")
            + HelpExampleRpc("getaddressesbylabel", "\"tabby\"")
                },
            }.Check(request);

    LOCK(pwallet->cs_wallet);

    std::string label = LabelFromValue(request.params[0]);

    // Find all addresses that have the given label
    UniValue ret(UniValue::VOBJ);
    std::set<std::string> addresses;
    for (const std::pair<const CTxDestination, CAddressBookData>& item : pwallet->mapAddressBook) {
        if (item.second.name == label) {
            std::string address = EncodeDestination(item.first);
            // CWallet::mapAddressBook is not expected to contain duplicate
            // address strings, but build a separate set as a precaution just in
            // case it does.
            bool unique = addresses.emplace(address).second;
            CHECK_NONFATAL(unique);
            // UniValue::pushKV checks if the key exists in O(N)
            // and since duplicate addresses are unexpected (checked with
            // std::set in O(log(N))), UniValue::__pushKV is used instead,
            // which currently is O(1).
            ret.__pushKV(address, AddressBookDataToJSON(item.second, false));
        }
    }

    if (ret.empty()) {
        throw JSONRPCError(RPC_WALLET_INVALID_LABEL_NAME, std::string("No addresses with label " + label));
    }

    return ret;
}

static UniValue listlabels(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"listlabels",
                "\nReturns the list of all labels, or labels that are assigned to addresses with a specific purpose.\n",
                {
                    {"purpose", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "Address purpose to list labels for ('send','receive'). An empty string is the same as not providing this argument."},
                },
                RPCResult{
            "[               (json array of string)\n"
            "  \"label\",      (string) Label name\n"
            "  ...\n"
            "]\n"
                },
                RPCExamples{
            "\nList all labels\n"
            + HelpExampleCli("listlabels", "") +
            "\nList labels that have receiving addresses\n"
            + HelpExampleCli("listlabels", "receive") +
            "\nList labels that have sending addresses\n"
            + HelpExampleCli("listlabels", "send") +
            "\nAs a JSON-RPC call\n"
            + HelpExampleRpc("listlabels", "receive")
                },
            }.Check(request);

    LOCK(pwallet->cs_wallet);

    std::string purpose;
    if (!request.params[0].isNull()) {
        purpose = request.params[0].get_str();
    }

    // Add to a set to sort by label name, then insert into Univalue array
    std::set<std::string> label_set;
    for (const std::pair<const CTxDestination, CAddressBookData>& entry : pwallet->mapAddressBook) {
        if (purpose.empty() || entry.second.purpose == purpose) {
            label_set.insert(entry.second.name);
        }
    }

    UniValue ret(UniValue::VARR);
    for (const std::string& name : label_set) {
        ret.push_back(name);
    }

    return ret;
}

UniValue sethdseed(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"sethdseed",
                "\nSet or generate a new HD wallet seed. Non-HD wallets will not be upgraded to being a HD wallet. Wallets that are already\n"
                "HD will have a new HD seed set so that new keys added to the keypool will be derived from this new seed.\n"
                "\nNote that you will need to MAKE A NEW BACKUP of your wallet after setting the HD wallet seed." +
                    HelpRequiringPassphrase(pwallet) + "\n",
                {
                    {"newkeypool", RPCArg::Type::BOOL, /* default */ "true", "Whether to flush old unused addresses, including change addresses, from the keypool and regenerate it.\n"
            "                             If true, the next address from getnewaddress and change address from getrawchangeaddress will be from this new seed.\n"
            "                             If false, addresses (including change addresses if the wallet already had HD Chain Split enabled) from the existing\n"
            "                             keypool will be used until it has been depleted."},
                    {"seed", RPCArg::Type::STR, /* default */ "random seed", "The WIF private key to use as the new HD seed.\n"
            "                             The seed value can be retrieved using the dumpwallet command. It is the private key marked hdseed=1"},
                },
                RPCResults{},
                RPCExamples{
                    HelpExampleCli("sethdseed", "")
            + HelpExampleCli("sethdseed", "false")
            + HelpExampleCli("sethdseed", "true \"wifkey\"")
            + HelpExampleRpc("sethdseed", "true, \"wifkey\"")
                },
            }.Check(request);

    LegacyScriptPubKeyMan& spk_man = EnsureLegacyScriptPubKeyMan(*pwallet);

    if (pwallet->chain().isInitialBlockDownload()) {
        throw JSONRPCError(RPC_CLIENT_IN_INITIAL_DOWNLOAD, "Cannot set a new HD seed while still in Initial Block Download");
    }

    if (pwallet->IsWalletFlagSet(WALLET_FLAG_DISABLE_PRIVATE_KEYS)) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Cannot set a HD seed to a wallet with private keys disabled");
    }

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    // Do not do anything to non-HD wallets
    if (!pwallet->CanSupportFeature(FEATURE_HD)) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Cannot set a HD seed on a non-HD wallet. Start with -upgradewallet in order to upgrade a non-HD wallet to HD");
    }

    EnsureWalletIsUnlocked(pwallet);

    bool flush_key_pool = true;
    if (!request.params[0].isNull()) {
        flush_key_pool = request.params[0].get_bool();
    }

    CPubKey master_pub_key;
    if (request.params[1].isNull()) {
        master_pub_key = spk_man.GenerateNewSeed();
    } else {
        CKey key = DecodeSecret(request.params[1].get_str());
        if (!key.IsValid()) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid private key");
        }

        if (HaveKey(spk_man, key)) {
            throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Already have this key (either as an HD seed or as a loose private key)");
        }

        master_pub_key = spk_man.DeriveNewSeed(key);
    }

    spk_man.SetHDSeed(master_pub_key);
    if (flush_key_pool) spk_man.NewKeyPool();

    return NullUniValue;
}

UniValue walletfillpsbtdata(const JSONRPCRequest& request)
{
    if (!g_con_elementsmode)
        throw std::runtime_error("PSBT operations are disabled when not in elementsmode.\n");

    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    if (request.fHelp || request.params.size() < 1 || request.params.size() > 4)
        throw std::runtime_error(
            RPCHelpMan{"walletfillpsbtdata",
                "\nUpdate a PSBT with input information from our wallet\n"
                + HelpRequiringPassphrase(pwallet) + "\n",
                {
                    {"psbt", RPCArg::Type::STR, RPCArg::Optional::NO, "The transaction base64 string"},
                    {"bip32derivs", RPCArg::Type::BOOL, /* default */ "false", "If true, includes the BIP 32 derivation paths for public keys if we know them"},
                },
                RPCResult{
                    "{\n"
                    "  \"psbt\" : \"value\",        (string) The base64-encoded partially signed transaction\n"
                    "}\n"
                },
                RPCExamples{
                    HelpExampleCli("walletfillpsbtdata", "\"psbt\"")
                    + HelpExampleRpc("walletfillpsbtdata", "\"psbt\"")
                }
            }.ToString()
        );

    RPCTypeCheck(request.params, {UniValue::VSTR, UniValue::VBOOL});

    // Unserialize the transaction
    PartiallySignedTransaction psbtx;
    std::string error;
    if (!DecodeBase64PSBT(psbtx, request.params[0].get_str(), error)) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, strprintf("TX decode failed %s", error));
    }

    bool bip32derivs = request.params[1].isNull() ? false : request.params[1].get_bool();
    const TransactionError err = FillPSBTData(pwallet, psbtx, bip32derivs);
    if (err != TransactionError::OK) {
        throw JSONRPCTransactionError(err);
    }

    UniValue result(UniValue::VOBJ);
    result.pushKV("psbt", EncodePSBT(psbtx));
    return result;
}

UniValue walletsignpsbt(const JSONRPCRequest& request)
{
    if (!g_con_elementsmode)
        throw std::runtime_error("PSBT operations are disabled when not in elementsmode.\n");

    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    if (request.fHelp || request.params.size() < 1 || request.params.size() > 4)
        throw std::runtime_error(
            RPCHelpMan{"walletsignpsbt",
                "\nSign all PSBT iputs that we can sign for.\n"
                + HelpRequiringPassphrase(pwallet) + "\n",
                {
                    {"psbt", RPCArg::Type::STR, RPCArg::Optional::NO, "The transaction base64 string"},
                    {"sighashtype", RPCArg::Type::STR, /* default */ "ALL", "The signature hash type to sign with if not specified by the PSBT. Must be one of\n"
                        "       \"ALL\"\n"
                        "       \"NONE\"\n"
                        "       \"SINGLE\"\n"
                        "       \"ALL|ANYONECANPAY\"\n"
                        "       \"NONE|ANYONECANPAY\"\n"
                        "       \"SINGLE|ANYONECANPAY\""},
                    {"imbalance_ok", RPCArg::Type::BOOL, /* default */ "false", "Sign even if the transaction amounts do not balance"},
                },
                RPCResult{
                    "{\n"
                    "  \"psbt\" : \"value\",          (string) The base64-encoded partially signed transaction\n"
                    "  \"complete\" : true|false,   (boolean) If the transaction has a complete set of signatures\n"
                    "}\n"
                },
                RPCExamples{
                    HelpExampleCli("walletsignpsbt", "\"psbt\"")
                    + HelpExampleRpc("walletsignpsbt", "\"psbt\"")
                }
            }.ToString()
        );

    RPCTypeCheck(request.params, {UniValue::VSTR, UniValue::VSTR, UniValue::VBOOL});

    // Unserialize the transaction
    PartiallySignedTransaction psbtx;
    std::string error;
    if (!DecodeBase64PSBT(psbtx, request.params[0].get_str(), error)) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, strprintf("TX decode failed %s", error));
    }

    // Get the sighash type
    int nHashType = ParseSighashString(request.params[1]);
    bool imbalance_ok = request.params[2].isNull() ? false : request.params[2].get_bool();

    bool complete;
    const TransactionError err = SignPSBT(pwallet, psbtx, complete, nHashType, true, imbalance_ok);
    if (err != TransactionError::OK) {
        throw JSONRPCTransactionError(err);
    }

    UniValue result(UniValue::VOBJ);
    result.pushKV("psbt", EncodePSBT(psbtx));
    result.pushKV("complete", complete);

    return result;
}

UniValue walletprocesspsbt(const JSONRPCRequest& request)
{
    if (!g_con_elementsmode)
        throw std::runtime_error("PSBT operations are disabled when not in elementsmode.\n");

    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"walletprocesspsbt",
                "\nUpdate a PSBT with input information from our wallet and then sign inputs\n"
                "that we can sign for.\n\n"
                "NOTE: When working with Confidential Assets transactions, it is necessary to\n"
                "blind the transaction after filling it in from the wallet and before signing\n"
                "it. This RPC will fail when working with such transaction. Instead of using\n"
                "this RPC, use the following sequence:\n"
                " - walletfillpsbtdata\n"
                " - blindpsbt\n"
                " - walletsignpsbt\n" +
                    HelpRequiringPassphrase(pwallet) + "\n",
                {
                    {"psbt", RPCArg::Type::STR, RPCArg::Optional::NO, "The transaction base64 string"},
                    {"sign", RPCArg::Type::BOOL, /* default */ "true", "Also sign the transaction when updating"},
                    {"sighashtype", RPCArg::Type::STR, /* default */ "ALL", "The signature hash type to sign with if not specified by the PSBT. Must be one of\n"
            "       \"ALL\"\n"
            "       \"NONE\"\n"
            "       \"SINGLE\"\n"
            "       \"ALL|ANYONECANPAY\"\n"
            "       \"NONE|ANYONECANPAY\"\n"
            "       \"SINGLE|ANYONECANPAY\""},
                    {"bip32derivs", RPCArg::Type::BOOL, /* default */ "false", "If true, includes the BIP 32 derivation paths for public keys if we know them"},
                },
                RPCResult{
            "{\n"
            "  \"psbt\" : \"value\",          (string) The base64-encoded partially signed transaction\n"
            "  \"complete\" : true|false,   (boolean) If the transaction has a complete set of signatures\n"
            "  ]\n"
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("walletprocesspsbt", "\"psbt\"")
                },
            }.Check(request);

    RPCTypeCheck(request.params, {UniValue::VSTR, UniValue::VBOOL, UniValue::VSTR});

    // Unserialize the transaction
    PartiallySignedTransaction psbtx;
    std::string error;
    if (!DecodeBase64PSBT(psbtx, request.params[0].get_str(), error)) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, strprintf("TX decode failed %s", error));
    }

    // Get the sighash type
    int nHashType = ParseSighashString(request.params[2]);

    // Fill transaction with our data and also sign
    bool sign = request.params[1].isNull() ? true : request.params[1].get_bool();
    bool bip32derivs = request.params[3].isNull() ? false : request.params[3].get_bool();
    bool complete = true;
    const TransactionError err = FillPSBT(pwallet, psbtx, complete, nHashType, sign, bip32derivs);
    if (err != TransactionError::OK) {
        throw JSONRPCTransactionError(err);
    }

    UniValue result(UniValue::VOBJ);
    CDataStream ssTx(SER_NETWORK, PROTOCOL_VERSION);
    ssTx << psbtx;
    result.pushKV("psbt", EncodeBase64(ssTx.str()));
    result.pushKV("complete", complete);

    return result;
}

UniValue walletcreatefundedpsbt(const JSONRPCRequest& request)
{
    if (!g_con_elementsmode)
        throw std::runtime_error("PSBT operations are disabled when not in elementsmode.\n");

    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

            RPCHelpMan{"walletcreatefundedpsbt",
                "\nCreates and funds a transaction in the Partially Signed Transaction format. Inputs will be added if supplied inputs are not enough\n"
                "Implements the Creator and Updater roles.\n",
                {
                    {"inputs", RPCArg::Type::ARR, RPCArg::Optional::NO, "A json array of json objects",
                        {
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                                {
                                    {"txid", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The transaction id"},
                                    {"vout", RPCArg::Type::NUM, RPCArg::Optional::NO, "The output number"},
                                    {"sequence", RPCArg::Type::NUM, RPCArg::Optional::NO, "The sequence number"},
                                    {"pegin_bitcoin_tx", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The raw bitcoin transaction (in hex) depositing bitcoin to the mainchain_address generated by getpeginaddress"},
                                    {"pegin_txout_proof", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "A rawtxoutproof (in hex) generated by the mainchain daemon's `gettxoutproof` containing a proof of only bitcoin_tx"},
                                    {"pegin_claim_script", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The witness program generated by getpeginaddress."},
                                },
                            },
                        },
                        },
                    {"outputs", RPCArg::Type::ARR, RPCArg::Optional::NO, "a json array with outputs (key-value pairs), where none of the keys are duplicated.\n"
                            "That is, each address can only appear once and there can only be one 'data' object.\n"
                            "For compatibility reasons, a dictionary, which holds the key-value pairs directly, is also\n"
                            "                             accepted as second parameter.",
                        {
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                                {
                                    {"address", RPCArg::Type::AMOUNT, RPCArg::Optional::NO, "A key-value pair. The key (string) is the address, the value (float or string) is the amount in " + CURRENCY_UNIT + ""},
                                },
                                },
                            {"", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED, "",
                                {
                                    {"data", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "A key-value pair. The key must be \"data\", the value is hex-encoded data"},
                                },
                            },
                        },
                    },
                    {"locktime", RPCArg::Type::NUM, /* default */ "0", "Raw locktime. Non-0 value also locktime-activates inputs"},
                    {"options", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED_NAMED_ARG, "",
                        {
                            {"changeAddress", RPCArg::Type::STR_HEX, /* default */ "pool address", "The address to receive the change"},
                            {"changePosition", RPCArg::Type::NUM, /* default */ "random", "The index of the change output"},
                            {"change_type", RPCArg::Type::STR, /* default */ "set by -changetype", "The output type to use. Only valid if changeAddress is not specified. Options are \"legacy\", \"p2sh-segwit\", and \"bech32\"."},
                            {"includeWatching", RPCArg::Type::BOOL, /* default */ "true for watch-only wallets, otherwise false", "Also select inputs which are watch only"},
                            {"lockUnspents", RPCArg::Type::BOOL, /* default */ "false", "Lock selected unspent outputs"},
                            {"feeRate", RPCArg::Type::AMOUNT, /* default */ "not set: makes wallet determine the fee", "Set a specific fee rate in " + CURRENCY_UNIT + "/kB"},
                            {"subtractFeeFromOutputs", RPCArg::Type::ARR, /* default */ "empty array", "A json array of integers.\n"
                            "                              The fee will be equally deducted from the amount of each specified output.\n"
                            "                              Those recipients will receive less bitcoins than you enter in their corresponding amount field.\n"
                            "                              If no outputs are specified here, the sender pays the fee.",
                                {
                                    {"vout_index", RPCArg::Type::NUM, RPCArg::Optional::OMITTED, "The zero-based output index, before a change output is added."},
                                },
                            },
                            {"replaceable", RPCArg::Type::BOOL, /* default */ "wallet default", "Marks this transaction as BIP125 replaceable.\n"
                            "                              Allows this transaction to be replaced by a transaction with higher fees"},
                            {"conf_target", RPCArg::Type::NUM, /* default */ "Fallback to wallet's confirmation target", "Confirmation target (in blocks)"},
                            {"estimate_mode", RPCArg::Type::STR, /* default */ "UNSET", "The fee estimate mode, must be one of:\n"
                            "         \"UNSET\"\n"
                            "         \"ECONOMICAL\"\n"
                            "         \"CONSERVATIVE\""},
                        },
                        "options"},
                    {"bip32derivs", RPCArg::Type::BOOL, /* default */ "false", "If true, includes the BIP 32 derivation paths for public keys if we know them"},
                    {"solving_data", RPCArg::Type::OBJ, RPCArg::Optional::OMITTED_NAMED_ARG, "Keys and scripts needed for producing a final transaction with a dummy signature. Used for fee estimation during coin selection.\n",
                        {
                            {"pubkeys", RPCArg::Type::ARR, /* default */ "empty array", "A json array of public keys.\n",
                                {
                                    {"pubkey", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "A public key"},
                                },
                            },
                            {"scripts", RPCArg::Type::ARR, /* default */ "empty array", "A json array of scripts.\n",
                                {
                                    {"script", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "A script"},
                                },
                            },
                            {"descriptors", RPCArg::Type::ARR, /* default */ "empty array", "A json array of descriptors.\n",
                                {
                                    {"descriptor", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "A descriptor"},
                                },
                            }
                        }
                    },
                },
                RPCResult{
                            "{\n"
                            "  \"psbt\": \"value\",        (string)  The resulting raw transaction (base64-encoded string)\n"
                            "  \"fee\":       n,         (numeric) Fee in " + CURRENCY_UNIT + " the resulting transaction pays\n"
                            "  \"changepos\": n          (numeric) The position of the added change output, or -1\n"
                            "}\n"
                                },
                                RPCExamples{
                            "\nCreate a transaction with no inputs\n"
                            + HelpExampleCli("walletcreatefundedpsbt", "\"[{\\\"txid\\\":\\\"myid\\\",\\\"vout\\\":0}]\" \"[{\\\"data\\\":\\\"00010203\\\"}]\"")
                                },
                            }.Check(request);

    RPCTypeCheck(request.params, {
        UniValue::VARR,
        UniValueType(), // ARR or OBJ, checked later
        UniValue::VNUM,
        UniValue::VOBJ,
        UniValue::VBOOL
        }, true
    );

    CAmount fee;
    int change_position;
    bool rbf = pwallet->m_signal_rbf;
    const UniValue &replaceable_arg = request.params[3]["replaceable"];
    if (!replaceable_arg.isNull()) {
        RPCTypeCheckArgument(replaceable_arg, UniValue::VBOOL);
        rbf = replaceable_arg.isTrue();
    }
    // It's hard to control the behavior of FundTransaction, so we will wait
    //   until after it's done, then extract the blinding keys from the output
    //   nonces.
    CMutableTransaction rawTx = ConstructTransaction(request.params[0], request.params[1], request.params[2], rbf, NullUniValue /* CA: assets_in */, nullptr /* output_pubkeys_out */, true /* allow_peg_in */);
    FundTransaction(pwallet, rawTx, fee, change_position, request.params[3], request.params[5]);

    // Make a blank psbt
    PartiallySignedTransaction psbtx(rawTx);
    for (unsigned int i = 0; i < rawTx.vout.size(); ++i) {
        if (!psbtx.tx->vout[i].nNonce.IsNull()) {
            // Extract blinding key and clear the nonce
            psbtx.outputs[i].blinding_pubkey = CPubKey(psbtx.tx->vout[i].nNonce.vchCommitment);
            psbtx.tx->vout[i].nNonce.SetNull();
        }
    }

    // Fill transaction with out data but don't sign
    bool bip32derivs = request.params[4].isNull() ? false : request.params[4].get_bool();
    bool complete = true;
    const TransactionError err = FillPSBT(pwallet, psbtx, complete, 1, false, bip32derivs);
    if (err != TransactionError::OK) {
        throw JSONRPCTransactionError(err);
    }

    // Add peg-in stuff if it's there
    for (unsigned int i = 0; i < rawTx.vin.size(); ++i) {
        if (psbtx.tx->vin[i].m_is_pegin) {
            CScriptWitness& pegin_witness = psbtx.tx->witness.vtxinwit[i].m_pegin_witness;
            CAmount val;
            VectorReader vr_val(SER_NETWORK, PROTOCOL_VERSION, pegin_witness.stack[0], 0);
            vr_val >> val;
            psbtx.inputs[i].value = val;
            VectorReader vr_asset(SER_NETWORK, PROTOCOL_VERSION, pegin_witness.stack[1], 0);
            vr_asset >> psbtx.inputs[i].asset;
            VectorReader vr_genesis(SER_NETWORK, PROTOCOL_VERSION, pegin_witness.stack[2], 0);
            vr_genesis >> psbtx.inputs[i].genesis_hash;
            psbtx.inputs[i].claim_script.assign(pegin_witness.stack[3].begin(), pegin_witness.stack[3].end());

            VectorReader vr_tx(SER_NETWORK, PROTOCOL_VERSION, pegin_witness.stack[4], 0);
            VectorReader vr_proof(SER_NETWORK, PROTOCOL_VERSION, pegin_witness.stack[5], 0);
            if (Params().GetConsensus().ParentChainHasPow()) {
                Sidechain::Bitcoin::CTransactionRef tx_btc;
                vr_tx >> tx_btc;
                psbtx.inputs[i].peg_in_tx = tx_btc;
                Sidechain::Bitcoin::CMerkleBlock tx_proof;
                vr_proof >> tx_proof;
                psbtx.inputs[i].txout_proof = tx_proof;
            } else {
                CTransactionRef tx_btc;
                vr_tx >> tx_btc;
                psbtx.inputs[i].peg_in_tx = tx_btc;
                CMerkleBlock tx_proof;
                vr_proof >> tx_proof;
                psbtx.inputs[i].txout_proof = tx_proof;
            }
            pegin_witness.SetNull();
            psbtx.tx->vin[i].m_is_pegin = false;
        }
    }

    // Serialize the PSBT
    CDataStream ssTx(SER_NETWORK, PROTOCOL_VERSION);
    ssTx << psbtx;

    UniValue result(UniValue::VOBJ);
    result.pushKV("psbt", EncodeBase64(ssTx.str()));
    result.pushKV("fee", ValueFromAmount(fee));
    result.pushKV("changepos", change_position);
    return result;
}

//
// ELEMENTS commands

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

UniValue signblock(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 1 || request.params.size() > 2)
        throw std::runtime_error(
            RPCHelpMan{"signblock",
                "\nSigns a block proposal, checking that it would be accepted first. Errors if it cannot sign the block. Note that this call adds the witnessScript to your wallet for signing purposes! This function is intended for QA and testing.\n",
                {
                    {"blockhex", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The hex-encoded block from getnewblockhex"},
                    {"witnessScript", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The hex-encoded witness script. Required for dynamic federation blocks. Argument is \"\" when the block is P2WPKH."},
                },
                RPCResult{
            "[\n"
            "    {\n"
            "        pubkeys,   (hex) The signature's pubkey\n"
            "        sig      (hex) The signature script\n"
            "    },\n"
            "    ...\n"
            "]\n"
                },
                RPCExamples{
                    HelpExampleCli("signblock", "0000002018c6f2f913f9902aeab...5ca501f77be96de63f609010000000000000000015100000000")
                },
            }.ToString());

    if (!g_signed_blocks) {
        throw JSONRPCError(RPC_MISC_ERROR, "Signed blocks are not active for this network.");
    }

    CBlock block;
    if (!DecodeHexBlk(block, request.params[0].get_str()))
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Block decode failed");

    LOCK(cs_main);

    LegacyScriptPubKeyMan* spk_man = pwallet->GetLegacyScriptPubKeyMan();
    if (!spk_man) {
        throw JSONRPCError(RPC_WALLET_ERROR, "This type of wallet does not support this command");
    }

    uint256 hash = block.GetHash();
    BlockMap::iterator mi = ::BlockIndex().find(hash);
    if (mi != ::BlockIndex().end())
        throw JSONRPCError(RPC_VERIFY_ERROR, "already have block");

    CBlockIndex* const pindexPrev = ::ChainActive().Tip();
    // TestBlockValidity only supports blocks built on the current Tip
    if (block.hashPrevBlock != pindexPrev->GetBlockHash())
        throw JSONRPCError(RPC_VERIFY_ERROR, "proposal was not based on our best chain");

    BlockValidationState state;
    if (!TestBlockValidity(state, Params(), block, pindexPrev, false, true) || !state.IsValid()) {
        std::string strRejectReason = state.GetRejectReason();
        if (strRejectReason.empty())
            throw JSONRPCError(RPC_VERIFY_ERROR, state.IsInvalid() ? "Block proposal was invalid" : "Error checking block proposal");
        throw JSONRPCError(RPC_VERIFY_ERROR, strRejectReason);
    }

    // Expose SignatureData internals in return value in lieu of "Partially Signed Bitcoin Blocks"
    SignatureData block_sigs;
    if (block.m_dynafed_params.IsNull()) {
        GenericSignScript(*spk_man, block.GetBlockHeader(), block.proof.challenge, block_sigs, SCRIPT_NO_SIGHASH_BYTE /* additional_flags */);
    } else {
        if (request.params[1].isNull()) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Signing dynamic blocks requires the witnessScript argument");
        }
        std::vector<unsigned char> witness_bytes(ParseHex(request.params[1].get_str()));
        // Note that we're adding the signblockscript to the wallet so it can actually
        // satisfy witness program scriptpubkeys
        if (!witness_bytes.empty()) {
            spk_man->AddCScript(CScript(witness_bytes.begin(), witness_bytes.end()));
        }
        GenericSignScript(*spk_man, block.GetBlockHeader(), block.m_dynafed_params.m_current.m_signblockscript, block_sigs, SCRIPT_VERIFY_NONE /* additional_flags */);
    }

    // Error if sig data didn't "grow"
    if (!block_sigs.complete && block_sigs.signatures.empty()) {
        throw JSONRPCError(RPC_VERIFY_ERROR, "Could not sign the block.");
    }
    UniValue ret(UniValue::VARR);
    for (const auto& signature : block_sigs.signatures) {
        UniValue obj(UniValue::VOBJ);
        obj.pushKV("pubkey", HexStr(signature.second.first.begin(), signature.second.first.end()));
        obj.pushKV("sig", HexStr(signature.second.second.begin(), signature.second.second.end()));
        ret.push_back(obj);
    }
    return ret;
}

UniValue getpeginaddress(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() != 0)
        throw std::runtime_error(
            RPCHelpMan{"getpeginaddress",
                "\nReturns information needed for claimpegin to move coins to the sidechain.\n"
                "The user should send coins from their Bitcoin wallet to the mainchain_address returned.\n"
                "IMPORTANT: Like getaddress, getpeginaddress adds new secrets to wallet.dat, necessitating backup on a regular basis.\n",
                {},
                RPCResult{
            "\"mainchain_address\"           (string) Mainchain Bitcoin deposit address to send bitcoin to\n"
            "\"claim_script\"             (string) The claim script in hex that was committed to. This may be required in `claimpegin` to retrieve pegged-in funds\n"
                },
                RPCExamples{
                    HelpExampleCli("getpeginaddress", "")
            + HelpExampleRpc("getpeginaddress", "")
                },
            }.ToString());

    LegacyScriptPubKeyMan* spk_man = pwallet->GetLegacyScriptPubKeyMan();
    if (!spk_man) {
        throw JSONRPCError(RPC_WALLET_ERROR, "This type of wallet does not support this command");
    }

    if (!pwallet->IsLocked()) {
        pwallet->TopUpKeyPool();
    }

    // Use native witness destination
    CTxDestination dest;
    std::string error;
    if (!pwallet->GetNewDestination(OutputType::BECH32, "", dest, error)) {
        throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, error);
    }

    CScript dest_script = GetScriptForDestination(dest);

    // Also add raw scripts to index to recognize later.
    spk_man->AddCScript(dest_script);

    // Get P2CH deposit address on mainchain from most recent fedpegscript.
    const auto& fedpegscripts = GetValidFedpegScripts(::ChainActive().Tip(), Params().GetConsensus(), true /* nextblock_validation */);
    CTxDestination mainchain_dest(WitnessV0ScriptHash(calculate_contract(fedpegscripts.front().second, dest_script)));
    // P2SH-wrapped is the only valid choice for non-dynafed chains but still an
    // option for dynafed-enabled ones as well
    if (!IsDynaFedEnabled(::ChainActive().Tip(), Params().GetConsensus()) ||
                fedpegscripts.front().first.IsPayToScriptHash()) {
        mainchain_dest = ScriptHash(GetScriptForDestination(mainchain_dest));
    }

    UniValue ret(UniValue::VOBJ);

    ret.pushKV("mainchain_address", EncodeParentDestination(mainchain_dest));
    ret.pushKV("claim_script", HexStr(dest_script));
    return ret;
}

//! Derive BIP32 tweak from master xpub to child pubkey.
bool DerivePubTweak(const std::vector<uint32_t>& vPath, const CPubKey& keyMaster, const ChainCode &ccMaster, std::vector<unsigned char>& tweakSum)
{
    tweakSum.clear();
    tweakSum.resize(32);
    std::vector<unsigned char> tweak;
    CPubKey keyParent = keyMaster;
    CPubKey keyChild;
    ChainCode ccChild;
    ChainCode ccParent = ccMaster;
    for (unsigned int i = 0; i < vPath.size(); i++) {
        if ((vPath[i] >> 31) != 0) {
            return false;
        }
        keyParent.Derive(keyChild, ccChild, vPath[i], ccParent, &tweak);
        assert(tweak.size() == 32);
        ccParent = ccChild;
        keyParent = keyChild;
        if (i == 0) {
            tweakSum = tweak;
        } else {
            bool ret = secp256k1_ec_privkey_tweak_add(secp256k1_ctx, tweakSum.data(), tweak.data());
            if (!ret) {
                return false;
            }
        }
    }
    return true;
}

// For general cryptographic design of peg-out authorization scheme, see: https://github.com/ElementsProject/secp256k1-zkp/blob/secp256k1-zkp/src/modules/whitelist/whitelist.md
UniValue initpegoutwallet(const JSONRPCRequest& request)
{

    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 1 || request.params.size() > 3)
        throw std::runtime_error(
            RPCHelpMan{"initpegoutwallet",
                "\nThis call is for Liquid network initialization on the Liquid wallet. The wallet generates a new Liquid pegout authorization key (PAK) and stores it in the Liquid wallet. It then combines this with the `bitcoin_descriptor` to finally create a PAK entry for the network. This allows the user to send Liquid coins directly to a secure offline Bitcoin wallet at the derived path from the bitcoin_descriptor using the `sendtomainchain` command. Losing the Liquid PAK or offline Bitcoin root key will result in the inability to pegout funds, so immediate backup upon initialization is required.\n" +
                HelpRequiringPassphrase(pwallet),
                {
                    {"bitcoin_descriptor", RPCArg::Type::STR, RPCArg::Optional::NO, "The Bitcoin descriptor that includes a single extended pubkey. Must be one of the following: pkh(<xpub>), sh(wpkh(<xpub>)), or wpkh(<xpub>). This is used as the destination chain for the Bitcoin destination wallet. The derivation path from the xpub is given by the descriptor, typically `0/k`, reflecting the external chain of the wallet. DEPRECATED: If a plain xpub is given, pkh(<xpub>) is assumed, with the `0/k` derivation from that xpub. See link for more details on script descriptors: https://github.com/bitcoin/bitcoin/blob/master/doc/descriptors.md"},
                    {"bip32_counter", RPCArg::Type::NUM , /* default */ "0", "The `k` in `0/k` to be set as the next address to derive from the `bitcoin_descriptor`. This will be stored in the wallet and incremented on each successful `sendtomainchain` invocation."},
                    {"liquid_pak", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED_NAMED_ARG, "The Liquid wallet pubkey in hex to be used as the Liquid PAK for pegout authorization. The private key must be in the wallet if argument is given. If this argument is not provided one will be generated and stored in the wallet automatically and returned."}
                },
                RPCResult{
            "{\n"
                "\"pakentry\"       (string) The resulting PAK entry to be used at network initialization time in the form of: `pak=<bitcoin_pak>:<liquid_pak>`.\n"
                "\"liquid_pak\"     (string) The Liquid PAK pubkey in hex, which is stored in the local Liquid wallet. This can be used in subsequent calls to `initpegoutwallet` to avoid generating a new `liquid_pak`.\n"
                "\"liquid_pak_address\" (string) The corresponding address for `liquid_pak`. Useful for `dumpprivkey` for wallet backup or transfer.\n"
                "\"address_lookahead\"(array)  The three next Bitcoin addresses the wallet will use for `sendtomainchain` based on `bip32_counter`.\n"
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("initpegoutwallet", "sh(wpkh(tpubDAY5hwtonH4NE8zY46ZMFf6B6F3fqMis7cwfNihXXpAg6XzBZNoHAdAzAZx2peoU8nTWFqvUncXwJ9qgE5VxcnUKxdut8F6mptVmKjfiwDQ/0/*))")
            + HelpExampleRpc("initpegoutwallet", "sh(wpkh(tpubDAY5hwtonH4NE8zY46ZMFf6B6F3fqMis7cwfNihXXpAg6XzBZNoHAdAzAZx2peoU8nTWFqvUncXwJ9qgE5VxcnUKxdut8F6mptVmKjfiwDQ/0/*))")
                },
            }.ToString());

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    LegacyScriptPubKeyMan* spk_man = pwallet->GetLegacyScriptPubKeyMan();
    if (!spk_man) {
        throw JSONRPCError(RPC_WALLET_ERROR, "This type of wallet does not support this command");
    }

    // Check that network cares about PAK
    if (!Params().GetEnforcePak()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "PAK enforcement is not enabled on this network.");
    }

    if (!pwallet->IsLocked())
        pwallet->TopUpKeyPool();

    // Generate a new key that is added to wallet or set from argument
    CPubKey online_pubkey;
    if (request.params.size() < 3) {
        std::string error;
        if (!pwallet->GetOnlinePakKey(online_pubkey, error)) {
            throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, error);
        }
    } else {
        online_pubkey = CPubKey(ParseHex(request.params[2].get_str()));
        if (!online_pubkey.IsFullyValid()) {
            throw JSONRPCError(RPC_WALLET_ERROR, "Error: Given liquid_pak is not valid.");
        }
        if (!spk_man->HaveKey(online_pubkey.GetID())) {
            throw JSONRPCError(RPC_WALLET_ERROR, "Error: liquid_pak could not be found in wallet");
        }
    }

    // Parse offline counter
    int counter = 0;
    if (request.params.size() > 1) {
        counter = request.params[1].get_int();
        if (counter < 0 || counter > 1000000000) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "bip32_counter must be between 0 and 1,000,000,000, inclusive.");
        }
    }

    std::string bitcoin_desc = request.params[0].get_str();
    std::string xpub_str = "";

    // First check for naked xpub, and impute it as pkh(<xpub>/0/*) for backwards compat
    CExtPubKey xpub = DecodeExtPubKey(bitcoin_desc);
    if (xpub.pubkey.IsFullyValid()) {
        bitcoin_desc = "pkh(" + bitcoin_desc + "/0/*)";
    }

    FlatSigningProvider provider;
    std::string error;
    auto desc = Parse(bitcoin_desc, provider, error); // don't require checksum
    if (!desc) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, error);
    } else if (!desc->IsRange()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "bitcoin_descriptor must be a ranged descriptor.");
    }

    // For our manual pattern matching, we don't want the checksum part.
    auto checksum_char = bitcoin_desc.find('#');
    if (checksum_char != std::string::npos) {
        bitcoin_desc = bitcoin_desc.substr(0, checksum_char);
    }

    // Three acceptable descriptors:
    bool is_liquid = Params().NetworkIDString() == "liquidv1";
    if (bitcoin_desc.substr(0, 8) ==  "sh(wpkh("
            && bitcoin_desc.substr(bitcoin_desc.size()-2, 2) == "))") {
        if(is_liquid) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "bitcoin_descriptor is not supported by Liquid; try pkh(<xpub>) or <xpub>.");
        }
        xpub_str = bitcoin_desc.substr(8, bitcoin_desc.size()-2);
    } else if (bitcoin_desc.substr(0, 5) ==  "wpkh("
            && bitcoin_desc.substr(bitcoin_desc.size()-1, 1) == ")") {
        if(is_liquid) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "bitcoin_descriptor is not supported by Liquid; try pkh(<xpub>) or <xpub>.");
        }
        xpub_str = bitcoin_desc.substr(5, bitcoin_desc.size()-1);
    } else if (bitcoin_desc.substr(0, 4) == "pkh("
            && bitcoin_desc.substr(bitcoin_desc.size()-1, 1) == ")") {
        xpub_str = bitcoin_desc.substr(4, bitcoin_desc.size()-1);
    } else {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "bitcoin_descriptor is not of any type supported: pkh(<xpub>), sh(wpkh(<xpub>)), wpkh(<xpub>), or <xpub>.");
    }

    // Strip off leading key origin
    if (xpub_str.find("]") != std::string::npos) {
        xpub_str = xpub_str.substr(xpub_str.find("]")+1, std::string::npos);
    }

    // Strip off following range
    xpub_str = xpub_str.substr(0, xpub_str.find("/"));

    xpub = DecodeExtPubKey(xpub_str);

    if (!xpub.pubkey.IsFullyValid()) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, "bitcoin_descriptor does not contain a valid extended pubkey for this network.");
    }

    // Parse master pubkey
    CPubKey masterpub = xpub.pubkey;
    secp256k1_pubkey masterpub_secp;
    int ret = secp256k1_ec_pubkey_parse(secp256k1_ctx, &masterpub_secp, masterpub.begin(), masterpub.size());
    if (ret != 1) {
        throw JSONRPCError(RPC_WALLET_ERROR, "bitcoin_descriptor could not be parsed.");
    }

    // Store the keys and metadata
    if (!pwallet->SetOnlinePubKey(online_pubkey) ||
            !pwallet->SetOfflineXPubKey(xpub) ||
            !pwallet->SetOfflineCounter(counter) ||
            !pwallet->SetOfflineDescriptor(bitcoin_desc)) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Error: Failure to initialize pegout wallet.");
    }

    // Negate the pubkey
    ret = secp256k1_ec_pubkey_negate(secp256k1_ctx, &masterpub_secp);

    std::vector<unsigned char> negatedpubkeybytes;
    negatedpubkeybytes.resize(33);
    size_t len = 33;
    ret = secp256k1_ec_pubkey_serialize(secp256k1_ctx, &negatedpubkeybytes[0], &len, &masterpub_secp, SECP256K1_EC_COMPRESSED);
    assert(ret == 1);
    assert(len == 33);
    assert(negatedpubkeybytes.size() == 33);

    UniValue address_list(UniValue::VARR);
    for (int i = counter; i < counter+3; i++) {
        std::vector<CScript> scripts;
        if (!desc->Expand(i, provider, scripts, provider)) {
            throw JSONRPCError(RPC_WALLET_ERROR, "Could not generate lookahead addresses with descriptor. This is a bug.");
        }
        CTxDestination destination;
        ExtractDestination(scripts[0], destination);
        address_list.push_back(EncodeParentDestination(destination));
    }
    UniValue pak(UniValue::VOBJ);
    pak.pushKV("pakentry", "pak=" + HexStr(negatedpubkeybytes) + ":" + HexStr(online_pubkey));
    pak.pushKV("liquid_pak", HexStr(online_pubkey));
    pak.pushKV("liquid_pak_address", EncodeDestination(PKHash(online_pubkey)));
    pak.pushKV("address_lookahead", address_list);
    return pak;
}

UniValue sendtomainchain_base(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 2 || request.params.size() > 3)
        throw std::runtime_error(
            RPCHelpMan{"sendtomainchain",
                "\nSends sidechain funds to the given mainchain address, through the federated pegin mechanism\n"
                + HelpRequiringPassphrase(pwallet),
                {
                    {"address", RPCArg::Type::STR, RPCArg::Optional::NO, "The destination address on Bitcoin mainchain"},
                    {"amount", RPCArg::Type::AMOUNT, RPCArg::Optional::NO, "The amount being sent to Bitcoin mainchain"},
                    {"subtractfeefromamount", RPCArg::Type::BOOL, /* default */ "false", "The fee will be deducted from the amount being pegged-out."},
                },
                RPCResult{
            "\"txid\"              (string) Transaction ID of the resulting sidechain transaction\n"
                },
                RPCExamples{
                    HelpExampleCli("sendtomainchain", "\"mgWEy4vBJSHt3mC8C2SEWJQitifb4qeZQq\" 0.1")
            + HelpExampleRpc("sendtomainchain", "\"mgWEy4vBJSHt3mC8C2SEWJQitifb4qeZQq\" 0.1")
                },
            }.ToString());

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    EnsureWalletIsUnlocked(pwallet);

    CTxDestination parent_address = DecodeParentDestination(request.params[0].get_str());
    if (!IsValidDestination(parent_address))
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid Bitcoin address");

    CAmount nAmount = AmountFromValue(request.params[1]);
    if (nAmount <= 0)
        throw JSONRPCError(RPC_TYPE_ERROR, "Invalid amount for send");

    bool subtract_fee = false;
    if (request.params.size() > 2) {
        subtract_fee = request.params[2].get_bool();
    }

    // Parse Bitcoin address for destination, embed script
    CScript mainchain_script(GetScriptForDestination(parent_address));

    uint256 genesisBlockHash = Params().ParentGenesisBlockHash();

    // Asset type is implicit, no need to add to script
    NullData nulldata;
    nulldata << std::vector<unsigned char>(genesisBlockHash.begin(), genesisBlockHash.end());
    nulldata << std::vector<unsigned char>(mainchain_script.begin(), mainchain_script.end());
    CTxDestination address(nulldata);

    EnsureWalletIsUnlocked(pwallet);

    mapValue_t mapValue;
    CCoinControl no_coin_control; // This is a deprecated API
    CTransactionRef tx = SendMoney(*locked_chain, pwallet, address, nAmount, Params().GetConsensus().pegged_asset, subtract_fee, no_coin_control, std::move(mapValue), true /* ignore_blind_fail */);

    return (*tx).GetHash().GetHex();

}

// ELEMENTS: Copied from script/descriptor.cpp

typedef std::vector<uint32_t> KeyPath;

/** Split a string on every instance of sep, returning a vector. */
std::vector<Span<const char>> Split(const Span<const char>& sp, char sep)
{
    std::vector<Span<const char>> ret;
    auto it = sp.begin();
    auto start = it;
    while (it != sp.end()) {
        if (*it == sep) {
            ret.emplace_back(start, it);
            start = it + 1;
        }
        ++it;
    }
    ret.emplace_back(start, it);
    return ret;
}

/** Parse a key path, being passed a split list of elements (the first element is ignored). */
bool ParseKeyPath(const std::vector<Span<const char>>& split, KeyPath& out)
{
    for (size_t i = 1; i < split.size(); ++i) {
        Span<const char> elem = split[i];
        bool hardened = false;
        if (elem.size() > 0 && (elem[elem.size() - 1] == '\'' || elem[elem.size() - 1] == 'h')) {
            elem = elem.first(elem.size() - 1);
            hardened = true;
        }
        uint32_t p;
        if (!ParseUInt32(std::string(elem.begin(), elem.end()), &p) || p > 0x7FFFFFFFUL) return false;
        out.push_back(p | (((uint32_t)hardened) << 31));
    }
    return true;
}

////////////////////////////

UniValue sendtomainchain_pak(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp))
        return NullUniValue;

    if (request.fHelp || request.params.size() < 2 || request.params.size() > 3)
        throw std::runtime_error(
            RPCHelpMan{"sendtomainchain",
                "\nSends Liquid funds to the Bitcoin mainchain, through the federated withdraw mechanism. The wallet internally generates the returned `bitcoin_address` via `bitcoin_descriptor` and `bip32_counter` previously set in `initpegoutwallet`. The counter will be incremented upon successful send, avoiding address re-use.\n"
                + HelpRequiringPassphrase(pwallet),
                {
                    {"address", RPCArg::Type::STR, RPCArg::Optional::NO, "Must be \"\". Only for non-PAK `sendtomainchain` compatibility."},
                    {"amount", RPCArg::Type::AMOUNT, RPCArg::Optional::NO, "The amount being sent to `bitcoin_address`."},
                    {"subtractfeefromamount", RPCArg::Type::BOOL, /* default */ "false", "The fee will be deducted from the amount being pegged-out."},
                },
                RPCResult{
            "{\n"
                "\"bitcoin_address\"   (string) The destination address on Bitcoin mainchain."
                "\"txid\"              (string) Transaction ID of the resulting Liquid transaction\n"
                "\"bitcoin_descriptor\"      (string) The xpubkey of the child destination address.\n"
                "\"bip32_counter\"   (string) The derivation counter for the `bitcoin_descriptor`.\n"
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("sendtomainchain", "\"\" 0.1")
            + HelpExampleRpc("sendtomainchain", "\"\" 0.1")
                },
            }.ToString());

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    EnsureWalletIsUnlocked(pwallet);

    if (!request.params[0].get_str().empty()) {
        throw JSONRPCError(RPC_TYPE_ERROR, "`address` argument must be \"\" for PAK-enabled networks as the address is generated automatically.");
    }

    //amount
    CAmount nAmount = AmountFromValue(request.params[1]);
    if (nAmount < 100000)
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid amount for send, must send more than 0.00100000 BTC");

    bool subtract_fee = false;
    if (request.params.size() > 2) {
        subtract_fee = request.params[2].get_bool();
    }

    CPAKList paklist = GetActivePAKList(::ChainActive().Tip(), Params().GetConsensus());
    if (paklist.IsReject()) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Pegout freeze is under effect to aid a pak transition to a new list. Please consult the network operator.");
    }

    // Fetch pegout key data
    int counter = pwallet->offline_counter;
    CExtPubKey& xpub = pwallet->offline_xpub;
    CPubKey& onlinepubkey = pwallet->online_key;

    if (counter < 0) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Pegout authorization for this wallet has not been set. Please call `initpegoutwallet` with the appropriate arguments first.");
    }

    FlatSigningProvider provider;
    std::string error;
    const auto descriptor = Parse(pwallet->offline_desc, provider, error);

    LegacyScriptPubKeyMan* spk_man = pwallet->GetLegacyScriptPubKeyMan();
    if (!spk_man) {
        throw JSONRPCError(RPC_WALLET_ERROR, "This type of wallet does not support this command");
    }

    // If descriptor not previously set, generate it
    if (!descriptor) {
        std::string offline_desc = "pkh(" + EncodeExtPubKey(xpub) + "0/*)";
        if (!pwallet->SetOfflineDescriptor(offline_desc)) {
            throw JSONRPCError(RPC_WALLET_ERROR, "Couldn't set wallet descriptor for peg-outs.");
        }
    }

    std::string desc_str = pwallet->offline_desc;
    std::string xpub_str = EncodeExtPubKey(xpub);

    // TODO: More properly expose key parsing functionality

    // Strip last parenths(up to 2) and "/*" to let ParseKeyPath do its thing
    desc_str.erase(std::remove(desc_str.begin(), desc_str.end(), ')'), desc_str.end());
    desc_str = desc_str.substr(0, desc_str.size()-2);

    // Since we know there are no key origin data, directly call inner parsing functions
    Span<const char> span(desc_str.data(), desc_str.size());
    auto split = Split(span, '/');
    KeyPath key_path;
    if (!ParseKeyPath(split, key_path)) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Stored keypath in descriptor cannot be parsed.");
    }
    key_path.push_back(counter);

    secp256k1_pubkey onlinepubkey_secp;
    if (secp256k1_ec_pubkey_parse(secp256k1_ctx, &onlinepubkey_secp, onlinepubkey.begin(), onlinepubkey.size()) != 1) {
        throw JSONRPCError(RPC_TYPE_ERROR, "Pubkey is invalid");
    }

    // Get index of given online key
    int whitelistindex=-1;
    std::vector<secp256k1_pubkey> pak_online = paklist.OnlineKeys();
    for (unsigned int i=0; i<pak_online.size(); i++) {
        if (memcmp((void *)&pak_online[i], (void *)&onlinepubkey_secp, sizeof(secp256k1_pubkey)) == 0) {
            whitelistindex = i;
            break;
        }
    }
    if (whitelistindex == -1)
        throw JSONRPCError(RPC_WALLET_ERROR, "Given online key is not in Pegout Authorization Key List");

    // Parse master pubkey
    CPubKey masterpub = xpub.pubkey;
    secp256k1_pubkey masterpub_secp;
    int ret = secp256k1_ec_pubkey_parse(secp256k1_ctx, &masterpub_secp, masterpub.begin(), masterpub.size());
    if (ret != 1) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Master pubkey could not be parsed.");
    }

    secp256k1_pubkey btcpub_secp;
    memcpy(&btcpub_secp, &masterpub_secp, sizeof(secp256k1_pubkey));

    // Negate master pubkey
    ret = secp256k1_ec_pubkey_negate(secp256k1_ctx, &masterpub_secp);

    // Make sure negated master pubkey is in PAK list at same index as online_pubkey
    if (memcmp((void *)&paklist.OfflineKeys()[whitelistindex], (void *)&masterpub_secp, sizeof(secp256k1_pubkey)) != 0) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Given bitcoin_descriptor cannot be found in same entry as known liquid_pak");
    }

    // Get online PAK
    CKey masterOnlineKey;
    if (!spk_man->GetKey(onlinepubkey.GetID(), masterOnlineKey))
        throw JSONRPCError(RPC_WALLET_ERROR, "Given online key is in master set but not in wallet");

    // Tweak offline pubkey by tweakSum aka sumkey to get bitcoin key
    std::vector<unsigned char> tweakSum;
    if (!DerivePubTweak(key_path, xpub.pubkey, xpub.chaincode, tweakSum)) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Could not create xpub tweak to generate proof.");
    }
    ret = secp256k1_ec_pubkey_tweak_add(secp256k1_ctx, &btcpub_secp, tweakSum.data());
    assert(ret);

    std::vector<unsigned char> btcpubkeybytes;
    btcpubkeybytes.resize(33);
    size_t btclen = 33;
    ret = secp256k1_ec_pubkey_serialize(secp256k1_ctx, &btcpubkeybytes[0], &btclen, &btcpub_secp, SECP256K1_EC_COMPRESSED);
    assert(ret == 1);
    assert(btclen == 33);
    assert(btcpubkeybytes.size() == 33);

    //Create, verify whitelist proof
    secp256k1_whitelist_signature sig;
    if(secp256k1_whitelist_sign(secp256k1_ctx, &sig, &paklist.OnlineKeys()[0], &paklist.OfflineKeys()[0], paklist.size(), &btcpub_secp, masterOnlineKey.begin(), &tweakSum[0], whitelistindex, NULL, NULL) != 1) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Pegout authorization proof signing failed");
    }

    if (secp256k1_whitelist_verify(secp256k1_ctx, &sig, &paklist.OnlineKeys()[0], &paklist.OfflineKeys()[0], paklist.size(), &btcpub_secp) != 1) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Pegout authorization proof was created and signed but is invalid");
    }

    //Serialize
    const size_t expectedOutputSize = 1 + 32 * (1 + paklist.size());
    assert(1 + 32 * (1 + 256) >= expectedOutputSize);
    unsigned char output[1 + 32 * (1 + 256)];
    size_t outlen = expectedOutputSize;
    secp256k1_whitelist_signature_serialize(secp256k1_ctx, output, &outlen, &sig);
    assert(outlen == expectedOutputSize);
    std::vector<unsigned char> whitelistproof(output, output + expectedOutputSize / sizeof(unsigned char));

    // Derive the end address in mainchain
    std::vector<CScript> scripts;
    if (!descriptor->Expand(counter, provider, scripts, provider)) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Could not generate mainchain destination with descriptor. This is a bug.");
    }
    assert(scripts.size() == 1);
    CScript mainchain_script = scripts[0];
    CTxDestination bitcoin_address;
    ExtractDestination(mainchain_script, bitcoin_address);

    uint256 genesisBlockHash = Params().ParentGenesisBlockHash();
    NullData nulldata;
    nulldata << std::vector<unsigned char>(genesisBlockHash.begin(), genesisBlockHash.end());
    nulldata << std::vector<unsigned char>(mainchain_script.begin(), mainchain_script.end());
    nulldata << btcpubkeybytes;
    nulldata << whitelistproof;
    CTxDestination address(nulldata);
    assert(GetScriptForDestination(nulldata).IsPegoutScript(genesisBlockHash));

    if (!ScriptHasValidPAKProof(GetScriptForDestination(nulldata), Params().ParentGenesisBlockHash(), paklist)) {
        throw JSONRPCError(RPC_TYPE_ERROR, "Resulting scriptPubKey is non-standard. Ensure pak=reject is not set");
    }

    mapValue_t mapValue;
    CCoinControl no_coin_control; // This is a deprecated API
    CTransactionRef tx = SendMoney(*locked_chain, pwallet, address, nAmount, Params().GetConsensus().pegged_asset, subtract_fee, no_coin_control, std::move(mapValue), true /* ignore_blind_fail */);

    pwallet->SetOfflineCounter(counter+1);

    std::stringstream ss;
    ss << counter;

    UniValue obj(UniValue::VOBJ);
    obj.pushKV("txid", tx->GetHash().GetHex());
    obj.pushKV("bitcoin_address", EncodeParentDestination(bitcoin_address));
    obj.pushKV("bip32_counter", ss.str());
    obj.pushKV("bitcoin_descriptor", pwallet->offline_desc);
    return obj;
}

// We only expose the appropriate peg-out method type per network
UniValue sendtomainchain(const JSONRPCRequest& request)
{
    if (Params().GetEnforcePak()) {
        return sendtomainchain_pak(request);
    } else {
        return sendtomainchain_base(request);
    }
}

extern UniValue signrawtransaction(const JSONRPCRequest& request);
extern UniValue sendrawtransaction(const JSONRPCRequest& request);

template<typename T_tx_ref, typename T_tx, typename T_merkle_block>
static UniValue createrawpegin(const JSONRPCRequest& request, T_tx_ref& txBTCRef, T_tx& tx_aux, T_merkle_block& merkleBlock)
{
    if (request.fHelp || request.params.size() < 2 || request.params.size() > 3)
        throw std::runtime_error(
            RPCHelpMan{"createrawpegin",
                "\nCreates a raw transaction to claim coins from the main chain by creating a pegin transaction with the necessary metadata after the corresponding Bitcoin transaction.\n"
                "Note that this call will not sign the transaction.\n"
                "If a transaction is not relayed it may require manual addition to a functionary mempool in order for it to be mined.\n",
                {
                    {"bitcoinTx", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The raw bitcoin transaction (in hex) depositing bitcoin to the mainchain_address generated by getpeginaddress"},
                    {"txoutproof", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "A rawtxoutproof (in hex) generated by the mainchain daemon's `gettxoutproof` containing a proof of only bitcoinTx"},
                    {"claim_script", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED_NAMED_ARG, "The witness program generated by getpeginaddress. Only needed if not in wallet."},
                },
                RPCResult{
            "{\n"
            "   \"hex\"       (string) Raw transaction in hex\n"
            "   \"mature\"            (bool) Whether the peg-in is mature (only included when validating peg-ins)\n"
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("createrawpegin", "\"0200000002b80a99d63ca943d72141750d983a3eeda3a5c5a92aa962884ffb141eb49ffb4f000000006a473044022031ffe1d76decdfbbdb7e2ee6010e865a5134137c261e1921da0348b95a207f9e02203596b065c197e31bcc2f80575154774ac4e80acd7d812c91d93c4ca6a3636f27012102d2130dfbbae9bd27eee126182a39878ac4e117d0850f04db0326981f43447f9efeffffffb80a99d63ca943d72141750d983a3eeda3a5c5a92aa962884ffb141eb49ffb4f010000006b483045022100cf041ce0eb249ae5a6bc33c71c156549c7e5ad877ae39e2e3b9c8f1d81ed35060220472d4e4bcc3b7c8d1b34e467f46d80480959183d743dad73b1ed0e93ec9fd14f012103e73e8b55478ab9c5de22e2a9e73c3e6aca2c2e93cd2bad5dc4436a9a455a5c44feffffff0200e1f5050000000017a914da1745e9b549bd0bfa1a569971c77eba30cd5a4b87e86cbe00000000001976a914a25fe72e7139fd3f61936b228d657b2548b3936a88acc0020000\", \"00000020976e918ed537b0f99028648f2a25c0bd4513644fb84d9cbe1108b4df6b8edf6ba715c424110f0934265bf8c5763d9cc9f1675a0f728b35b9bc5875f6806be3d19cd5b159ffff7f2000000000020000000224eab3da09d99407cb79f0089e3257414c4121cb85a320e1fd0f88678b6b798e0713a8d66544b6f631f9b6d281c71633fb91a67619b189a06bab09794d5554a60105\" \"0014058c769ffc7d12c35cddec87384506f536383f9c\"")
            + HelpExampleRpc("createrawpegin", "\"0200000002b80a99d63ca943d72141750d983a3eeda3a5c5a92aa962884ffb141eb49ffb4f000000006a473044022031ffe1d76decdfbbdb7e2ee6010e865a5134137c261e1921da0348b95a207f9e02203596b065c197e31bcc2f80575154774ac4e80acd7d812c91d93c4ca6a3636f27012102d2130dfbbae9bd27eee126182a39878ac4e117d0850f04db0326981f43447f9efeffffffb80a99d63ca943d72141750d983a3eeda3a5c5a92aa962884ffb141eb49ffb4f010000006b483045022100cf041ce0eb249ae5a6bc33c71c156549c7e5ad877ae39e2e3b9c8f1d81ed35060220472d4e4bcc3b7c8d1b34e467f46d80480959183d743dad73b1ed0e93ec9fd14f012103e73e8b55478ab9c5de22e2a9e73c3e6aca2c2e93cd2bad5dc4436a9a455a5c44feffffff0200e1f5050000000017a914da1745e9b549bd0bfa1a569971c77eba30cd5a4b87e86cbe00000000001976a914a25fe72e7139fd3f61936b228d657b2548b3936a88acc0020000\", \"00000020976e918ed537b0f99028648f2a25c0bd4513644fb84d9cbe1108b4df6b8edf6ba715c424110f0934265bf8c5763d9cc9f1675a0f728b35b9bc5875f6806be3d19cd5b159ffff7f2000000000020000000224eab3da09d99407cb79f0089e3257414c4121cb85a320e1fd0f88678b6b798e0713a8d66544b6f631f9b6d281c71633fb91a67619b189a06bab09794d5554a60105\", \"0014058c769ffc7d12c35cddec87384506f536383f9c\"")
                },
            }.ToString());

    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    if (!IsHex(request.params[0].get_str()) || !IsHex(request.params[1].get_str())) {
        throw JSONRPCError(RPC_TYPE_ERROR, "the first two arguments must be hex strings");
    }

    std::vector<unsigned char> txData = ParseHex(request.params[0].get_str());
    std::vector<unsigned char> txOutProofData = ParseHex(request.params[1].get_str());

    std::set<CScript> claim_scripts;
    if (request.params.size() > 2) {
        const std::string claim_script = request.params[2].get_str();
        if (!IsHex(claim_script)) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Given claim_script is not hex.");
        }
        // If given manually, no need for it to be a witness script
        std::vector<unsigned char> witnessBytes(ParseHex(claim_script));
        CScript witness_script(witnessBytes.begin(), witnessBytes.end());
        claim_scripts.insert(std::move(witness_script));
    }
    else {
        // Look for known wpkh address in wallet
        for (std::map<CTxDestination, CAddressBookData>::const_iterator iter = pwallet->mapAddressBook.begin(); iter != pwallet->mapAddressBook.end(); ++iter) {
            CScript dest_script = GetScriptForDestination(iter->first);
            claim_scripts.insert(std::move(dest_script));
        }
    }

    // Make the tx
    CMutableTransaction mtx;

    // Construct pegin input
    CreatePegInInput(mtx, 0, txBTCRef, merkleBlock, claim_scripts, txData, txOutProofData);

    // Manually construct peg-in transaction, sign it, and send it off.
    // Decrement the output value as much as needed given the total vsize to
    // pay the fees.

    if (!pwallet->IsLocked())
        pwallet->TopUpKeyPool();

    // Generate a new key that is added to wallet
    CTxDestination wpkhash;
    std::string error;
    if (!pwallet->GetNewDestination(OutputType::BECH32, "", wpkhash, error)) {
        throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, error);
    }

    // Get value for output
    CAmount value = 0;
    if (!GetAmountFromParentChainPegin(value, *txBTCRef, mtx.vin[0].prevout.n)) {
        throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Amounts to pegin must be explicit and asset must be %s", Params().GetConsensus().parent_pegged_asset.GetHex()));
    }

    // one wallet output and one fee output
    mtx.vout.push_back(CTxOut(Params().GetConsensus().pegged_asset, value, GetScriptForDestination(wpkhash)));
    mtx.vout.push_back(CTxOut(Params().GetConsensus().pegged_asset, 0, CScript()));

    // Estimate fee for transaction, decrement fee output(including witness data)
    unsigned int nBytes = GetVirtualTransactionSize(CTransaction(mtx)) +
        (1+1+72+1+33/WITNESS_SCALE_FACTOR);
    CCoinControl coin_control;
    CAmount nFeeNeeded = GetMinimumFee(*pwallet, nBytes, coin_control, nullptr);

    mtx.vout[0].nValue = mtx.vout[0].nValue.GetAmount() - nFeeNeeded;
    mtx.vout[1].nValue = mtx.vout[1].nValue.GetAmount() + nFeeNeeded;

    UniValue ret(UniValue::VOBJ);

    // Return hex
    std::string strHex = EncodeHexTx(CTransaction(mtx), RPCSerializationFlags());
    ret.pushKV("hex", strHex);

    // Additional block lee-way to avoid bitcoin block races
    if (gArgs.GetBoolArg("-validatepegin", Params().GetConsensus().has_parent_chain)) {
        unsigned int required_depth = Params().GetConsensus().pegin_min_depth + 2;
        std::vector<uint256> txHashes;
        std::vector<unsigned int> txIndices;
        merkleBlock.txn.ExtractMatches(txHashes, txIndices);
        if (txIndices[0] == 0) {
            required_depth = std::max(required_depth, (unsigned int)COINBASE_MATURITY+2);
        }
        ret.pushKV("mature", IsConfirmedBitcoinBlock(merkleBlock.header.GetHash(), required_depth, merkleBlock.txn.GetNumTransactions()));
    }

    return ret;
}

UniValue createrawpegin(const JSONRPCRequest& request)
{
    UniValue ret(UniValue::VOBJ);
    if (Params().GetConsensus().ParentChainHasPow()) {
        Sidechain::Bitcoin::CTransactionRef txBTCRef;
        Sidechain::Bitcoin::CTransaction tx_aux;
        Sidechain::Bitcoin::CMerkleBlock merkleBlock;
        ret = createrawpegin(request, txBTCRef, tx_aux, merkleBlock);
        if (!CheckParentProofOfWork(merkleBlock.header.GetHash(), merkleBlock.header.nBits, Params().GetConsensus())) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid tx out proof");
        }
    } else {
        CTransactionRef txBTCRef;
        CTransaction tx_aux;
        CMerkleBlock merkleBlock;
        ret = createrawpegin(request, txBTCRef, tx_aux, merkleBlock);
        if (!CheckProofSignedParent(merkleBlock.header, Params().GetConsensus())) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid tx out proof");
        }
    }
    return ret;
}

UniValue claimpegin(const JSONRPCRequest& request)
{

    if (request.fHelp || request.params.size() < 2 || request.params.size() > 3)
        throw std::runtime_error(
            RPCHelpMan{"claimpegin",
                "\nClaim coins from the main chain by creating a pegin transaction with the necessary metadata after the corresponding Bitcoin transaction.\n"
                "Note that the transaction will not be relayed unless it is buried at least 102 blocks deep.\n"
                "If a transaction is not relayed it may require manual addition to a functionary mempool in order for it to be mined.\n",
                {
                    {"bitcoinTx", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The raw bitcoin transaction (in hex) depositing bitcoin to the mainchain_address generated by getpeginaddress"},
                    {"txoutproof", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "A rawtxoutproof (in hex) generated by the mainchain daemon's `gettxoutproof` containing a proof of only bitcoinTx"},
                    {"claim_script", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED_NAMED_ARG, "The witness program generated by getpeginaddress. Only needed if not in wallet."},
                },
                RPCResult{
            "\"txid\"                 (string) Txid of the resulting sidechain transaction\n"
                },
                RPCExamples{
                    HelpExampleCli("claimpegin", "\"0200000002b80a99d63ca943d72141750d983a3eeda3a5c5a92aa962884ffb141eb49ffb4f000000006a473044022031ffe1d76decdfbbdb7e2ee6010e865a5134137c261e1921da0348b95a207f9e02203596b065c197e31bcc2f80575154774ac4e80acd7d812c91d93c4ca6a3636f27012102d2130dfbbae9bd27eee126182a39878ac4e117d0850f04db0326981f43447f9efeffffffb80a99d63ca943d72141750d983a3eeda3a5c5a92aa962884ffb141eb49ffb4f010000006b483045022100cf041ce0eb249ae5a6bc33c71c156549c7e5ad877ae39e2e3b9c8f1d81ed35060220472d4e4bcc3b7c8d1b34e467f46d80480959183d743dad73b1ed0e93ec9fd14f012103e73e8b55478ab9c5de22e2a9e73c3e6aca2c2e93cd2bad5dc4436a9a455a5c44feffffff0200e1f5050000000017a914da1745e9b549bd0bfa1a569971c77eba30cd5a4b87e86cbe00000000001976a914a25fe72e7139fd3f61936b228d657b2548b3936a88acc0020000\" \"00000020976e918ed537b0f99028648f2a25c0bd4513644fb84d9cbe1108b4df6b8edf6ba715c424110f0934265bf8c5763d9cc9f1675a0f728b35b9bc5875f6806be3d19cd5b159ffff7f2000000000020000000224eab3da09d99407cb79f0089e3257414c4121cb85a320e1fd0f88678b6b798e0713a8d66544b6f631f9b6d281c71633fb91a67619b189a06bab09794d5554a60105\" \"0014058c769ffc7d12c35cddec87384506f536383f9c\"")
            + HelpExampleRpc("claimpegin", "\"0200000002b80a99d63ca943d72141750d983a3eeda3a5c5a92aa962884ffb141eb49ffb4f000000006a473044022031ffe1d76decdfbbdb7e2ee6010e865a5134137c261e1921da0348b95a207f9e02203596b065c197e31bcc2f80575154774ac4e80acd7d812c91d93c4ca6a3636f27012102d2130dfbbae9bd27eee126182a39878ac4e117d0850f04db0326981f43447f9efeffffffb80a99d63ca943d72141750d983a3eeda3a5c5a92aa962884ffb141eb49ffb4f010000006b483045022100cf041ce0eb249ae5a6bc33c71c156549c7e5ad877ae39e2e3b9c8f1d81ed35060220472d4e4bcc3b7c8d1b34e467f46d80480959183d743dad73b1ed0e93ec9fd14f012103e73e8b55478ab9c5de22e2a9e73c3e6aca2c2e93cd2bad5dc4436a9a455a5c44feffffff0200e1f5050000000017a914da1745e9b549bd0bfa1a569971c77eba30cd5a4b87e86cbe00000000001976a914a25fe72e7139fd3f61936b228d657b2548b3936a88acc0020000\", \"00000020976e918ed537b0f99028648f2a25c0bd4513644fb84d9cbe1108b4df6b8edf6ba715c424110f0934265bf8c5763d9cc9f1675a0f728b35b9bc5875f6806be3d19cd5b159ffff7f2000000000020000000224eab3da09d99407cb79f0089e3257414c4121cb85a320e1fd0f88678b6b798e0713a8d66544b6f631f9b6d281c71633fb91a67619b189a06bab09794d5554a60105\", \"0014058c769ffc7d12c35cddec87384506f536383f9c\"")
                },
            }.ToString());

    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();
    CTransactionRef tx_ref;
    CMutableTransaction mtx;

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    if (::ChainstateActive().IsInitialBlockDownload()) {
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
    UniValue result = signrawtransactionwithwallet(request2);

    if (!DecodeHexTx(mtx, result["hex"].get_str(), false, true)) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    }

    // To check if it's not double spending an existing pegin UTXO, we check mempool acceptance.
    TxValidationState acceptState;
    LockAssertion lock(::cs_main); //TODO(stevenroose) replace with locked_chain later
    bool accepted = ::AcceptToMemoryPool(mempool, acceptState, MakeTransactionRef(mtx),
                            nullptr /* plTxnReplaced */, false /* bypass_limits */, pwallet->m_default_max_tx_fee, true /* test_accept */);
    if (!accepted) {
        std::string strError = strprintf("Error: The transaction was rejected! Reason given: %s", FormatStateMessage(acceptState));
        throw JSONRPCError(RPC_WALLET_ERROR, strError);
    }

    // Send it
    mapValue_t mapValue;
    pwallet->CommitTransaction(MakeTransactionRef(mtx), mapValue, {} /* orderForm */);

    return mtx.GetHash().GetHex();
}

// Rewind the outputs to unblinded, and push placeholders for blinding info. Not exported.
void FillBlinds(CWallet* pwallet, CMutableTransaction& tx, std::vector<uint256>& output_value_blinds, std::vector<uint256>& output_asset_blinds, std::vector<CPubKey>& output_pubkeys, std::vector<CKey>& asset_keys, std::vector<CKey>& token_keys) {

    // Resize witness before doing anything
    tx.witness.vtxinwit.resize(tx.vin.size());
    tx.witness.vtxoutwit.resize(tx.vout.size());

    for (size_t nOut = 0; nOut < tx.vout.size(); ++nOut) {
        CTxOut& out = tx.vout[nOut];
        if (out.nValue.IsExplicit()) {
            CPubKey pubkey(out.nNonce.vchCommitment);
            if (!pubkey.IsFullyValid()) {
                output_pubkeys.push_back(CPubKey());
            } else {
                output_pubkeys.push_back(pubkey);
            }
            output_value_blinds.push_back(uint256());
            output_asset_blinds.push_back(uint256());
        } else if (out.nValue.IsCommitment()) {
            CTxOutWitness* ptxoutwit = &tx.witness.vtxoutwit[nOut];
            uint256 blinding_factor;
            uint256 asset_blinding_factor;
            CAsset asset;
            CAmount amount;
            // This can only be used to recover things like change addresses and self-sends.
            if (UnblindConfidentialPair(pwallet->GetBlindingKey(&out.scriptPubKey), out.nValue, out.nAsset, out.nNonce, out.scriptPubKey, ptxoutwit->vchRangeproof, amount, blinding_factor, asset, asset_blinding_factor) != 0) {
                // Wipe out confidential info from output and output witness
                CScript scriptPubKey = tx.vout[nOut].scriptPubKey;
                CTxOut newOut(asset, amount, scriptPubKey);
                tx.vout[nOut] = newOut;
                ptxoutwit->SetNull();

                // Mark for re-blinding with same key that deblinded it
                CPubKey pubkey(pwallet->GetBlindingKey(&out.scriptPubKey).GetPubKey());
                output_pubkeys.push_back(pubkey);
                output_value_blinds.push_back(uint256());
                output_asset_blinds.push_back(uint256());
            } else {
                output_pubkeys.push_back(CPubKey());
                output_value_blinds.push_back(uint256());
                output_asset_blinds.push_back(uint256());
            }
        } else {
            // Null or invalid, do nothing for that output
            output_pubkeys.push_back(CPubKey());
            output_value_blinds.push_back(uint256());
            output_asset_blinds.push_back(uint256());
        }
    }

    // Fill out issuance blinding keys to be used directly as nonce for rangeproof
    for (size_t nIn = 0; nIn < tx.vin.size(); ++nIn) {
        CAssetIssuance& issuance = tx.vin[nIn].assetIssuance;
        if (issuance.IsNull()) {
            asset_keys.push_back(CKey());
            token_keys.push_back(CKey());
            continue;
        }

        // Calculate underlying asset for use as blinding key script
        CAsset asset;
        // New issuance, compute the asset ids
        if (issuance.assetBlindingNonce.IsNull()) {
            uint256 entropy;
            GenerateAssetEntropy(entropy, tx.vin[nIn].prevout, issuance.assetEntropy);
            CalculateAsset(asset, entropy);
        }
        // Re-issuance
        else {
            // TODO Give option to skip blinding when the reissuance token was derived without blinding ability. For now we assume blinded
            // hashAssetIdentifier doubles as the entropy on reissuance
            CalculateAsset(asset, issuance.assetEntropy);
        }

        // Special format for issuance blinding keys, unique for each transaction
        CScript blindingScript = CScript() << OP_RETURN << std::vector<unsigned char>(tx.vin[nIn].prevout.hash.begin(), tx.vin[nIn].prevout.hash.end()) << tx.vin[nIn].prevout.n;

        for (size_t nPseudo = 0; nPseudo < 2; nPseudo++) {
            bool issuance_asset = (nPseudo == 0);
            std::vector<CKey>& issuance_blinding_keys = issuance_asset ? asset_keys : token_keys;
            CConfidentialValue& conf_value = issuance_asset ? issuance.nAmount : issuance.nInflationKeys;
            if (conf_value.IsCommitment()) {
                // Rangeproof must exist
                if (tx.witness.vtxinwit.size() <= nIn) {
                    throw JSONRPCError(RPC_INVALID_PARAMETER, "Transaction issuance is already blinded but has no attached rangeproof.");
                }
                CTxInWitness& txinwit = tx.witness.vtxinwit[nIn];
                std::vector<unsigned char>& vchRangeproof = issuance_asset ? txinwit.vchIssuanceAmountRangeproof : txinwit.vchInflationKeysRangeproof;
                uint256 blinding_factor;
                uint256 asset_blinding_factor;
                CAmount amount;
                if (UnblindConfidentialPair(pwallet->GetBlindingKey(&blindingScript), conf_value, CConfidentialAsset(asset), CConfidentialNonce(), CScript(), vchRangeproof, amount, blinding_factor, asset, asset_blinding_factor) != 0) {
                    // Wipe out confidential info from issuance
                    vchRangeproof.clear();
                    conf_value = CConfidentialValue(amount);
                    // One key blinds both values, single key needed for issuance reveal
                    issuance_blinding_keys.push_back(pwallet->GetBlindingKey(&blindingScript));
                } else {
                    // If  unable to unblind, leave it alone in next blinding step
                    issuance_blinding_keys.push_back(CKey());
                }
            } else if (conf_value.IsExplicit()) {
                // Use wallet to generate blindingkey used directly as nonce
                // as user is not "sending" to anyone.
                // Always assumed we want to blind here.
                // TODO Signal intent for all blinding via API including replacing nonce commitment
                issuance_blinding_keys.push_back(pwallet->GetBlindingKey(&blindingScript));
            } else  {
                // Null or invalid, don't try anything but append an empty key
                issuance_blinding_keys.push_back(CKey());
            }
        }
    }
}

UniValue blindrawtransaction(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp))
        return NullUniValue;

    if (request.fHelp || (request.params.size() < 1 || request.params.size() > 5))
        throw std::runtime_error(
            RPCHelpMan{"blindrawtransaction",
                "\nConvert one or more outputs of a raw transaction into confidential ones using only wallet inputs.\n"
                "Returns the hex-encoded raw transaction.\n"
                "The output keys used can be specified by using a confidential address in createrawtransaction.\n"
                "This call may add an additional 0-value unspendable output in order to balance the blinders.\n",
                {
                    {"hexstring", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "A hex-encoded raw transaction."},
                    {"ignoreblindfail", RPCArg::Type::BOOL , /* default */ "true", "Return a transaction even when a blinding attempt fails due to number of blinded inputs/outputs."},
                    {"asset_commitments", RPCArg::Type::ARR, RPCArg::Optional::OMITTED_NAMED_ARG, "An array of input asset generators. If provided, this list must be empty, or match the final input commitment list, including ordering, to make a valid surjection proof. This list does not include generators for issuances, as these assets are inherently unblinded.",
                        {
                            {"assetcommitment", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED, "A hex-encoded asset commitment, one for each input."
            "                        Null commitments must be \"\"."},
                        }
                    },
                    {"blind_issuances", RPCArg::Type::BOOL , /* default */ "true", "Blind the issuances found in the raw transaction or not. All issuances will be blinded if true."},
                    {"totalblinder", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "Ignored for now."},
                },
                RPCResult{
            "\"transaction\"              (string) hex string of the transaction\n"
                },
                RPCExamples{""},
            }.ToString());

    std::vector<unsigned char> txData(ParseHexV(request.params[0], "argument 1"));
    CDataStream ssData(txData, SER_NETWORK, PROTOCOL_VERSION);
    CMutableTransaction tx;
    try {
        ssData >> tx;
    } catch (const std::exception &) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");
    }

    bool ignore_blind_fail = true;
    if (request.params.size() > 1) {
        ignore_blind_fail = request.params[1].get_bool();
    }

    std::vector<std::vector<unsigned char> > auxiliary_generators;
    if (request.params.size() > 2) {
        UniValue assetCommitments = request.params[2].get_array();
        if (assetCommitments.size() != 0 && assetCommitments.size() < tx.vin.size()) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Asset commitment array must have at least as many entries as transaction inputs.");
        }
        for (size_t nIn = 0; nIn < assetCommitments.size(); nIn++) {
            if (assetCommitments[nIn].isStr()) {
                std::string assetcommitment = assetCommitments[nIn].get_str();
                if (IsHex(assetcommitment) && assetcommitment.size() == 66) {
                    auxiliary_generators.push_back(ParseHex(assetcommitment));
                    continue;
                }
            }
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Asset commitments must be a hex encoded string of length 66.");
        }
    }

    bool blind_issuances = request.params[3].isNull() || request.params[3].get_bool();

    LOCK(pwallet->cs_wallet);

    const auto& fedpegscripts = GetValidFedpegScripts(::ChainActive().Tip(), Params().GetConsensus(), true /* nextblock_validation */);

    std::vector<uint256> input_blinds;
    std::vector<uint256> input_asset_blinds;
    std::vector<CAsset> input_assets;
    std::vector<CAmount> input_amounts;
    int n_blinded_ins = 0;
    for (size_t nIn = 0; nIn < tx.vin.size(); ++nIn) {
        COutPoint prevout = tx.vin[nIn].prevout;

        // Special handling for pegin inputs: no blinds and explicit amount/asset.
        if (tx.vin[nIn].m_is_pegin) {
            std::string err;
            if (tx.witness.vtxinwit.size() != tx.vin.size() || !IsValidPeginWitness(tx.witness.vtxinwit[nIn].m_pegin_witness, fedpegscripts, prevout, err, false)) {
                throw JSONRPCError(RPC_INVALID_PARAMETER, strprintf("Transaction contains invalid peg-in input: %s", err));
            }
            CTxOut pegin_output = GetPeginOutputFromWitness(tx.witness.vtxinwit[nIn].m_pegin_witness);
            input_blinds.push_back(uint256());
            input_asset_blinds.push_back(uint256());
            input_assets.push_back(pegin_output.nAsset.GetAsset());
            input_amounts.push_back(pegin_output.nValue.GetAmount());
            continue;
        }

        std::map<uint256, CWalletTx>::iterator it = pwallet->mapWallet.find(prevout.hash);
        if (it == pwallet->mapWallet.end() || pwallet->IsMine(tx.vin[nIn]) == ISMINE_NO) {
            // For inputs we don't own, input assetcommitments for the surjection must be supplied.
            if (auxiliary_generators.size() > 0) {
                input_blinds.push_back(uint256());
                input_asset_blinds.push_back(uint256());
                input_assets.push_back(CAsset());
                input_amounts.push_back(-1);
                continue;
            }
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter: transaction spends from non-wallet output and no assetcommitment list was given.");
        }

        if (prevout.n >= it->second.tx->vout.size()) {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid parameter: transaction spends non-existing output");
        }
        input_blinds.push_back(it->second.GetOutputAmountBlindingFactor(prevout.n));
        input_asset_blinds.push_back(it->second.GetOutputAssetBlindingFactor(prevout.n));
        input_assets.push_back(it->second.GetOutputAsset(prevout.n));
        input_amounts.push_back(it->second.GetOutputValueOut(prevout.n));
        if (it->second.tx->vout[prevout.n].nValue.IsCommitment()) {
            n_blinded_ins += 1;
        }
    }

    std::vector<uint256> output_blinds;
    std::vector<uint256> output_asset_blinds;
    std::vector<CPubKey> output_pubkeys;
    std::vector<CKey> asset_keys;
    std::vector<CKey> token_keys;
    // This fills out issuance blinding data for you from the wallet itself
    FillBlinds(pwallet, tx, output_blinds, output_asset_blinds, output_pubkeys, asset_keys, token_keys);

    if (!blind_issuances) {
        asset_keys.clear();
        token_keys.clear();
    }

    // How many are we trying to blind?
    int num_pubkeys = 0;
    unsigned int key_index = 0;
    for (unsigned int i = 0; i < output_pubkeys.size(); i++) {
        const CPubKey& key = output_pubkeys[i];
        if (key.IsValid()) {
            num_pubkeys++;
            key_index = i;
        }
    }
    for (const CKey& key : asset_keys) {
        if (key.IsValid()) num_pubkeys++;
    }
    for (const CKey& key : token_keys) {
        if (key.IsValid()) num_pubkeys++;
    }

    if (num_pubkeys == 0 && n_blinded_ins == 0) {
        // Vacuous, just return the transaction
        return EncodeHexTx(CTransaction(tx));
    } else if (n_blinded_ins > 0 && num_pubkeys == 0) {
        // Blinded inputs need to balanced with something to be valid, make a dummy.
        CTxOut newTxOut(tx.vout.back().nAsset.GetAsset(), 0, CScript() << OP_RETURN);
        tx.vout.push_back(newTxOut);
        num_pubkeys++;
        output_pubkeys.push_back(pwallet->GetBlindingPubKey(newTxOut.scriptPubKey));
    } else if (n_blinded_ins == 0 && num_pubkeys == 1) {
        if (ignore_blind_fail) {
            // Just get rid of the ECDH key in the nonce field and return
            tx.vout[key_index].nNonce.SetNull();
            return EncodeHexTx(CTransaction(tx));
        } else {
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Unable to blind transaction: Add another output to blind in order to complete the blinding.");
        }
    }

    if (BlindTransaction(input_blinds, input_asset_blinds, input_assets, input_amounts, output_blinds, output_asset_blinds, output_pubkeys, asset_keys, token_keys, tx, (auxiliary_generators.size() ? &auxiliary_generators : NULL)) != num_pubkeys) {
        // TODO Have more rich return values, communicating to user what has been blinded
        // User may be ok not blinding something that for instance has no corresponding type on input
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Unable to blind transaction: Are you sure each asset type to blind is represented in the inputs?");
    }

    return EncodeHexTx(CTransaction(tx));
}

static UniValue unblindrawtransaction(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    if (request.fHelp || request.params.size() != 1)
        throw std::runtime_error(
            RPCHelpMan{"unblindrawtransaction",
                "\nRecovers unblinded transaction outputs from blinded outputs and issuance inputs when possible using wallet's known blinding keys, and strips related witness data.\n",
                {
                    {"hex", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "The hex string of the raw transaction."},
                },
                RPCResult{
                                       "{\n"
            "  \"hex\":       \"value\", (string)  The resulting unblinded raw transaction (hex-encoded string)\n"
                                       "}\n"
                },
                RPCExamples{
                    HelpExampleCli("unblindrawtransaction", "\"blindedtransactionhex\"")
                },
            }.ToString());

    RPCTypeCheck(request.params, {UniValue::VSTR});

    CMutableTransaction tx;
    if (!DecodeHexTx(tx, request.params[0].get_str()))
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "TX decode failed");

    std::vector<uint256> output_value_blinds;
    std::vector<uint256> output_asset_blinds;
    std::vector<CPubKey> output_pubkeys;
    std::vector<CKey> asset_keys;
    std::vector<CKey> token_keys;
    FillBlinds(pwallet, tx, output_value_blinds, output_asset_blinds, output_pubkeys, asset_keys, token_keys);

    UniValue result(UniValue::VOBJ);
    result.pushKV("hex", EncodeHexTx(CTransaction(tx)));
    return result;
}

static CTransactionRef SendGenerationTransaction(const CScript& asset_script, const CPubKey &asset_pubkey, const CScript& token_script, const CPubKey &token_pubkey, CAmount asset_amount, CAmount token_amount, IssuanceDetails* issuance_details, interfaces::Chain::Lock& locked_chain, CWallet* pwallet)
{
    CAsset reissue_token = issuance_details->reissuance_token;
    CAmount curBalance = pwallet->GetBalance().m_mine_trusted[reissue_token];

    if (!reissue_token.IsNull() && curBalance <= 0) {
        throw JSONRPCError(RPC_WALLET_INSUFFICIENT_FUNDS, "No available reissuance tokens in wallet.");
    }

    std::vector<CRecipient> vecSend;
    // Signal outputs to skip "funding" with fixed asset numbers 1, 2, ...
    // We don't know the asset during initial issuance until inputs are chosen
    if (asset_script.size() > 0) {
        vecSend.push_back({asset_script, asset_amount, CAsset(uint256S("1")), asset_pubkey, false});
    }
    if (token_script.size() > 0) {
        CRecipient recipient = {token_script, token_amount, CAsset(uint256S("2")), token_pubkey, false};
        // We need to select the issuance token(s) to spend
        if (!reissue_token.IsNull()) {
            recipient.asset = reissue_token;
            recipient.nAmount = curBalance; // Or 1?
            // If the issuance token *is* the fee asset, subtract fee from this output
            if (reissue_token == ::policyAsset) {
                recipient.fSubtractFeeFromAmount = true;
            }
        }
        vecSend.push_back(recipient);
    }

    CAmount nFeeRequired;
    int nChangePosRet = -1;
    std::string strError;
    CCoinControl dummy_control;
    BlindDetails blind_details;
    CTransactionRef tx_ref(MakeTransactionRef());
    if (!pwallet->CreateTransaction(locked_chain, vecSend, tx_ref, nFeeRequired, nChangePosRet, strError, dummy_control, true, &blind_details, issuance_details)) {
        throw JSONRPCError(RPC_WALLET_ERROR, strError);
    }

    mapValue_t map_value;
    pwallet->CommitTransaction(tx_ref, std::move(map_value), {} /* orderForm */, &blind_details);

    return tx_ref;
}

UniValue issueasset(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    if (request.fHelp || request.params.size() < 2 || request.params.size() > 3)
        throw std::runtime_error(
            RPCHelpMan{"issueasset",
                "\nCreate an asset. Must have funds in wallet to do so. Returns asset hex id.\n"
                "For more fine-grained control such as non-empty contract-hashes to commit\n"
                "to an issuance policy, see `rawissueasset` RPC call.\n",
                {
                    {"assetamount", RPCArg::Type::AMOUNT, RPCArg::Optional::NO, "Amount of asset to generate. Note that the amount is BTC-like, with 8 decimal places."},
                    {"tokenamount", RPCArg::Type::AMOUNT, RPCArg::Optional::NO, "Amount of reissuance tokens to generate. Note that the amount is BTC-like, with 8 decimal places. These will allow you to reissue the asset if in wallet using `reissueasset`. These tokens are not consumed during reissuance."},
                    {"blind", RPCArg::Type::BOOL , /* default */ "true", "Whether to blind the issuances."},
                },
                RPCResult{
            "{                        (json object)\n"
            "  \"txid\":\"<txid>\",   (string) Transaction id for issuance.\n"
            "  \"vin\":\"n\",         (numeric) The input position of the issuance in the transaction.\n"
            "  \"entropy\":\"<entropy>\", (string) Entropy of the asset type.\n"
            "  \"asset\":\"<asset>\", (string) Asset type for issuance.\n"
            "  \"token\":\"<token>\", (string) Token type for issuance.\n"
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("issueasset", "10 0")
            + HelpExampleRpc("issueasset", "10, 0")
                },
            }.ToString());

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    if (!g_con_elementsmode) {
        throw JSONRPCError(RPC_TYPE_ERROR, "Issuance can only be done on elements-style chains. Note: `-regtest` is Bitcoin's regtest mode, instead try `-chain=<custom chain name>`");
    }

    CAmount nAmount = AmountFromValue(request.params[0]);
    CAmount nTokens = AmountFromValue(request.params[1]);
    if (nAmount == 0 && nTokens == 0) {
        throw JSONRPCError(RPC_TYPE_ERROR, "Issuance must have one non-zero component");
    }

    bool blind_issuances = request.params.size() < 3 || request.params[2].get_bool();

    if (!pwallet->IsLocked())
        pwallet->TopUpKeyPool();

    // Generate a new key that is added to wallet
    std::string error;
    CPubKey newKey;
    CTxDestination asset_dest;
    CTxDestination token_dest;
    CPubKey asset_dest_blindpub;
    CPubKey token_dest_blindpub;

    if (nAmount > 0) {
        if (!pwallet->GetNewDestination(OutputType::LEGACY, "", asset_dest, error)) {
            throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, error);
        }
        asset_dest_blindpub = pwallet->GetBlindingPubKey(GetScriptForDestination(asset_dest));
    }
    if (nTokens > 0) {
        if (!pwallet->GetNewDestination(OutputType::LEGACY, "", token_dest, error)) {
            throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, error);
        }
        token_dest_blindpub = pwallet->GetBlindingPubKey(GetScriptForDestination(token_dest));
    }

    uint256 dummyentropy;
    CAsset dummyasset;
    IssuanceDetails issuance_details;
    issuance_details.blind_issuance = blind_issuances;
    CTransactionRef tx_ref = SendGenerationTransaction(GetScriptForDestination(asset_dest), asset_dest_blindpub, GetScriptForDestination(token_dest), token_dest_blindpub, nAmount, nTokens, &issuance_details, *locked_chain, pwallet);

    // Calculate asset type, assumes first vin is used for issuance
    CAsset asset;
    CAsset token;
    assert(!tx_ref->vin.empty());
    GenerateAssetEntropy(issuance_details.entropy, tx_ref->vin[0].prevout, uint256());
    CalculateAsset(asset, issuance_details.entropy);
    CalculateReissuanceToken(token, issuance_details.entropy, blind_issuances);

    UniValue ret(UniValue::VOBJ);
    ret.pushKV("txid", tx_ref->GetHash().GetHex());
    ret.pushKV("vin", 0);
    ret.pushKV("entropy", issuance_details.entropy.GetHex());
    ret.pushKV("asset", asset.GetHex());
    ret.pushKV("token", token.GetHex());
    return ret;
}

UniValue reissueasset(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    if (request.fHelp || request.params.size() != 2)
        throw std::runtime_error(
            RPCHelpMan{"reissueasset",
                "\nCreate more of an already issued asset. Must have reissuance token in wallet to do so. Reissuing does not affect your reissuance token balance, only asset.\n"
                "For more fine-grained control such as reissuing from a multi-signature address cold wallet, see `rawreissueasset` RPC call.\n",
                {
                    {"asset", RPCArg::Type::STR, RPCArg::Optional::NO, "The asset you want to re-issue. The corresponding token must be in your wallet."},
                    {"assetamount", RPCArg::Type::AMOUNT, RPCArg::Optional::NO, "Amount of additional asset to generate. Note that the amount is BTC-like, with 8 decimal places."},
                },
                RPCResult{
            "{                        (json object)\n"
            "  \"txid\":\"<txid>\",   (string) Transaction id for issuance.\n"
            "  \"vin\":\"n\",         (numeric) The input position of the issuance in the transaction.\n"
            "}\n"
                },
                RPCExamples{
                    HelpExampleCli("reissueasset", "<asset> 0")
            + HelpExampleRpc("reissueasset", "<asset>, 0")
                },
            }.ToString());

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    if (!g_con_elementsmode) {
        throw JSONRPCError(RPC_TYPE_ERROR, "Issuance can only be done on elements-style chains. Note: `-regtest` is Bitcoin's regtest mode, instead try `-chain=<custom chain name>`");
    }

    std::string assetstr = request.params[0].get_str();
    CAsset asset = GetAssetFromString(assetstr);

    CAmount nAmount = AmountFromValue(request.params[1]);
    if (nAmount <= 0) {
        throw JSONRPCError(RPC_TYPE_ERROR, "Reissuance must create a non-zero amount.");
    }

    if (!pwallet->IsLocked()) {
        pwallet->TopUpKeyPool();
    }

    // Find the entropy and reissuance token in wallet
    IssuanceDetails issuance_details;
    issuance_details.reissuance_asset = asset;
    std::map<uint256, std::pair<CAsset, CAsset> > tokenMap = pwallet->GetReissuanceTokenTypes();
    for (const auto& it : tokenMap) {
        if (it.second.second == asset) {
            issuance_details.entropy = it.first;
            issuance_details.reissuance_token = it.second.first;
        }
        if (it.second.first == asset) {
            throw JSONRPCError(RPC_WALLET_ERROR, "Asset given is a reissuance token type and can not be reissued.");
        }
    }
    if (issuance_details.reissuance_token.IsNull()) {
        throw JSONRPCError(RPC_WALLET_ERROR, "Asset reissuance token definition could not be found in wallet.");
    }

    // Add destination for the to-be-created asset
    std::string error;
    CTxDestination asset_dest;
    if (!pwallet->GetNewDestination(OutputType::LEGACY, "", asset_dest, error)) {
        throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, error);
    }
    CPubKey asset_dest_blindpub = pwallet->GetBlindingPubKey(GetScriptForDestination(asset_dest));

    // Add destination for tokens we are moving
    CTxDestination token_dest;
    if (!pwallet->GetNewDestination(OutputType::LEGACY, "", token_dest, error)) {
        throw JSONRPCError(RPC_WALLET_KEYPOOL_RAN_OUT, error);
    }
    CPubKey token_dest_blindpub = pwallet->GetBlindingPubKey(GetScriptForDestination(token_dest));

    // Attempt a send.
    CTransactionRef tx_ref = SendGenerationTransaction(GetScriptForDestination(asset_dest), asset_dest_blindpub, GetScriptForDestination(token_dest), token_dest_blindpub, nAmount, -1, &issuance_details, *locked_chain, pwallet);
    assert(!tx_ref->vin.empty());

    UniValue obj(UniValue::VOBJ);
    obj.pushKV("txid", tx_ref->GetHash().GetHex());
    for (uint64_t i = 0; i < tx_ref->vin.size(); i++) {
        if (!tx_ref->vin[i].assetIssuance.IsNull()) {
            obj.pushKV("vin", i);
            break;
        }
    }

    return obj;
}

UniValue listissuances(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    if (request.fHelp || request.params.size() > 1)
        throw std::runtime_error(
            RPCHelpMan{"listissuances",
                "\nList all issuances known to the wallet for the given asset, or for all issued assets if none provided.\n",
                {
                    {"asset", RPCArg::Type::STR, RPCArg::Optional::OMITTED, "The asset whose issaunces you wish to list. Accepts either the asset hex or the locally assigned asset label."},
                },
                RPCResult{
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
                },
                RPCExamples{
                    HelpExampleCli("listissuances", "<asset>")
            + HelpExampleRpc("listissuances", "<asset>")
                },
            }.ToString());

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    std::string assetstr;
    CAsset asset_filter;
    if (request.params.size() > 0) {
        assetstr = request.params[0].get_str();
        asset_filter = GetAssetFromString(assetstr);
    }

    UniValue issuancelist(UniValue::VARR);
    for (const auto& it : pwallet->mapWallet) {
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
            if (issuance.assetBlindingNonce.IsNull()) {
                GenerateAssetEntropy(entropy, pcoin->tx->vin[vinIndex].prevout, issuance.assetEntropy);
                CalculateAsset(asset, entropy);
                // Null is considered explicit
                CalculateReissuanceToken(token, entropy, issuance.nAmount.IsCommitment());
                item.pushKV("isreissuance", false);
                item.pushKV("token", token.GetHex());
                CAmount itamount = pcoin->GetIssuanceAmount(vinIndex, true);
                item.pushKV("tokenamount", (itamount == -1 ) ? -1 : ValueFromAmount(itamount));
                item.pushKV("tokenblinds", pcoin->GetIssuanceBlindingFactor(vinIndex, true).GetHex());
                item.pushKV("entropy", entropy.GetHex());
            } else {
                CalculateAsset(asset, issuance.assetEntropy);
                item.pushKV("isreissuance", true);
                item.pushKV("entropy", issuance.assetEntropy.GetHex());
            }
            item.pushKV("txid", pcoin->tx->GetHash().GetHex());
            item.pushKV("vin", vinIndex);
            item.pushKV("asset", asset.GetHex());
            const std::string label = gAssetsDir.GetLabel(asset);
            if (label != "") {
                item.pushKV("assetlabel", label);
            }
            CAmount iaamount = pcoin->GetIssuanceAmount(vinIndex, false);
            item.pushKV("assetamount", (iaamount == -1 ) ? -1 : ValueFromAmount(iaamount));
            item.pushKV("assetblinds", pcoin->GetIssuanceBlindingFactor(vinIndex, false).GetHex());
            if (!asset_filter.IsNull() && asset_filter != asset) {
                continue;
            }
            issuancelist.push_back(item);
        }
    }
    return issuancelist;

}

UniValue destroyamount(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    if (request.fHelp || request.params.size() < 1 || request.params.size() > 3)
        throw std::runtime_error(
            RPCHelpMan{"destroyamount",
                "\nDestroy an amount of a given asset.\n\n",
                {
                    {"asset", RPCArg::Type::STR, RPCArg::Optional::NO, "Hex asset id or asset label to destroy."},
                    {"amount", RPCArg::Type::AMOUNT, RPCArg::Optional::NO, "The amount to destroy (8 decimals above the minimal unit)."},
                    {"comment", RPCArg::Type::STR, RPCArg::Optional::OMITTED_NAMED_ARG, "A comment used to store what the transaction is for.\n"
            "                             This is not part of the transaction, just kept in your wallet."},
                },
                RPCResult{
            "\"transactionid\"  (string) The transaction id.\n"
                },
                RPCExamples{
                    HelpExampleCli("destroyamount", "\"bitcoin\" 100")
            + HelpExampleCli("destroyamount", "\"bitcoin\" 100 \"destroy assets\"")
            + HelpExampleRpc("destroyamount", "\"bitcoin\" 100 \"destroy assets\"")
                },
            }.ToString());

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    std::string strasset = request.params[0].get_str();
    CAsset asset = GetAssetFromString(strasset);

    CAmount nAmount = AmountFromValue(request.params[1]);
    if (nAmount <= 0) {
        throw JSONRPCError(RPC_TYPE_ERROR, "Invalid amount to destroy");
    }

    mapValue_t mapValue;
    if (request.params.size() > 2 && !request.params[2].isNull() && !request.params[2].get_str().empty()) {
        mapValue["comment"] = request.params[2].get_str();
    }

    EnsureWalletIsUnlocked(pwallet);

    NullData nulldata;
    CTxDestination address(nulldata);
    CCoinControl no_coin_control; // This is a deprecated API
    CTransactionRef tx = SendMoney(*locked_chain, pwallet, address, nAmount, asset, false, no_coin_control, std::move(mapValue), true);

    return tx->GetHash().GetHex();
}

// Only used for functionary integration tests
UniValue generatepegoutproof(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    if (request.fHelp || request.params.size() != 3)
        throw std::runtime_error(
            RPCHelpMan{"generatepegoutproof",
                "\nONLY FOR TESTING: Generates pegout authorization proof for pegout based on the summed privkey and returns in hex. Result should be passed as an argument in `sendtomainchain`. Caution: Whitelist proof-validating mempools will filter incorrect pegoutproofs but aren't consensus enforced!\n",
                {
                    {"sumkey", RPCArg::Type::STR, RPCArg::Optional::NO, "Base58 summed key of Bitcoin and offline key"},
                    {"btcpubkey", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "Hex pegout destination Bitcoin pubkey"},
                    {"onlinepubkey", RPCArg::Type::STR_HEX, RPCArg::Optional::NO, "hex `online pubkey`"},
                },
                RPCResult{
            "\"pegoutproof\"              (string, hex) pegout authorization proof to be passed into sendtomainchain\n"
                },
                RPCExamples{
                    HelpExampleCli("generatepegoutproof", "\"cQtNrRngdc4RJ9CkuTVKVLyxPFsijiTJySob24xCdKXGohdFhXML\" \"02c611095119e3dc96db428a0e190a3e142237bcd2efa4fb358257497885af3ab6\" \"0390695fff5535780df1e04c1f6c10e7c0a399fa56cfce34bf8108d0a9bc7a437b\"")
            + HelpExampleRpc("generatepegoutproof", "\"cQtNrRngdc4RJ9CkuTVKVLyxPFsijiTJySob24xCdKXGohdFhXML\" \"02c611095119e3dc96db428a0e190a3e142237bcd2efa4fb358257497885af3ab6\" \"0390695fff5535780df1e04c1f6c10e7c0a399fa56cfce34bf8108d0a9bc7a437b\"")
                },
            }.ToString());

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    if (!IsHex(request.params[1].get_str()))
        throw JSONRPCError(RPC_TYPE_ERROR, "btcpubkey must be hex string");
    if (!IsHex(request.params[2].get_str()))
        throw JSONRPCError(RPC_TYPE_ERROR, "onlinepubkey must be hex string");

    //Parse private keys

    CKey summedSecret = DecodeSecret(request.params[0].get_str());
    if (!summedSecret.IsValid()) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Invalid summed private key encoding");
    }

    std::vector<unsigned char> sumprivkeybytes(summedSecret.begin(), summedSecret.end());
    std::vector<unsigned char> btcpubkeybytes = ParseHex(request.params[1].get_str());
    std::vector<unsigned char> onlinepubkeybytes = ParseHex(request.params[2].get_str());

    //Parse onlinepubkey
    CPubKey onlinepubkey;
    onlinepubkey.Set(onlinepubkeybytes.begin(), onlinepubkeybytes.end());
    if (!onlinepubkey.IsFullyValid())
        throw JSONRPCError(RPC_WALLET_ERROR, "Invalid online pubkey");
    secp256k1_pubkey onlinepubkey_secp;
    if (!secp256k1_ec_pubkey_parse(secp256k1_ctx, &onlinepubkey_secp, &onlinepubkeybytes[0], onlinepubkeybytes.size()))
        throw JSONRPCError(RPC_WALLET_ERROR, "Invalid online pubkey");

    CPAKList paklist = GetActivePAKList(::ChainActive().Tip(), Params().GetConsensus());
    if (paklist.IsReject()) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Pegout freeze is under effect to aid a pak transition to a new list. Please consult the network operator.");
    }

    LegacyScriptPubKeyMan* spk_man = pwallet->GetLegacyScriptPubKeyMan();
    if (!spk_man) {
        throw JSONRPCError(RPC_WALLET_ERROR, "This type of wallet does not support this command");
    }

    //Find PAK online pubkey on PAK list
    int whitelistindex=-1;
    std::vector<secp256k1_pubkey> pak_online = paklist.OnlineKeys();
    for (unsigned int i=0; i<pak_online.size(); i++) {
        if (!memcmp((void *)&pak_online[i], (void *)&onlinepubkey_secp, sizeof(secp256k1_pubkey)))
            whitelistindex = i;
    }
    if (whitelistindex == -1)
        throw JSONRPCError(RPC_WALLET_ERROR, "Given online key is not in Pegout Authorization Key List");

    CKey masterOnlineKey;
    if (!spk_man->GetKey(onlinepubkey.GetID(), masterOnlineKey))
        throw JSONRPCError(RPC_WALLET_ERROR, "Given online key is in master set but not in wallet");

    //Parse own offline pubkey
    secp256k1_pubkey btcpubkey;
    if (secp256k1_ec_pubkey_parse(secp256k1_ctx, &btcpubkey, &btcpubkeybytes[0], btcpubkeybytes.size()) != 1)
        throw JSONRPCError(RPC_WALLET_ERROR, "btcpubkey is invalid pubkey");

    //Create, verify whitelist proof
    secp256k1_whitelist_signature sig;
    if(secp256k1_whitelist_sign(secp256k1_ctx, &sig, &paklist.OnlineKeys()[0], &paklist.OfflineKeys()[0], paklist.size(), &btcpubkey, masterOnlineKey.begin(), &sumprivkeybytes[0], whitelistindex, NULL, NULL) != 1)
        throw JSONRPCError(RPC_WALLET_ERROR, "Pegout authorization proof signing failed");

    if (secp256k1_whitelist_verify(secp256k1_ctx, &sig, &paklist.OnlineKeys()[0], &paklist.OfflineKeys()[0], paklist.size(), &btcpubkey) != 1)
        throw JSONRPCError(RPC_WALLET_ERROR, "Pegout authorization proof was created and signed but is invalid");

    //Serialize and return as hex
    size_t expectedOutputSize = 1 + 32 * (1 + paklist.size());
    const size_t preSize = expectedOutputSize;
    assert(1 + 32 * (1 + 256) >= expectedOutputSize);
    unsigned char output[1 + 32 * (1 + 256)];
    secp256k1_whitelist_signature_serialize(secp256k1_ctx, output, &expectedOutputSize, &sig);
    assert(expectedOutputSize == preSize);
    std::vector<unsigned char> voutput(output, output + expectedOutputSize / sizeof(output[0]));

    return HexStr(voutput.begin(), voutput.end());
}

// Only used for functionary integration tests
UniValue getpegoutkeys(const JSONRPCRequest& request)
{
    std::shared_ptr<CWallet> const wallet = GetWalletForJSONRPCRequest(request);
    CWallet* const pwallet = wallet.get();

    if (!EnsureWalletIsAvailable(pwallet, request.fHelp)) {
        return NullUniValue;
    }

    if (request.fHelp || request.params.size() != 2)
        throw std::runtime_error(
            RPCHelpMan{"getpegoutkeys",
                "\n(DEPRECATED) Please see `initpegoutwallet` and `sendtomainchain` for best-supported and easiest workflow. This call is for the Liquid network participants' `offline` wallet ONLY. Returns `sumkeys` corresponding to the sum of the Offline PAK and the imported Bitcoin key. The wallet must have the Offline private PAK to succeed. The output will be used in `generatepegoutproof` and `sendtomainchain`. Care is required to keep the bitcoin private key, as well as the `sumkey` safe, as a leak of both results in the leak of your `offlinekey`. Therefore it is recommended to create Bitcoin keys and do Bitcoin transaction signing directly on an offline wallet co-located with your offline Liquid wallet.\n",
                {
                    {"btcprivkey", RPCArg::Type::STR, RPCArg::Optional::NO, "Base58 Bitcoin private key that will be combined with the offline privkey"},
                    {"offlinepubkey", RPCArg::Type::STR_HEX, RPCArg::Optional::OMITTED_NAMED_ARG, "Hex pubkey of key to combine with btcprivkey. Primarily intended for integration testing."},
                },
                RPCResult{
            "\"sumkey\"              (string) Base58 string of the sumkey.\n"
            "\"btcpubkey\"           (string) Hex string of the bitcoin pubkey that corresponds to the pegout destination Bitcoin address\n"
            "\"btcaddress\"          (string) Destination Bitcoin address for the funds being pegged out using these keys"
                },
                RPCExamples{
                    HelpExampleCli("getpegoutkeys", "")
            + HelpExampleCli("getpegoutkeys", "\"5Kb8kLf9zgWQnogidDA76MzPL6TsZZY36hWXMssSzNydYXYB9KF\" \"0389275d512326f7016e014d8625f709c01f23bd0dc16522bf9845a9ee1ef6cbf9\"")
            + HelpExampleRpc("getpegoutkeys", "")
           + HelpExampleRpc("getpegoutkeys", "\"5Kb8kLf9zgWQnogidDA76MzPL6TsZZY36hWXMssSzNydYXYB9KF\", \"0389275d512326f7016e014d8625f709c01f23bd0dc16522bf9845a9ee1ef6cbf9\"")
                },
            }.ToString());

    auto locked_chain = pwallet->chain().lock();
    LOCK(pwallet->cs_wallet);

    LegacyScriptPubKeyMan* spk_man = pwallet->GetLegacyScriptPubKeyMan();
    if (!spk_man) {
        throw JSONRPCError(RPC_WALLET_ERROR, "This type of wallet does not support this command");
    }

    if (!request.params[1].isStr() || !IsHex(request.params[1].get_str()) || request.params[1].get_str().size() != 66) {
        throw JSONRPCError(RPC_TYPE_ERROR, "offlinepubkey must be hex string of size 66");
    }

    std::vector<unsigned char> offlinepubbytes = ParseHex(request.params[1].get_str());
    CPubKey offline_pub = CPubKey(offlinepubbytes.begin(), offlinepubbytes.end());

    if (!offline_pub.IsFullyValid()) {
        throw JSONRPCError(RPC_TYPE_ERROR, "offlinepubkey is not a valid pubkey");
    }

    CKey pegoutkey;
    if (!spk_man->GetKey(offline_pub.GetID(), pegoutkey))
        throw JSONRPCError(RPC_WALLET_ERROR, "Offline key can not be found in wallet");

    CKey bitcoinkey = DecodeSecret(request.params[0].get_str());
    if (!bitcoinkey.IsValid()) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY, "Private key outside allowed range");
    }

    CPubKey bitcoinpubkey = bitcoinkey.GetPubKey();
    assert(bitcoinkey.VerifyPubKey(bitcoinpubkey));

    std::vector<unsigned char> pegoutkeybytes(pegoutkey.begin(), pegoutkey.end());
    std::vector<unsigned char> pegoutsubkeybytes(bitcoinkey.begin(), bitcoinkey.end());

    if (!secp256k1_ec_privkey_tweak_add(secp256k1_ctx, &pegoutkeybytes[0], &pegoutsubkeybytes[0]))
        throw JSONRPCError(RPC_WALLET_ERROR, "Summed key invalid");

    CKey sumseckey;
    sumseckey.Set(pegoutkeybytes.begin(), pegoutkeybytes.end(), true);

    UniValue ret(UniValue::VOBJ);
    ret.pushKV("sumkey", EncodeSecret(sumseckey));
    ret.pushKV("btcpubkey", HexStr(bitcoinpubkey.begin(), bitcoinpubkey.end()));
    ret.pushKV("btcaddress", EncodeParentDestination(PKHash(bitcoinpubkey.GetID())));

    return ret;
}

// END ELEMENTS commands
//

UniValue abortrescan(const JSONRPCRequest& request); // in rpcdump.cpp
UniValue dumpprivkey(const JSONRPCRequest& request); // in rpcdump.cpp
UniValue importblindingkey(const JSONRPCRequest& request); // in rpcdump.cpp
UniValue importmasterblindingkey(const JSONRPCRequest& request); // in rpcdump.cpp
UniValue importissuanceblindingkey(const JSONRPCRequest& request); // in rpcdump.cpp
UniValue dumpblindingkey(const JSONRPCRequest& request); // in rpcdump.cpp
UniValue dumpmasterblindingkey(const JSONRPCRequest& request); // in rpcdump.cpp
UniValue dumpissuanceblindingkey(const JSONRPCRequest& request); // in rpcdump.cpp
UniValue importprivkey(const JSONRPCRequest& request);
UniValue importaddress(const JSONRPCRequest& request);
UniValue importpubkey(const JSONRPCRequest& request);
UniValue dumpwallet(const JSONRPCRequest& request);
UniValue importwallet(const JSONRPCRequest& request);
UniValue importprunedfunds(const JSONRPCRequest& request);
UniValue removeprunedfunds(const JSONRPCRequest& request);
UniValue importmulti(const JSONRPCRequest& request);
UniValue getwalletpakinfo(const JSONRPCRequest& request);

// clang-format off
static const CRPCCommand commands[] =
{ //  category              name                                actor (function)                argNames
    //  --------------------- ------------------------          -----------------------         ----------
    { "rawtransactions",    "fundrawtransaction",               &fundrawtransaction,            {"hexstring","options","iswitness","solving_data"} },
    { "wallet",             "abandontransaction",               &abandontransaction,            {"txid"} },
    { "wallet",             "abortrescan",                      &abortrescan,                   {} },
    { "wallet",             "addmultisigaddress",               &addmultisigaddress,            {"nrequired","keys","label","address_type"} },
    { "wallet",             "backupwallet",                     &backupwallet,                  {"destination"} },
    { "wallet",             "bumpfee",                          &bumpfee,                       {"txid", "options"} },
    { "wallet",             "createwallet",                     &createwallet,                  {"wallet_name", "disable_private_keys", "blank", "passphrase", "avoid_reuse"} },
    { "wallet",             "dumpprivkey",                      &dumpprivkey,                   {"address"}  },
    { "wallet",             "dumpwallet",                       &dumpwallet,                    {"filename"} },
    { "wallet",             "encryptwallet",                    &encryptwallet,                 {"passphrase"} },
    { "wallet",             "getaddressesbylabel",              &getaddressesbylabel,           {"label"} },
    { "wallet",             "getaddressinfo",                   &getaddressinfo,                {"address"} },
    { "wallet",             "getbalance",                       &getbalance,                    {"dummy","minconf","include_watchonly","avoid_reuse","assetlabel"} },
    { "wallet",             "getnewaddress",                    &getnewaddress,                 {"label","address_type"} },
    { "wallet",             "getrawchangeaddress",              &getrawchangeaddress,           {"address_type"} },
    { "wallet",             "getreceivedbyaddress",             &getreceivedbyaddress,          {"address","minconf","assetlabel"} },
    { "wallet",             "getreceivedbylabel",               &getreceivedbylabel,            {"label","minconf","assetlabel"} },
    { "wallet",             "gettransaction",                   &gettransaction,                {"txid","include_watchonly","verbose","assetlabel"} },
    { "wallet",             "getunconfirmedbalance",            &getunconfirmedbalance,         {} },
    { "wallet",             "getbalances",                      &getbalances,                   {} },
    { "wallet",             "getwalletinfo",                    &getwalletinfo,                 {} },
    { "wallet",             "importaddress",                    &importaddress,                 {"address","label","rescan","p2sh"} },
    { "wallet",             "importmulti",                      &importmulti,                   {"requests","options"} },
    { "wallet",             "importprivkey",                    &importprivkey,                 {"privkey","label","rescan"} },
    { "wallet",             "importprunedfunds",                &importprunedfunds,             {"rawtransaction","txoutproof"} },
    { "wallet",             "importpubkey",                     &importpubkey,                  {"pubkey","label","rescan"} },
    { "wallet",             "importwallet",                     &importwallet,                  {"filename"} },
    { "wallet",             "keypoolrefill",                    &keypoolrefill,                 {"newsize"} },
    { "wallet",             "listaddressgroupings",             &listaddressgroupings,          {} },
    { "wallet",             "listlabels",                       &listlabels,                    {"purpose"} },
    { "wallet",             "listlockunspent",                  &listlockunspent,               {} },
    { "wallet",             "listreceivedbyaddress",            &listreceivedbyaddress,         {"minconf","include_empty","include_watchonly","address_filter","assetlabel"} },
    { "wallet",             "listreceivedbylabel",              &listreceivedbylabel,           {"minconf","include_empty","include_watchonly"} },
    { "wallet",             "listsinceblock",                   &listsinceblock,                {"blockhash","target_confirmations","include_watchonly","include_removed"} },
    { "wallet",             "listtransactions",                 &listtransactions,              {"label|dummy","count","skip","include_watchonly"} },
    { "wallet",             "listunspent",                      &listunspent,                   {"minconf","maxconf","addresses","include_unsafe","query_options"} },
    { "wallet",             "listwalletdir",                    &listwalletdir,                 {} },
    { "wallet",             "listwallets",                      &listwallets,                   {} },
    { "wallet",             "loadwallet",                       &loadwallet,                    {"filename"} },
    { "wallet",             "lockunspent",                      &lockunspent,                   {"unlock","transactions"} },
    { "wallet",             "removeprunedfunds",                &removeprunedfunds,             {"txid"} },
    { "wallet",             "rescanblockchain",                 &rescanblockchain,              {"start_height", "stop_height"} },
    { "wallet",             "sendmany",                         &sendmany,                      {"dummy","amounts","minconf","comment","subtractfeefrom","replaceable","conf_target","estimate_mode", "output_assets", "ignoreblindfail"} },
    { "wallet",             "sendtoaddress",                    &sendtoaddress,                 {"address","amount","comment","comment_to","subtractfeefromamount","replaceable","conf_target","estimate_mode","avoid_reuse", "assetlabel", "ignorblindfail"} },
    { "wallet",             "sethdseed",                        &sethdseed,                     {"newkeypool","seed"} },
    { "wallet",             "setlabel",                         &setlabel,                      {"address","label"} },
    { "wallet",             "settxfee",                         &settxfee,                      {"amount"} },
    { "wallet",             "setwalletflag",                    &setwalletflag,                 {"flag","value"} },
    { "wallet",             "signmessage",                      &signmessage,                   {"address","message"} },
    { "wallet",             "signrawtransactionwithwallet",     &signrawtransactionwithwallet,  {"hexstring","prevtxs","sighashtype"} },
    { "wallet",             "unloadwallet",                     &unloadwallet,                  {"wallet_name"} },
    { "wallet",             "walletcreatefundedpsbt",           &walletcreatefundedpsbt,        {"inputs","outputs","locktime","options","bip32derivs","solving_data"} },
    { "wallet",             "walletlock",                       &walletlock,                    {} },
    { "wallet",             "walletpassphrase",                 &walletpassphrase,              {"passphrase","timeout"} },
    { "wallet",             "walletpassphrasechange",           &walletpassphrasechange,        {"oldpassphrase","newpassphrase"} },
    { "wallet",             "walletprocesspsbt",                &walletprocesspsbt,             {"psbt","sign","sighashtype","bip32derivs"} },
    { "wallet",             "walletfillpsbtdata",               &walletfillpsbtdata,            {"psbt","bip32derivs"} },
    { "wallet",             "walletsignpsbt",                   &walletsignpsbt,                {"psbt","sighashtype","imbalance_ok"} },
    // ELEMENTS:
    { "wallet",             "getpeginaddress",                  &getpeginaddress,               {} },
    { "wallet",             "claimpegin",                       &claimpegin,                    {"bitcoin_tx", "txoutproof", "claim_script"} },
    { "wallet",             "createrawpegin",                   &createrawpegin,                {"bitcoin_tx", "txoutproof", "claim_script"} },
    { "wallet",             "blindrawtransaction",              &blindrawtransaction,           {"hexstring", "ignoreblindfail", "asset_commitments", "blind_issuances", "totalblinder"} },
    { "wallet",             "unblindrawtransaction",            &unblindrawtransaction,         {"hex"} },
    { "wallet",             "sendtomainchain",                  &sendtomainchain,               {"address", "amount", "subtractfeefromamount"} },
    { "wallet",             "initpegoutwallet",                 &initpegoutwallet,              {"bitcoin_descriptor", "bip32_counter", "liquid_pak"} },
    { "wallet",             "getwalletpakinfo",                 &getwalletpakinfo,              {} },
    { "wallet",             "importblindingkey",                &importblindingkey,             {"address", "hexkey"}},
    { "wallet",             "importmasterblindingkey",          &importmasterblindingkey,       {"hexkey"}},
    { "wallet",             "importissuanceblindingkey",        &importissuanceblindingkey,     {"txid", "vin", "blindingkey"}},
    { "wallet",             "dumpblindingkey",                  &dumpblindingkey,               {"address"}},
    { "wallet",             "dumpmasterblindingkey",            &dumpmasterblindingkey,         {}},
    { "wallet",             "dumpissuanceblindingkey",          &dumpissuanceblindingkey,       {"txid", "vin"}},
    { "wallet",             "signblock",                        &signblock,                     {"blockhex", "witnessScript"}},
    { "wallet",             "listissuances",                    &listissuances,                 {"asset"}},
    { "wallet",             "issueasset",                       &issueasset,                    {"assetamount", "tokenamount", "blind"}},
    { "wallet",             "reissueasset",                     &reissueasset,                  {"asset", "assetamount"}},
    { "wallet",             "destroyamount",                    &destroyamount,                 {"asset", "amount", "comment"} },
    { "hidden",             "generatepegoutproof",              &generatepegoutproof,           {"sumkey", "btcpubkey", "onlinepubkey"} },
    { "hidden",             "getpegoutkeys",                    &getpegoutkeys,                 {"btcprivkey", "offlinepubkey"} },
};
// clang-format on

void RegisterWalletRPCCommands(interfaces::Chain& chain, std::vector<std::unique_ptr<interfaces::Handler>>& handlers)
{
    for (unsigned int vcidx = 0; vcidx < ARRAYLEN(commands); vcidx++)
        handlers.emplace_back(chain.handleRpc(commands[vcidx]));
}

interfaces::Chain* g_rpc_chain = nullptr;
