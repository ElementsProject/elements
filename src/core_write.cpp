// Copyright (c) 2009-2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <core_io.h>

#include <consensus/consensus.h>
#include <consensus/validation.h>
#include <issuance.h>
#include <key_io.h>
#include <script/script.h>
#include <script/sign.h>
#include <script/standard.h>
#include <serialize.h>
#include <streams.h>
#include <undo.h>
#include <univalue.h>
#include <util/check.h>
#include <util/strencodings.h>
#include <util/system.h>

#include <secp256k1_rangeproof.h>

static secp256k1_context* secp256k1_blind_context = NULL;

class RPCRawTransaction_ECC_Init {
public:
    RPCRawTransaction_ECC_Init() {
        assert(secp256k1_blind_context == NULL);

        secp256k1_context *ctx = secp256k1_context_create(SECP256K1_CONTEXT_NONE);
        assert(ctx != NULL);

        secp256k1_blind_context = ctx;
    }

    ~RPCRawTransaction_ECC_Init() {
        secp256k1_context *ctx = secp256k1_blind_context;
        secp256k1_blind_context = NULL;

        if (ctx) {
            secp256k1_context_destroy(ctx);
        }
    }
};
static RPCRawTransaction_ECC_Init ecc_init_on_load;

UniValue ValueFromAmount(const CAmount amount)
{
    static_assert(COIN > 1);
    int64_t quotient = amount / COIN;
    int64_t remainder = amount % COIN;
    if (amount < 0) {
        quotient = -quotient;
        remainder = -remainder;
    }
    return UniValue(UniValue::VNUM,
            strprintf("%s%d.%08d", amount < 0 ? "-" : "", quotient, remainder));
}

std::string FormatScript(const CScript& script)
{
    std::string ret;
    CScript::const_iterator it = script.begin();
    opcodetype op;
    while (it != script.end()) {
        CScript::const_iterator it2 = it;
        std::vector<unsigned char> vch;
        if (script.GetOp(it, op, vch)) {
            if (op == OP_0) {
                ret += "0 ";
                continue;
            } else if ((op >= OP_1 && op <= OP_16) || op == OP_1NEGATE) {
                ret += strprintf("%i ", op - OP_1NEGATE - 1);
                continue;
            } else if (op >= OP_NOP && op <= OP_NOP10) {
                std::string str(GetOpName(op));
                if (str.substr(0, 3) == std::string("OP_")) {
                    ret += str.substr(3, std::string::npos) + " ";
                    continue;
                }
            }
            if (vch.size() > 0) {
                ret += strprintf("0x%x 0x%x ", HexStr(std::vector<uint8_t>(it2, it - vch.size())),
                                               HexStr(std::vector<uint8_t>(it - vch.size(), it)));
            } else {
                ret += strprintf("0x%x ", HexStr(std::vector<uint8_t>(it2, it)));
            }
            continue;
        }
        ret += strprintf("0x%x ", HexStr(std::vector<uint8_t>(it2, script.end())));
        break;
    }
    return ret.substr(0, ret.size() - 1);
}

const std::map<unsigned char, std::string> mapSigHashTypes = {
    {static_cast<unsigned char>(SIGHASH_ALL), std::string("ALL")},
    {static_cast<unsigned char>(SIGHASH_ALL|SIGHASH_ANYONECANPAY), std::string("ALL|ANYONECANPAY")},
    {static_cast<unsigned char>(SIGHASH_NONE), std::string("NONE")},
    {static_cast<unsigned char>(SIGHASH_NONE|SIGHASH_ANYONECANPAY), std::string("NONE|ANYONECANPAY")},
    {static_cast<unsigned char>(SIGHASH_SINGLE), std::string("SINGLE")},
    {static_cast<unsigned char>(SIGHASH_SINGLE|SIGHASH_ANYONECANPAY), std::string("SINGLE|ANYONECANPAY")},
};

std::string SighashToStr(unsigned char sighash_type)
{
    const auto& it = mapSigHashTypes.find(sighash_type);
    if (it == mapSigHashTypes.end()) return "";
    return it->second;
}

/**
 * Create the assembly string representation of a CScript object.
 * @param[in] script    CScript object to convert into the asm string representation.
 * @param[in] fAttemptSighashDecode    Whether to attempt to decode sighash types on data within the script that matches the format
 *                                     of a signature. Only pass true for scripts you believe could contain signatures. For example,
 *                                     pass false, or omit the this argument (defaults to false), for scriptPubKeys.
 */
std::string ScriptToAsmStr(const CScript& script, const bool fAttemptSighashDecode)
{
    std::string str;
    opcodetype opcode;
    std::vector<unsigned char> vch;
    CScript::const_iterator pc = script.begin();
    while (pc < script.end()) {
        if (!str.empty()) {
            str += " ";
        }
        if (!script.GetOp(pc, opcode, vch)) {
            str += "[error]";
            return str;
        }
        if (0 <= opcode && opcode <= OP_PUSHDATA4) {
            if (vch.size() <= static_cast<std::vector<unsigned char>::size_type>(4)) {
                str += strprintf("%d", CScriptNum(vch, false).getint());
            } else {
                // the IsUnspendable check makes sure not to try to decode OP_RETURN data that may match the format of a signature
                if (fAttemptSighashDecode && !script.IsUnspendable()) {
                    std::string strSigHashDecode;
                    // goal: only attempt to decode a defined sighash type from data that looks like a signature within a scriptSig.
                    // this won't decode correctly formatted public keys in Pubkey or Multisig scripts due to
                    // the restrictions on the pubkey formats (see IsCompressedOrUncompressedPubKey) being incongruous with the
                    // checks in CheckSignatureEncoding.
                    if (CheckSignatureEncoding(vch, SCRIPT_VERIFY_STRICTENC, nullptr)) {
                        const unsigned char chSigHashType = vch.back();
                        const auto it = mapSigHashTypes.find(chSigHashType);
                        if (it != mapSigHashTypes.end()) {
                            strSigHashDecode = "[" + it->second + "]";
                            vch.pop_back(); // remove the sighash type byte. it will be replaced by the decode.
                        }
                    }
                    str += HexStr(vch) + strSigHashDecode;
                } else {
                    str += HexStr(vch);
                }
            }
        } else {
            str += GetOpName(opcode);
        }
    }
    return str;
}

std::string EncodeHexTx(const CTransaction& tx, const int serializeFlags)
{
    CDataStream ssTx(SER_NETWORK, PROTOCOL_VERSION | serializeFlags);
    ssTx << tx;
    return HexStr(ssTx);
}

void ScriptToUniv(const CScript& script, UniValue& out, bool include_address)
{
    out.pushKV("asm", ScriptToAsmStr(script));
    out.pushKV("hex", HexStr(script));

    std::vector<std::vector<unsigned char>> solns;
    TxoutType type = Solver(script, solns);
    out.pushKV("type", GetTxnOutputType(type));

    CTxDestination address;
    if (include_address && ExtractDestination(script, address) && type != TxoutType::PUBKEY) {
        out.pushKV("address", EncodeDestination(address));
    }
}

// ELEMENTS:
static void SidechainScriptPubKeyToJSON(const CScript& scriptPubKey, UniValue& out, bool fIncludeHex, bool include_addresses, bool is_parent_chain)
{
    const std::string prefix = is_parent_chain ? "pegout_" : "";
    TxoutType type;
    CTxDestination address;
    std::vector<CTxDestination> addresses;
    int nRequired;

    out.pushKV(prefix + "asm", ScriptToAsmStr(scriptPubKey));
    if (fIncludeHex)
        out.pushKV(prefix + "hex", HexStr(scriptPubKey));

    if (!ExtractDestinations(scriptPubKey, type, addresses, nRequired) || type == TxoutType::PUBKEY) {
        out.pushKV(prefix + "type", GetTxnOutputType(type));
        return;
    }

    if (ExtractDestination(scriptPubKey, address)) {
        if (is_parent_chain) {
            out.pushKV(prefix + "address", EncodeParentDestination(address));
        } else {
            out.pushKV(prefix + "address", EncodeDestination(address));
        }
    }
    out.pushKV(prefix + "type", GetTxnOutputType(type));

    if (include_addresses) {
        UniValue a(UniValue::VARR);
        if (is_parent_chain) {
            for (const CTxDestination& addr : addresses) {
                a.push_back(EncodeParentDestination(addr));
            }
        } else {
            for (const CTxDestination& addr : addresses) {
                a.push_back(EncodeDestination(addr));
            }
        }
        out.pushKV(prefix + "addresses", a);
        out.pushKV(prefix + "reqSigs", nRequired);
    }
}

// TODO: from v23 ("addresses" and "reqSigs" deprecated) this method should be refactored to remove the `include_addresses` option
// this method can also be combined with `ScriptToUniv` as they will overlap
void ScriptPubKeyToUniv(const CScript& scriptPubKey,
                        UniValue& out, bool fIncludeHex, bool include_addresses)
{
    SidechainScriptPubKeyToJSON(scriptPubKey, out, fIncludeHex, include_addresses, false);

    uint256 pegout_chain;
    CScript pegout_scriptpubkey;
    if (scriptPubKey.IsPegoutScript(pegout_chain, pegout_scriptpubkey)) {
        out.pushKV("pegout_chain", pegout_chain.GetHex());
        SidechainScriptPubKeyToJSON(pegout_scriptpubkey, out, fIncludeHex, include_addresses, true);
    }
}

void TxToUniv(const CTransaction& tx, const uint256& hashBlock, bool include_addresses, UniValue& entry, bool include_hex, int serialize_flags, const CTxUndo* txundo)
{
    entry.pushKV("txid", tx.GetHash().GetHex());
    entry.pushKV("hash", tx.GetWitnessHash().GetHex());
    if (g_con_elementsmode) {
        entry.pushKV("wtxid", tx.GetWitnessHash().GetHex());
        entry.pushKV("withash", tx.GetWitnessOnlyHash().GetHex());
    }
    // Transaction version is actually unsigned in consensus checks, just signed in memory,
    // so cast to unsigned before giving it to the user.
    entry.pushKV("version", static_cast<int64_t>(static_cast<uint32_t>(tx.nVersion)));
    entry.pushKV("size", (int)::GetSerializeSize(tx, PROTOCOL_VERSION));
    entry.pushKV("vsize", (GetTransactionWeight(tx) + WITNESS_SCALE_FACTOR - 1) / WITNESS_SCALE_FACTOR);
    entry.pushKV("weight", GetTransactionWeight(tx));
    entry.pushKV("locktime", (int64_t)tx.nLockTime);

    UniValue vin{UniValue::VARR};

    for (unsigned int i = 0; i < tx.vin.size(); i++) {
        const CTxIn& txin = tx.vin[i];
        UniValue in(UniValue::VOBJ);
        if (tx.IsCoinBase()) {
            in.pushKV("coinbase", HexStr(txin.scriptSig));
        } else {
            in.pushKV("txid", txin.prevout.hash.GetHex());
            in.pushKV("vout", (int64_t)txin.prevout.n);
            UniValue o(UniValue::VOBJ);
            o.pushKV("asm", ScriptToAsmStr(txin.scriptSig, true));
            o.pushKV("hex", HexStr(txin.scriptSig));
            in.pushKV("scriptSig", o);
            in.pushKV("is_pegin", txin.m_is_pegin);
        }
        in.pushKV("sequence", (int64_t)txin.nSequence);

        // ELEMENTS:
        if (tx.witness.vtxinwit.size() > i) {
            const CScriptWitness &scriptWitness = tx.witness.vtxinwit[i].scriptWitness;
            if (!scriptWitness.IsNull()) {
                UniValue txinwitness(UniValue::VARR);
                for (const auto &item : scriptWitness.stack) {
                    txinwitness.push_back(HexStr(item));
                }
                in.pushKV("txinwitness", txinwitness);
            }
        }

        if (tx.witness.vtxinwit.size() > i && !tx.witness.vtxinwit[i].m_pegin_witness.IsNull()) {
            UniValue pegin_witness(UniValue::VARR);
            for (const auto& item : tx.witness.vtxinwit[i].m_pegin_witness.stack) {
                pegin_witness.push_back(HexStr(item));
            }
            in.pushKV("pegin_witness", pegin_witness);
        }
        const CAssetIssuance& issuance = txin.assetIssuance;
        if (!issuance.IsNull()) {
            UniValue issue(UniValue::VOBJ);
            issue.pushKV("assetBlindingNonce", issuance.assetBlindingNonce.GetHex());
            CAsset asset;
            CAsset token;
            uint256 entropy;
            if (issuance.assetBlindingNonce.IsNull()) {
                GenerateAssetEntropy(entropy, txin.prevout, issuance.assetEntropy);
                issue.pushKV("assetEntropy", entropy.GetHex());
                CalculateAsset(asset, entropy);
                CalculateReissuanceToken(token, entropy, issuance.nAmount.IsCommitment());
                issue.pushKV("isreissuance", false);
                issue.pushKV("token", token.GetHex());
            }
            else {
                issue.pushKV("assetEntropy", issuance.assetEntropy.GetHex());
                issue.pushKV("isreissuance", true);
                CalculateAsset(asset, issuance.assetEntropy);
            }
            issue.pushKV("asset", asset.GetHex());

            if (issuance.nAmount.IsExplicit()) {
                issue.pushKV("assetamount", ValueFromAmount(issuance.nAmount.GetAmount()));
            } else if (issuance.nAmount.IsCommitment()) {
                issue.pushKV("assetamountcommitment", HexStr(issuance.nAmount.vchCommitment));
            }
            if (issuance.nInflationKeys.IsExplicit()) {
                issue.pushKV("tokenamount", ValueFromAmount(issuance.nInflationKeys.GetAmount()));
            } else if (issuance.nInflationKeys.IsCommitment()) {
                issue.pushKV("tokenamountcommitment", HexStr(issuance.nInflationKeys.vchCommitment));
            }
            in.pushKV("issuance", issue);
        }
        // END ELEMENTS

        vin.push_back(in);
    }
    entry.pushKV("vin", vin);

    CAmountMap fee_map{};
    UniValue vout(UniValue::VARR);
    for (unsigned int i = 0; i < tx.vout.size(); i++) {
        const CTxOut& txout = tx.vout[i];

        UniValue out(UniValue::VOBJ);

        if (txout.nValue.IsExplicit()) {
            out.pushKV("value", ValueFromAmount(txout.nValue.GetAmount()));
        } else {
            int exp;
            int mantissa;
            uint64_t minv;
            uint64_t maxv;
            const CTxOutWitness* ptxoutwit = tx.witness.vtxoutwit.size() <= i? NULL: &tx.witness.vtxoutwit[i];
            if (ptxoutwit) {
                if (ptxoutwit->vchRangeproof.size() && secp256k1_rangeproof_info(secp256k1_blind_context, &exp, &mantissa, &minv, &maxv, &ptxoutwit->vchRangeproof[0], ptxoutwit->vchRangeproof.size())) {
                    if (exp == -1) {
                        out.pushKV("value", ValueFromAmount((CAmount)minv));
                    } else {
                        out.pushKV("value-minimum", ValueFromAmount((CAmount)minv));
                        out.pushKV("value-maximum", ValueFromAmount((CAmount)maxv));
                    }
                    out.pushKV("ct-exponent", exp);
                    out.pushKV("ct-bits", mantissa);
                }

                if (ptxoutwit->vchSurjectionproof.size()) {
                    out.pushKV("surjectionproof", HexStr(ptxoutwit->vchSurjectionproof));
                }
            }
            out.pushKV("valuecommitment", txout.nValue.GetHex());
        }
        if (g_con_elementsmode) {
            if (txout.IsFee()) {
                fee_map[txout.nAsset.GetAsset()] += txout.nValue.GetAmount();
            }

            if (txout.nAsset.IsExplicit()) {
                out.pushKV("asset", txout.nAsset.GetAsset().GetHex());
            } else {
                out.pushKV("assetcommitment", txout.nAsset.GetHex());
            }

            out.pushKV("commitmentnonce", txout.nNonce.GetHex());
            CPubKey pubkey(txout.nNonce.vchCommitment);
            out.pushKV("commitmentnonce_fully_valid", pubkey.IsFullyValid());
        }
        out.pushKV("n", (int64_t)i);

        UniValue o(UniValue::VOBJ);
        ScriptPubKeyToUniv(txout.scriptPubKey, o, true, include_addresses);
        out.pushKV("scriptPubKey", o);
        vout.push_back(out);
    }
    entry.pushKV("vout", vout);

    // ELEMENTS: add fee map rather than single fee. Unlike other areas of the RPC,
    //  we do not look up labels here and will always use the asset hex (contrast
    //  `AmountMapToUniv` in rpc/util.cpp. This is because this is a pure function
    //  so we do not have access to `policyAsset` or `gAssetsDir`. (We will get link
    //  errors if we try to use these.)
    if (g_con_elementsmode) {
        UniValue fee_obj(UniValue::VOBJ);
        for(std::map<CAsset, CAmount>::const_iterator it = fee_map.begin(); it != fee_map.end(); ++it) {
            fee_obj.pushKV(it->first.GetHex(), ValueFromAmount(it->second));
        }
        entry.pushKV("fee", fee_obj);
    }

    if (!hashBlock.IsNull())
        entry.pushKV("blockhash", hashBlock.GetHex());

    if (include_hex) {
        entry.pushKV("hex", EncodeHexTx(tx, serialize_flags)); // The hex-encoded transaction. Used the name "hex" to be consistent with the verbose output of "getrawtransaction".
    }
}
