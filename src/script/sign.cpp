// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2014 The Bitcoin developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "script/sign.h"

#include "primitives/transaction.h"
#include "pubkey.h"
#include "key.h"
#include "keystore.h"
#include "script/standard.h"
#include "uint256.h"

#include <boost/foreach.hpp>

using namespace std;

typedef vector<unsigned char> valtype;

TransactionSignatureCreator::TransactionSignatureCreator(const CKeyStore& keystoreIn, const CTransaction* txToIn, unsigned int nInIn, const CTxOutValue& nValueIn, int nHashTypeIn) : BaseSignatureCreator(keystoreIn), txTo(txToIn), nIn(nInIn), nHashType(nHashTypeIn), checker(txTo, nIn, nValueIn) {}

bool TransactionSignatureCreator::CreateSig(std::vector<unsigned char>& vchSig, const CKeyID& address, const CScript& scriptCode) const
{
    CKey key;
    if (!keystore.GetKey(address, key))
        return false;

    uint256 hash = SignatureHash(scriptCode, checker.GetValueIn(), *txTo, nIn, nHashType);
    if (!key.Sign(hash, vchSig))
        return false;
    vchSig.push_back((unsigned char)nHashType);
    return true;
}

bool TransactionSignatureCreator::CreatePartialSigNonce(std::vector<unsigned char>& nonce, const CKeyID& keyid, const CScript& scriptCode) const
{
    CKey key;
    if (!keystore.GetKey(keyid, key))
        return false;

    uint256 hash = SignatureHash(scriptCode, checker.GetValueIn(), *txTo, nIn, nHashType);
    return key.PartialSigningNonce(hash, nonce);
}

bool TransactionSignatureCreator::CreatePartialSig(std::vector<unsigned char>& vchSig, const CKeyID& keyid, const CScript& scriptCode, const std::vector<unsigned char>& my_pubnonce, const std::vector<std::vector<unsigned char> >& other_pubnonces, const std::vector<CPubKey>& other_pubkeys) const
{
    CKey key;
    if (!keystore.GetKey(keyid, key))
        return false;

    uint256 hash = SignatureHash(scriptCode, checker.GetValueIn(), *txTo, nIn, nHashType);
    return key.PartialSign(hash, other_pubnonces, other_pubkeys, my_pubnonce, vchSig);
}

bool TransactionSignatureCreator::CombinePartialSigs(std::vector<unsigned char>& out, const std::vector<std::vector<unsigned char> >& ins) const
{
    if (!CombinePartialSignatures(ins, out))
        return false;
    out.push_back((unsigned char)nHashType);
    return true;
}

static bool Sign1(const CKeyID& address, const BaseSignatureCreator& creator, const CScript& scriptCode, CScript& scriptSigRet)
{
    vector<unsigned char> vchSig;
    if (!creator.CreateSig(vchSig, address, scriptCode))
        return false;
    scriptSigRet << vchSig;
    return true;
}

static bool SignN(const vector<valtype>& multisigdata, const BaseSignatureCreator& creator, const CScript& scriptCode, CScript& scriptSigRet)
{
    int nSigned = 0;
    int nRequired = multisigdata.front()[0];
    for (unsigned int i = 1; i < multisigdata.size()-1 && nSigned < nRequired; i++)
    {
        const valtype& pubkey = multisigdata[i];
        CKeyID keyID = CPubKey(pubkey).GetID();
        if (Sign1(keyID, creator, scriptCode, scriptSigRet))
            ++nSigned;
    }
    return nSigned==nRequired;
}

static bool ParsePartialTreeSig(const std::vector<valtype>& parsedSig, std::map<CPubKey, valtype>& mapNonces, std::map<std::pair<CPubKey, CPubKey>, valtype>& mapSigs) {
    for (std::vector<valtype>::const_iterator it = parsedSig.begin(); it != parsedSig.end(); ++it) {
        const valtype& data = *it;
        CPubKey key, key2;
        if (data.size() == 0) continue;
        if (data[0] == 0 && data.size() > 34) {
            key.Set(data.begin() + 1, data.begin() + 34);
            if (!key.IsValid()) return false;
            mapNonces[key] = valtype(data.begin() + 34, data.end());
        } else if (data[0] == 1 && data.size() > 67) {
            key.Set(data.begin() + 1, data.begin() + 34);
            if (!key.IsValid()) return false;
            key2.Set(data.begin() + 34, data.begin() + 67);
            if (!key2.IsValid()) return false;
            mapSigs[std::make_pair(key, key2)] = valtype(data.begin() + 67, data.end());
        } else {
            continue;
        }
    }
    return true;
}

static std::vector<valtype> SerializePartialTreeSig(const std::map<CPubKey, valtype>& mapNonces, const std::map<std::pair<CPubKey, CPubKey>, valtype>& mapSigs) {
    std::vector<valtype> ret;
    for (std::map<CPubKey, valtype>::const_iterator it = mapNonces.begin(); it != mapNonces.end(); ++it) {
        valtype add;
        add.push_back((unsigned char)0);
        add.insert(add.end(), it->first.begin(), it->first.end());
        add.insert(add.end(), it->second.begin(), it->second.end());
        ret.push_back(add);
    }
    for (std::map<std::pair<CPubKey, CPubKey>, valtype>::const_iterator it = mapSigs.begin(); it != mapSigs.end(); ++it) {
        valtype add;
        add.push_back((unsigned char)1);
        add.insert(add.end(), it->first.first.begin(), it->first.first.end());
        add.insert(add.end(), it->first.second.begin(), it->first.second.end());
        add.insert(add.end(), it->second.begin(), it->second.end());
        ret.push_back(add);
    }
    return ret;
}

namespace
{
struct SignKeyTreeFilter : public KeyTreeFilter
{
    const std::map<CPubKey, valtype>* nonces;

    SignKeyTreeFilter(const std::map<CPubKey, valtype>* nonces_) : nonces(nonces_) {}

    bool operator()(const CPubKey& pubkey)
    {
        return nonces->count(pubkey) > 0;
    }
};
}

static CScript PushAll(const vector<valtype>& values);

static bool SignTreeSig(const BaseSignatureCreator* creator, const std::vector<valtype>& vSolutions, const CScript* scriptCode, CScript& scriptSig, const std::vector<valtype>* scriptSigIn1, const std::vector<valtype>* scriptSigIn2)
{
    // Combine existing nonces and signatures
    std::map<CPubKey, valtype> mapNonces;
    std::map<std::pair<CPubKey, CPubKey>, valtype> mapSigs;
    if (scriptSigIn2) {
        ParsePartialTreeSig(*scriptSigIn2, mapNonces, mapSigs);
    }
    if (scriptSigIn1) {
        ParsePartialTreeSig(*scriptSigIn1, mapNonces, mapSigs);
    }

    // Retrieve the tree.
    uint256 hash;
    memcpy(hash.begin(), &vSolutions[1][0], 32);
    bool havetree = false;
    KeyTree tree;
    if (creator && creator->KeyStore().GetKeyTree(hash, tree)) {
        if (tree.hash != hash) {
            assert(!"Tree hash and requested hash mismatch");
        }
        havetree = true;
    }

    // Create nonces where possible
    if (havetree && scriptCode) {
        std::set<CPubKey> leaves = GetAllLeaves(&tree.root);
        for (std::set<CPubKey>::const_iterator it = leaves.begin(); it != leaves.end(); ++it) {
            if (mapNonces.count(*it) == 0) {
                valtype nonce;
                if (creator->CreatePartialSigNonce(nonce, it->GetID(), *scriptCode)) {
                    mapNonces[*it] = nonce;
                }
            }
        }
    }

    // Find a permissible subset of pubkeys
    SignKeyTreeFilter filter(&mapNonces);
    std::vector<uint256> branch;
    uint64_t position;
    std::vector<CPubKey> pubkeys;
    uint256 root;
    if (havetree && HasMatch(&tree.root, &filter)) {
        if (!GetMerkleBranch(&tree.root, &filter, &root, NULL, &position, &branch, &pubkeys)) {
            assert(!"No merkle branch found despite matching filter");
        }
        if (root != hash) {
            assert(!"Recomputed merkle root differs from merkle root in scriptPubKey");
        }
        CPubKey combinedpubkey;
        if (!CombinePubKeys(pubkeys, combinedpubkey)) {
            assert(!"Cannot create combined pubkey");
        }
        std::vector<valtype> allsigs;
        bool haveall = true;
        valtype combinedsig;
        if (pubkeys.size() == 1) {
            if (!creator->CreateSig(combinedsig, pubkeys[0].GetID(), *scriptCode)) {
                haveall = false;
            }
        } else {
            for (std::vector<CPubKey>::const_iterator it = pubkeys.begin(); it != pubkeys.end(); ++it) {
                std::pair<CPubKey, CPubKey> id = make_pair<CPubKey, CPubKey>(combinedpubkey, *it);
                if (mapSigs.count(id) == 0) {
                    // Try signing for this missing pubkey
                    CKey key;
                    if (scriptCode && creator->KeyStore().GetKey(it->GetID(), key)) {
                        valtype sig;
                        valtype my_pubnonce;
                        std::vector<valtype> other_pubnonces;
                        other_pubnonces.reserve(pubkeys.size() - 1);
                        std::vector<CPubKey> other_pubkeys;
                        other_pubkeys.reserve(pubkeys.size() - 1);
                        for (std::vector<CPubKey>::const_iterator it2 = pubkeys.begin(); it2 != pubkeys.end(); ++it2) {
                            if (it == it2) {
                                my_pubnonce = mapNonces[*it2];
                            } else {
                                other_pubnonces.push_back(mapNonces[*it2]);
                                other_pubkeys.push_back(*it2);
                            }
                        }
                        if (!creator->CreatePartialSig(sig, it->GetID(), *scriptCode, my_pubnonce, other_pubnonces, other_pubkeys)) {
                            assert(!"Failed to create partial signature, despite valid secret key");
                        }
                        mapSigs[id] = sig;
                        allsigs.push_back(sig);
                    } else {
                        haveall = false;
                    }
                } else {
                    allsigs.push_back(mapSigs[id]);
                }
            }
            if (haveall && !creator->CombinePartialSigs(combinedsig, allsigs)) {
                assert(!"Cannot combine partial signatures");
            }
        }
        if (haveall) {
            scriptSig.clear();
            scriptSig << combinedsig;
            scriptSig << ToByteVector(combinedpubkey);
            CScript walk;
            for (std::vector<uint256>::const_iterator it = branch.begin(); it != branch.end(); ++it) {
                CScript add;
                if (*it == uint256()) {
                    add << OP_1;
                } else {
                    valtype merklenode;
                    merklenode.resize(32);
                    memcpy(&merklenode[0], it->begin(), 32);
                    add << merklenode;
                }
                if (position & 1) {
                    add << OP_0;
                } else {
                    add << OP_1;
                }
                walk = add + walk;
                position >>= 1;
            }
            scriptSig += walk;
            return true;
        }
    }

    scriptSig = PushAll(SerializePartialTreeSig(mapNonces, mapSigs));
    return false;
}

/**
 * Sign scriptPubKey using signature made with creator.
 * Signatures are returned in scriptSigRet (or returns false if scriptPubKey can't be signed),
 * unless whichTypeRet is TX_SCRIPTHASH, in which case scriptSigRet is the redemption script.
 * Returns false if scriptPubKey could not be completely satisfied.
 */
static bool SignStep(const BaseSignatureCreator& creator, const CScript& scriptPubKey,
                     CScript& scriptSigRet, txnouttype& whichTypeRet)
{
    vector<valtype> stack;
    EvalScript(stack, scriptSigRet, SCRIPT_VERIFY_STRICTENC, BaseSignatureChecker());
    scriptSigRet.clear();

    vector<valtype> vSolutions;
    if (!Solver(scriptPubKey, whichTypeRet, vSolutions))
        return false;

    CKeyID keyID;
    switch (whichTypeRet)
    {
    case TX_NONSTANDARD:
    case TX_NULL_DATA:
    case TX_WITHDRAW_LOCK:
        return false;
    case TX_WITHDRAW_OUT:
        {
        scriptSigRet.clear();
        CScript scriptPubKey2(scriptPubKey.end() - 2 - 20 - 2, scriptPubKey.end() - 1);
        assert(Solver(scriptPubKey2, whichTypeRet, vSolutions) && whichTypeRet == TX_SCRIPTHASH);
        whichTypeRet = TX_WITHDRAW_OUT;
        return creator.KeyStore().GetCScript(uint160(vSolutions[0]), scriptSigRet);
        }
    case TX_PUBKEY:
        keyID = CPubKey(vSolutions[0]).GetID();
        return Sign1(keyID, creator, scriptPubKey, scriptSigRet);
    case TX_PUBKEYHASH:
        keyID = CKeyID(uint160(vSolutions[0]));
        if (!Sign1(keyID, creator, scriptPubKey, scriptSigRet))
            return false;
        else
        {
            CPubKey vch;
            creator.KeyStore().GetPubKey(keyID, vch);
            scriptSigRet << ToByteVector(vch);
        }
        return true;
    case TX_SCRIPTHASH:
        return creator.KeyStore().GetCScript(uint160(vSolutions[0]), scriptSigRet);

    case TX_MULTISIG:
        scriptSigRet << OP_0; // workaround CHECKMULTISIG bug
        return (SignN(vSolutions, creator, scriptPubKey, scriptSigRet));

    case TX_TREESIG:
        return SignTreeSig(&creator, vSolutions, &scriptPubKey, scriptSigRet, &stack, NULL);

    case TX_TRUE:
        return true;
    }
    return false;
}

bool ProduceSignature(const BaseSignatureCreator& creator, const CScript& fromPubKey, CScript& scriptSig)
{
    if (VerifyScript(scriptSig, fromPubKey, STANDARD_SCRIPT_VERIFY_FLAGS, creator.Checker()))
        return true;

    txnouttype whichType;
    CScript scriptSigOriginal = scriptSig;
    if (!SignStep(creator, fromPubKey, scriptSig, whichType))
        return false;

    if (whichType == TX_SCRIPTHASH || whichType == TX_WITHDRAW_OUT)
    {
        // SignStep returns the subscript that need to be evaluated;
        // the final scriptSig is the signatures from that
        // and then the serialized subscript:
        CScript subscript = scriptSig;
        scriptSig = scriptSigOriginal;

        txnouttype subType;
        bool fSolved =
            SignStep(creator, subscript, scriptSig, subType) && subType != TX_SCRIPTHASH;
        // Append serialized subscript whether or not it is completely signed:
        scriptSig << static_cast<valtype>(subscript);
        if (whichType == TX_WITHDRAW_OUT)
            scriptSig << OP_0;
        if (!fSolved) return false;
    }

    // Test solution
    return VerifyScript(scriptSig, fromPubKey, STANDARD_SCRIPT_VERIFY_FLAGS, creator.Checker());
}

bool SignSignature(const CKeyStore &keystore, const CScript& fromPubKey, const CTxOutValue& nValue, CMutableTransaction& txTo, unsigned int nIn, int nHashType)
{
    assert(nIn < txTo.vin.size());
    CTxIn& txin = txTo.vin[nIn];

    CTransaction txToConst(txTo);
    TransactionSignatureCreator creator(keystore, &txToConst, nIn, nValue, nHashType);

    return ProduceSignature(creator, fromPubKey, txin.scriptSig);
}

bool SignSignature(const CKeyStore &keystore, const CTransaction& txFrom, CMutableTransaction& txTo, unsigned int nIn, int nHashType)
{
    assert(nIn < txTo.vin.size());
    CTxIn& txin = txTo.vin[nIn];
    assert(txin.prevout.n < txFrom.vout.size());
    const CTxOut& txout = txFrom.vout[txin.prevout.n];

    return SignSignature(keystore, txout.scriptPubKey, txout.nValue, txTo, nIn, nHashType);
}

static CScript PushAll(const vector<valtype>& values)
{
    CScript result;
    BOOST_FOREACH(const valtype& v, values)
        result << v;
    return result;
}

static CScript CombineMultisig(const CScript& scriptPubKey, const BaseSignatureChecker& checker,
                               const vector<valtype>& vSolutions,
                               const vector<valtype>& sigs1, const vector<valtype>& sigs2)
{
    // Combine all the signatures we've got:
    set<valtype> allsigs;
    BOOST_FOREACH(const valtype& v, sigs1)
    {
        if (!v.empty())
            allsigs.insert(v);
    }
    BOOST_FOREACH(const valtype& v, sigs2)
    {
        if (!v.empty())
            allsigs.insert(v);
    }

    // Build a map of pubkey -> signature by matching sigs to pubkeys:
    assert(vSolutions.size() > 1);
    unsigned int nSigsRequired = vSolutions.front()[0];
    unsigned int nPubKeys = vSolutions.size()-2;
    map<valtype, valtype> sigs;
    BOOST_FOREACH(const valtype& sig, allsigs)
    {
        for (unsigned int i = 0; i < nPubKeys; i++)
        {
            const valtype& pubkey = vSolutions[i+1];
            if (sigs.count(pubkey))
                continue; // Already got a sig for this pubkey

            if (checker.CheckSig(sig, pubkey, scriptPubKey))
            {
                sigs[pubkey] = sig;
                break;
            }
        }
    }
    // Now build a merged CScript:
    unsigned int nSigsHave = 0;
    CScript result; result << OP_0; // pop-one-too-many workaround
    for (unsigned int i = 0; i < nPubKeys && nSigsHave < nSigsRequired; i++)
    {
        if (sigs.count(vSolutions[i+1]))
        {
            result << sigs[vSolutions[i+1]];
            ++nSigsHave;
        }
    }
    // Fill any missing with OP_0:
    for (unsigned int i = nSigsHave; i < nSigsRequired; i++)
        result << OP_0;

    return result;
}

static CScript CombineSignatures(const CScript& scriptPubKey, const BaseSignatureChecker& checker,
                                 const txnouttype txType, const vector<valtype>& vSolutions,
                                 vector<valtype>& sigs1, vector<valtype>& sigs2)
{
    switch (txType)
    {
    case TX_NONSTANDARD:
    case TX_NULL_DATA:
    case TX_WITHDRAW_LOCK:
    case TX_TRUE:
        // Don't know anything about this, assume bigger one is correct:
        if (sigs1.size() >= sigs2.size())
            return PushAll(sigs1);
        return PushAll(sigs2);
    case TX_PUBKEY:
    case TX_PUBKEYHASH:
        // Signatures are bigger than placeholders or empty scripts:
        if (sigs1.empty() || sigs1[0].empty())
            return PushAll(sigs2);
        return PushAll(sigs1);
    case TX_WITHDRAW_OUT:
    case TX_SCRIPTHASH:
        if (sigs1.empty())
            return PushAll(sigs2);
        else if (sigs2.empty() || sigs2.back().empty())
            return PushAll(sigs1);
        else if (sigs1.back().empty())
            return PushAll(sigs2);
        else
        {
            // Recur to combine:
            if (txType == TX_WITHDRAW_OUT) {
                sigs1.pop_back();
                sigs2.pop_back();
            }
            valtype spk = sigs1.back();
            CScript pubKey2(spk.begin(), spk.end());

            txnouttype txType2;
            vector<vector<unsigned char> > vSolutions2;
            Solver(pubKey2, txType2, vSolutions2);
            sigs1.pop_back();
            sigs2.pop_back();
            CScript result = CombineSignatures(pubKey2, checker, txType2, vSolutions2, sigs1, sigs2);
            result << spk;
            if (txType == TX_WITHDRAW_OUT)
                result << OP_0;
            return result;
        }
    case TX_MULTISIG:
        return CombineMultisig(scriptPubKey, checker, vSolutions, sigs1, sigs2);
    case TX_TREESIG:
        CScript result;
        SignTreeSig(NULL, vSolutions, NULL, result, &sigs1, &sigs2);
        return result;
    }

    return CScript();
}

CScript CombineSignatures(const CScript& scriptPubKey, const CTransaction& txTo, unsigned int nIn, const CTxOutValue& nValue,
                          const CScript& scriptSig1, const CScript& scriptSig2)
{
    TransactionNoWithdrawsSignatureChecker checker(&txTo, nIn, nValue);
    return CombineSignatures(scriptPubKey, checker, scriptSig1, scriptSig2);
}

CScript CombineSignatures(const CScript& scriptPubKey, const BaseSignatureChecker& checker,
                          const CScript& scriptSig1, const CScript& scriptSig2)
{
    if (VerifyScript(scriptSig1, scriptPubKey, STANDARD_SCRIPT_VERIFY_FLAGS, checker)) {
        return scriptSig1;
    }
    if (VerifyScript(scriptSig2, scriptPubKey, STANDARD_SCRIPT_VERIFY_FLAGS, checker)) {
        return scriptSig2;
    }

    txnouttype txType;
    vector<vector<unsigned char> > vSolutions;
    Solver(scriptPubKey, txType, vSolutions);

    vector<valtype> stack1;
    EvalScript(stack1, scriptSig1, SCRIPT_VERIFY_STRICTENC, BaseSignatureChecker());
    vector<valtype> stack2;
    EvalScript(stack2, scriptSig2, SCRIPT_VERIFY_STRICTENC, BaseSignatureChecker());

    return CombineSignatures(scriptPubKey, checker, txType, vSolutions, stack1, stack2);
}
