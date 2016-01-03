// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2014 The Bitcoin developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef H_BITCOIN_SCRIPT_GENERIC
#define H_BITCOIN_SCRIPT_GENERIC

#include "hash.h"
#include "script/interpreter.h"
#include "script/sign.h"

class SimpleSignatureChecker : public BaseSignatureChecker
{
public:
    uint256 hash;

    SimpleSignatureChecker(const uint256& hashIn) : hash(hashIn) {};
    bool CheckSig(const std::vector<unsigned char>& vchSig, const std::vector<unsigned char>& vchPubKey, const CScript& scriptCode) const
    {
        CPubKey pubkey(vchPubKey);
        if (!pubkey.IsValid())
            return false;
        if (vchSig.empty())
            return false;
        return pubkey.Verify(hash, vchSig);
    }
};

class SimpleSignatureCreator : public BaseSignatureCreator
{
    SimpleSignatureChecker checker;

public:
    SimpleSignatureCreator(const CKeyStore& keystoreIn, const uint256& hashIn) : BaseSignatureCreator(keystoreIn), checker(hashIn) {};
    const BaseSignatureChecker& Checker() const { return checker; }
    bool CreateSig(std::vector<unsigned char>& vchSig, const CKeyID& keyid, const CScript& scriptCode) const
    {
        CKey key;
        if (!keystore.GetKey(keyid, key))
            return false;
        return key.Sign(checker.hash, vchSig);
    }
    bool CreatePartialSigNonce(std::vector<unsigned char>& vchSigNonce, const CKeyID& keyid, const CScript& scriptCode) const
    {
        CKey key;
        if (!keystore.GetKey(keyid, key))
            return false;
        return key.PartialSigningNonce(checker.hash, vchSigNonce);
    }
    bool CreatePartialSig(std::vector<unsigned char>& vchSig, const CKeyID& keyid, const CScript& scriptCode, const std::vector<unsigned char>& my_pubnonce, const std::vector<std::vector<unsigned char> >& other_pubnonces, const std::vector<CPubKey>& other_pubkeys) const
    {
        CKey key;
        if (!keystore.GetKey(keyid, key))
            return false;
        return key.PartialSign(checker.hash, other_pubnonces, other_pubkeys, my_pubnonce, vchSig);
    }
    bool CombinePartialSigs(std::vector<unsigned char>& out, const std::vector<std::vector<unsigned char> >& ins) const
    {
        return CombinePartialSignatures(ins, out);
    }
};

template<typename T>
bool GenericVerifyScript(const CScript& scriptSig, const CScript& scriptPubKey, unsigned int flags, const T& data)
{
    return VerifyScript(scriptSig, scriptPubKey, flags, SimpleSignatureChecker(SerializeHash(data)));
}

template<typename T>
bool GenericSignScript(const CKeyStore& keystore, const T& data, const CScript& fromPubKey, CScript& scriptSig)
{
    return ProduceSignature(SimpleSignatureCreator(keystore, SerializeHash(data)), fromPubKey, scriptSig);
}

template<typename T>
CScript GenericCombineSignatures(CScript scriptPubKey, const T& data, const CScript& scriptSig1, const CScript& scriptSig2)
{
    return CombineSignatures(scriptPubKey, SimpleSignatureChecker(SerializeHash(data)), scriptSig1, scriptSig2);
}

#endif // H_BITCOIN_SCRIPT_GENERIC
