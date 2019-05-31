// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2018 The Bitcoin developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef H_BITCOIN_SCRIPT_GENERIC
#define H_BITCOIN_SCRIPT_GENERIC

#include <hash.h>
#include <script/interpreter.h>
#include <script/sign.h>
#include <keystore.h>

class SimpleSignatureChecker : public BaseSignatureChecker
{
public:
    uint256 hash;

    SimpleSignatureChecker(const uint256& hashIn) : hash(hashIn) {};
    bool CheckSig(const std::vector<unsigned char>& vchSig, const std::vector<unsigned char>& vchPubKey, const CScript& scriptCode, SigVersion sigversion) const
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
    SimpleSignatureCreator(const uint256& hashIn) : checker(hashIn) {};
    const BaseSignatureChecker& Checker() const { return checker; }
    bool CreateSig(const SigningProvider& provider, std::vector<unsigned char>& vchSig, const CKeyID& keyid, const CScript& scriptCode, SigVersion sigversion) const
    {
        CKey key;
        if (!provider.GetKey(keyid, key))
            return false;
        return key.Sign(checker.hash, vchSig);
    }
};

template<typename T>
bool GenericVerifyScript(const CScript& scriptSig, const CScriptWitness& witness, const CScript& scriptPubKey, unsigned int flags, const T& data)
{
    return VerifyScript(scriptSig, scriptPubKey, &witness, flags, SimpleSignatureChecker(SerializeHash(data)));
}

template<typename T>
bool GenericSignScript(const CKeyStore& keystore, const T& data, const CScript& fromPubKey, SignatureData& scriptSig)
{
    return ProduceSignature(keystore, SimpleSignatureCreator(SerializeHash(data)), fromPubKey, scriptSig, SCRIPT_NO_SIGHASH_BYTE);
}

#endif // H_BITCOIN_SCRIPT_GENERIC
