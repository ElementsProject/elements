// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2018 The Bitcoin developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef H_BITCOIN_SCRIPT_GENERIC
#define H_BITCOIN_SCRIPT_GENERIC

#include <hash.h>
#include <script/interpreter.h>
#include <script/sign.h>
#include <script/signingprovider.h>


class SimpleSignatureChecker : public BaseSignatureChecker
{
public:
    uint256 hash;
    bool sighash_byte;

    SimpleSignatureChecker(const uint256& hashIn, bool sighash_byte_in) : hash(hashIn), sighash_byte(sighash_byte_in) {};
    bool CheckECDSASignature(const std::vector<unsigned char>& vchSig, const std::vector<unsigned char>& vchPubKey, const CScript& scriptCode, SigVersion sigversion, unsigned int flags) const override
    {
        std::vector<unsigned char> vchSigCopy(vchSig);
        CPubKey pubkey(vchPubKey);
        if (!pubkey.IsValid())
            return false;
        if (vchSig.empty())
            return false;
        // Get rid of sighash byte before verifying hash
        // Note: We only accept SIGHASH_ALL!
        if (sighash_byte) {
            const unsigned char popped_byte = vchSigCopy.back();
            vchSigCopy.pop_back();
            if (popped_byte != SIGHASH_ALL) {
                return false;
            }
        }
        return pubkey.Verify(hash, vchSig);
    }
};

class SimpleSignatureCreator : public BaseSignatureCreator
{
    SimpleSignatureChecker checker;
    bool sighash_byte;

public:
    SimpleSignatureCreator(const uint256& hashIn, bool sighash_byte_in) : checker(hashIn, sighash_byte_in), sighash_byte(sighash_byte_in) {};
    const BaseSignatureChecker& Checker() const override { return checker; }
    bool CreateSig(const SigningProvider& provider, std::vector<unsigned char>& vchSig, const CKeyID& keyid, const CScript& scriptCode, SigVersion sigversion, unsigned int flags) const override
    {
        CKey key;
        if (!provider.GetKey(keyid, key))
            return false;
        if (!key.Sign(checker.hash, vchSig)) {
            return false;
        }
        // We only support sighash all for malleability reasons(it is not committed in sighash)
        if (sighash_byte) {
            vchSig.push_back(SIGHASH_ALL);
        }
        return true;
    }
    // ELEMENTS: for now we do not support Schnorr signing in block headers
    bool CreateSchnorrSig(const SigningProvider& provider, std::vector<unsigned char>& sig, const XOnlyPubKey& pubkey, const uint256* leaf_hash, const uint256* merkle_root, SigVersion sigversion) const override
    {
        return false;
    }
};

template<typename T>
bool GenericVerifyScript(const CScript& scriptSig, const CScriptWitness& witness, const CScript& scriptPubKey, unsigned int flags, const T& data)
{
    bool sighash_byte = (flags & SCRIPT_NO_SIGHASH_BYTE) ? false : true;
    // Note: Our hash doesn't commit to the sighash byte
    return VerifyScript(scriptSig, scriptPubKey, &witness, flags, SimpleSignatureChecker(SerializeHash(data), sighash_byte));
}

template<typename T>
bool GenericSignScript(const FillableSigningProvider& keystore, const T& data, const CScript& fromPubKey, SignatureData& scriptSig, unsigned int additional_flags)
{
    bool sighash_byte = (additional_flags & SCRIPT_NO_SIGHASH_BYTE) ? false : true;
    // Note: Our hash doesn't commit to the sighash byte
    return ProduceSignature(keystore, SimpleSignatureCreator(SerializeHash(data), sighash_byte), fromPubKey, scriptSig, additional_flags);
}

#endif // H_BITCOIN_SCRIPT_GENERIC
