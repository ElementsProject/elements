// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2014 The Bitcoin developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_SCRIPT_SIGN_H
#define BITCOIN_SCRIPT_SIGN_H

#include "script/interpreter.h"

class CKeyID;
class CKeyStore;
class CScript;
class CTransaction;

struct CMutableTransaction;

/** Virtual base class for signature creators. */
class BaseSignatureCreator {
protected:
    const CKeyStore& keystore;

public:
    BaseSignatureCreator(const CKeyStore& keystoreIn) : keystore(keystoreIn) {}
    const CKeyStore& KeyStore() const { return keystore; };
    virtual ~BaseSignatureCreator() {}
    virtual const BaseSignatureChecker& Checker() const =0;

    /** Create a singular (non-script) signature. */
    virtual bool CreateSig(std::vector<unsigned char>& vchSig, const CKeyID& keyid, const CScript& scriptCode) const =0;

    /** Deal with partial signatures to produce a multisignature. */
    virtual bool CreatePartialSigNonce(std::vector<unsigned char>& vchSigNonce, const CKeyID& keyid, const CScript& scriptCode) const =0;
    virtual bool CreatePartialSig(std::vector<unsigned char>& vchSig, const CKeyID& keyid, const CScript& scriptCode, const std::vector<unsigned char>& my_pubnonce, const std::vector<std::vector<unsigned char> >& other_pubnonces, const std::vector<CPubKey>& other_pubkeys) const =0;
    virtual bool CombinePartialSigs(std::vector<unsigned char>& out, const std::vector<std::vector<unsigned char> >& ins) const =0;
};

/** A signature creator for transactions. */
class TransactionSignatureCreator : public BaseSignatureCreator {
    const CTransaction* txTo;
    unsigned int nIn;
    int nHashType;
    const TransactionNoWithdrawsSignatureChecker checker;

public:
    TransactionSignatureCreator(const CKeyStore& keystoreIn, const CTransaction* txToIn, unsigned int nInIn, const CTxOutValue& nValueIn, int nHashTypeIn=SIGHASH_ALL);
    const BaseSignatureChecker& Checker() const { return checker; }
    bool CreateSig(std::vector<unsigned char>& vchSig, const CKeyID& keyid, const CScript& scriptCode) const;
    bool CreatePartialSigNonce(std::vector<unsigned char>& vchSigNonce, const CKeyID& keyid, const CScript& scriptCode) const;
    bool CreatePartialSig(std::vector<unsigned char>& vchSig, const CKeyID& keyid, const CScript& scriptCode, const std::vector<unsigned char>& my_pubnonce, const std::vector<std::vector<unsigned char> >& other_pubnonces, const std::vector<CPubKey>& other_pubkeys) const;
    bool CombinePartialSigs(std::vector<unsigned char>& out, const std::vector<std::vector<unsigned char> >& ins) const;
};

/** Produce a script signature using a generic signature creator. */
bool ProduceSignature(const BaseSignatureCreator& creator, const CScript& scriptPubKey, CScript& scriptSig);

/** Produce a script signature for a transaction. */
bool SignSignature(const CKeyStore& keystore, const CScript& fromPubKey, const CTxOutValue& nAmount, CMutableTransaction& txTo, unsigned int nIn, int nHashType=SIGHASH_ALL);
bool SignSignature(const CKeyStore& keystore, const CTransaction& txFrom, CMutableTransaction& txTo, unsigned int nIn, int nHashType=SIGHASH_ALL);

/** Combine two script signatures using a generic signature checker, intelligently, possibly with OP_0 placeholders. */
CScript CombineSignatures(const CScript& scriptPubKey, const BaseSignatureChecker& checker, const CScript& scriptSig1, const CScript& scriptSig2);

/** Combine two script signatures on transactions. */
CScript CombineSignatures(const CScript& scriptPubKey, const CTransaction& txTo, unsigned int nIn, const CTxOutValue& nValue, const CScript& scriptSig1, const CScript& scriptSig2);

#endif // BITCOIN_SCRIPT_SIGN_H
