// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2014 The Bitcoin developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_PRIMITIVES_TRANSACTION_H
#define BITCOIN_PRIMITIVES_TRANSACTION_H

#include "amount.h"
#include "hash.h"
#include "script/script.h"
#include "serialize.h"
#include "uint256.h"

#define SERIALIZE_VERSION_MASK_NO_WITNESS   0x40000000
#define SERIALIZE_VERSION_MASK_ONLY_WITNESS 0x80000000
#define SERIALIZE_VERSION_MASK_BITCOIN_TX   0x20000000
#define SERIALIZE_VERSION_MASK_PREHASH      0x10000000

class CTxOutValue
{
public:
    static const size_t nCommitmentSize = 33;

    std::vector<unsigned char> vchCommitment;
    std::vector<unsigned char> vchRangeproof;
    std::vector<unsigned char> vchNonceCommitment;

    CTxOutValue();
    CTxOutValue(CAmount);
    CTxOutValue(const std::vector<unsigned char>& vchValueCommitment, const std::vector<unsigned char>& vchRangeproofIn);

    ADD_SERIALIZE_METHODS;

    template<typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action, int nType, int nVersion)
    {
        bool fBitcoinTx = nVersion & SERIALIZE_VERSION_MASK_BITCOIN_TX;
        bool fWitness = (nVersion & SERIALIZE_VERSION_MASK_NO_WITNESS) == 0;
        bool fOnlyWitness = nVersion & SERIALIZE_VERSION_MASK_ONLY_WITNESS;
        assert(!fBitcoinTx || IsAmount() || (IsNull() && ser_action.ForRead()));
        if (fBitcoinTx) {
            CAmount amount = 0;
            if (!ser_action.ForRead())
                amount = GetAmount();
            READWRITE(amount);
            if (ser_action.ForRead())
                SetToAmount(amount);
        } else {
            if (!fOnlyWitness) READWRITE(REF(CFlatData(&vchCommitment[0], &vchCommitment[nCommitmentSize])));
            if (fWitness) {
                if (nVersion & SERIALIZE_VERSION_MASK_PREHASH) {
                    uint256 prehash = (CHashWriter(nType, nVersion) << vchRangeproof << vchNonceCommitment).GetHash();
                    READWRITE(prehash);
                } else {
                    READWRITE(vchRangeproof);
                    READWRITE(vchNonceCommitment);
                }
            }
        }
    }

    bool IsValid() const;
    bool IsNull() const;
    bool IsAmount() const;

    CAmount GetAmount() const;
    void SetToAmount(CAmount nAmount);

    friend bool operator==(const CTxOutValue& a, const CTxOutValue& b);
    friend bool operator!=(const CTxOutValue& a, const CTxOutValue& b);
};

/** An outpoint - a combination of a transaction hash and an index n into its vout */
class COutPoint
{
public:
    uint256 hash;
    uint32_t n;

    COutPoint() { SetNull(); }
    COutPoint(uint256 hashIn, uint32_t nIn) { hash = hashIn; n = nIn; }

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action, int nType, int nVersion) {
        READWRITE(FLATDATA(*this));
    }

    void SetNull() { hash = 0; n = (uint32_t) -1; }
    bool IsNull() const { return (hash == 0 && n == (uint32_t) -1); }

    friend bool operator<(const COutPoint& a, const COutPoint& b)
    {
        return (a.hash < b.hash || (a.hash == b.hash && a.n < b.n));
    }

    friend bool operator==(const COutPoint& a, const COutPoint& b)
    {
        return (a.hash == b.hash && a.n == b.n);
    }

    friend bool operator!=(const COutPoint& a, const COutPoint& b)
    {
        return !(a == b);
    }

    std::string ToString() const;
};

/** An input of a transaction.  It contains the location of the previous
 * transaction's output that it claims and a signature that matches the
 * output's public key.
 */
class CTxIn
{
public:
    COutPoint prevout;
    CScript scriptSig;
    uint32_t nSequence;

    CTxIn()
    {
        nSequence = ~(uint32_t)0;
    }

    explicit CTxIn(COutPoint prevoutIn, CScript scriptSigIn=CScript(), uint32_t nSequenceIn=~(uint32_t)0);
    CTxIn(uint256 hashPrevTx, uint32_t nOut, CScript scriptSigIn=CScript(), uint32_t nSequenceIn=~(uint32_t)0);

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action, int nType, int nVersion) {
        bool fWitness = (nVersion & SERIALIZE_VERSION_MASK_NO_WITNESS) == 0;
        bool fOnlyWitness = nVersion & SERIALIZE_VERSION_MASK_ONLY_WITNESS;
        assert((nType != SER_GETHASH && !fOnlyWitness && fWitness) || nType == SER_GETHASH);
        if (!fOnlyWitness) READWRITE(prevout);
        if (fWitness)      READWRITE(scriptSig);
        if (!fOnlyWitness) READWRITE(nSequence);
    }

    friend bool operator==(const CTxIn& a, const CTxIn& b)
    {
        return (a.prevout   == b.prevout &&
                a.scriptSig == b.scriptSig &&
                a.nSequence == b.nSequence);
    }

    friend bool operator!=(const CTxIn& a, const CTxIn& b)
    {
        return !(a == b);
    }

    std::string ToString() const;
};

/** An output of a transaction.  It contains the public key that the next input
 * must be able to sign with to claim it.
 */
class CTxOut
{
public:
    CTxOutValue nValue;
    CScript scriptPubKey;

    CTxOut()
    {
        SetNull();
    }

    CTxOut(const CTxOutValue& valueIn, CScript scriptPubKeyIn);

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action, int nType, int nVersion) {
        READWRITE(nValue);
        READWRITE(scriptPubKey);
    }

    void SetNull()
    {
        nValue = CTxOutValue();
        scriptPubKey.clear();
    }

    bool IsNull() const
    {
        return nValue.IsNull() && scriptPubKey.empty();
    }

    bool IsDust(CFeeRate minRelayTxFee) const
    {
        if (!nValue.IsAmount())
            return false;  // FIXME

        // "Dust" is defined in terms of CTransaction::minRelayTxFee,
        // which has units satoshis-per-kilobyte.
        // If you'd pay more than 1/3 in fees
        // to spend something, then we consider it dust.
        // A typical txout is 34 bytes big, and will
        // need a CTxIn of at least 148 bytes to spend:
        // so dust is a txout less than 546 satoshis 
        // with default minRelayTxFee.
        size_t nSize = GetSerializeSize(SER_DISK,0)+148u;
        return (nValue.GetAmount() < 3*minRelayTxFee.GetFee(nSize));
    }

    friend bool operator==(const CTxOut& a, const CTxOut& b)
    {
        return (a.nValue       == b.nValue &&
                a.scriptPubKey == b.scriptPubKey);
    }

    friend bool operator!=(const CTxOut& a, const CTxOut& b)
    {
        return !(a == b);
    }

    std::string ToString() const;
};

struct CMutableTransaction;

/** The basic transaction that is broadcasted on the network and contained in
 * blocks.  A transaction can contain multiple inputs and outputs.
 */
class CTransaction
{
private:
    /** Memory only. */
    const uint256 hash;
    const uint256 hashWitness; // Just witness
    const uint256 hashFull; // Including witness
    const uint256 hashBitcoin; // For Bitcoin Transactions
    void UpdateHash() const;

public:
    static const int32_t CURRENT_VERSION=1;

    // The local variables are made const to prevent unintended modification
    // without updating the cached hash value. However, CTransaction is not
    // actually immutable; deserialization and assignment are implemented,
    // and bypass the constness. This is safe, as they update the entire
    // structure, including the hash.
    const int32_t nVersion;
    const std::vector<CTxIn> vin;
    const CAmount nTxFee;
    const std::vector<CTxOut> vout;
    const uint32_t nLockTime;

    /** Construct a CTransaction that qualifies as IsNull() */
    CTransaction();

    /** Convert a CMutableTransaction into a CTransaction. */
    CTransaction(const CMutableTransaction &tx);

    CTransaction& operator=(const CTransaction& tx);

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action, int nType, int nVersion) {
        bool fWitness = (nVersion & SERIALIZE_VERSION_MASK_NO_WITNESS) == 0;
        bool fOnlyWitness = nVersion & SERIALIZE_VERSION_MASK_ONLY_WITNESS;
        bool fBitcoinTx = nVersion & SERIALIZE_VERSION_MASK_BITCOIN_TX;
        assert(!fBitcoinTx || (fBitcoinTx && fWitness && !fOnlyWitness));
        assert((nType != SER_GETHASH && !fOnlyWitness && fWitness) || nType == SER_GETHASH);
        if (!fOnlyWitness)                READWRITE(*const_cast<int32_t*>(&this->nVersion));
                                          READWRITE(*const_cast<std::vector<CTxIn>*>(&vin));
        if (!fBitcoinTx && !fOnlyWitness) READWRITE(*const_cast<CAmount*>(&nTxFee));
        if (!fOnlyWitness)                READWRITE(*const_cast<std::vector<CTxOut>*>(&vout));
        if (!fOnlyWitness)                READWRITE(*const_cast<uint32_t*>(&nLockTime));
        if (ser_action.ForRead())
            UpdateHash();
    }

    bool IsNull() const {
        return vin.empty() && vout.empty();
    }

    /* Transaction hash without witness information */
    const uint256& GetHash() const {
        return hash;
    }

    /* Transaction hash including witness information */
    const uint256& GetFullHash() const {
        return hashFull;
    }

    /* Hash of just witness information */
    const uint256& GetWitnessHash() const {
        return hashWitness;
    }

    /* Transaction hash including witness information */
    const uint256& GetBitcoinHash() const {
        assert(hashBitcoin != 0);
        return hashBitcoin;
    }

    // Compute priority, given priority of inputs and (optionally) tx size
    double ComputePriority(double dPriorityInputs, unsigned int nTxSize=0) const;

    // Compute modified tx size for priority calculation (optionally given tx size)
    unsigned int CalculateModifiedSize(unsigned int nTxSize=0) const;

    bool IsCoinBase() const
    {
        return (vin.size() == 1 && vin[0].prevout.IsNull());
    }

    //! Asset definition transactions must have more than 1 input
    bool IsAssetDefinition() const
    {
        return (vin.size() > 1 && vin[0].prevout.IsNull());
    }

    friend bool operator==(const CTransaction& a, const CTransaction& b)
    {
        return a.hash == b.hash;
    }

    friend bool operator!=(const CTransaction& a, const CTransaction& b)
    {
        return a.hash != b.hash;
    }

    std::string ToString() const;
};

/** A mutable version of CTransaction. */
struct CMutableTransaction
{
    int32_t nVersion;
    std::vector<CTxIn> vin;
    CAmount nTxFee;
    std::vector<CTxOut> vout;
    uint32_t nLockTime;

    CMutableTransaction();
    CMutableTransaction(const CTransaction& tx);

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action, int nType, int nVersion) {
        bool fWitness = (nVersion & SERIALIZE_VERSION_MASK_NO_WITNESS) == 0;
        bool fOnlyWitness = nVersion & SERIALIZE_VERSION_MASK_ONLY_WITNESS;
        bool fBitcoinTx = nVersion & SERIALIZE_VERSION_MASK_BITCOIN_TX;
        assert(!fBitcoinTx);
        assert((nType != SER_GETHASH && !fOnlyWitness && fWitness) || nType == SER_GETHASH);
        if (!fOnlyWitness) READWRITE(this->nVersion);
                           READWRITE(vin);
        if (!fOnlyWitness) READWRITE(nTxFee);
        if (!fOnlyWitness) READWRITE(vout);
        if (!fOnlyWitness) READWRITE(nLockTime);
    }

    bool IsCoinBase() const
    {
        return (vin.size() == 1 && vin[0].prevout.IsNull());
    }

    /** Compute the hash of this CMutableTransaction. This is computed on the
     * fly, as opposed to GetHash() in CTransaction, which uses a cached result.
     */
    uint256 GetHash() const;
};

#endif // BITCOIN_PRIMITIVES_TRANSACTION_H
