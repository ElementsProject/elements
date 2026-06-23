// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2022 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_PRIMITIVES_TRANSACTION_H
#define BITCOIN_PRIMITIVES_TRANSACTION_H

#include <attributes.h>
#include <consensus/amount.h>
#include <script/script.h>
#include <serialize.h>
#include <uint256.h>
#include <primitives/confidential.h>
#include <primitives/txwitness.h>
#include <util/transaction_identifier.h> // IWYU pragma: export

#include <cstddef>
#include <cstdint>
#include <ios>
#include <limits>
#include <memory>
#include <numeric>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

/** An outpoint - a combination of a transaction hash and an index n into its vout */
class COutPoint
{
public:
    Txid hash;
    uint32_t n;

    //
    // ELEMENTS flags:

    /* If this flag is set, the CTxIn including this COutPoint has a
     * CAssetIssuance object. */
    static const uint32_t OUTPOINT_ISSUANCE_FLAG = (1 << 31);

    /* If this flag is set, the CTxIn including this COutPoint
     * is a peg-in input. */
    static const uint32_t OUTPOINT_PEGIN_FLAG = (1 << 30);

    /* The inverse of the combination of the preceding flags. Used to
     * extract the original meaning of `n` as the index into the
     * transaction's output array. */
    static const uint32_t OUTPOINT_INDEX_MASK = 0x3fffffff;

    // END ELEMENTS
    //

    static constexpr uint32_t NULL_INDEX = std::numeric_limits<uint32_t>::max();

    COutPoint(): n(NULL_INDEX) { }
    COutPoint(const Txid& hashIn, uint32_t nIn): hash(hashIn), n(nIn) { }

    SERIALIZE_METHODS(COutPoint, obj) { READWRITE(obj.hash, obj.n); }

    void SetNull() { hash.SetNull(); n = NULL_INDEX; }
    bool IsNull() const { return (hash.IsNull() && n == NULL_INDEX); }

    friend bool operator<(const COutPoint& a, const COutPoint& b)
    {
        return std::tie(a.hash, a.n) < std::tie(b.hash, b.n);
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

    //
    // ELEMENTS:

    CAssetIssuance assetIssuance;

    /* If this is set to true, the input is interpreted as a
     * peg-in claim and processed as such */
    bool m_is_pegin = false;

    // END ELEMENTS
    //

    /**
     * Setting nSequence to this value for every input in a transaction
     * disables nLockTime/IsFinalTx().
     * It fails OP_CHECKLOCKTIMEVERIFY/CheckLockTime() for any input that has
     * it set (BIP 65).
     * It has SEQUENCE_LOCKTIME_DISABLE_FLAG set (BIP 68/112).
     */
    static const uint32_t SEQUENCE_FINAL = 0xffffffff;
    /**
     * This is the maximum sequence number that enables both nLockTime and
     * OP_CHECKLOCKTIMEVERIFY (BIP 65).
     * It has SEQUENCE_LOCKTIME_DISABLE_FLAG set (BIP 68/112).
     */
    static const uint32_t MAX_SEQUENCE_NONFINAL{SEQUENCE_FINAL - 1};

    // Below flags apply in the context of BIP 68. BIP 68 requires the tx
    // version to be set to 2, or higher.
    /**
     * If this flag is set, CTxIn::nSequence is NOT interpreted as a
     * relative lock-time.
     * It skips SequenceLocks() for any input that has it set (BIP 68).
     * It fails OP_CHECKSEQUENCEVERIFY/CheckSequence() for any input that has
     * it set (BIP 112).
     */
    static const uint32_t SEQUENCE_LOCKTIME_DISABLE_FLAG = (1U << 31);

    /**
     * If CTxIn::nSequence encodes a relative lock-time and this flag
     * is set, the relative lock-time has units of 512 seconds,
     * otherwise it specifies blocks with a granularity of 1. */
    static const uint32_t SEQUENCE_LOCKTIME_TYPE_FLAG = (1 << 22);

    /**
     * If CTxIn::nSequence encodes a relative lock-time, this mask is
     * applied to extract that lock-time from the sequence field. */
    static const uint32_t SEQUENCE_LOCKTIME_MASK = 0x0000ffff;

    /**
     * In order to use the same number of bits to encode roughly the
     * same wall-clock duration, and because blocks are naturally
     * limited to occur every 600s on average, the minimum granularity
     * for time-based relative lock-time is fixed at 512 seconds.
     * Converting from CTxIn::nSequence to seconds is performed by
     * multiplying by 512 = 2^9, or equivalently shifting up by
     * 9 bits. */
    static const int SEQUENCE_LOCKTIME_GRANULARITY = 9;

    CTxIn()
    {
        nSequence = SEQUENCE_FINAL;
    }

    explicit CTxIn(COutPoint prevoutIn, CScript scriptSigIn=CScript(), uint32_t nSequenceIn=SEQUENCE_FINAL);
    CTxIn(Txid hashPrevTx, uint32_t nOut, CScript scriptSigIn=CScript(), uint32_t nSequenceIn=SEQUENCE_FINAL);

    // ELEMENTS: explicit serialization methods for selective asset/pegin encoding
    template <typename Stream>
    inline void Serialize(Stream& s) const {
        bool fHasAssetIssuance;
        COutPoint outpoint;
        if (!g_con_elementsmode || prevout.n == (uint32_t) -1) {
            // Coinbase inputs do not have asset issuances attached
            // to them.
            fHasAssetIssuance = false;
            outpoint = prevout;
        } else {
            // The issuance and pegin bits can't be set as it is used to indicate
            // the presence of the asset issuance or pegin objects. They should
            // never be set anyway as that would require a parent
            // transaction with over one billion outputs.
            assert(!(prevout.n & ~COutPoint::OUTPOINT_INDEX_MASK));
            // The assetIssuance object is used to represent both new
            // asset generation and reissuance of existing asset types.
            fHasAssetIssuance = !assetIssuance.IsNull();
            // The mode is placed in the upper bits of the outpoint's
            // index field. The IssuanceMode enum values are chosen to
            // make this as simple as a bitwise-OR.
            outpoint.hash = prevout.hash;
            outpoint.n = prevout.n & COutPoint::OUTPOINT_INDEX_MASK;
            if (fHasAssetIssuance) {
                outpoint.n |= COutPoint::OUTPOINT_ISSUANCE_FLAG;
            }
            if (m_is_pegin) {
                outpoint.n |= COutPoint::OUTPOINT_PEGIN_FLAG;
            }
        }

        // These are the same as bitcoin...
        s << outpoint;
        s << scriptSig;
        s << nSequence;
        // ...but then we add asset issuance data for issuances
        if (fHasAssetIssuance) {
            s << assetIssuance;
        }
    }

    template <typename Stream>
    inline void Unserialize(Stream& s) {
        bool fHasAssetIssuance;
        COutPoint outpoint;
        s >> outpoint;

        if (!g_con_elementsmode || outpoint.n == (uint32_t) -1) {
            // No asset issuance for Coinbase inputs.
            fHasAssetIssuance = false;
            prevout = outpoint;
            m_is_pegin = false;
        } else {
            // The presence of the asset issuance object is indicated by
            // a bit set in the outpoint index field.
            fHasAssetIssuance = !!(outpoint.n & COutPoint::OUTPOINT_ISSUANCE_FLAG);
            // The interpretation of this input as a peg-in is indicated by
            // a bit set in the outpoint index field.
            m_is_pegin = !!(outpoint.n & COutPoint::OUTPOINT_PEGIN_FLAG);
            // The mode, if set, must be masked out of the outpoint so
            // that the in-memory index field retains its traditional
            // meaning of identifying the index into the output array
            // of the previous transaction.
            prevout.hash = outpoint.hash;
            prevout.n = outpoint.n & COutPoint::OUTPOINT_INDEX_MASK;
        }

        s >> scriptSig;
        s >> nSequence;

        if (fHasAssetIssuance) {
            s >> assetIssuance;
            if (assetIssuance.IsNull()) {
                throw std::ios_base::failure("Superfluous issuance record");
            }
        } else {
            assetIssuance.SetNull();
        }
    }

    friend bool operator==(const CTxIn& a, const CTxIn& b)
    {
        return (a.prevout   == b.prevout &&
                a.scriptSig == b.scriptSig &&
                a.nSequence     == b.nSequence &&
                a.assetIssuance == b.assetIssuance);
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
    CConfidentialAsset nAsset;
    CConfidentialValue nValue;
    CConfidentialNonce nNonce;
    CScript scriptPubKey;

    CTxOut()
    {
        SetNull();
    }

    CTxOut(const CConfidentialAsset& nAssetIn, const CConfidentialValue& nValueIn, CScript scriptPubKeyIn);

    // ELEMENTS: explicit serialization methods for different g_con_elementsmode serializations
    template <typename Stream>
    inline void Serialize(Stream& s) const {
        if (g_con_elementsmode) {
            s << nAsset;
            s << nValue;
            s << nNonce;
        } else {
            s << nValue.GetAmount();
        }
        s << scriptPubKey;
    }

    template <typename Stream>
    inline void Unserialize(Stream& s) {
        if (g_con_elementsmode) {
            s >> nAsset;
            s >> nValue;
            s >> nNonce;
            if (nAsset.IsNull() || nValue.IsNull()) {
                throw std::ios_base::failure("Confidential values may not be null");
            }
        } else {
            CAmount value;
            s >> value;
            nValue.SetToAmount(value);
        }
        s >> scriptPubKey;
    }

    void SetNull()
    {
        nAsset.SetNull();
        nValue.SetNull();
        nNonce.SetNull();
        scriptPubKey.clear();
    }

    bool IsNull() const
    {
        if (!g_con_elementsmode) {
            // Ignore the asset and the nonce in compatibility mode.
            return nValue.IsNull() && scriptPubKey.empty();
        }

        return nAsset.IsNull() && nValue.IsNull() && nNonce.IsNull() && scriptPubKey.empty();
    }

    bool IsFee() const {
        return g_con_elementsmode && scriptPubKey == CScript()
            && nValue.IsExplicit() && nAsset.IsExplicit();
    }

    friend bool operator==(const CTxOut& a, const CTxOut& b)
    {
        return (a.nAsset == b.nAsset &&
                a.nValue == b.nValue &&
                a.nNonce == b.nNonce &&
                a.scriptPubKey == b.scriptPubKey);
    }

    friend bool operator!=(const CTxOut& a, const CTxOut& b)
    {
        return !(a == b);
    }

    std::string ToString() const;

    friend bool operator<(const CTxOut& a, const CTxOut& b)
    {
        return a.scriptPubKey < b.scriptPubKey;
    }
};

struct CMutableTransaction;

struct TransactionSerParams {
    const bool allow_witness;
    SER_PARAMS_OPFUNC
};
static constexpr TransactionSerParams TX_WITH_WITNESS{.allow_witness = true};
static constexpr TransactionSerParams TX_NO_WITNESS{.allow_witness = false};

/**
 * Basic transaction serialization format:
 * - uint32_t version
 * - std::vector<CTxIn> vin
 * - std::vector<CTxOut> vout
 * - uint32_t nLockTime
 *
 * Extended transaction serialization format:
 * - uint32_t version
 * - unsigned char dummy = 0x00
 * - unsigned char flags (!= 0)
 * - std::vector<CTxIn> vin
 * - std::vector<CTxOut> vout
 * - if (flags & 1):
 *   - CScriptWitness scriptWitness; (deserialized into CTxIn)
 * - uint32_t nLockTime
 */
template<typename Stream, typename TxType>
void UnserializeTransaction(TxType& tx, Stream& s, const TransactionSerParams& params)
{
    const bool fAllowWitness = params.allow_witness;

    s >> tx.version;
    unsigned char flags = 0;
    tx.vin.clear();
    tx.vout.clear();
    tx.witness.SetNull();

    // Witness serialization is different between Elements and Core.
    // See code comments in SerializeTransaction for details about the differences.
    if (g_con_elementsmode) {
        s >> flags;
        s >> tx.vin;
        s >> tx.vout;
        s >> tx.nLockTime;
        if (flags & 1) {
            /* The witness flag is present. */
            flags ^= 1;
            tx.witness.vtxinwit.resize(tx.vin.size());
            tx.witness.vtxoutwit.resize(tx.vout.size());
            s >> tx.witness;
            if (!tx.HasWitness()) {
                /* It's illegal to encode witnesses when all witness stacks are empty. */
                throw std::ios_base::failure("Superfluous witness record");
            }
        }
    } else {
        /* Try to read the vin. In case the dummy is there, this will be read as an empty vector. */
        s >> tx.vin;
        if (tx.vin.size() == 0 && fAllowWitness) {
            /* We read a dummy or an empty vin. */
            s >> flags;
            if (flags != 0) {
                s >> tx.vin;
                s >> tx.vout;
            }
        } else {
            /* We read a non-empty vin. Assume a normal vout follows. */
            s >> tx.vout;
        }

        if ((flags & 1) && fAllowWitness) {
            /* The witness flag is present. */
            flags ^= 1;
            tx.witness.vtxinwit.resize(tx.vin.size());
            tx.witness.vtxoutwit.resize(tx.vout.size());
            for (size_t i = 0; i < tx.vin.size(); i++) {
                s >> tx.witness.vtxinwit[i].scriptWitness.stack;
                // ELEMENTS:
                if (tx.vin[i].m_is_pegin) {
                    s >> tx.witness.vtxinwit[i].m_pegin_witness.stack;
                }
            }

            if (!tx.HasWitness()) {
                /* It's illegal to encode witnesses when all witness stacks are empty. */
                throw std::ios_base::failure("Superfluous witness record");
            }
        }
        s >> tx.nLockTime;
    }

    if (flags) {
        /* Unknown flag in the serialization */
        throw std::ios_base::failure("Unknown transaction optional data");
    }
}

template<typename Stream, typename TxType>
void SerializeTransaction(const TxType& tx, Stream& s, const TransactionSerParams& params)
{
    const bool fAllowWitness = params.allow_witness;

    s << tx.version;

    // Consistency check
    assert(tx.witness.vtxinwit.size() <= tx.vin.size());
    assert(tx.witness.vtxoutwit.size() <= tx.vout.size());

    // Check whether witnesses need to be serialized.
    unsigned char flags = 0;
    if (fAllowWitness && tx.HasWitness()) {
        flags |= 1;
    }

    // Witness serialization is different between Elements and Core.
    if (g_con_elementsmode) {
        // In Elements-style serialization, all normal data is serialized first and the
        // witnesses all in the end.
        s << flags;
        s << tx.vin;
        s << tx.vout;
        s << tx.nLockTime;
        if (flags & 1) {
            const_cast<CTxWitness*>(&tx.witness)->vtxinwit.resize(tx.vin.size());
            const_cast<CTxWitness*>(&tx.witness)->vtxoutwit.resize(tx.vout.size());
            s << tx.witness;
        }
    } else {
        // In Core-style serialization, we encode the input dummy and the witnesses
        // follow the outputs before the nLockTime.

        if (flags) {
            /* Use extended format in case witnesses are to be serialized. */
            std::vector<CTxIn> vinDummy;
            s << vinDummy;
            s << flags;
        }
        s << tx.vin;
        s << tx.vout;

        if (flags & 1) {
            const_cast<CTxWitness*>(&tx.witness)->vtxinwit.resize(tx.vin.size());
            const_cast<CTxWitness*>(&tx.witness)->vtxoutwit.resize(tx.vout.size());
            for (size_t i = 0; i < tx.vin.size(); i++) {
                s << tx.witness.vtxinwit[i].scriptWitness.stack;
                // ELEMENTS:
                if (tx.vin[i].m_is_pegin) {
                    s << tx.witness.vtxinwit[i].m_pegin_witness.stack;
                }
            }
        }
        s << tx.nLockTime;
    }
}

template<typename TxType>
inline CAmount CalculateOutputValue(const TxType& tx, CAsset policyAsset)
{
    return std::accumulate(tx.vout.cbegin(), tx.vout.cend(), CAmount{0},
        [&policyAsset](CAmount sum, const auto& txout) {
            return txout.nAsset.GetAsset() == policyAsset ? sum + txout.nValue.GetAmount() : sum;
        });
}

/** The basic transaction that is broadcasted on the network and contained in
 * blocks.  A transaction can contain multiple inputs and outputs.
 */
class CTransaction
{
public:
    // Default transaction version.
    static const int32_t CURRENT_VERSION;

    // The local variables are made const to prevent unintended modification
    // without updating the cached hash value. However, CTransaction is not
    // actually immutable; deserialization and assignment are implemented,
    // and bypass the constness. This is safe, as they update the entire
    // structure, including the hash.
    const std::vector<CTxIn> vin;
    const std::vector<CTxOut> vout;
    const uint32_t version;
    const uint32_t nLockTime;
    // For elements we need to keep track of some extra state for script witness outside of vin
    const CTxWitness witness;

private:
    /** Memory only. */
    const bool m_has_witness;
    const Txid hash;
    const Wtxid m_witness_hash;

    Txid ComputeHash() const;
    Wtxid ComputeWitnessHash() const;

    bool ComputeHasWitness() const;

public:
    /** Convert a CMutableTransaction into a CTransaction. */
    explicit CTransaction(const CMutableTransaction& tx);
    explicit CTransaction(CMutableTransaction&& tx);

    template <typename Stream>
    inline void Serialize(Stream& s) const {
        SerializeTransaction(*this, s, s.template GetParams<TransactionSerParams>());
    }

    /** This deserializing constructor is provided instead of an Unserialize method.
     *  Unserialize is not possible, since it would require overwriting const fields. */
    template <typename Stream>
    CTransaction(deserialize_type, const TransactionSerParams& params, Stream& s) : CTransaction(CMutableTransaction(deserialize, params, s)) {}
    template <typename Stream>
    CTransaction(deserialize_type, Stream& s) : CTransaction(CMutableTransaction(deserialize, s)) {}

    bool IsNull() const {
        return vin.empty() && vout.empty();
    }

    const Txid& GetHash() const LIFETIMEBOUND { return hash; }
    const Wtxid& GetWitnessHash() const LIFETIMEBOUND { return m_witness_hash; };
    // ELEMENTS: the witness only hash used in elements witness roots
    uint256 GetWitnessOnlyHash() const;

    // Return sum of txouts.
    CAmountMap GetValueOutMap() const;

    /**
     * Get the total transaction size in bytes, including witness data.
     * "Total Size" defined in BIP141 and BIP144.
     * @return Total transaction size in bytes
     */
    unsigned int GetTotalSize() const;

    bool IsCoinBase() const
    {
        return (vin.size() == 1 && vin[0].prevout.IsNull());
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

    bool HasWitness() const { return m_has_witness; }
};

/** A mutable version of CTransaction. */
struct CMutableTransaction
{
    std::vector<CTxIn> vin;
    std::vector<CTxOut> vout;
    uint32_t version;
    uint32_t nLockTime;
    // For elements we need to keep track of some extra state for script witness outside of vin
    CTxWitness witness;

    explicit CMutableTransaction();
    explicit CMutableTransaction(const CTransaction& tx);

    template <typename Stream>
    inline void Serialize(Stream& s) const {
        SerializeTransaction(*this, s, s.template GetParams<TransactionSerParams>());
    }

    template <typename Stream>
    inline void Unserialize(Stream& s) {
        UnserializeTransaction(*this, s, s.template GetParams<TransactionSerParams>());
    }

    template <typename Stream>
    CMutableTransaction(deserialize_type, const TransactionSerParams& params, Stream& s) {
        UnserializeTransaction(*this, s, params);
    }

    template <typename Stream>
    CMutableTransaction(deserialize_type, Stream& s) {
        Unserialize(s);
    }

    /** Compute the hash of this CMutableTransaction. This is computed on the
     * fly, as opposed to GetHash() in CTransaction, which uses a cached result.
     */
    Txid GetHash() const;

    bool HasWitness() const
    {
        return !witness.IsNull();
    }
};

typedef std::shared_ptr<const CTransaction> CTransactionRef;
template <typename Tx> static inline CTransactionRef MakeTransactionRef(Tx&& txIn) { return std::make_shared<const CTransaction>(std::forward<Tx>(txIn)); }

/** A generic txid reference (txid or wtxid). */
class GenTxid
{
    bool m_is_wtxid;
    uint256 m_hash;
    GenTxid(bool is_wtxid, const uint256& hash) : m_is_wtxid(is_wtxid), m_hash(hash) {}

public:
    static GenTxid Txid(const uint256& hash) { return GenTxid{false, hash}; }
    static GenTxid Wtxid(const uint256& hash) { return GenTxid{true, hash}; }
    bool IsWtxid() const { return m_is_wtxid; }
    const uint256& GetHash() const LIFETIMEBOUND { return m_hash; }
    friend bool operator==(const GenTxid& a, const GenTxid& b) { return a.m_is_wtxid == b.m_is_wtxid && a.m_hash == b.m_hash; }
    friend bool operator<(const GenTxid& a, const GenTxid& b) { return std::tie(a.m_is_wtxid, a.m_hash) < std::tie(b.m_is_wtxid, b.m_hash); }
};

#endif // BITCOIN_PRIMITIVES_TRANSACTION_H
