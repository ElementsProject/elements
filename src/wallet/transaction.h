// Copyright (c) 2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_WALLET_TRANSACTION_H
#define BITCOIN_WALLET_TRANSACTION_H

#include <consensus/amount.h>
#include <primitives/transaction.h>
#include <serialize.h>
#include <wallet/ismine.h>
#include <threadsafety.h>
#include <tinyformat.h>
#include <util/overloaded.h>
#include <util/strencodings.h>
#include <util/string.h>

#include <list>
#include <variant>
#include <vector>

namespace wallet {
//! State of transaction confirmed in a block.
struct TxStateConfirmed {
    uint256 confirmed_block_hash;
    int confirmed_block_height;
    int position_in_block;

    explicit TxStateConfirmed(const uint256& block_hash, int height, int index) : confirmed_block_hash(block_hash), confirmed_block_height(height), position_in_block(index) {}
};

//! State of transaction added to mempool.
struct TxStateInMempool {
};

//! State of rejected transaction that conflicts with a confirmed block.
struct TxStateConflicted {
    uint256 conflicting_block_hash;
    int conflicting_block_height;

    explicit TxStateConflicted(const uint256& block_hash, int height) : conflicting_block_hash(block_hash), conflicting_block_height(height) {}
};

//! State of transaction not confirmed or conflicting with a known block and
//! not in the mempool. May conflict with the mempool, or with an unknown block,
//! or be abandoned, never broadcast, or rejected from the mempool for another
//! reason.
struct TxStateInactive {
    bool abandoned;

    explicit TxStateInactive(bool abandoned = false) : abandoned(abandoned) {}
};

//! State of transaction loaded in an unrecognized state with unexpected hash or
//! index values. Treated as inactive (with serialized hash and index values
//! preserved) by default, but may enter another state if transaction is added
//! to the mempool, or confirmed, or abandoned, or found conflicting.
struct TxStateUnrecognized {
    uint256 block_hash;
    int index;

    TxStateUnrecognized(const uint256& block_hash, int index) : block_hash(block_hash), index(index) {}
};

//! All possible CWalletTx states
using TxState = std::variant<TxStateConfirmed, TxStateInMempool, TxStateConflicted, TxStateInactive, TxStateUnrecognized>;

//! Subset of states transaction sync logic is implemented to handle.
using SyncTxState = std::variant<TxStateConfirmed, TxStateInMempool, TxStateInactive>;

//! Try to interpret deserialized TxStateUnrecognized data as a recognized state.
static inline TxState TxStateInterpretSerialized(TxStateUnrecognized data)
{
    if (data.block_hash == uint256::ZERO) {
        if (data.index == 0) return TxStateInactive{};
    } else if (data.block_hash == uint256::ONE) {
        if (data.index == -1) return TxStateInactive{/*abandoned=*/true};
    } else if (data.index >= 0) {
        return TxStateConfirmed{data.block_hash, /*height=*/-1, data.index};
    } else if (data.index == -1) {
        return TxStateConflicted{data.block_hash, /*height=*/-1};
    }
    return data;
}

//! Get TxState serialized block hash. Inverse of TxStateInterpretSerialized.
static inline uint256 TxStateSerializedBlockHash(const TxState& state)
{
    return std::visit(util::Overloaded{
        [](const TxStateInactive& inactive) { return inactive.abandoned ? uint256::ONE : uint256::ZERO; },
        [](const TxStateInMempool& in_mempool) { return uint256::ZERO; },
        [](const TxStateConfirmed& confirmed) { return confirmed.confirmed_block_hash; },
        [](const TxStateConflicted& conflicted) { return conflicted.conflicting_block_hash; },
        [](const TxStateUnrecognized& unrecognized) { return unrecognized.block_hash; }
    }, state);
}

//! Get TxState serialized block index. Inverse of TxStateInterpretSerialized.
static inline int TxStateSerializedIndex(const TxState& state)
{
    return std::visit(util::Overloaded{
        [](const TxStateInactive& inactive) { return inactive.abandoned ? -1 : 0; },
        [](const TxStateInMempool& in_mempool) { return 0; },
        [](const TxStateConfirmed& confirmed) { return confirmed.position_in_block; },
        [](const TxStateConflicted& conflicted) { return -1; },
        [](const TxStateUnrecognized& unrecognized) { return unrecognized.index; }
    }, state);
}


typedef std::map<std::string, std::string> mapValue_t;

/** Legacy class used for deserializing vtxPrev for backwards compatibility.
 * vtxPrev was removed in commit 93a18a3650292afbb441a47d1fa1b94aeb0164e3,
 * but old wallet.dat files may still contain vtxPrev vectors of CMerkleTxs.
 * These need to get deserialized for field alignment when deserializing
 * a CWalletTx, but the deserialized values are discarded.**/
class CMerkleTx
{
public:
    template<typename Stream>
    void Unserialize(Stream& s)
    {
        CTransactionRef tx;
        uint256 hashBlock;
        std::vector<uint256> vMerkleBranch;
        int nIndex;

        s >> tx >> hashBlock >> vMerkleBranch >> nIndex;
    }
};

/**
 * A transaction with a bunch of additional info that only the owner cares about.
 * It includes any unrecorded transactions needed to link it back to the block chain.
 */
class CWalletTx
{
public:
    /**
     * Key/value map with information about the transaction.
     *
     * The following keys can be read and written through the map and are
     * serialized in the wallet database:
     *
     *     "comment", "to"   - comment strings provided to sendtoaddress,
     *                         and sendmany wallet RPCs
     *     "replaces_txid"   - txid (as HexStr) of transaction replaced by
     *                         bumpfee on transaction created by bumpfee
     *     "replaced_by_txid" - txid (as HexStr) of transaction created by
     *                         bumpfee on transaction replaced by bumpfee
     *     "from", "message" - obsolete fields that could be set in UI prior to
     *                         2011 (removed in commit 4d9b223)
     *
     * The following keys are serialized in the wallet database, but shouldn't
     * be read or written through the map (they will be temporarily added and
     * removed from the map during serialization):
     *
     *     "fromaccount"     - serialized strFromAccount value
     *     "n"               - serialized nOrderPos value
     *     "timesmart"       - serialized nTimeSmart value
     *     "spent"           - serialized vfSpent value that existed prior to
     *                         2014 (removed in commit 93a18a3)
     */
    mutable mapValue_t mapValue;
    std::vector<std::pair<std::string, std::string> > vOrderForm;
    unsigned int fTimeReceivedIsTxTime;
    unsigned int nTimeReceived; //!< time received by this node
    /**
     * Stable timestamp that never changes, and reflects the order a transaction
     * was added to the wallet. Timestamp is based on the block time for a
     * transaction added as part of a block, or else the time when the
     * transaction was received if it wasn't part of a block, with the timestamp
     * adjusted in both cases so timestamp order matches the order transactions
     * were added to the wallet. More details can be found in
     * CWallet::ComputeTimeSmart().
     */
    unsigned int nTimeSmart;
    /**
     * From me flag is set to 1 for transactions that were created by the wallet
     * on this bitcoin node, and set to 0 for transactions that were created
     * externally and came in through the network or sendrawtransaction RPC.
     */
    bool fFromMe;
    int64_t nOrderPos; //!< position in ordered transaction list
    std::multimap<int64_t, CWalletTx*>::const_iterator m_it_wtxOrdered;

    // memory only
    enum AmountType { DEBIT, CREDIT, IMMATURE_CREDIT, AVAILABLE_CREDIT, AMOUNTTYPE_ENUM_ELEMENTS };
    mutable CachableAmountMap m_amounts[AMOUNTTYPE_ENUM_ELEMENTS];
    /**
     * This flag is true if all m_amounts caches are empty. This is particularly
     * useful in places where MarkDirty is conditionally called and the
     * condition can be expensive and thus can be skipped if the flag is true.
     * See MarkDestinationsDirty.
     */
    mutable bool m_is_cache_empty{true};
    mutable bool fChangeCached;
    mutable CAmountMap nChangeCached;

    CWalletTx(CTransactionRef tx, const TxState& state) : tx(std::move(tx)), m_state(state)
    {
        Init();
    }

    void Init()
    {
        mapValue.clear();
        vOrderForm.clear();
        fTimeReceivedIsTxTime = false;
        nTimeReceived = 0;
        nTimeSmart = 0;
        fFromMe = false;
        fChangeCached = false;
        nChangeCached = CAmountMap();
        nOrderPos = -1;
    }

    CTransactionRef tx;
    TxState m_state;

    template<typename Stream>
    void Serialize(Stream& s) const
    {
        mapValue_t mapValueCopy = mapValue;

        mapValueCopy["fromaccount"] = "";
        if (nOrderPos != -1) {
            mapValueCopy["n"] = ToString(nOrderPos);
        }
        if (nTimeSmart) {
            mapValueCopy["timesmart"] = strprintf("%u", nTimeSmart);
        }

        std::vector<uint8_t> dummy_vector1; //!< Used to be vMerkleBranch
        std::vector<uint8_t> dummy_vector2; //!< Used to be vtxPrev
        bool dummy_bool = false; //!< Used to be fSpent
        uint256 serializedHash = TxStateSerializedBlockHash(m_state);
        int serializedIndex = TxStateSerializedIndex(m_state);
        s << tx << serializedHash << dummy_vector1 << serializedIndex << dummy_vector2 << mapValueCopy << vOrderForm << fTimeReceivedIsTxTime << nTimeReceived << fFromMe << dummy_bool;
    }

    template<typename Stream>
    void Unserialize(Stream& s)
    {
        Init();

        std::vector<uint256> dummy_vector1; //!< Used to be vMerkleBranch
        std::vector<CMerkleTx> dummy_vector2; //!< Used to be vtxPrev
        bool dummy_bool; //! Used to be fSpent
        uint256 serialized_block_hash;
        int serializedIndex;
        s >> tx >> serialized_block_hash >> dummy_vector1 >> serializedIndex >> dummy_vector2 >> mapValue >> vOrderForm >> fTimeReceivedIsTxTime >> nTimeReceived >> fFromMe >> dummy_bool;

        m_state = TxStateInterpretSerialized({serialized_block_hash, serializedIndex});

        const auto it_op = mapValue.find("n");
        nOrderPos = (it_op != mapValue.end()) ? LocaleIndependentAtoi<int64_t>(it_op->second) : -1;
        const auto it_ts = mapValue.find("timesmart");
        nTimeSmart = (it_ts != mapValue.end()) ? static_cast<unsigned int>(LocaleIndependentAtoi<int64_t>(it_ts->second)) : 0;

        mapValue.erase("fromaccount");
        mapValue.erase("spent");
        mapValue.erase("n");
        mapValue.erase("timesmart");
    }

    void SetTx(CTransactionRef arg)
    {
        tx = std::move(arg);
    }

    //! make sure balances are recalculated
    void MarkDirty(const CWallet& wallet)
    {
        m_amounts[DEBIT].Reset();
        m_amounts[CREDIT].Reset();
        m_amounts[IMMATURE_CREDIT].Reset();
        m_amounts[AVAILABLE_CREDIT].Reset();
        fChangeCached = false;
        m_is_cache_empty = true;
        WipeUnknownBlindingData(wallet);
    }

    /** True if only scriptSigs are different */
    bool IsEquivalentTo(const CWalletTx& tx) const;

    bool InMempool() const;

    int64_t GetTxTime() const;

    template<typename T> const T* state() const { return std::get_if<T>(&m_state); }
    template<typename T> T* state() { return std::get_if<T>(&m_state); }

    bool isAbandoned() const { return state<TxStateInactive>() && state<TxStateInactive>()->abandoned; }
    bool isConflicted() const { return state<TxStateConflicted>(); }
    bool isUnconfirmed() const { return !isAbandoned() && !isConflicted() && !isConfirmed(); }
    bool isConfirmed() const { return state<TxStateConfirmed>(); }
    const uint256& GetHash() const { return tx->GetHash(); }
    bool IsCoinBase() const { return tx->IsCoinBase(); }

    // ELEMENTS
private:
    /* Computes, stores and returns the unblinded info, or retrieves if already computed previously.
    * @param[in]    map_index - Where to store the blinding data. Issuance data is stored after the output data, with additional index offset calculated via GetPseudoInputOffset
    * @param[in]    vchRangeproof - The rangeproof to unwind
    * @param[in]    conf_value - The value to unblind
    * @param[in]    conf_asset - The asset to unblind
    * @param[in]    nonce - The nonce used to ECDH with the blinding key. This is null for issuance as blinding key is directly used as nonce
    * @param[in]    scriptPubKey - The script being committed to by the rangeproof
    * @param[out]   blinding_pubkey_out - Pointer to the recovered pubkey of the destination
    * @param[out]   value_out - Pointer to the CAmount where the unblinded amount will be stored
    * @param[out]   value_factor_out - Pointer to the recovered value blinding factor of the output
    * @param[out]   asset_out - Pointer to the recovered underlying asset type
    * @param[out]   asset_factor_out - Pointer to the recovered asset blinding factor of the output
    */
    void GetBlindingData(const CWallet& wallet, const unsigned int map_index, const std::vector<unsigned char>& vchRangeproof, const CConfidentialValue& conf_value, const CConfidentialAsset& conf_asset, const CConfidentialNonce nonce, const CScript& scriptPubKey, CPubKey* blinding_pubkey_out, CAmount* value_out, uint256* value_factor_out, CAsset* asset_out, uint256* asset_factor_out) const;
    void WipeUnknownBlindingData(const CWallet& wallet);

public:
    // For use in wallet transaction creation to remember 3rd party values
    // Unneeded for issuance.
    void SetBlindingData(const unsigned int output_index, const CPubKey& blinding_pubkey, const CAmount value, const uint256& value_factor, const CAsset& asset, const uint256& asset_factor);

    // Convenience method to retrieve all blinding data at once, for an ordinary non-issuance tx
    void GetNonIssuanceBlindingData(const CWallet& wallet, const unsigned int output_index, CPubKey* blinding_pubkey_out, CAmount* value_out, uint256* value_factor_out, CAsset* asset_out, uint256* asset_factor_out) const;

    //! Returns either the blinding factor (if it is to us) or 0
    uint256 GetOutputAmountBlindingFactor(const CWallet& wallet, unsigned int output_index) const;
    uint256 GetOutputAssetBlindingFactor(const CWallet& wallet, unsigned int output_index) const;
    //! Get the issuance CAssets for both the asset itself and the issuing tokens
    void GetIssuanceAssets(unsigned int vinIndex, CAsset* out_asset, CAsset* out_reissuance_token) const;
    // ! Return map of issued assets at input_index
    CAmountMap GetIssuanceAssets(const CWallet& wallet, unsigned int input_index) const;
    // ! Returns receiver's blinding pubkey
    CPubKey GetOutputBlindingPubKey(const CWallet& wallet, unsigned int output_index) const;
    //! Get the issuance blinder for either the asset itself or the issuing tokens
    uint256 GetIssuanceBlindingFactor(const CWallet& wallet, unsigned int input_index, bool reissuance_token) const;
    //! Get the issuance amount for either the asset itself or the issuing tokens
    CAmount GetIssuanceAmount(const CWallet& wallet, unsigned int input_index, bool reissuance_token) const;

    //! Get the mapValue offset for a specific vin index and type of issuance pseudo-input
    unsigned int GetPseudoInputOffset(unsigned int input_index, bool reissuance_token) const;
    // END ELEMENTS

    //! Returns either the value out (if it is known) or -1
    CAmount GetOutputValueOut(const CWallet& wallet, unsigned int ouput_index) const;
    //! Returns the underlying asset type, or 0 if unknown
    CAsset GetOutputAsset(const CWallet& wallet, unsigned int output_index) const;

    // END ELEMENTS

    // Disable copying of CWalletTx objects to prevent bugs where instances get
    // copied in and out of the mapWallet map, and fields are updated in the
    // wrong copy.
    CWalletTx(CWalletTx const &) = delete;
    void operator=(CWalletTx const &x) = delete;
};
} // namespace wallet

#endif // BITCOIN_WALLET_TRANSACTION_H
