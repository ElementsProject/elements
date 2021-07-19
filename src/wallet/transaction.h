// Copyright (c) 2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_WALLET_TRANSACTION_H
#define BITCOIN_WALLET_TRANSACTION_H

#include <amount.h>
#include <primitives/transaction.h>
#include <serialize.h>
#include <wallet/ismine.h>
#include <threadsafety.h>
#include <tinyformat.h>
#include <util/strencodings.h>
#include <util/string.h>

#include <list>
#include <vector>

struct COutputEntry;

typedef std::map<std::string, std::string> mapValue_t;

//Get the marginal bytes of spending the specified output
int CalculateMaximumSignedInputSize(const CTxOut& txout, const CWallet* pwallet, bool use_max_sig = false);

static inline void ReadOrderPos(int64_t& nOrderPos, mapValue_t& mapValue)
{
    if (!mapValue.count("n"))
    {
        nOrderPos = -1; // TODO: calculate elsewhere
        return;
    }
    nOrderPos = atoi64(mapValue["n"]);
}

static inline void WriteOrderPos(const int64_t& nOrderPos, mapValue_t& mapValue)
{
    if (nOrderPos == -1)
        return;
    mapValue["n"] = ToString(nOrderPos);
}

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
private:
    const CWallet* const pwallet;

    /** Constant used in hashBlock to indicate tx has been abandoned, only used at
     * serialization/deserialization to avoid ambiguity with conflicted.
     */
    static constexpr const uint256& ABANDON_HASH = uint256::ONE;

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
    // TODO: Remove "NO_THREAD_SAFETY_ANALYSIS" and replace it with the correct
    // annotation "EXCLUSIVE_LOCKS_REQUIRED(pwallet->cs_wallet)". The
    // annotation "NO_THREAD_SAFETY_ANALYSIS" was temporarily added to avoid
    // having to resolve the issue of member access into incomplete type CWallet.
    CAmountMap GetCachableAmount(AmountType type, const isminefilter& filter, bool recalculate = false) const NO_THREAD_SAFETY_ANALYSIS;
    mutable CachableAmountMap m_amounts[AMOUNTTYPE_ENUM_ELEMENTS];
    /**
     * This flag is true if all m_amounts caches are empty. This is particularly
     * useful in places where MarkDirty is conditionally called and the
     * condition can be expensive and thus can be skipped if the flag is true.
     * See MarkDestinationsDirty.
     */
    mutable bool m_is_cache_empty{true};
    mutable bool fChangeCached;
    mutable bool fInMempool;
    mutable CAmountMap nChangeCached;

    CWalletTx(const CWallet* wallet, CTransactionRef arg)
        : pwallet(wallet),
          tx(std::move(arg))
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
        fInMempool = false;
        nChangeCached = CAmountMap();
        nOrderPos = -1;
        m_confirm = Confirmation{};
    }

    CTransactionRef tx;

    /** New transactions start as UNCONFIRMED. At BlockConnected,
     * they will transition to CONFIRMED. In case of reorg, at BlockDisconnected,
     * they roll back to UNCONFIRMED. If we detect a conflicting transaction at
     * block connection, we update conflicted tx and its dependencies as CONFLICTED.
     * If tx isn't confirmed and outside of mempool, the user may switch it to ABANDONED
     * by using the abandontransaction call. This last status may be override by a CONFLICTED
     * or CONFIRMED transition.
     */
    enum Status {
        UNCONFIRMED,
        CONFIRMED,
        CONFLICTED,
        ABANDONED
    };

    /** Confirmation includes tx status and a triplet of {block height/block hash/tx index in block}
     * at which tx has been confirmed. All three are set to 0 if tx is unconfirmed or abandoned.
     * Meaning of these fields changes with CONFLICTED state where they instead point to block hash
     * and block height of the deepest conflicting tx.
     */
    struct Confirmation {
        Status status;
        int block_height;
        uint256 hashBlock;
        int nIndex;
        Confirmation(Status s = UNCONFIRMED, int b = 0, uint256 h = uint256(), int i = 0) : status(s), block_height(b), hashBlock(h), nIndex(i) {}
    };

    Confirmation m_confirm;

    template<typename Stream>
    void Serialize(Stream& s) const
    {
        mapValue_t mapValueCopy = mapValue;

        mapValueCopy["fromaccount"] = "";
        WriteOrderPos(nOrderPos, mapValueCopy);
        if (nTimeSmart) {
            mapValueCopy["timesmart"] = strprintf("%u", nTimeSmart);
        }

        std::vector<char> dummy_vector1; //!< Used to be vMerkleBranch
        std::vector<char> dummy_vector2; //!< Used to be vtxPrev
        bool dummy_bool = false; //!< Used to be fSpent
        uint256 serializedHash = isAbandoned() ? ABANDON_HASH : m_confirm.hashBlock;
        int serializedIndex = isAbandoned() || isConflicted() ? -1 : m_confirm.nIndex;
        s << tx << serializedHash << dummy_vector1 << serializedIndex << dummy_vector2 << mapValueCopy << vOrderForm << fTimeReceivedIsTxTime << nTimeReceived << fFromMe << dummy_bool;
    }

    template<typename Stream>
    void Unserialize(Stream& s)
    {
        Init();

        std::vector<uint256> dummy_vector1; //!< Used to be vMerkleBranch
        std::vector<CMerkleTx> dummy_vector2; //!< Used to be vtxPrev
        bool dummy_bool; //! Used to be fSpent
        int serializedIndex;
        s >> tx >> m_confirm.hashBlock >> dummy_vector1 >> serializedIndex >> dummy_vector2 >> mapValue >> vOrderForm >> fTimeReceivedIsTxTime >> nTimeReceived >> fFromMe >> dummy_bool;

        /* At serialization/deserialization, an nIndex == -1 means that hashBlock refers to
         * the earliest block in the chain we know this or any in-wallet ancestor conflicts
         * with. If nIndex == -1 and hashBlock is ABANDON_HASH, it means transaction is abandoned.
         * In same context, an nIndex >= 0 refers to a confirmed transaction (if hashBlock set) or
         * unconfirmed one. Older clients interpret nIndex == -1 as unconfirmed for backward
         * compatibility (pre-commit 9ac63d6).
         */
        if (serializedIndex == -1 && m_confirm.hashBlock == ABANDON_HASH) {
            setAbandoned();
        } else if (serializedIndex == -1) {
            setConflicted();
        } else if (!m_confirm.hashBlock.IsNull()) {
            m_confirm.nIndex = serializedIndex;
            setConfirmed();
        }

        ReadOrderPos(nOrderPos, mapValue);
        nTimeSmart = mapValue.count("timesmart") ? (unsigned int)atoi64(mapValue["timesmart"]) : 0;

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
    void MarkDirty()
    {
        m_amounts[DEBIT].Reset();
        m_amounts[CREDIT].Reset();
        m_amounts[IMMATURE_CREDIT].Reset();
        m_amounts[AVAILABLE_CREDIT].Reset();
        fChangeCached = false;
        m_is_cache_empty = true;
        WipeUnknownBlindingData();
    }

    //! filter decides which addresses will count towards the debit
    CAmountMap GetDebit(const isminefilter& filter) const;
    CAmountMap GetCredit(const isminefilter& filter) const;
    CAmountMap GetImmatureCredit(bool fUseCache=true) const;
    // TODO: Remove "NO_THREAD_SAFETY_ANALYSIS" and replace it with the correct
    // annotation "EXCLUSIVE_LOCKS_REQUIRED(pwallet->cs_wallet)". The
    // annotation "NO_THREAD_SAFETY_ANALYSIS" was temporarily added to avoid
    // having to resolve the issue of member access into incomplete type CWallet.
    CAmountMap GetAvailableCredit(bool fUseCache=true, const isminefilter& filter=ISMINE_SPENDABLE) const NO_THREAD_SAFETY_ANALYSIS;
    CAmountMap GetImmatureWatchOnlyCredit(const bool fUseCache=true) const;
    // TODO: Remove "NO_THREAD_SAFETY_ANALYSIS" and replace it with the correct
    // annotation "EXCLUSIVE_LOCKS_REQUIRED(pwallet->cs_wallet)". The
    // annotation "NO_THREAD_SAFETY_ANALYSIS" was temporarily added to avoid
    // having to resolve the issue of member access into incomplete type CWallet.
    CAmountMap GetChange() const NO_THREAD_SAFETY_ANALYSIS;

    /** Get the marginal bytes if spending the specified output from this transaction */
    int GetSpendSize(unsigned int out, bool use_max_sig = false) const
    {
        return CalculateMaximumSignedInputSize(tx->vout[out], pwallet, use_max_sig);
    }

    void GetAmounts(std::list<COutputEntry>& listReceived,
                    std::list<COutputEntry>& listSent, CAmount& nFee, const isminefilter& filter) const;

    bool IsFromMe(const isminefilter& filter) const
    {
        return (GetDebit(filter) > CAmountMap());
    }

    /** True if only scriptSigs are different */
    bool IsEquivalentTo(const CWalletTx& tx) const;

    bool InMempool() const;
    bool IsTrusted() const;

    int64_t GetTxTime() const;

    /** Pass this transaction to node for mempool insertion and relay to peers if flag set to true */
    bool SubmitMemoryPoolAndRelay(std::string& err_string, bool relay);

    // ELEMENTS:

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
    void GetBlindingData(const unsigned int map_index, const std::vector<unsigned char>& vchRangeproof, const CConfidentialValue& conf_value, const CConfidentialAsset& conf_asset, const CConfidentialNonce nonce, const CScript& scriptPubKey, CPubKey* blinding_pubkey_out, CAmount* value_out, uint256* value_factor_out, CAsset* asset_out, uint256* asset_factor_out) const;
    void WipeUnknownBlindingData();

public:
    // For use in wallet transaction creation to remember 3rd party values
    // Unneeded for issuance.
    void SetBlindingData(const unsigned int output_index, const CPubKey& blinding_pubkey, const CAmount value, const uint256& value_factor, const CAsset& asset, const uint256& asset_factor);

    // Convenience method to retrieve all blinding data at once, for an ordinary non-issuance tx
    void GetNonIssuanceBlindingData(const unsigned int output_index, CPubKey* blinding_pubkey_out, CAmount* value_out, uint256* value_factor_out, CAsset* asset_out, uint256* asset_factor_out) const;

    //! Returns either the value out (if it is known) or -1
    CAmount GetOutputValueOut(unsigned int ouput_index) const;

    //! Returns either the blinding factor (if it is to us) or 0
    uint256 GetOutputAmountBlindingFactor(unsigned int output_index) const;
    uint256 GetOutputAssetBlindingFactor(unsigned int output_index) const;
    //! Returns the underlying asset type, or 0 if unknown
    CAsset GetOutputAsset(unsigned int output_index) const;
    //! Get the issuance CAssets for both the asset itself and the issuing tokens
    void GetIssuanceAssets(unsigned int vinIndex, CAsset* out_asset, CAsset* out_reissuance_token) const;
    // ! Return map of issued assets at input_index
    CAmountMap GetIssuanceAssets(unsigned int input_index) const;
    // ! Returns receiver's blinding pubkey
    CPubKey GetOutputBlindingPubKey(unsigned int output_index) const;
    //! Get the issuance blinder for either the asset itself or the issuing tokens
    uint256 GetIssuanceBlindingFactor(unsigned int input_index, bool reissuance_token) const;
    //! Get the issuance amount for either the asset itself or the issuing tokens
    CAmount GetIssuanceAmount(unsigned int input_index, bool reissuance_token) const;

    //! Get the mapValue offset for a specific vin index and type of issuance pseudo-input
    unsigned int GetPseudoInputOffset(unsigned int input_index, bool reissuance_token) const;

    // TODO: Remove "NO_THREAD_SAFETY_ANALYSIS" and replace it with the correct
    // annotation "EXCLUSIVE_LOCKS_REQUIRED(pwallet->cs_wallet)". The annotation
    // "NO_THREAD_SAFETY_ANALYSIS" was temporarily added to avoid having to
    // resolve the issue of member access into incomplete type CWallet. Note
    // that we still have the runtime check "AssertLockHeld(pwallet->cs_wallet)"
    // in place.
    std::set<uint256> GetConflicts() const NO_THREAD_SAFETY_ANALYSIS;

    /**
     * Return depth of transaction in blockchain:
     * <0  : conflicts with a transaction this deep in the blockchain
     *  0  : in memory pool, waiting to be included in a block
     * >=1 : this many blocks deep in the main chain
     */
    // TODO: Remove "NO_THREAD_SAFETY_ANALYSIS" and replace it with the correct
    // annotation "EXCLUSIVE_LOCKS_REQUIRED(pwallet->cs_wallet)". The annotation
    // "NO_THREAD_SAFETY_ANALYSIS" was temporarily added to avoid having to
    // resolve the issue of member access into incomplete type CWallet. Note
    // that we still have the runtime check "AssertLockHeld(pwallet->cs_wallet)"
    // in place.
    int GetDepthInMainChain() const NO_THREAD_SAFETY_ANALYSIS;
    bool IsInMainChain() const { return GetDepthInMainChain() > 0; }

    /**
     * @return number of blocks to maturity for this transaction:
     *  0 : is not a coinbase transaction, or is a mature coinbase transaction
     * >0 : is a coinbase transaction which matures in this many blocks
     */
    int GetBlocksToMaturity() const;
    bool isAbandoned() const { return m_confirm.status == CWalletTx::ABANDONED; }
    void setAbandoned()
    {
        m_confirm.status = CWalletTx::ABANDONED;
        m_confirm.hashBlock = uint256();
        m_confirm.block_height = 0;
        m_confirm.nIndex = 0;
    }
    bool isConflicted() const { return m_confirm.status == CWalletTx::CONFLICTED; }
    void setConflicted() { m_confirm.status = CWalletTx::CONFLICTED; }
    bool isUnconfirmed() const { return m_confirm.status == CWalletTx::UNCONFIRMED; }
    void setUnconfirmed() { m_confirm.status = CWalletTx::UNCONFIRMED; }
    bool isConfirmed() const { return m_confirm.status == CWalletTx::CONFIRMED; }
    void setConfirmed() { m_confirm.status = CWalletTx::CONFIRMED; }
    const uint256& GetHash() const { return tx->GetHash(); }
    bool IsCoinBase() const { return tx->IsCoinBase(); }
    bool IsImmatureCoinBase() const;

    // Disable copying of CWalletTx objects to prevent bugs where instances get
    // copied in and out of the mapWallet map, and fields are updated in the
    // wrong copy.
    CWalletTx(CWalletTx const &) = delete;
    void operator=(CWalletTx const &x) = delete;
};

#endif // BITCOIN_WALLET_TRANSACTION_H
