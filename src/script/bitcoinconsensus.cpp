// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <script/bitcoinconsensus.h>

#include <primitives/transaction.h>
#include <pubkey.h>
#include <script/interpreter.h>
#include <streams.h>
#include <version.h>

namespace {

/** A class that deserializes a single CTransaction one time. */
class TxInputStream
{
public:
    TxInputStream(int nTypeIn, int nVersionIn, const unsigned char *txTo, size_t txToLen) :
    m_type(nTypeIn),
    m_version(nVersionIn),
    m_data(txTo),
    m_remaining(txToLen)
    {}

    void read(char* pch, size_t nSize)
    {
        if (nSize > m_remaining)
            throw std::ios_base::failure(std::string(__func__) + ": end of data");

        if (pch == nullptr)
            throw std::ios_base::failure(std::string(__func__) + ": bad destination buffer");

        if (m_data == nullptr)
            throw std::ios_base::failure(std::string(__func__) + ": bad source buffer");

        memcpy(pch, m_data, nSize);
        m_remaining -= nSize;
        m_data += nSize;
    }

    template<typename T>
    TxInputStream& operator>>(T&& obj)
    {
        ::Unserialize(*this, obj);
        return *this;
    }

    int GetVersion() const { return m_version; }
    int GetType() const { return m_type; }
private:
    const int m_type;
    const int m_version;
    const unsigned char* m_data;
    size_t m_remaining;
};

inline int set_error(bitcoinconsensus_error* ret, bitcoinconsensus_error serror)
{
    if (ret)
        *ret = serror;
    return 0;
}

struct ECCryptoClosure
{
    ECCVerifyHandle handle;
};

ECCryptoClosure instance_of_eccryptoclosure;
} // namespace

/** Check that all specified flags are part of the libconsensus interface. */
static bool verify_flags(unsigned int flags)
{
    return (flags & ~(bitcoinconsensus_SCRIPT_FLAGS_VERIFY_ALL)) == 0;
}

static int verify_script(const unsigned char *parent_genesis_hash, const unsigned char *parent_pegged_asset,
                                    const unsigned char *scriptPubKey, unsigned int scriptPubKeyLen, CConfidentialValue amount,
                                    const unsigned char *txTo        , unsigned int txToLen,
                                    unsigned int nIn, unsigned int flags, bitcoinconsensus_error* err)
{
    if (!verify_flags(flags)) {
        return set_error(err, bitcoinconsensus_ERR_INVALID_FLAGS);
    }
    try {
        TxInputStream stream(SER_NETWORK, PROTOCOL_VERSION, txTo, txToLen);
        CTransaction tx(deserialize, stream);
        if (nIn >= tx.vin.size())
            return set_error(err, bitcoinconsensus_ERR_TX_INDEX);
        if (GetSerializeSize(tx, PROTOCOL_VERSION) != txToLen)
            return set_error(err, bitcoinconsensus_ERR_TX_SIZE_MISMATCH);

        // Regardless of the verification result, the tx did not error.
        set_error(err, bitcoinconsensus_ERR_OK);

        auto parent_genesis_hash_ = parent_genesis_hash ? uint256{parent_genesis_hash, 32} : uint256{};
        auto parent_pegged_asset_ = CAsset(parent_pegged_asset ? uint256{parent_pegged_asset, 32} : uint256{});
        PrecomputedTransactionData txdata(parent_genesis_hash_, parent_pegged_asset_);
        txdata.Init(tx, {});
        const CScriptWitness* pScriptWitness = (tx.witness.vtxinwit.size() > nIn ? &tx.witness.vtxinwit[nIn].scriptWitness : NULL);
        return VerifyScript(tx.vin[nIn].scriptSig, CScript(scriptPubKey, scriptPubKey + scriptPubKeyLen), pScriptWitness, flags, TransactionSignatureChecker(&tx, nIn, amount, txdata), NULL);
    } catch (const std::exception&) {
        return set_error(err, bitcoinconsensus_ERR_TX_DESERIALIZE); // Error deserializing
    }
}

int bitcoinconsensus_verify_script_with_amount(const unsigned char *parent_genesis_hash, const unsigned char *parent_pegged_asset,
                                    const unsigned char *scriptPubKey, unsigned int scriptPubKeyLen,
                                    const unsigned char *amount, unsigned int amountLen,
                                    const unsigned char *txTo        , unsigned int txToLen,
                                    unsigned int nIn, unsigned int flags, bitcoinconsensus_error* err)
{
    try {
        TxInputStream stream(SER_NETWORK, PROTOCOL_VERSION, amount, amountLen);
        CConfidentialValue am;
        stream >> am;

        return ::verify_script(parent_genesis_hash, parent_pegged_asset, scriptPubKey, scriptPubKeyLen, am, txTo, txToLen, nIn, flags, err);
    } catch (const std::exception&) {
        return set_error(err, bitcoinconsensus_ERR_TX_DESERIALIZE); // Error deserializing
    }
}


int bitcoinconsensus_verify_script(const unsigned char *parent_genesis_hash, const unsigned char *parent_pegged_asset,
                                   const unsigned char *scriptPubKey, unsigned int scriptPubKeyLen,
                                   const unsigned char *txTo        , unsigned int txToLen,
                                   unsigned int nIn, unsigned int flags, bitcoinconsensus_error* err)
{
    if (flags & bitcoinconsensus_SCRIPT_FLAGS_VERIFY_WITNESS) {
        return set_error(err, bitcoinconsensus_ERR_AMOUNT_REQUIRED);
    }

    CConfidentialValue am(0);
    return ::verify_script(parent_genesis_hash, parent_pegged_asset, scriptPubKey, scriptPubKeyLen, am, txTo, txToLen, nIn, flags, err);
}

unsigned int bitcoinconsensus_version()
{
    // Just use the API version for now
    return BITCOINCONSENSUS_API_VER;
}
