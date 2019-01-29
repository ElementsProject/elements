
#ifndef BITCOIN_PRIMITIVES_CONFIDENTIAL_H
#define BITCOIN_PRIMITIVES_CONFIDENTIAL_H

#include <amount.h>
#include <asset.h>
#include <script/script.h>
#include <serialize.h>
#include <span.h>
#include <uint256.h>
#include <utilstrencodings.h>

extern bool g_con_elementswitness;

/**
 * Confidential assets, values, and nonces all share enough code in common
 * that it makes sense to define a common abstract base class. */
template<size_t ExplicitSize, unsigned char PrefixA, unsigned char PrefixB>
class CConfidentialCommitment
{
public:
    static const size_t nExplicitSize = ExplicitSize;
    static const size_t nCommittedSize = 33;

    std::vector<unsigned char> vchCommitment;

    CConfidentialCommitment() { SetNull(); }

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action) {
        unsigned char version = vchCommitment.empty()? 0: vchCommitment[0];
        READWRITE(version);
        if (ser_action.ForRead()) {
            switch (version) {
                /* Null */
                case 0:
                    vchCommitment.clear();
                    return;
                /* Explicit value */
                case 1:
                    vchCommitment.resize(nExplicitSize);
                    break;
                /* Confidential commitment */
                case PrefixA:
                case PrefixB:
                    vchCommitment.resize(nCommittedSize);
                    break;
                /* Invalid serialization! */
                default:
                    throw std::ios_base::failure("Unrecognized serialization prefix");
            }
            vchCommitment[0] = version;
        }
        if (vchCommitment.size() > 1) {
            READWRITE(REF(Span<unsigned char>(vchCommitment.data() + 1, vchCommitment.size()-1)));
        }
    }

    /* Null is the default state when no explicit asset or confidential
     * asset commitment has been set. */
    bool IsNull() const { return vchCommitment.empty(); }
    void SetNull() { vchCommitment.clear(); }

    bool IsExplicit() const
    {
        return vchCommitment.size()==nExplicitSize && vchCommitment[0]==1;
    }

    bool IsCommitment() const
    {
        return vchCommitment.size()==nCommittedSize && (vchCommitment[0]==PrefixA || vchCommitment[0]==PrefixB);
    }

    bool IsValid() const
    {
        return IsNull() || IsExplicit() || IsCommitment();
    }

    std::string GetHex() const { return HexStr(vchCommitment); }

    friend bool operator==(const CConfidentialCommitment& a, const CConfidentialCommitment& b)
    {
        return a.vchCommitment == b.vchCommitment;
    }

    friend bool operator!=(const CConfidentialCommitment& a, const CConfidentialCommitment& b)
    {
        return !(a == b);
    }
};

/** A commitment to a blinded asset, or an explicit asset NUMS identifier */
class CConfidentialAsset : public CConfidentialCommitment<33, 10, 11>
{
public:
    CConfidentialAsset() {
        SetNull();
    }
    CConfidentialAsset(CAsset asset) { SetToAsset(asset); }

    void SetNull() {
        vchCommitment.clear();

        // Set to dummy asset when not doing CA.
        if (!g_con_elementswitness) {
            SetToAsset(CAsset());
        }
    }

    /* An explicit asset identifier is a 256-bit nothing-up-my-sleeve number
     * that used as auxiliary input to the Pedersen commitment setup to create
     * a generator which acts as the asset tag. */
    const CAsset& GetAsset() const
    {
        assert(IsExplicit());
        return *reinterpret_cast<const CAsset*>(&vchCommitment[1]);
    }
    void SetToAsset(const CAsset& asset);

};

/** A 33-byte commitment to a confidential value, or a 64-bit explicit value. */
class CConfidentialValue : public CConfidentialCommitment<9, 8, 9>
{
public:
    CConfidentialValue() { SetNull(); }
    CConfidentialValue(CAmount nAmount) { SetToAmount(nAmount); }

    /* An explicit value is called an amount. The first byte indicates it is
     * an explicit value, and the remaining 8 bytes is the value serialized as
     * a 64-bit big-endian integer. */
    CAmount GetAmount() const
    {
        if (!g_con_elementswitness && IsNull()) {
            return -1;
        }

        assert(IsExplicit());;
        return ReadBE64(&vchCommitment[1]);
    }
    void SetToAmount(CAmount nAmount);
};

/**
 * A 33-byte data field that typically is used to convey to the
 * recipient the ECDH ephemeral key (an EC point) for deriving the
 * transaction output blinding factor. */
class CConfidentialNonce : public CConfidentialCommitment<33, 2, 3>
{
public:
    CConfidentialNonce() { SetNull(); }
};

/** A new asset issuance, or a reissuance (inflation) of an existing asset */
class CAssetIssuance
{
public:
    // == 0
    //   Indicates new asset issuance.
    // != 0
    //   This is a revelation of the blinding factor for the input,
    //   which shows that the input being spent is of the reissuance
    //   capability type for the asset being inflated.
    uint256 assetBlindingNonce;

    // New asset issuance:
    //   This is a 32-byte nonce of no consensus-defined meaning,
    //   but is used as additional entropy to the asset tag calculation.
    //   This is used by higher-layer protocols for defining the
    //   Ricardian contract governing the asset.
    // Existing asset reissuance:
    //   The original asset entropy (combination of Ricardian contract
    //   and outpoint used) which was used to generate the fixed asset
    //   tag and reissuance tokens.
    uint256 assetEntropy;

    // Both explicit and blinded issuance amounts are supported
    // (see class definition for CConfidentialValue for details).
    CConfidentialValue nAmount;

    // If nonzero, specifies the number of asset issuance tokens to
    // generate. These tokens are made available to the outputs of the
    // generating transaction.
    CConfidentialValue nInflationKeys;

public:
    CAssetIssuance()
    {
        SetNull();
    }

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action)
    {
        READWRITE(assetBlindingNonce);
        READWRITE(assetEntropy);
        READWRITE(nAmount);
        READWRITE(nInflationKeys);
    }

    void SetNull() { nAmount.SetNull(); nInflationKeys.SetNull(); }
    bool IsNull() const { return (nAmount.IsNull() && nInflationKeys.IsNull()); }

    friend bool operator==(const CAssetIssuance& a, const CAssetIssuance& b)
    {
        return a.assetBlindingNonce == b.assetBlindingNonce &&
               a.assetEntropy == b.assetEntropy &&
               a.nAmount == b.nAmount &&
               a.nInflationKeys == b.nInflationKeys;
    }

    friend bool operator!=(const CAssetIssuance& a, const CAssetIssuance& b)
    {
        return !(a == b);
    }

    std::string ToString() const;
};

#endif // BITCOIN_PRIMITIVES_CONFIDENTIAL_H
