#ifndef BITCOIN_ASSET_H
#define BITCOIN_ASSET_H

#include <uint256.h>

#include <consensus/amount.h>
#include <serialize.h>
#include <iostream>

/**
 *  Native Asset Issuance
 *
 *  An asset identifier tag, a 256 bits serialized hash (sha256) defined
 *  by the issuance transaction from which the output’s coins are derived.
 *  Each output contains coins from a single asset/currency.
 *  For the host currency, the similarly-calculated hash of the chain’s genesis
 *  block is used instead.
**/
struct CAsset {
    uint256 id;

    CAsset() { }
    explicit CAsset(const uint256& idIn) : id(idIn) { }
    explicit CAsset(const std::vector<unsigned char>& vchIDIn) : id(vchIDIn) { }

    SERIALIZE_METHODS(CAsset, obj) { READWRITE(obj.id); }

    bool IsNull() const { return id.IsNull(); }
    void SetNull() { id.SetNull(); }

    unsigned char* begin() { return id.begin(); }
    unsigned char* end() { return id.end(); }
    const unsigned char* begin() const { return id.begin(); }
    const unsigned char* end() const { return id.end(); }

    std::string GetHex() const { return id.GetHex(); }
    void SetHex(const std::string& str) { id.SetHex(str); }

    friend bool operator==(const CAsset& a, const CAsset& b)
    {
        return a.id == b.id;
    }

    friend bool operator!=(const CAsset& a, const CAsset& b)
    {
        return !(a == b);
    }

    friend bool operator<(const CAsset& a, const CAsset& b)
    {
        return a.id < b.id;
    }
};

/** Used for consensus fee and general wallet accounting*/
typedef std::map<CAsset, CAmount> CAmountMap;

CAmountMap& operator+=(CAmountMap& a, const CAmountMap& b);
CAmountMap& operator-=(CAmountMap& a, const CAmountMap& b);
CAmountMap operator+(const CAmountMap& a, const CAmountMap& b);
CAmountMap operator-(const CAmountMap& a, const CAmountMap& b);

// WARNING: Comparisons are only looking for *complete* ordering.
// For strict inequality checks, if any entry would fail the non-strict
// inequality, the comparison will fail. Therefore it is possible
// that all inequality comparison checks may fail.
// Therefore if >/< fails against a CAmountMap(), this means there
// are all zeroes or one or more negative values.
//
// Examples: 1A + 2B <= 1A + 2B + 1C
//      and  1A + 2B <  1A + 2B + 1C
//                   but
//           !(1A + 2B == 1A + 2B + 1C)
//-------------------------------------
//           1A + 2B == 1A + 2B
//      and  1A + 2B <= 1A + 2B
//                   but
//           !(1A + 2B < 1A + 2B)
//-------------------------------------
//           !(1A + 2B == 2B - 1C)
//           !(1A + 2B >= 2B - 1C)
//                     ...
//           !(1A + 2B < 2B - 1C)
//      and   1A + 2B != 2B - 1C
bool operator<(const CAmountMap& a, const CAmountMap& b);
bool operator<=(const CAmountMap& a, const CAmountMap& b);
bool operator>(const CAmountMap& a, const CAmountMap& b);
bool operator>=(const CAmountMap& a, const CAmountMap& b);
bool operator==(const CAmountMap& a, const CAmountMap& b);
bool operator!=(const CAmountMap& a, const CAmountMap& b);
bool operator!(const CAmountMap& a); // Check if all values are 0

inline bool MoneyRange(const CAmountMap& mapValue, const CAsset& pegged_asset) {
    for(CAmountMap::const_iterator it = mapValue.begin(); it != mapValue.end(); it++) {
        if (it->second < 0 || ((pegged_asset.IsNull() || it->first == pegged_asset) && it->second > MAX_MONEY)) {
            return false;
        }
    }
   return true;
}

inline bool MoneyRange(const CAmountMap& mapValue) {
    return MoneyRange(mapValue, CAsset());
}

CAmount valueFor(const CAmountMap& mapValue, const CAsset& asset);

std::ostream& operator<<(std::ostream& out, const CAmountMap& map);

#endif // BITCOIN_ASSET_H
