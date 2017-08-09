// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_AMOUNT_H
#define BITCOIN_AMOUNT_H

#include "serialize.h"
#include "uint256.h"
#include <stdlib.h>
#include <string>

/** Amount in satoshis (Can be negative) */
typedef int64_t CAmount;

static const CAmount COIN = 100000000;
static const CAmount CENT = 1000000;

extern const std::string CURRENCY_UNIT;

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

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action) {
        READWRITE(id);
    }

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

/** No amount larger than this (in satoshi) is valid.
 *
 * Note that this constant is *not* the total money supply, which in Bitcoin
 * currently happens to be less than 21,000,000 BTC for various reasons, but
 * rather a sanity check. As this sanity check is used by consensus-critical
 * validation code, the exact value of the MAX_MONEY constant is consensus
 * critical; in unusual circumstances like a(nother) overflow bug that allowed
 * for the creation of coins out of thin air modification could lead to a fork.
 * */
static const CAmount MAX_MONEY = 21000000 * COIN;
inline bool MoneyRange(const CAmount& nValue) { return (nValue >= 0 && nValue <= MAX_MONEY); }

inline bool MoneyRange(const CAmountMap& mapValue) {
    for(CAmountMap::const_iterator it = mapValue.begin(); it != mapValue.end(); it++)
        if (it->second < 0 || it->second > MAX_MONEY)
            return false;
   return true;
}
/**
 * Fee rate in satoshis per kilobyte: CAmount / kB
 */
class CFeeRate
{
private:
    CAmount nSatoshisPerK; // unit is satoshis-per-1,000-bytes
public:
    /** Fee rate of 0 satoshis per kB */
    CFeeRate() : nSatoshisPerK(0) { }
    explicit CFeeRate(const CAmount& _nSatoshisPerK): nSatoshisPerK(_nSatoshisPerK) { }
    /** Constructor for a fee rate in satoshis per kB. The size in bytes must not exceed (2^63 - 1)*/
    CFeeRate(const CAmount& nFeePaid, size_t nBytes);
    CFeeRate(const CFeeRate& other) { nSatoshisPerK = other.nSatoshisPerK; }
    /**
     * Return the fee in satoshis for the given size in bytes.
     */
    CAmount GetFee(size_t nBytes) const;
    /**
     * Return the fee in satoshis for a size of 1000 bytes
     */
    CAmount GetFeePerK() const { return GetFee(1000); }
    friend bool operator<(const CFeeRate& a, const CFeeRate& b) { return a.nSatoshisPerK < b.nSatoshisPerK; }
    friend bool operator>(const CFeeRate& a, const CFeeRate& b) { return a.nSatoshisPerK > b.nSatoshisPerK; }
    friend bool operator==(const CFeeRate& a, const CFeeRate& b) { return a.nSatoshisPerK == b.nSatoshisPerK; }
    friend bool operator<=(const CFeeRate& a, const CFeeRate& b) { return a.nSatoshisPerK <= b.nSatoshisPerK; }
    friend bool operator>=(const CFeeRate& a, const CFeeRate& b) { return a.nSatoshisPerK >= b.nSatoshisPerK; }
    CFeeRate& operator+=(const CFeeRate& a) { nSatoshisPerK += a.nSatoshisPerK; return *this; }
    std::string ToString() const;

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action) {
        READWRITE(nSatoshisPerK);
    }
};

#endif //  BITCOIN_AMOUNT_H
