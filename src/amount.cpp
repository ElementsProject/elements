// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2015 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "amount.h"

#include "tinyformat.h"

const std::string CURRENCY_UNIT = "BTC";

CFeeRate::CFeeRate(const CAmount& nFeePaid, size_t nBytes_)
{
    assert(nBytes_ <= uint64_t(std::numeric_limits<int64_t>::max()));
    int64_t nSize = int64_t(nBytes_);

    if (nSize > 0)
        nSatoshisPerK = nFeePaid * 1000 / nSize;
    else
        nSatoshisPerK = 0;
}

CAmount CFeeRate::GetFee(size_t nBytes_) const
{
    assert(nBytes_ <= uint64_t(std::numeric_limits<int64_t>::max()));
    int64_t nSize = int64_t(nBytes_);

    CAmount nFee = nSatoshisPerK * nSize / 1000;

    if (nFee == 0 && nSize != 0) {
        if (nSatoshisPerK > 0)
            nFee = CAmount(1);
        if (nSatoshisPerK < 0)
            nFee = CAmount(-1);
    }

    return nFee;
}

std::string CFeeRate::ToString() const
{
    return strprintf("%d.%08d %s/kB", nSatoshisPerK / COIN, nSatoshisPerK % COIN, CURRENCY_UNIT);
}

CAmountMap& operator+=(CAmountMap& a, const CAmountMap& b)
{
    for(std::map<CAssetID, CAmount>::const_iterator it = b.begin(); it != b.end(); ++it)
        a[it->first] += it->second;
    return a;
}

CAmountMap& operator-=(CAmountMap& a, const CAmountMap& b)
{
    for(std::map<CAssetID, CAmount>::const_iterator it = b.begin(); it != b.end(); ++it)
        a[it->first] -= it->second;
    return a;
}

CAmountMap operator+(const CAmountMap& a, const CAmountMap& b)
{
    CAmountMap c;
    for(std::map<CAssetID, CAmount>::const_iterator it = a.begin(); it != a.end(); ++it)
        c[it->first] += it->second;
    for(std::map<CAssetID, CAmount>::const_iterator it = b.begin(); it != b.end(); ++it)
        c[it->first] += it->second;
    return c;
}

CAmountMap operator-(const CAmountMap& a, const CAmountMap& b)
{
    CAmountMap c;
    for(std::map<CAssetID, CAmount>::const_iterator it = a.begin(); it != a.end(); ++it)
        c[it->first] += it->second;
    for(std::map<CAssetID, CAmount>::const_iterator it = b.begin(); it != b.end(); ++it)
        c[it->first] -= it->second;
    return c;
}
