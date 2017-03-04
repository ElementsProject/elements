// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
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
    for(std::map<CAsset, CAmount>::const_iterator it = b.begin(); it != b.end(); ++it)
        a[it->first] += it->second;
    return a;
}

CAmountMap& operator-=(CAmountMap& a, const CAmountMap& b)
{
    for(std::map<CAsset, CAmount>::const_iterator it = b.begin(); it != b.end(); ++it)
        a[it->first] -= it->second;
    return a;
}

CAmountMap operator+(const CAmountMap& a, const CAmountMap& b)
{
    CAmountMap c;
    for(std::map<CAsset, CAmount>::const_iterator it = a.begin(); it != a.end(); ++it)
        c[it->first] += it->second;
    for(std::map<CAsset, CAmount>::const_iterator it = b.begin(); it != b.end(); ++it)
        c[it->first] += it->second;
    return c;
}

CAmountMap operator-(const CAmountMap& a, const CAmountMap& b)
{
    CAmountMap c;
    for(std::map<CAsset, CAmount>::const_iterator it = a.begin(); it != a.end(); ++it)
        c[it->first] += it->second;
    for(std::map<CAsset, CAmount>::const_iterator it = b.begin(); it != b.end(); ++it)
        c[it->first] -= it->second;
    return c;
}

bool operator<(const CAmountMap& a, const CAmountMap& b)
{
    bool smallerElement = false;
    for(std::map<CAsset, CAmount>::const_iterator it = b.begin(); it != b.end(); ++it) {
        CAmount aValue = a.count(it->first) ? a.find(it->first)->second : 0;
        if (aValue > it->second)
            return false;
        if (aValue < it->second)
            smallerElement = true;
    }
    for(std::map<CAsset, CAmount>::const_iterator it = a.begin(); it != a.end(); ++it) {
        CAmount bValue = b.count(it->first) ? b.find(it->first)->second : 0;
        if (it->second > bValue)
            return false;
        if (it->second < bValue)
            smallerElement = true;
    }
    return smallerElement;
}

bool operator<=(const CAmountMap& a, const CAmountMap& b)
{
    for(std::map<CAsset, CAmount>::const_iterator it = b.begin(); it != b.end(); ++it) {
        CAmount aValue = a.count(it->first) ? a.find(it->first)->second : 0;
        if (aValue > it->second)
            return false;
    }
    for(std::map<CAsset, CAmount>::const_iterator it = a.begin(); it != a.end(); ++it) {
        CAmount bValue = b.count(it->first) ? b.find(it->first)->second : 0;
        if (it->second > bValue)
            return false;
    }
    return true;
}

bool operator>(const CAmountMap& a, const CAmountMap& b)
{
    bool largerElement = false;
    for(std::map<CAsset, CAmount>::const_iterator it = b.begin(); it != b.end(); ++it) {
        CAmount aValue = a.count(it->first) ? a.find(it->first)->second : 0;
        if (aValue < it->second)
            return false;
        if (aValue > it->second)
            largerElement = true;
    }
    for(std::map<CAsset, CAmount>::const_iterator it = a.begin(); it != a.end(); ++it) {
        CAmount bValue = b.count(it->first) ? b.find(it->first)->second : 0;
        if (it->second < bValue)
            return false;
        if (it->second > bValue)
            largerElement = true;
    }
    return largerElement;
}

bool operator>=(const CAmountMap& a, const CAmountMap& b)
{
    for(std::map<CAsset, CAmount>::const_iterator it = b.begin(); it != b.end(); ++it) {
        if ((a.count(it->first) ? a.find(it->first)->second : 0) < it->second)
            return false;
    }
    for(std::map<CAsset, CAmount>::const_iterator it = a.begin(); it != a.end(); ++it) {
        if (it->second < (b.count(it->first) ? b.find(it->first)->second : 0))
            return false;
    }
    return true;
}

bool operator==(const CAmountMap& a, const CAmountMap& b)
{
    for(std::map<CAsset, CAmount>::const_iterator it = a.begin(); it != a.end(); ++it) {
        if ((b.count(it->first) ? b.find(it->first)->second : 0) != it->second)
            return false;
    }
    for(std::map<CAsset, CAmount>::const_iterator it = b.begin(); it != b.end(); ++it) {
        if ((a.count(it->first) ? a.find(it->first)->second : 0) != it->second)
            return false;
    }
    return true;
}

bool operator!=(const CAmountMap& a, const CAmountMap& b)
{
    return !(a == b);
}

bool hasNegativeValue(const CAmountMap& amount)
{
    for(std::map<CAsset, CAmount>::const_iterator it = amount.begin(); it != amount.end(); ++it) {
        if (it->second < 0)
            return true;
    }
    return false;
}

bool hasNonPostiveValue(const CAmountMap& amount)
{
    for(std::map<CAsset, CAmount>::const_iterator it = amount.begin(); it != amount.end(); ++it) {
        if (it->second <= 0)
            return true;
    }
    return false;
}
