
#include <asset.h>
#include <assetsdir.h>
#include <core_io.h>
#include <logging.h>
#include <policy/policy.h>


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

// Attaches labeled balance reports to UniValue obj with asset filter
// "" displays *all* assets as VOBJ pairs, while named assets must have
// been entered via -assetdir configuration argument and are returned as VNUM.
UniValue AmountMapToUniv(const CAmountMap& balanceOrig, std::string strasset)
{
    // Make sure the policyAsset is always present in the balance map.
    CAmountMap balance = balanceOrig;
    balance[::policyAsset] += 0;
    LogPrintf("AmountMapToUniv:\n");
    PrintAmountMap(balance);

    // If we don't do assets or a specific asset is given, we filter out once asset.
    if (!g_con_elementswitness || strasset != "") {
        if (g_con_elementswitness) {
            return ValueFromAmount(balance[GetAssetFromString(strasset)]);
        } else {
            return ValueFromAmount(balance[::policyAsset]);
        }
    }

    UniValue obj(UniValue::VOBJ);
    for(std::map<CAsset, CAmount>::const_iterator it = balance.begin(); it != balance.end(); ++it) {
        // Unknown assets
        if (it->first.IsNull())
            continue;
        UniValue pair(UniValue::VOBJ);
        std::string label = gAssetsDir.GetLabel(it->first);
        if (label == "") {
            label = it->first.GetHex();
        }
        obj.pushKV(label, ValueFromAmount(it->second));
    }
    return obj;
}

void PrintAmountMap(const CAmountMap& amount) {
    for(std::map<CAsset, CAmount>::const_iterator it = amount.begin(); it != amount.end(); ++it) {
        LogPrintf("- %s: %s\n", it->first.GetHex(), it->second);
    }
}

