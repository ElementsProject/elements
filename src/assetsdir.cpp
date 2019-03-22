// Copyright (c) 2017-2017 The Elements Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "assetsdir.h"
#include "chainparams.h"

#include "tinyformat.h"
#include "utilstrencodings.h"

#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/split.hpp>

void CAssetsDir::Set(const CAsset& asset, const AssetMetadata& metadata)
{
    // No asset or label repetition
    if (GetLabel(asset) != "")
        throw std::runtime_error(strprintf("duplicated asset '%s'", asset.GetHex()));
    if (GetAsset(metadata.GetLabel()) != CAsset())
        throw std::runtime_error(strprintf("duplicated label '%s'", metadata.GetLabel()));

    mapAssetMetadata[asset] = metadata;
    mapAssets[metadata.GetLabel()] = asset;
}

void CAssetsDir::SetHex(const std::string& assetHex, const std::string& label)
{
    if (!IsHex(assetHex) || assetHex.size() != 64)
        throw std::runtime_error("The asset must be hex string of length 64");

    const std::vector<std::string> protectedLabels = {"", "*", "CBT", "Cbt", "cbt"};
    for (std::string proLabel : protectedLabels) {
        if (label == proLabel) {
            throw std::runtime_error(strprintf("'%s' label is protected", proLabel));
        }
    }
    Set(CAsset(uint256S(assetHex)), AssetMetadata(label));
}

void CAssetsDir::InitFromStrings(const std::vector<std::string>& assetsToInit)
{
    for (std::string strToSplit : assetsToInit) {
        std::vector<std::string> vAssets;
        boost::split(vAssets, strToSplit, boost::is_any_of(":"));
        if (vAssets.size() != 2) {
            throw std::runtime_error("-assetdir parameters malformed, expecting asset:label");
        }
        SetHex(vAssets[0], vAssets[1]);
    }
    // Set "CBT" to the pegged asset for tests
    Set(Params().GetConsensus().pegged_asset, AssetMetadata("CBT"));
    // Add labels for all policy assets
    if (Params().GetConsensus().freezelist_asset != CAsset()) {
        Set(Params().GetConsensus().freezelist_asset, AssetMetadata("FREEZELIST"));
    }
    if (Params().GetConsensus().burnlist_asset != CAsset()) {
        Set(Params().GetConsensus().burnlist_asset, AssetMetadata("BURNLIST"));
    }
    if (Params().GetConsensus().whitelist_asset != CAsset()) {
        Set(Params().GetConsensus().whitelist_asset, AssetMetadata("WHITELIST"));
    }
    if (Params().GetConsensus().challenge_asset != CAsset()) {
        Set(Params().GetConsensus().challenge_asset, AssetMetadata("CHALLENGE"));
    }
}

CAsset CAssetsDir::GetAsset(const std::string& label) const
{
    auto it = mapAssets.find(label);
    if (it != mapAssets.end())
        return it->second;
    return CAsset();
}

AssetMetadata CAssetsDir::GetMetadata(const CAsset& asset) const
{
    auto it = mapAssetMetadata.find(asset);
    if (it != mapAssetMetadata.end())
        return it->second;
    return AssetMetadata("");
}

std::string CAssetsDir::GetLabel(const CAsset& asset) const
{
    return GetMetadata(asset).GetLabel();
}

std::vector<CAsset> CAssetsDir::GetKnownAssets() const
{
    std::vector<CAsset> knownAssets;
    for (auto it = mapAssets.begin(); it != mapAssets.end(); it++) {
        knownAssets.push_back(it->second);
    }
    return knownAssets;
}
