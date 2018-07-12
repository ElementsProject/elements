// Copyright (c) 2017-2017 The Elements Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_ASSETSDIR_H
#define BITCOIN_ASSETSDIR_H

#include "amount.h"

#include <map>

class AssetMetadata
{
    std::string label;
public:
    AssetMetadata() : label("") {};
    AssetMetadata(std::string _label) : label(_label) {};

    const std::string& GetLabel() const
    {
        return label;
    }
};

class CAssetsDir
{
    std::map<CAsset, AssetMetadata> mapAssetMetadata;
    std::map<std::string, CAsset> mapAssets;

    void Set(const CAsset& asset, const AssetMetadata& metadata);
    void SetHex(const std::string& assetHex, const std::string& label);
public:
    void InitFromStrings(const std::vector<std::string>& assetsToInit, const std::string& pegged_asset_name);

    /**
     * @param  label A label string
     * @return asset id corresponding to the asset label
     */
    CAsset GetAsset(const std::string& label) const;

    AssetMetadata GetMetadata(const CAsset& asset) const;

    /** @return the label associated to the asset id */
    std::string GetLabel(const CAsset& asset) const;

    std::vector<CAsset> GetKnownAssets() const;
};

#endif // BITCOIN_ASSETSDIR_H
