
#ifndef BITCOIN_ASSETSDIR_H
#define BITCOIN_ASSETSDIR_H

#include <asset.h>

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

/**
 * Returns asset id corresponding to the given asset expression, which is either an asset label or a hex value.
 * @param  strasset A label string or a hex value corresponding to an asset
 * @return       The asset ID for the given expression
 */
CAsset GetAssetFromString(const std::string& strasset);

// GLOBAL:
class CAssetsDir;

extern const CAssetsDir& gAssetsDir;

void InitGlobalAssetDir(const std::vector<std::string>& assetsToInit, const std::string& pegged_asset_name);

#endif // BITCOIN_ASSETSDIR_H
