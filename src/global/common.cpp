// Copyright (c) 2017-2017 The Elements Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "global/common.h"

#include "assetsdir.h"

CAssetsDir _gAssetsDir;
const CAssetsDir& gAssetsDir = _gAssetsDir;

void InitGlobalAssetDir(const std::vector<std::string>& assetsToInit, const std::string& pegged_asset_name)
{
    _gAssetsDir.InitFromStrings(assetsToInit, pegged_asset_name);
}
