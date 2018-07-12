// Copyright (c) 2017-2017 The Elements Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_GLOBAL_COMMON_H
#define BITCOIN_GLOBAL_COMMON_H

#include <string>
#include <vector>

class CAssetsDir;

extern const CAssetsDir& gAssetsDir;

void InitGlobalAssetDir(const std::vector<std::string>& assetsToInit, const std::string& pegged_asset_name);

#endif // BITCOIN_GLOBAL_COMMON_H
