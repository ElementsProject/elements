// Copyright (c) 2017-2017 The Elements Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "assetsdir.h"
#include "chainparams.h"

#include "test/test_bitcoin.h"

#include <boost/test/unit_test.hpp>

BOOST_FIXTURE_TEST_SUITE(assetsdir_tests, BasicTestingSetup)

BOOST_AUTO_TEST_CASE(assetsdirTests)
{
    CAssetsDir tAssetsDir;
    const std::string defaultPeggedLabel = "bitcoin";
    const std::string defaultPeggedAssetHex = Params().GetConsensus().pegged_asset.GetHex();
    const CAsset defaultPeggedAsset = Params().GetConsensus().pegged_asset;
    const std::string exampleAssetHex = "fa821b0be5e1387adbcb69dbb3ad33edb5e470831c7c938c4e7b344edbe8bb11";
    const CAsset exampleAsset = CAsset(uint256S(exampleAssetHex));
    const std::vector<std::string> protectedLabels = {"*", defaultPeggedLabel, "bitcoin", "Bitcoin", "btc"};

    for (std:: string protectedLabel : protectedLabels) {
        std::vector<std::string> assetsToInitProtected = {exampleAssetHex + ":" + protectedLabel};
        BOOST_CHECK_THROW(tAssetsDir.InitFromStrings(assetsToInitProtected, defaultPeggedLabel), std::runtime_error);
    }

    const std::vector<std::string> exAssetsToInit = {exampleAssetHex + ":other"};
    tAssetsDir.InitFromStrings(exAssetsToInit, defaultPeggedLabel);

    BOOST_CHECK(exampleAsset == tAssetsDir.GetAsset("other"));
    BOOST_CHECK_EQUAL("other", tAssetsDir.GetLabel(exampleAsset));
    // "bitcoin" is hardcoded for python tests
    BOOST_CHECK(defaultPeggedAsset == tAssetsDir.GetAsset(defaultPeggedLabel));
    BOOST_CHECK_EQUAL(defaultPeggedLabel, tAssetsDir.GetLabel(defaultPeggedAsset));
    BOOST_CHECK(defaultPeggedAsset == tAssetsDir.GetAsset(tAssetsDir.GetLabel(CAsset(uint256S(defaultPeggedAssetHex)))));

    const std::vector<std::string> assetsToInitRepeatedHex = {exampleAssetHex + ":other", exampleAssetHex + ":other2"};
    BOOST_CHECK_THROW(tAssetsDir.InitFromStrings(assetsToInitRepeatedHex, defaultPeggedLabel), std::runtime_error);

    const std::vector<std::string> assetsToInitRepeatedLabel = {exampleAssetHex + ":other", defaultPeggedAssetHex + ":other"};
    BOOST_CHECK_THROW(tAssetsDir.InitFromStrings(assetsToInitRepeatedLabel, defaultPeggedLabel), std::runtime_error);
}

BOOST_AUTO_TEST_SUITE_END()
