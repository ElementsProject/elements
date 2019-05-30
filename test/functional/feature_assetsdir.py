#!/usr/bin/env python3
# Copyright (c) 2014-2016 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

#
# Test use of assetdir to locally label assets.
# Test listissuances returns a list of all issuances or specific issuances based on asset hex or asset label.
#

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal, assert_greater_than

class AssetdirTests(BitcoinTestFramework):
    """
    Test use of assetdir to specify asset labels.
    Test listissuances returns a list of all issuances or specific issuances based on asset hex or asset label.
    """

    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 1
        [["-initialfreecoins=2100000000000000", "-anyonecanspendaremine=1", "-con_connect_genesis_outputs=1", "-con_blocksubsidy=0"]]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def setup_network(self, split=False):
        self.setup_nodes()

    def run_test(self):
        self.nodes[0].generate(101)

        #Issue two assets that we will later label using the assetdir parameter
        issuance1 = self.nodes[0].issueasset(100, 1, False)
        asset1hex = issuance1["asset"]

        issuance2 = self.nodes[0].issueasset(100, 1, False)
        asset2hex = issuance2["asset"]

        #Stop and restart the nodes, providing the assetdir parameter to locally label the assets
        self.stop_nodes()
        self.start_nodes([["-assetdir=" + asset1hex + ":asset1", "-assetdir=" + asset2hex + ":asset2"]])

        #Check that listissuances return all issuances
        issuances = self.nodes[0].listissuances()
        assert_equal(len(issuances), 2)

        #Check all asset labels have been set: 'asset1', 'asset2'
        #We can not be sure they will always be returned in the same order so will loop each one
        label = ""
        for issue in issuances:
            label += issue["assetlabel"]

        assert_greater_than(label.find("asset1"), -1)
        assert_greater_than(label.find("asset2"), -1)

        #Check we can get a list of isuances for a given label
        issuances = self.nodes[0].listissuances("asset1")
        assert_equal(len(issuances), 1)
        assert_equal(issuances[0]["assetlabel"], "asset1")

        #Check we can get a list of issuances for a given hex
        issuances = self.nodes[0].listissuances(asset2hex)
        assert_equal(len(issuances), 1)
        assert_equal(issuances[0]["assetlabel"], "asset2")

if __name__ == '__main__':
    AssetdirTests().main()

