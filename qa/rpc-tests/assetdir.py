#!/usr/bin/env python3
# Copyright (c) 2014-2016 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

#
# Test use of assetdir to locally label assets.
# Test listissuances returns a list of all issuances or specific issuances based on asset hex or asset label.
#

from decimal import Decimal
from test_framework.test_framework import BitcoinTestFramework
from test_framework.authproxy import JSONRPCException
from test_framework.util import *

class AssetdirTests(BitcoinTestFramework):
    """
    Test use of assetdir to specify asset labels.
    Test listissuances returns a list of all issuances or specific issuances based on asset hex or asset label.
    """

    def __init__(self):
        super().__init__()
        self.setup_clean_chain = True
        self.num_nodes = 1

    def setup_network(self, split=False):
        self.nodes = start_nodes(self.num_nodes, self.options.tmpdir)

    def run_test(self):
        #Claim all anyone-can-spend 'bitcoin'
        self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), 21000000, "", "", True)
        self.nodes[0].generate(101)

        #Issue two assets that we will later label using the assetdir parameter
        issuance1=self.nodes[0].issueasset(100, 1, False)
        asset1hex=issuance1["asset"]

        issuance2=self.nodes[0].issueasset(100, 1, False)
        asset2hex=issuance2["asset"]

        #Stop and restart the nodes, providing the assetdir parameter to locally label the assets
        stop_nodes(self.nodes)
        self.nodes=start_nodes(self.num_nodes, self.options.tmpdir, [["-assetdir=" + asset1hex + ":asset1", "-assetdir=" + asset2hex + ":asset2"]])

        #Check that listissuances returns all 3 issuances
        issuances=self.nodes[0].listissuances()
        assert_equal(len(issuances), 3)
        
        #Check all 3 asset labels have been set: 'bitcoin', 'asset1', 'asset2'
        #We can not be sure they will always be returned in the same order so will loop each one
        label=""
        for issue in issuances:
            label+=issue["assetlabel"]
        
        assert_greater_than(label.find("bitcoin"), -1)
        assert_greater_than(label.find("asset1"), -1)
        assert_greater_than(label.find("asset2"), -1)

        #Check we can get a list of isuances for a given label
        issuances=self.nodes[0].listissuances("bitcoin")
        assert_equal(len(issuances), 1)
        assert_equal(issuances[0]["assetlabel"], "bitcoin")

        issuances=self.nodes[0].listissuances("asset1")
        assert_equal(len(issuances), 1)
        assert_equal(issuances[0]["assetlabel"], "asset1")

        #Check we can get a list of issuances for a given hex
        issuances=self.nodes[0].listissuances(asset2hex)
        assert_equal(len(issuances), 1)
        assert_equal(issuances[0]["assetlabel"], "asset2")

        #Check a non-existant label or hex raises an error
        rpc_error=True
        try:
            self.nodes[0].listissuances("doesnotexist")
            rpc_error=False
        except Exception as e:
            assert_equal(e.error["code"], -4)

        try:
            self.nodes[0].listissuances("0000000000000000000000000000000000000000000000000000000000000000")
            rpc_error=False
        except Exception as e:
            assert_equal(e.error["code"], -4)

        #Check that the code did error
        assert_equal(rpc_error, True)

if __name__ == '__main__':
    AssetdirTests().main()

