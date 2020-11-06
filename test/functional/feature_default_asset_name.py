#!/usr/bin/env python3
# Copyright (c) 2014-2016 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

#
# Test chain initialisation when specifying default asset name.
#

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal, connect_nodes_bi

class NamedDefaultAssetTest(BitcoinTestFramework):
    """
    Test creation of default asset is named according to defaultpeggedasset parameter

    """

    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 2

        #Set default asset name
        self.extra_args = [["-defaultpeggedassetname=testasset", "-initialfreecoins=2100000000000000", "-anyonecanspendaremine=1", "-con_connect_genesis_outputs=1", "-con_blocksubsidy=0"]]*2

    def setup_network(self, split=False):
        self.setup_nodes()
        connect_nodes_bi(self.nodes, 0, 1)
        self.sync_all()

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):
        #Claim all anyone-can-spend coins and test that calling sendtoaddress without providing the assetlabel parameter results in the specified default pegged asset being sent.
        self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), 21000000, "", "", True)
        self.nodes[0].generate(101)
        self.sync_all()

        #Check the default asset is named correctly
        walletinfo1 = self.nodes[0].getwalletinfo()
        assert_equal(walletinfo1["balance"]["testasset"], 21000000)

        #Send some of the default asset to the second node
        self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 1, "", "", False)
        self.nodes[0].generate(101)
        self.sync_all()

        #Check balances are correct and asset is named correctly
        walletinfo1 = self.nodes[0].getwalletinfo()
        assert_equal(walletinfo1["balance"]["testasset"], 20999999)

        walletinfo2 = self.nodes[1].getwalletinfo()
        assert_equal(walletinfo2["balance"]["testasset"], 1)

        #Check we send the default 'testasset' when calling 'sendmany' without needing to provide the relevant asset label
        outputs = {self.nodes[1].getnewaddress(): 1.0, self.nodes[1].getnewaddress(): 3.0}
        self.nodes[0].sendmany("", outputs)
        self.nodes[0].generate(101)
        self.sync_all()

        #Check balances are correct and asset is named correctly
        walletinfo1 = self.nodes[0].getwalletinfo()
        assert_equal(walletinfo1["balance"]["testasset"], 20999995)

        walletinfo2 = self.nodes[1].getwalletinfo()
        assert_equal(walletinfo2["balance"]["testasset"], 5)

if __name__ == '__main__':
    NamedDefaultAssetTest().main()
