#!/usr/bin/env python3
# Copyright (c) 2014-2016 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

#
# Test chain initialisation when specifying number of reissuance tokens to issue.
#

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import connect_nodes_bi, assert_equal

class InitialReissuanceTokenTest(BitcoinTestFramework):
    """
    Test creation of initial reissuance token for default asset on chain set up

    """

    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 2

        #Set number of initial reissuance tokens and also set initial free coins less than max so we can reissue more later
        self.extra_args = [["-initialreissuancetokens=200000000", "-initialfreecoins=2000000000000000", "-anyonecanspendaremine=1", "-con_connect_genesis_outputs=1", "-con_blocksubsidy=0", "-blindedaddresses=1"]]*2

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def setup_network(self, split=False):
        self.setup_nodes()
        connect_nodes_bi(self.nodes, 0, 1)
        self.sync_all()

    def run_test(self):
        self.nodes[0].generate(101)
        self.sync_all()

        walletinfo = self.nodes[0].getwalletinfo()
        balance = walletinfo['balance']
        token = ""

        #Get the hex of the reissuance token
        for i in balance:
            token = i
            if token != "bitcoin":
                break

        # Claim all anyone-can-spend reissuance tokens, which also blinds the token output
        # which is required for re-issuance: https://github.com/ElementsProject/elements/issues/259
        self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), 2, "", "", False, False, 6, "UNSET", False, token)
        self.nodes[0].generate(101)
        self.sync_all()

        #Check balances
        walletinfo1 = self.nodes[0].getwalletinfo()
        assert_equal(walletinfo1["balance"]["bitcoin"], 20000000)
        assert_equal(walletinfo1["balance"][token], 2)

        #Reissue some of the default asset
        self.nodes[0].reissueasset("bitcoin", 1234)
        self.nodes[0].generate(101)
        self.sync_all()

        #Check the reissuance worked
        walletinfo1 = self.nodes[0].getwalletinfo()
        assert_equal(walletinfo1["balance"]["bitcoin"], 20001234)

        #Send some 'bitcoin' to node 2 so they can fund a reissuance transaction
        self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 1, "", "", False)

        #Send a reissuance token to node 2 so they can reissue the default asset
        self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 1, "", "", False, False, 6, "UNSET", False, token)
        self.nodes[0].generate(101)
        self.sync_all()

        #Reissue some of the default asset
        self.nodes[1].reissueasset("bitcoin", 1000)
        self.nodes[1].generate(101)
        self.sync_all()

        #Check balance is the 1 'bitcoin' sent from node 1 plus the 1000 'bitcoin' reissued by node 2
        walletinfo2 = self.nodes[1].getwalletinfo()
        assert_equal(walletinfo2["balance"]["bitcoin"], 1001)

if __name__ == '__main__':
    InitialReissuanceTokenTest().main()
