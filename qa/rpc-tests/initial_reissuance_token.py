#!/usr/bin/env python3
# Copyright (c) 2014-2016 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

#
# Test chain initialisation when specifying number of reissuance tokens to issue.
#

from decimal import Decimal
from test_framework.test_framework import BitcoinTestFramework
from test_framework.authproxy import JSONRPCException
from test_framework.util import *

class InitialReissuanceTokenTest(BitcoinTestFramework):
    """
    Test creation of initial reissuance token for default asset on chain set up

    """

    def __init__(self):
        super().__init__()
        self.setup_clean_chain = True
        self.num_nodes = 2

        #Set number of initial reissuance tokens and also set initial free coins less than max so we can reissue more later
        self.node_args = [["-initialreissuancetokens=200000000", "-initialfreecoins=2000000000000000"], ["-initialreissuancetokens=200000000", "-initialfreecoins=2000000000000000"]]

    def setup_network(self, split=False):
        self.nodes = start_nodes(self.num_nodes, self.options.tmpdir, self.node_args)
        connect_nodes_bi(self.nodes,0,1)
        self.is_network_split = False
        self.sync_all()

    def run_test(self):
        #Claim all anyone-can-spend 'bitcoin'
        self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), 20000000, "", "", True)
        self.nodes[0].generate(101)
        self.sync_all()

        walletinfo=self.nodes[0].getwalletinfo()
        balance=walletinfo['balance']
        token=""

        #Get the hex of the reissuance token
        for i in balance:
            token = i
            if token != "bitcoin":
                break

        #Claim all anyone-can-spend reissuance tokens
        self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), 2, "", "", False, token)
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
        self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 1, "", "", False, token)
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
