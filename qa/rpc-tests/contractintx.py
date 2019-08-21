#!/usr/bin/env python3
# Copyright (c) 2014-2016 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *
import filecmp
import time

class ContractInTxTest (BitcoinTestFramework):

    def __init__(self):
        super().__init__()
        self.setup_clean_chain = True
        self.num_nodes = 3
        self.extra_args = [['-txindex'] for i in range(3)]
        self.extra_args[0].append("-regtest=0")
        self.extra_args[0].append("-contractintx=1")
        self.extra_args[1].append("-regtest=0")
        self.extra_args[1].append("-contractintx=1")
        self.extra_args[2].append("-regtest=0")
        self.extra_args[2].append("-contractintx=0")

    def setup_network(self, split=False):
        self.nodes = start_nodes(3, self.options.tmpdir, self.extra_args[:3])
        connect_nodes_bi(self.nodes,0,1)
        connect_nodes_bi(self.nodes,1,2)
        connect_nodes_bi(self.nodes,0,2)
        self.is_network_split=False
        self.sync_all()

    def run_test (self):
    
        self.nodes[0].generate(101)
        self.sync_all()

        genhash = self.nodes[0].getblockhash(0)
        genblock = self.nodes[0].getblock(genhash)

        #send coins from node 0 to node 1
        addr1 = self.nodes[1].getnewaddress()
        txid1 = self.nodes[0].sendtoaddress(addr1,100.0)

        self.nodes[0].generate(101)
        self.sync_all()

        rawtx1 = self.nodes[0].getrawtransaction(txid1,True)
        assert(rawtx1['confirmations'] == 101)

        #send some coins from node 0 to node 2
        addr2 = self.nodes[2].getnewaddress()
        txid2 = self.nodes[0].sendtoaddress(addr2,100.0)

        self.nodes[0].generate(101)
        self.sync_all()

        #send some coins back from node 2 to node 0
        addr3 = self.nodes[0].getnewaddress()
        txid3 = self.nodes[2].sendtoaddress(addr3,50.0)

        #check txid3 is in the mempool of node 2
        memp1 = self.nodes[2].getrawmempool()

        assert(txid3 in memp1)

        #check txid3 is not in the mempool of node 0 (blocked)
        memp2 = self.nodes[0].getrawmempool()

        assert(not txid3 in memp2)

if __name__ == '__main__':
 ContractInTxTest().main()
