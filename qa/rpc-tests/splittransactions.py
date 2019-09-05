#!/usr/bin/env python3
# Copyright (c) 2019 CommerceBlock developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *

class SplitTxTest (BitcoinTestFramework):

    def check_fee_amount(self, curr_balance, balance_with_fee, fee_per_byte, tx_size):
        """Return curr_balance after asserting the fee was in range"""
        fee = balance_with_fee - curr_balance
        assert_fee_amount(fee, tx_size, fee_per_byte * 1000)
        return curr_balance

    def __init__(self):
        super().__init__()
        self.setup_clean_chain = True
        self.num_nodes = 4
        self.extra_args = [['-usehd={:d}'.format(i%2==0)] for i in range(4)]
        self.extra_args[0].append("-txindex")
        self.extra_args[1].append("-txindex")
        self.extra_args[2].append("-txindex")

    def setup_network(self, split=False):
        self.nodes = start_nodes(3, self.options.tmpdir, self.extra_args[:3])
        connect_nodes_bi(self.nodes,0,1)
        connect_nodes_bi(self.nodes,1,2)
        connect_nodes_bi(self.nodes,0,2)
        self.is_network_split=False
        self.sync_all()

    def run_test (self):
        numOutputs = 500;
        for i in range(numOutputs):
            self.nodes[2].issueasset('1.0','0', False)
            if i % 99 == 0:
                self.nodes[2].generate(1)
                self.sync_all()

        self.nodes[2].sendtoaddress(self.nodes[1].getnewaddress(), self.nodes[2].getbalance()["CBT"], "", "", True, "CBT")
        assert_equal(self.nodes[2].getbalance("", 0, False, "CBT"), 0)
        self.nodes[2].generate(1)
        self.sync_all()
        assert(self.nodes[1].getbalance("", 0, False, "CBT") > 20999999)

        addr1 = self.nodes[0].getnewaddress();
        self.nodes[2].sendanytoaddress(addr1, 495, "", "", True, True, 1)
        val = 0
        for txid in self.nodes[2].getrawmempool():
            tx = self.nodes[2].getrawtransaction(txid, True)
            for vout in tx['vout']:
                val += vout['value']
        assert(val == 497)

        newblock = self.nodes[0].generate(1)
        self.sync_all()

if __name__ == '__main__':
    SplitTxTest().main()
