#!/usr/bin/env python3
# Copyright (c) 2019 CommerceBlock developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *

class SendAnyTest (BitcoinTestFramework):

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

        # Check that there's 100 UTXOs on each of the nodes
        assert_equal(len(self.nodes[0].listunspent()), 100)
        assert_equal(len(self.nodes[1].listunspent()), 100)
        assert_equal(len(self.nodes[2].listunspent()), 100)

        walletinfo = self.nodes[2].getbalance()
        assert_equal(walletinfo["CBT"], 21000000)

        self.nodes[2].generate(101)
        self.sync_all()

        # Issue some assets to use for sendany different cases
        self.nodes[2].issueasset('5.0','0', False)
        self.nodes[2].generate(1)
        self.nodes[2].issueasset('4.99999999','0', False)
        self.nodes[2].generate(1)
        self.nodes[2].issueasset('0.00000001','0', False)
        self.nodes[2].generate(1)
        self.nodes[2].issueasset('4.0','0', False)
        self.nodes[2].generate(1)
        self.nodes[2].issueasset('2.0','0', False)
        self.nodes[2].generate(1)
        self.nodes[2].issueasset('1.0','0', False)
        self.nodes[2].generate(1)
        self.sync_all()

        self.nodes[2].sendtoaddress(self.nodes[1].getnewaddress(), self.nodes[2].getbalance()["CBT"], "", "", True, "CBT")
        assert_equal(self.nodes[1].getbalance("", 0, False, "CBT"), 20790000.00000000)
        assert_equal(self.nodes[2].getbalance("", 0, False, "CBT"), 0)
        self.nodes[2].generate(1)
        self.sync_all()

        addr1 = self.nodes[1].getnewaddress();

        # Edge case where first asset is 5 and output is 5. Fee makes the asset go over the limit and an extra ones has to be chosen.
        tx = self.nodes[2].sendanytoaddress(addr1, 5, "", "", True, False)
        assert(tx in self.nodes[2].getrawmempool())
        self.nodes[2].generate(1)
        self.sync_all()

        # Descending asset balances for sendany selection
        tx = self.nodes[2].sendanytoaddress(addr1, 5.5, "", "", True, False, 1)
        assert(tx in self.nodes[2].getrawmempool())
        self.nodes[2].generate(1)
        self.sync_all()

        # Ascending asset balances for sendany selection
        tx = self.nodes[2].sendanytoaddress(addr1, 2.5, "", "", True, False, 2)
        assert(tx in self.nodes[2].getrawmempool())
        self.nodes[2].generate(1)
        self.sync_all()

        # Send all balance
        balance = 0
        for _, val in self.nodes[2].getbalance().items():
            balance += val
        tx = self.nodes[2].sendanytoaddress(addr1, balance - Decimal('0.0002'), "", "", True, False, 2)
        assert(tx in self.nodes[2].getrawmempool())
        self.nodes[2].generate(1)
        self.sync_all()

        # Issue some assets and send them to node 0
        issue = self.nodes[1].issueasset('10.0','0', False)
        self.nodes[1].generate(1)
        self.nodes[1].sendtoaddress(self.nodes[0].getnewaddress(), 9, "", "", False, issue["asset"])
        self.nodes[1].generate(1)

        issue = self.nodes[1].issueasset('10.0','0', False)
        self.nodes[1].generate(1)
        self.nodes[1].sendtoaddress(self.nodes[0].getnewaddress(), 9, "", "", False, issue["asset"])
        self.nodes[1].generate(1)
        self.sync_all()

        # Two balances of 9; send 9
        tx = self.nodes[0].sendanytoaddress(addr1, 9, "", "", True, False)
        assert(tx in self.nodes[0].getrawmempool())
        self.nodes[0].generate(1)
        self.sync_all()

if __name__ == '__main__':
    SendAnyTest().main()
