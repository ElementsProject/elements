#!/usr/bin/env python3
# Copyright (c) 2019 CommerceBlock developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *
import random

class SplitTxTest (BitcoinTestFramework):

    def check_fee_amount(self, curr_balance, balance_with_fee, fee_per_byte, tx_size):
        """Return curr_balance after asserting the fee was in range"""
        fee = balance_with_fee - curr_balance
        assert_fee_amount(fee, tx_size, fee_per_byte * 1000)
        return curr_balance

    def get_balance_sum(self, balance_map):
        balance = 0
        for _, v in balance_map.items():
            balance += v
        return balance

    def __init__(self):
        super().__init__()
        self.setup_clean_chain = True
        self.num_nodes = 4
        self.extra_args = [['-usehd={:d}'.format(i%2==0)] for i in range(4)]
        self.extra_args[0].append("-txindex")
        self.extra_args[1].append("-txindex")
        self.extra_args[2].append("-txindex")
        self.extra_args[3].append("-txindex")

    def setup_network(self, split=False):
        self.nodes = start_nodes(4, self.options.tmpdir, self.extra_args[:4])
        connect_nodes_bi(self.nodes,0,1)
        connect_nodes_bi(self.nodes,1,2)
        connect_nodes_bi(self.nodes,0,2)
        connect_nodes_bi(self.nodes,0,3)
        connect_nodes_bi(self.nodes,1,3)
        connect_nodes_bi(self.nodes,2,3)
        self.is_network_split=False
        self.sync_all()

    def run_test (self):
        # Issue 500 assets
        numOutputs = 500;
        values = [0.1, 1.9, 0.5, 1.5, 0.7, 1.3, 0.9, 1.1, 0.8, 1.2]
        for i in range(numOutputs):
            self.nodes[2].issueasset(values[i%10],'0', False)
            if i % 99 == 0:
                self.nodes[2].generate(1)
                self.sync_all()

        self.nodes[2].sendtoaddress(self.nodes[3].getnewaddress(), self.nodes[2].getbalance()["CBT"], "", "", True, "CBT")
        self.nodes[2].generate(1)
        self.sync_all()

        # Also issue 50 assets with reissuance
        numAssets = 150;
        for i in range(numAssets):
            issuance = self.nodes[3].issueasset(10, 0, False)
            self.nodes[3].generate(1)
            self.sync_all()

            # split the asset in 5 addresses
            raw_issuance = self.nodes[3].getrawtransaction(issuance['txid'], True)
            vout = 0
            for txout in raw_issuance['vout']:
                if txout['asset'] == issuance['asset']:
                    vout = txout['n']
            addrs = [self.nodes[3].getnewaddress(), self.nodes[3].getnewaddress(), self.nodes[3].getnewaddress(),\
                    self.nodes[3].getnewaddress(), self.nodes[3].getnewaddress()]
            tx = self.nodes[3].createrawtransaction([{"txid":issuance['txid'], "vout":vout, "asset":issuance['asset']}], {addrs[0]: 1.5, addrs[1]: 2.5, addrs[2]: 0.5, addrs[3]: 3.5, addrs[4]: 1.9998, "fee": 0.0002}, 0, {addrs[0]: issuance['asset'], addrs[1]: issuance['asset'], addrs[2]: issuance['asset'], addrs[3]: issuance['asset'], addrs[4]: issuance['asset'], "fee": issuance['asset']})
            signed_tx = self.nodes[3].signrawtransaction(tx)
            self.nodes[3].sendrawtransaction(signed_tx['hex'])
            self.nodes[3].generate(1)
            self.sync_all()

        self.nodes[3].sendtoaddress(self.nodes[1].getnewaddress(), self.nodes[3].getbalance()["CBT"], "", "", True, "CBT")
        self.nodes[3].generate(1)
        self.sync_all()

        # Send almost all the balance from node 2, requiring transaction splitting
        addr1 = self.nodes[0].getnewaddress();
        txids = self.nodes[2].sendanytoaddress(addr1, 499.5, "", "", True, True, 1)
        assert(len(txids) == 2)

        valPaid = 0
        for txid in self.nodes[2].getrawmempool():
            tx = self.nodes[2].getrawtransaction(txid, True)
            for vout in tx['vout']:
                scriptPub = vout['scriptPubKey']
                if 'addresses' in scriptPub and addr1 in scriptPub['addresses']:
                    valPaid += vout['value']

        assert(valPaid == 499.5)
        self.sync_all()
        newblock = self.nodes[0].generate(1)
        self.sync_all()
        assert(len(self.nodes[2].getblock(newblock[0], True)['tx']) == 3)
        assert(self.get_balance_sum(self.nodes[0].getbalance()) == 499.5)

        # Send almost all the balance from node 3, requiring transaction splitting
        addr2 = self.nodes[0].getnewaddress();
        txids = self.nodes[3].sendanytoaddress(addr2, 1400, "", "", True, True, 1)
        assert(len(txids) == 2)

        valPaid = 0
        for txid in self.nodes[3].getrawmempool():
            tx = self.nodes[3].getrawtransaction(txid, True)
            for vout in tx['vout']:
                scriptPub = vout['scriptPubKey']
                if 'addresses' in scriptPub and addr2 in scriptPub['addresses']:
                    valPaid += vout['value']

        assert(valPaid == 1400)
        self.sync_all()
        newblock = self.nodes[0].generate(1)
        self.sync_all()
        assert(len(self.nodes[3].getblock(newblock[0], True)['tx']) == 3)
        assert(self.get_balance_sum(self.nodes[0].getbalance()) == 1899.5)


if __name__ == '__main__':
    SplitTxTest().main()
