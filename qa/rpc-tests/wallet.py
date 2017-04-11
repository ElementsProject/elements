#!/usr/bin/env python2
# Copyright (c) 2014 The Bitcoin Core developers
# Distributed under the MIT/X11 software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

#
# Exercise the wallet.  Ported from wallet.sh.  
# Does the following:
#

from test_framework import BitcoinTestFramework
from util import *


class WalletTest (BitcoinTestFramework):

    def setup_chain(self):
        print("Initializing test directory "+self.options.tmpdir)
        initialize_chain_clean(self.options.tmpdir, 3)

    def setup_network(self, split=False):
        self.nodes = start_nodes(3, self.options.tmpdir)
        connect_nodes_bi(self.nodes,0,1)
        connect_nodes_bi(self.nodes,1,2)
        connect_nodes_bi(self.nodes,0,2)
        self.is_network_split=False
        self.sync_all()

    def run_test (self):
        print "Mining blocks..."

        self.nodes[0].setgenerate(True, 1)

        self.sync_all()
        self.nodes[1].setgenerate(True, 101)
        self.sync_all()

        genesis_balance = 10500000
        assert_equal(self.nodes[0].getbalance(), genesis_balance)
        assert_equal(self.nodes[1].getbalance(), genesis_balance)
        assert_equal(self.nodes[2].getbalance(), genesis_balance)

        # Send 21 BTC from 0 to 2 using sendtoaddress call.
        # Second transaction will be child of first, and will require a fee
        self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 11)
        self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 10)

        # Have node0 mine a block, thus he will collect his own fee. 
        self.nodes[0].setgenerate(True, 1)
        self.sync_all()

        # Have node1 generate 100 blocks (so node0 can recover the fee)
        self.nodes[1].setgenerate(True, 100)
        self.sync_all()

        assert_equal(self.nodes[0].getbalance(), genesis_balance - 21)
        assert_equal(self.nodes[1].getbalance(), 0)
        assert_equal(self.nodes[2].getbalance(), 21)

        # Node0 should have two unspent outputs.
        # Create a couple of transactions to send them to node2, submit them through 
        # node1, and make sure both node0 and node2 pick them up properly: 
        node0utxos = self.nodes[0].listunspent(1)
        assert_equal(len(node0utxos), 2)

        # create both transactions
        txns_to_send = []
        fee = Decimal(20000)/Decimal(100000000)
        for utxo in node0utxos:
            inputs = []
            outputs = {}
            inputs.append({ "txid" : utxo["txid"], "vout" : utxo["vout"], "nValue": utxo["amount"]})
            outputs[self.nodes[2].getnewaddress("from1")] = utxo["amount"] - fee/len(node0utxos)
            raw_tx = self.nodes[0].createrawtransaction(inputs, outputs)
            raw_tx = self.nodes[0].blindrawtransaction(raw_tx)
            txns_to_send.append(self.nodes[0].signrawtransaction(raw_tx))

        # Have node 1 (miner) send the transactions
        self.nodes[1].sendrawtransaction(txns_to_send[0]["hex"], True)
        self.nodes[1].sendrawtransaction(txns_to_send[1]["hex"], True)

        # Have node1 mine a block to confirm transactions:
        self.nodes[1].setgenerate(True, 1)
        self.sync_all()

        assert_equal(self.nodes[0].getbalance(), 0)
        assert_equal(self.nodes[2].getbalance(), genesis_balance - fee)
        assert_equal(self.nodes[2].getbalance("from1"), genesis_balance - fee - 21)


if __name__ == '__main__':
    WalletTest ().main ()
