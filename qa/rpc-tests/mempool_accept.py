#!/usr/bin/env python3
# Copyright (c) 2014-2016 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

#
# Test re-org scenarios with a mempool that contains transactions
# that spend (directly or indirectly) coinbase transactions.
#

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *

class MempoolAcceptanceTest(BitcoinTestFramework):
    def __init__(self):
        super().__init__()
        self.setup_clean_chain = True
        self.num_nodes = 2

    def setup_network(self, split=False):
        self.nodes = start_nodes(2, self.options.tmpdir)
        connect_nodes_bi(self.nodes,0,1)
        self.is_network_split=False
        self.sync_all()

    def run_test (self):

        # Check that there's 100 UTXOs on each of the nodes                                             
        assert_equal(len(self.nodes[0].listunspent()), 100)
        assert_equal(len(self.nodes[1].listunspent()), 100)

        walletinfo = self.nodes[0].getwalletinfo()
        assert_equal(walletinfo['balance']["CBT"], 21000000)

        print("Mining blocks...")
        self.nodes[0].generate(101)
        self.sync_all()

        assert_equal(self.nodes[0].getbalance("", 0, False, "CBT"), 21000000)
        assert_equal(self.nodes[1].getbalance("", 0, False, "CBT"), 21000000)

        address_node1 = self.nodes[0].getnewaddress()

        pa_txid = self.nodes[0].sendtoaddress(address_node1,1)
        self.nodes[1].generate(1)
        self.sync_all()

        #get the raw transaction
        rawtx = self.nodes[0].getrawtransaction(pa_txid)

        #check if we can send the transaction again (once it is in the mempool)
        result_test = self.nodes[0].testmempoolaccept(rawtx)

        assert_equal(result_test["reject-reason"],"257: txn-already-in-mempool")

        #confirm it
        self.nodes[0].generate(10)
        self.sync_all()

        #check if we can send it again
        result_test = self.nodes[0].testmempoolaccept(rawtx)

        assert_equal(result_test["reject-reason"],"257: txn-already-known")

        dectx = self.nodes[0].decoderawtransaction(rawtx)

        #try to spend the output again
        txin = dectx["vin"][0]["txid"]
        vout = dectx["vin"][0]["vout"]

        value = 0
        for oput in dectx["vout"]:
            value += oput["value"]

        input1 = {}
        input1["txid"] = txin
        input1["vout"] = vout

        inputs = []
        inputs.append(input1)

        address2 = self.nodes[0].getnewaddress()

        outputs = {}
        outputs[address2] = value

        newtx = self.nodes[0].createrawtransaction(inputs,outputs)
        signednewtx = self.nodes[0].signrawtransaction(newtx)
        result_test = self.nodes[0].testmempoolaccept(signednewtx["hex"])

        assert_equal(result_test["reject-reason"],"18: bad-txns-inputs-spent")


if __name__ == '__main__':
    MempoolAcceptanceTest().main()