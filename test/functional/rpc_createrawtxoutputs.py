#!/usr/bin/env python3
# Copyright (c) 2015-2018 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test transaction signing using the signrawtransaction* RPCs."""

from test_framework.test_framework import BitcoinTestFramework
import decimal

class RpcCreateRawTxOutputsTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 3

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):
        node0,node1,node2 = self.nodes

        # 50 BTC each, rest will be 25 BTC each
        node0.generate(149)
        self.sync_all()

        self.do_createraw()

    def do_createraw(self):
        node0,node1,node2 = self.nodes

        # test createrawtxoutputs RPC
        addr1 = node2.getnewaddress()
        addr2 = node2.getnewaddress()
        issue1 = node2.issueasset(10.0,0,False)
        issue2 = node2.issueasset(10.0,0,False)
        self.sync_all()
        node0.generate(10)
        self.sync_all()

        rawissue1 = node2.getrawtransaction(issue1["txid"],True)
        for vout in rawissue1["vout"]:
            if vout["asset"] == issue1["asset"]: vout1 = vout["n"]
        rawissue2 = node2.getrawtransaction(issue2["txid"],True)
        for vout in rawissue2["vout"]:
            if vout["asset"] == issue2["asset"]: vout2 = vout["n"]

        inputs = []
        outputs = []
        inputs.append({"txid":issue1["txid"],"vout":vout1})
        inputs.append({"txid":issue2["txid"],"vout":vout2})
        outputs.append({"address":addr1,"amount":10.0,"asset":issue1["asset"]})
        outputs.append({"address":addr1,"amount":5.0,"asset":issue2["asset"]})
        outputs.append({"address":addr2,"amount":4.99,"asset":issue2["asset"]})
        outputs.append({"address":"fee","amount":0.01,"asset":issue2["asset"]})
        outputs.append({"data":"deadbeef","amount":0.0,"asset":issue2["asset"]})

        # create a transaction with same address outputs
        node2.createrawtxoutputs(inputs,outputs)
        node2.signrawtransaction(rawtx)
        node2.sendrawtransaction(signtx["hex"])

        self.sync_all()
        node0.generate(1)
        self.sync_all()

        txdec = node2.getrawtransaction(sendtx,True)

        assert txdec["confirmations"] == 1
        assert len(txdec["vout"]) == 5


if __name__ == '__main__':
    RpcCreateRawTxOutputsTest().main()
