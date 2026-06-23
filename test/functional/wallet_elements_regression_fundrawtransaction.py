#!/usr/bin/env python3
# Copyright (c) 2017-2020 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from test_framework.blocktools import COINBASE_MATURITY
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    assert_raises_rpc_error,
)

class WalletTest(BitcoinTestFramework):
    def add_options(self, parser):
        self.add_wallet_options(parser)

    def set_test_params(self):
        self.num_nodes = 1
        self.extra_args = [['-blindedaddresses=1']] * self.num_nodes

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):
        self.generate(self.nodes[0], COINBASE_MATURITY + 1)

        assert_equal(self.nodes[0].getbalance(), {'bitcoin': 2550})

        self.log.info("Issue asset")
        issue = self.nodes[0].issueasset(1, 0)
        asset = issue['asset']

        self.log.info("Send some of issued asset and policy asset to ourselves in a single transaction")
        rawtx = self.nodes[0].createrawtransaction([], [{self.nodes[0].getnewaddress(): 1, "asset": asset}, {self.nodes[0].getnewaddress(): 2}], 0, False)
        funded = self.nodes[0].fundrawtransaction(rawtx)
        blinded = self.nodes[0].blindrawtransaction(funded["hex"])
        signed = self.nodes[0].signrawtransactionwithwallet(blinded)
        txid = self.nodes[0].sendrawtransaction(signed["hex"])

        self.log.info("Spend both outputs in a new transaction")
        # since we support multiple assets, we make fundrawtransaction require the raw tx to have outputs for each pre-selected input asset type
        rawtx = self.nodes[0].createrawtransaction([{"txid":txid, "vout":0}, {"txid":txid, "vout":1}], [{self.nodes[0].getnewaddress():5}])
        assert_raises_rpc_error(-4, "Transaction is missing an output for input asset", self.nodes[0].fundrawtransaction, rawtx)
        rawtx = self.nodes[0].createrawtransaction([{"txid":txid, "vout":0}, {"txid":txid, "vout":1}], [{self.nodes[0].getnewaddress():5}, {self.nodes[0].getnewaddress(): 1, "asset": asset}])
        funded = self.nodes[0].fundrawtransaction(rawtx)
        blinded = self.nodes[0].blindrawtransaction(funded["hex"])
        signed = self.nodes[0].signrawtransactionwithwallet(blinded)
        txid = self.nodes[0].sendrawtransaction(signed["hex"])

if __name__ == '__main__':
    WalletTest(__file__).main()
