#!/usr/bin/env python3
# Copyright (c) 2017-2020 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
from decimal import Decimal

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
)

class WalletTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 3
        self.extra_args = [[
            "-blindedaddresses=1",
            "-minrelaytxfee=0",
            "-blockmintxfee=0",
            "-mintxfee=0",
        ]] * self.num_nodes

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):
        # initial state when setup_clean_chain is False
        assert_equal(self.nodes[0].getbalance(), {'bitcoin': Decimal('1250')})
        assert_equal(self.nodes[1].getbalance(), {'bitcoin': Decimal('1250')})
        assert_equal(self.nodes[2].getbalance(), {'bitcoin': Decimal('1250')})
        assert_equal(self.nodes[0].getblockchaininfo()["blocks"], 200)

        self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 10)
        self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 20)
        self.generate(self.nodes[0], 1)
        assert_equal(self.nodes[0].getblockchaininfo()["blocks"], 201)
        assert_equal(self.nodes[0].getbalance(), {'bitcoin': Decimal('1269.99897200')})
        assert_equal(self.nodes[1].getbalance(), {'bitcoin': Decimal('1260')})
        assert_equal(self.nodes[2].getbalance(), {'bitcoin': Decimal('1270')})

        # send a zero fee_rate transaction, which should not add a fee output
        addr = self.nodes[1].getnewaddress()
        txid = self.nodes[0].sendtoaddress(address=addr, amount=1, fee_rate=0)
        tx = self.nodes[0].getrawtransaction(txid, 2)
        # there should be no fees
        assert "bitcoin" not in tx["fee"]
        assert_equal(tx["fee"], {})
        # and no fee output
        assert_equal(len(tx["vout"]),2)
        for output in tx["vout"]:
            assert output["scriptPubKey"]["type"] != "fee"

        self.generate(self.nodes[0], 1)
        assert_equal(self.nodes[0].getblockchaininfo()["blocks"], 202)

        assert_equal(self.nodes[0].getbalance(), {'bitcoin': Decimal('1318.99897200')})
        assert_equal(self.nodes[1].getbalance(), {'bitcoin': Decimal('1261')})
        assert_equal(self.nodes[2].getbalance(), {'bitcoin': Decimal('1270')})

if __name__ == '__main__':
    WalletTest().main()
