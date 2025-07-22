#!/usr/bin/env python3
# Copyright (c) 2017-2020 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
from decimal import Decimal

from test_framework.blocktools import COINBASE_MATURITY
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
)

class WalletTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 3
        self.extra_args = [[
            "-blindedaddresses=1",
            "-initialfreecoins=2100000000000000",
            "-con_blocksubsidy=0",
            "-con_connect_genesis_outputs=1",
            "-txindex=1",
            "-minrelaytxfee=0",
            "-blockmintxfee=0",
            "-mintxfee=0",
        ]] * self.num_nodes
        self.extra_args[0].append("-anyonecanspendaremine=1")

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):
        self.generate(self.nodes[0], COINBASE_MATURITY + 1)
        self.sync_all()

        new_addr = self.nodes[1].getnewaddress()
        self.nodes[0].sendtoaddress(new_addr, 10)
        self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 20)
        self.generate(self.nodes[0], 1)
        assert_equal(self.nodes[0].getblockchaininfo()["blocks"], 102)
        assert_equal(self.nodes[0].getbalance(), {'bitcoin': Decimal('20999969.99900900')})
        assert_equal(self.nodes[1].getbalance(), {'bitcoin': Decimal('10.00000000')})
        assert_equal(self.nodes[2].getbalance(), {'bitcoin': Decimal('20.00000000')})

        addr = self.nodes[1].getnewaddress()
        txid = self.nodes[0].sendtoaddress(addr, 1, None, None, None, None, None, None, None, None, None, 0, False)
        tx = self.nodes[0].gettransaction(txid)
        assert_equal(tx["fee"]["bitcoin"], 0)
        hex = self.nodes[0].getrawtransaction(txid)
        self.generate(self.nodes[0], 1)
        assert_equal(self.nodes[0].getblockchaininfo()["blocks"], 103)

        decoded = self.nodes[0].decoderawtransaction(hex)
        # there should be no fee output
        assert_equal(decoded["fee"], {})
        assert_equal(len(decoded["vout"]),2)
        assert_equal(self.nodes[0].getbalance(), {'bitcoin': Decimal('20999968.99900900')})
        assert_equal(self.nodes[1].getbalance(), {'bitcoin': Decimal('11.00000000')})
        assert_equal(self.nodes[2].getbalance(), {'bitcoin': Decimal('20.00000000')})

if __name__ == '__main__':
    WalletTest().main()
