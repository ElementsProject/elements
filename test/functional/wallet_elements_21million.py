#!/usr/bin/env python3
# Copyright (c) 2017-2020 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from test_framework.blocktools import COINBASE_MATURITY
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
)

class WalletTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 3
        self.extra_args = [['-blindedaddresses=1']] * self.num_nodes

    def setup_network(self, split=False):
        self.setup_nodes()
        self.connect_nodes(0, 1)
        self.connect_nodes(1, 2)
        self.connect_nodes(0, 2)
        self.sync_all()

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):
        self.generate(self.nodes[0], COINBASE_MATURITY + 1)

        assert_equal(self.nodes[0].getbalance(), {'bitcoin': 50})
        assert_equal(self.nodes[1].getbalance(), {'bitcoin': 0})

        self.log.info("Issue more than 21 million of a non-policy asset")
        issuance = self.nodes[0].issueasset(100_000_000, 100)
        asset = issuance['asset']
        self.generate(self.nodes[0], 1)
        assert_equal(self.nodes[0].getbalance()[asset], 100_000_000)

        self.log.info("Reissue more than 21 million of a non-policy asset")
        self.nodes[0].reissueasset(asset, 100_000_000)
        self.generate(self.nodes[0], 1)
        assert_equal(self.nodes[0].getbalance()[asset], 200_000_000)

        # send more than 21 million of that asset
        addr = self.nodes[1].getnewaddress()
        self.nodes[0].sendtoaddress(address=addr, amount=22_000_000, assetlabel=asset)
        self.generate(self.nodes[0], 1)
        assert_equal(self.nodes[0].getbalance()[asset], 178_000_000)
        assert_equal(self.nodes[1].getbalance()[asset], 22_000_000)

        # unload/load wallet
        self.nodes[1].unloadwallet("")
        self.nodes[1].loadwallet("")
        assert_equal(self.nodes[1].getbalance()[asset], 22_000_000)

        # send more than 45 million of that asset
        addr = self.nodes[2].getnewaddress()
        self.nodes[0].sendtoaddress(address=addr, amount=46_000_000, assetlabel=asset)
        self.generate(self.nodes[0], 1)
        assert_equal(self.nodes[0].getbalance()[asset], 132_000_000)
        assert_equal(self.nodes[2].getbalance()[asset], 46_000_000)

        # unload/load wallet
        self.nodes[2].unloadwallet("")
        self.nodes[2].loadwallet("")
        assert_equal(self.nodes[2].getbalance()[asset], 46_000_000)

        # send some policy asset to node 1 for fees
        addr = self.nodes[1].getnewaddress()
        self.nodes[0].sendtoaddress(address=addr, amount=1)
        self.generate(self.nodes[0], 1)
        assert_equal(self.nodes[1].getbalance()['bitcoin'], 1)
        assert_equal(self.nodes[1].getbalance()[asset], 22_000_000)

        # send the remainders
        addr = self.nodes[2].getnewaddress()
        self.nodes[0].sendtoaddress(address=addr, amount=132_000_000, assetlabel=asset)
        addr = self.nodes[2].getnewaddress()
        self.nodes[1].sendtoaddress(address=addr, amount=22_000_000, assetlabel=asset)
        self.sync_mempools()
        self.generate(self.nodes[0], 1)

        assert asset not in self.nodes[0].getbalance()
        assert asset not in self.nodes[1].getbalance()
        assert_equal(self.nodes[2].getbalance()[asset], 200_000_000)

        # unload/load wallet
        self.nodes[2].unloadwallet("")
        self.nodes[2].loadwallet("")
        assert_equal(self.nodes[2].getbalance()[asset], 200_000_000)

if __name__ == '__main__':
    WalletTest().main()
