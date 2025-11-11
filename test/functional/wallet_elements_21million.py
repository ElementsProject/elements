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
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 3
        args = [
            "-blindedaddresses=1"
        ]
        self.extra_args = [
            args + ["-acceptunlimitedissuances=1"],
            args + ["-acceptunlimitedissuances=1"],
            args, # node 2 blocks unblinded issuances out of moneyrange (default -acceptunlimitedissuances=0)
        ]

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

        self.log.info("Issue more than 21 million of a unblinded non-policy asset")
        issuance = self.nodes[0].issueasset(300_000_000, 100, False)
        unblinded_asset = issuance['asset']
        self.generate(self.nodes[0], 1)
        assert_equal(self.nodes[0].getbalance()[unblinded_asset], 300_000_000)

        self.log.info("Reissue more than 21 million of a unblinded non-policy asset")
        self.nodes[0].reissueasset(unblinded_asset, 200_000_000)
        self.generate(self.nodes[0], 1)
        assert_equal(self.nodes[0].getbalance()[unblinded_asset], 500_000_000)

        self.log.info("Issue more than 21 million of a unblinded reissuance token")
        issuance = self.nodes[0].issueasset(300_000_000, 100_000_000, False)
        self.generate(self.nodes[0], 1)
        assert_equal(self.nodes[0].getbalance()[issuance['asset']], 300_000_000)
        assert_equal(self.nodes[0].getbalance()[issuance['token']], 100_000_000)

        # send more than 21 million of that asset
        addr = self.nodes[1].getnewaddress()
        self.nodes[0].sendtoaddress(address=addr, amount=22_000_000, assetlabel=asset)
        self.generate(self.nodes[0], 1)
        assert_equal(self.nodes[0].getbalance()[asset], 178_000_000)
        assert_equal(self.nodes[1].getbalance()[asset], 22_000_000)

        # unload/load wallet
        self.nodes[1].unloadwallet(self.default_wallet_name)
        self.nodes[1].loadwallet(self.default_wallet_name)
        assert_equal(self.nodes[1].getbalance()[asset], 22_000_000)

        # send more than 45 million of that asset
        addr = self.nodes[2].getnewaddress()
        self.nodes[0].sendtoaddress(address=addr, amount=46_000_000, assetlabel=asset)
        self.generate(self.nodes[0], 1)
        assert_equal(self.nodes[0].getbalance()[asset], 132_000_000)
        assert_equal(self.nodes[2].getbalance()[asset], 46_000_000)

        # unload/load wallet
        self.nodes[2].unloadwallet(self.default_wallet_name)
        self.nodes[2].loadwallet(self.default_wallet_name)
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
        self.nodes[2].unloadwallet(self.default_wallet_name)
        self.nodes[2].loadwallet(self.default_wallet_name)
        assert_equal(self.nodes[2].getbalance()[asset], 200_000_000)

        # send some policy asset to node 2 for fees
        addr = self.nodes[2].getnewaddress()
        self.nodes[0].sendtoaddress(address=addr, amount=1)
        self.generate(self.nodes[0], 1)
        assert_equal(self.nodes[2].getbalance()['bitcoin'], 1)

        self.log.info("Issue more than 21 million of a non-policy asset on node 2 - rejected from mempool")
        issuance = self.nodes[2].issueasset(300_000_000, 100, False)
        asset = issuance['asset']
        issuance_tx = self.nodes[2].gettransaction(issuance["txid"])
        assert_raises_rpc_error(-26, "issuance-out-of-range", self.nodes[2].sendrawtransaction, issuance_tx['hex'])
        self.generate(self.nodes[0], 1)
        assert(asset not in self.nodes[2].getbalance())
        # transaction should be accepted on node 0
        self.nodes[0].sendrawtransaction(issuance_tx["hex"])
        assert(issuance['txid'] in self.nodes[0].getrawmempool())
        assert(issuance['txid'] not in self.nodes[2].getrawmempool())
        self.generate(self.nodes[0], 1)
        assert(asset not in self.nodes[0].getbalance())
        assert_equal(self.nodes[2].getbalance()[asset], 300_000_000)

        self.log.info("Reissue more than 21 million of a unblinded non-policy asset on node 2 - rejected from mempool")
        issuance = self.nodes[2].issueasset(3_000_000, 100, False)
        asset = issuance['asset']
        unblinded_asset = issuance['asset']
        self.generate(self.nodes[2], 1)
        assert_equal(self.nodes[2].getbalance()[unblinded_asset], 3_000_000)
        reissuance = self.nodes[2].reissueasset(unblinded_asset, 200_000_000)
        reissuance_tx = self.nodes[2].gettransaction(reissuance["txid"])
        assert_raises_rpc_error(-26, "issuance-out-of-range", self.nodes[2].sendrawtransaction, reissuance_tx['hex'])
        # transaction should be accepted on node 0
        self.nodes[0].sendrawtransaction(reissuance_tx["hex"])
        assert(reissuance['txid'] in self.nodes[0].getrawmempool())
        assert(reissuance['txid'] not in self.nodes[2].getrawmempool())
        self.generate(self.nodes[0], 1)
        assert(asset not in self.nodes[0].getbalance())
        assert_equal(self.nodes[2].getbalance()[asset], 203_000_000)

        self.log.info("Issue more than 21 million reissuance tokens on node 2 - rejected from mempool")
        issuance = self.nodes[2].issueasset(3_000_000, 200_000_000, False)
        asset = issuance['asset']
        token = issuance['token']
        issuance_tx = self.nodes[2].gettransaction(issuance["txid"])
        assert_raises_rpc_error(-26, "issuance-out-of-range", self.nodes[2].sendrawtransaction, issuance_tx['hex'])
        self.generate(self.nodes[0], 1)
        assert(asset not in self.nodes[2].getbalance())
        assert(token not in self.nodes[2].getbalance())
        # transaction should be accepted on node 0
        self.nodes[0].sendrawtransaction(issuance_tx["hex"])
        assert(issuance['txid'] in self.nodes[0].getrawmempool())
        assert(issuance['txid'] not in self.nodes[2].getrawmempool())
        self.generate(self.nodes[0], 1)
        assert(asset not in self.nodes[0].getbalance())
        assert_equal(self.nodes[2].getbalance()[asset], 3_000_000)
        assert_equal(self.nodes[2].getbalance()[token], 200_000_000)

if __name__ == '__main__':
    WalletTest().main()
