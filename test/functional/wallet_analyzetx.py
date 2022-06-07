#!/usr/bin/env python3
# Copyright (c) 2021 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test analyzerawtransaction.
"""

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_approx,
    assert_equal,
)

def assert_analysis(analysis, expected):
    if "bitcoin" not in expected:
        expected["bitcoin"] = 0.0
    assert_equal(len(analysis), len(expected))
    for key in expected:
        assert_approx(analysis[key], expected[key], 0.0000001)

class AnalyzeTxTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 2
        elements_args = ["-blindedaddresses=1", "-initialfreecoins=2100000000000000", "-con_blocksubsidy=0", "-con_connect_genesis_outputs=1", "-anyonecanspendaremine=1"]
        self.extra_args = [elements_args, elements_args]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def setup_network(self, split=False):
        self.setup_nodes()

    def run_test(self):
        node0 = self.nodes[0]
        node1 = self.nodes[1]
        self.connect_nodes(0, 1)

        node0.generate(1) # Leave IBD

        node0.createwallet(wallet_name='w0')
        w0 = node0.get_wallet_rpc('w0')
        node1.createwallet(wallet_name='w1')
        w1 = node1.get_wallet_rpc('w1')

        w0.rescanblockchain()
        assetdata = w0.issueasset(10000000, 100)
        asset = assetdata["asset"]

        address1 = w1.getnewaddress()

        tx = node1.createrawtransaction([], [{address1: 5.0}], 0, False, {address1: asset})

        # node0 should be unaffected
        analysis = w0.analyzerawtransaction(tx)
        assert_analysis(analysis, {})

        # node1 should see a +5 asset
        analysis = w1.analyzerawtransaction(tx)
        assert_analysis(analysis, {asset: 5.0})

        # w0 funds transaction; it should now see a decrease in bitcoin (tx fee) and the asset, and w1 should see the same as above
        funding = w0.fundrawtransaction(tx)
        tx = funding["hex"]
        bitcoin_fee = float(funding["fee"])

        # node0 sees decrease in bitcoin and the asset
        analysis = w0.analyzerawtransaction(tx)
        assert_analysis(analysis, {"bitcoin": -bitcoin_fee, asset: -5.0})

        # node1 sees same as before
        analysis = w1.analyzerawtransaction(tx)
        assert_analysis(analysis, {asset: 5.0})

        # after blinding the transaction, nodes should still be able to read correctly
        tx = w0.blindrawtransaction(tx)

        # node0 sees decrease in bitcoin and the asset
        analysis = w0.analyzerawtransaction(tx)
        assert_analysis(analysis, {"bitcoin": -bitcoin_fee, asset: -5.0})

        # node1 sees same as before
        analysis = w1.analyzerawtransaction(tx)
        assert_analysis(analysis, {asset: 5.0})


if __name__ == '__main__':
    AnalyzeTxTest().main()
