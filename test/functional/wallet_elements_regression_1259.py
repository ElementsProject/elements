#!/usr/bin/env python3
# Copyright (c) 2017-2020 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Tests that fundrawtransaction correcly handles the case of sending many
inputs of an issued asset, with no policy asset recipient.

See: https://github.com/ElementsProject/elements/issues/1259

This test issues an asset and creates many utxos, which are then used as inputs in
a consolidation transaction created with the various raw transaction calls.
"""
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
        ]] * self.num_nodes
        self.extra_args[0].append("-anyonecanspendaremine=1")

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):
        self.generate(self.nodes[0], COINBASE_MATURITY + 1)
        self.sync_all()

        self.log.info(f"Send some policy asset to node 1")
        self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 10)
        self.generate(self.nodes[0], 1)

        self.log.info(f"Issuing an asset from node 0")
        issuance = self.nodes[0].issueasset(1000, 1, True)
        self.generate(self.nodes[0], 1)
        asset = issuance["asset"]
        self.log.info(f"Asset ID is {asset}")

        # create many outputs of the new asset on node 1
        num_utxos = 45
        value = 10
        fee_rate = 10
        self.log.info(f"Sending {num_utxos} utxos of asset to node 1")
        for i in range(num_utxos):
            self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), value, "", "", False, False, None, None, None, asset, False, fee_rate, True)
            self.generate(self.nodes[0], 1)

        # create a raw tx on node 1 consolidating the asset utxos
        self.log.info(f"Create the raw consolidation transaction")
        hex = self.nodes[1].createrawtransaction([], [{ 'asset': asset, self.nodes[2].getnewaddress(): num_utxos * value }])

        # fund the raw tx
        self.log.info(f"Fund the raw transaction")
        raw_tx = self.nodes[1].fundrawtransaction(hex, True)

        # blind and sign the tx
        self.log.info(f"Blind and sign the raw transaction")
        hex = self.nodes[1].blindrawtransaction(raw_tx['hex'])
        signed_tx = self.nodes[1].signrawtransactionwithwallet(hex)
        assert_equal(signed_tx['complete'], True)

        # decode tx
        tx = self.nodes[1].decoderawtransaction(signed_tx['hex'])

        assert_equal(len(tx['vin']), num_utxos + 1)
        assert_equal(len(tx['vout']), 3)
        assert_equal(tx['fee'], {'b2e15d0d7a0c94e4e2ce0fe6e8691b9e451377f6e46e8045a86f7c4b5d4f0f23': Decimal('0.00112380')}) # fee output

        # send and mine the tx
        self.log.info(f"Send the raw transaction")
        self.nodes[1].sendrawtransaction(signed_tx['hex'])
        self.generate(self.nodes[1], 1)
        self.sync_all()
        balance = self.nodes[2].getbalance()
        assert_equal(balance[asset], Decimal(num_utxos * value))


if __name__ == '__main__':
    WalletTest().main()
