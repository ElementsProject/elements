#!/usr/bin/env python3
# Copyright (c) 2017-2020 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test blinding logic when change is dropped and we have only one other blinded input

Constructs a transaction with a sufficiently small change output that it
gets dropped, in which there is only one other blinded input. In the case
that we have no blinded inputs, we would need to add an OP_RETURN output
to the transaction, neccessitating special logic.

Check that this special logic still results in a correct transaction that
sends the money to the desired recipient (and that the recipient is able
to receive/spend the money).
"""

from decimal import Decimal

from test_framework.blocktools import COINBASE_MATURITY
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    satoshi_round,
)

class WalletCtTest(BitcoinTestFramework):
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
        self.extra_args[0].append("-anyonecanspendaremine=1") # first node gets the coins

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):
        # Mine 101 blocks to get the initial coins out of IBD
        self.nodes[0].generate(COINBASE_MATURITY + 1)
        self.nodes[0].syncwithvalidationinterfacequeue()
        self.sync_all()

        for i in range(self.num_nodes):
            self.log.info(f"Starting with node {i} balance: {self.nodes[i].getbalance()}")

        # Send 1 coin to a new wallet
        txid = self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 1)
        self.log.info(f"Sent one coin to node 1 in {txid}")
        self.nodes[0].generate(2)
        self.sync_all()

        # Try to send those coins to yet another wallet, sending a large enough amount
        # that the change output is dropped.
        amt = satoshi_round(Decimal(0.9995))
        txid = self.nodes[1].sendtoaddress(self.nodes[2].getnewaddress(), amt)
        self.log.info(f"Sent {amt} LBTC to node 2 in {txid}")
        self.nodes[1].generate(2)
        self.sync_all()

        for i in range(self.num_nodes):
            self.log.info(f"Finished with node {i} balance: {self.nodes[i].getbalance()}")

        assert_equal(self.nodes[1].getbalance(), { "bitcoin": Decimal(0) })
        assert_equal(self.nodes[2].getbalance(), { "bitcoin": amt })

if __name__ == '__main__':
    WalletCtTest().main()

