#!/usr/bin/env python3
# Copyright (c) 2017-2017 The Elements Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test custom -anyonecanspendaremine chainparams."""

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import start_nodes, connect_nodes_bi, assert_raises_jsonrpc

class AnyoneCanSpendTest(BitcoinTestFramework):

    def __init__(self):
        super().__init__()
        self.setup_clean_chain = True
        self.num_nodes = 2
        self.extra_args = [["-anyonecanspendaremine=0"], ["-anyonecanspendaremine"]]

    def setup_network(self, split=False):
        self.nodes = start_nodes(self.num_nodes, self.options.tmpdir, extra_args=self.extra_args)
        connect_nodes_bi(self.nodes,0,1)
        self.is_network_split=False
        self.sync_all()

    def run_test(self):
        self.nodes[0].generate(100)
        self.sync_all()

        address = self.nodes[0].getnewaddress()
        # Show error when disabled
        assert_raises_jsonrpc(-6, 'Insufficient funds', self.nodes[0].sendtoaddress, address, 1)

        # Using -anyonecanspendaremine bypasses the error
        self.nodes[1].sendtoaddress(address, 1)

if __name__ == '__main__':
    AnyoneCanSpendTest().main()
