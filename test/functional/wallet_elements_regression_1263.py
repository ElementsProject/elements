#!/usr/bin/env python3
# Copyright (c) 2017-2020 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test getpeginaddress when started with Bitcoin chain params.

This doesn't make sense and should fail gracefully, but is causing a segfault.
This functional test should catch any regression to this fix.
"""

from test_framework.util import assert_raises_rpc_error
from test_framework.test_framework import BitcoinTestFramework

class RegressionTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 1
        self.chain = "regtest"

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):
        self.log.info("Start in Bitcoin regtest mode")
        self.nodes[0].createwallet("pegin")
        rpc = self.nodes[0].get_wallet_rpc("pegin")
        self.generatetoaddress(self.nodes[0], 1, rpc.getnewaddress())

        self.log.info("Call getpeginaddress")
        assert_raises_rpc_error(-32603, "No valid fedpegscripts. Not running in Elements mode, check your 'chain' param.", rpc.getpeginaddress)

if __name__ == '__main__':
    RegressionTest().main()
