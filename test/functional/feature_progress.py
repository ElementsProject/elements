#!/usr/bin/env python3
# Copyright (c) 2015-2016 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

#
# Test progress code
#

import time

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    Decimal,
)

def assert_close(f1, f2):
    assert abs(Decimal(f1)-f2) < 0.1

class ProgressTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 2
        self.extra_args = [["-debug", "-con_npowtargetspacing=1", "-maxtimeadjustment=0"]] * self.num_nodes

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def setup_network(self):
        self.setup_nodes()
        self.starttime = int(time.time())

    def setmocktime(self, ntime):
        for node in self.nodes:
            node.setmocktime(self.starttime + ntime)

    def run_test(self):
        node1 = self.nodes[0]
        node2 = self.nodes[1]
        self.setmocktime(0)

        blocks = []
        for i in range(10):
            self.setmocktime(i)
            blocks.extend(node1.generate(1))

        self.setmocktime(19)
        assert_close(0.5, node1.getblockchaininfo()["verificationprogress"])

        assert node2.getblockchaininfo()["initialblockdownload"]

        self.setmocktime(10)
        for i in range(10):
            node2.submitblock(node1.getblock(blocks[i], False))
            progress = node2.getblockchaininfo()["verificationprogress"]
            assert_close(i/10.0, progress)

        assert not node2.getblockchaininfo()["initialblockdownload"]

if __name__ == '__main__':
    ProgressTest().main()
