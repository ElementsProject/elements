#!/usr/bin/env python3
# Copyright (c) 2014-2018 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test the -alertnotify, -blocknotify and -walletnotify options."""
import os

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal, wait_until, connect_nodes_bi

class NotificationsTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 2
        self.setup_clean_chain = True

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def setup_network(self):
        self.alert_filename = os.path.join(self.options.tmpdir, "alert.txt")
        self.block_filename = os.path.join(self.options.tmpdir, "blocks.txt")
        self.tx_filename = os.path.join(self.options.tmpdir, "transactions.txt")

        # -alertnotify and -blocknotify on node0, walletnotify on node1
        self.extra_args = [["-blockversion=2",
                            "-alertnotify=echo %%s >> %s" % self.alert_filename,
                            "-blocknotify=echo %%s >> %s" % self.block_filename],
                           ["-blockversion=211",
                            "-rescan",
                            "-walletnotify=echo %%s >> %s" % self.tx_filename]]
        super().setup_network()

    def run_test(self):
        self.log.info("test -blocknotify")
        block_count = 10
        blocks = self.nodes[1].generate(block_count)

        # wait at most 10 seconds for expected file size before reading the content
        wait_until(lambda: os.path.isfile(self.block_filename) and os.stat(self.block_filename).st_size >= (block_count * 65), timeout=10)

        # file content should equal the generated blocks hashes
        with open(self.block_filename, 'r', encoding="utf-8") as f:
            assert_equal(sorted(blocks), sorted(l.strip() for l in f.read().splitlines()))

        self.log.info("test -walletnotify")
        # wait at most 10 seconds for expected file size before reading the content
        wait_until(lambda: os.path.isfile(self.tx_filename) and os.stat(self.tx_filename).st_size >= (block_count * 65), timeout=10)

        # file content should equal the generated transaction hashes
        txids_rpc = list(map(lambda t: t['txid'], self.nodes[1].listtransactions("*", block_count)))
        with open(self.tx_filename, 'r', encoding="ascii") as f:
            assert_equal(sorted(txids_rpc), sorted(l.strip() for l in f.read().splitlines()))
        os.remove(self.tx_filename)

        self.log.info("test -walletnotify after rescan")
        # restart node to rescan to force wallet notifications
        self.restart_node(1)
        connect_nodes_bi(self.nodes, 0, 1)

        wait_until(lambda: os.path.isfile(self.tx_filename) and os.stat(self.tx_filename).st_size >= (block_count * 65), timeout=10)

        # file content should equal the generated transaction hashes
        txids_rpc = list(map(lambda t: t['txid'], self.nodes[1].listtransactions("*", block_count)))
        with open(self.tx_filename, 'r', encoding="ascii") as f:
            assert_equal(sorted(txids_rpc), sorted(l.strip() for l in f.read().splitlines()))

        # TODO: add test for `-alertnotify` large fork notifications

if __name__ == '__main__':
    NotificationsTest().main()
