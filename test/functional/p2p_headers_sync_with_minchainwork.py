#!/usr/bin/env python3
# Copyright (c) 2019-present The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test that we reject low difficulty headers to prevent our block tree from filling up with useless bloat"""

from test_framework.test_framework import BitcoinTestFramework

# from test_framework.p2p import (
#     CBlockHeader,
#     P2PInterface,
# )

import time

NODE1_BLOCKS_REQUIRED = 15
NODE2_BLOCKS_REQUIRED = 2047


class RejectLowDifficultyHeadersTest(BitcoinTestFramework):
    def set_test_params(self):
        self.rpc_timeout *= 4  # To avoid timeout when generating BLOCKS_TO_MINE
        self.setup_clean_chain = True
        self.num_nodes = 4
        self.chain = "regtest"
        # Node0 has no required chainwork; node1 requires 15 blocks on top of the genesis block; node2 requires 2047
        self.extra_args = [["-minimumchainwork=0x0", "-checkblockindex=0"], ["-minimumchainwork=0x1f", "-checkblockindex=0"], ["-minimumchainwork=0x1000", "-checkblockindex=0"], ["-minimumchainwork=0x1000", "-checkblockindex=0", "-whitelist=noban@127.0.0.1"]]

    def add_options(self, parser):
        self.add_wallet_options(parser)

    def setup_network(self):
        self.setup_nodes()
        self.reconnect_all()
        self.sync_all()

    def disconnect_all(self):
        self.disconnect_nodes(0, 1)
        self.disconnect_nodes(0, 2)
        self.disconnect_nodes(0, 3)

    def reconnect_all(self):
        self.connect_nodes(0, 1)
        self.connect_nodes(0, 2)
        self.connect_nodes(0, 3)

    def mocktime_all(self, time):
        for n in self.nodes:
            n.setmocktime(time)

    def test_chains_sync_when_long_enough(self):
        self.log.info("Generate blocks on the node with no required chainwork, and verify nodes 1 and 2 have no new headers in their headers tree")
        with self.nodes[1].assert_debug_log(expected_msgs=["[net] Ignoring low-work chain (height=14)"]), self.nodes[2].assert_debug_log(expected_msgs=["[net] Ignoring low-work chain (height=14)"]), self.nodes[3].assert_debug_log(expected_msgs=["Synchronizing blockheaders, height: 14"]):
            self.generatetoaddress(self.nodes[0], NODE1_BLOCKS_REQUIRED-1, address, sync_fun=self.no_op)

        # Node3 should always allow headers due to noban permissions
        self.log.info("Check that node3 will sync headers (due to noban permissions)")

        def check_node3_chaintips(num_tips, tip_hash, height):
            node3_chaintips = self.nodes[3].getchaintips()
            assert len(node3_chaintips) == num_tips
            assert {
                'height': height,
                'hash': tip_hash,
                'branchlen': height,
                'status': 'headers-only',
            } in node3_chaintips

        check_node3_chaintips(2, self.nodes[0].getbestblockhash(), NODE1_BLOCKS_REQUIRED-1)

        for node in self.nodes[1:3]:
            chaintips = node.getchaintips()
            assert len(chaintips) == 1
            assert {
                'height': 0,
                'hash': '0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206',
                'branchlen': 0,
                'status': 'active',
            } in chaintips

        self.log.info("Generate more blocks to satisfy node1's minchainwork requirement, and verify node2 still has no new headers in headers tree")
        with self.nodes[2].assert_debug_log(expected_msgs=["[net] Ignoring low-work chain (height=15)"]), self.nodes[3].assert_debug_log(expected_msgs=["Synchronizing blockheaders, height: 15"]):
            self.generatetoaddress(self.nodes[0], NODE1_BLOCKS_REQUIRED - self.nodes[0].getblockcount(), address, sync_fun=self.no_op)
        self.sync_blocks(self.nodes[0:2]) # node3 will sync headers (noban permissions) but not blocks (due to minchainwork)

        assert {
            'height': 0,
            'hash': '0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206',
            'branchlen': 0,
            'status': 'active',
        } in self.nodes[2].getchaintips()

        assert len(self.nodes[2].getchaintips()) == 1

        self.log.info("Generate long chain for node0/node1")
        self.generatetoaddress(self.nodes[0], NODE1_BLOCKS_REQUIRED-self.nodes[0].getblockcount(), address, sync_fun=self.no_op)
        self.log.info("Check that node3 accepted these headers as well")
        check_node3_chaintips(2, self.nodes[0].getbestblockhash(), NODE1_BLOCKS_REQUIRED)

        self.log.info("Generate long chain for node0/node1/node3")
        self.generatetoaddress(self.nodes[0], NODE2_BLOCKS_REQUIRED-self.nodes[0].getblockcount(), address, sync_fun=self.no_op)

        self.log.info("Verify that node2 and node3 will sync the chain when it gets long enough")
        self.sync_blocks()

    def test_large_reorgs_can_succeed(self):
        self.log.info("Test that a 2000+ block reorg, starting from a point that is more than 2000 blocks before a locator entry, can succeed")

        self.sync_all() # Ensure all nodes are synced.
        self.disconnect_all()

        # locator(block at height T) will have heights:
        # [T, T-1, ..., T-10, T-12, T-16, T-24, T-40, T-72, T-136, T-264,
        #  T-520, T-1032, T-2056, T-4104, ...]
        # So mine a number of blocks > 4104 to ensure that the first window of
        # received headers during a sync are fully between locator entries.
        BLOCKS_TO_MINE = 4110

        self.generatetoaddress(self.nodes[0], BLOCKS_TO_MINE, address, sync_fun=self.no_op)
        self.generatetoaddress(self.nodes[1], BLOCKS_TO_MINE+2, address, sync_fun=self.no_op)

        self.reconnect_all()

        self.mocktime_all(int(time.time()))  # Temporarily hold time to avoid internal timeouts
        self.sync_blocks(timeout=300) # Ensure tips eventually agree
        self.mocktime_all(0)


    def run_test(self):
        # ELEMENTS: setup a bcrt1 address to mine to, since our deterministic privkeys are invalid for bitcoin regtest
        # calls to self.generate have been replaced with self.generatetoaddress with this global address
        self.nodes[0].createwallet("miner")
        wallet = self.nodes[0].get_wallet_rpc("miner")
        global address
        address = wallet.getnewaddress()

        # ELEMENTS: presync test moved to p2p_headers_presync.py to use elements regtest

        self.test_chains_sync_when_long_enough()

        self.test_large_reorgs_can_succeed()


if __name__ == '__main__':
    RejectLowDifficultyHeadersTest(__file__).main()
