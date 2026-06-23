#!/usr/bin/env python3
# Copyright (c) 2019-2022 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test that we reject low difficulty headers to prevent our block tree from filling up with useless bloat"""

from test_framework.test_framework import BitcoinTestFramework

from test_framework.p2p import (
    CBlockHeader,
    P2PInterface,
)

from test_framework.messages import (
    msg_headers,
)

from test_framework.blocktools import (
    NORMAL_GBT_REQUEST_PARAMS,
    create_block,
)

from test_framework.util import assert_equal

class PreSyncHeadersTest(BitcoinTestFramework):
    def set_test_params(self):
        self.rpc_timeout *= 4  # To avoid timeout when generating BLOCKS_TO_MINE
        self.setup_clean_chain = True
        self.num_nodes = 4
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

    def run_test(self):
        # ELEMENTS: this test taken from p2p_headers_sync_with_mainchainwork.py to run on elements regtest
        self.nodes[0].createwallet("miner")
        wallet = self.nodes[0].get_wallet_rpc("miner")
        global address
        address = wallet.getnewaddress()

        self.log.info("Test that getpeerinfo() includes headers presync height")

        # Disconnect network, so that we can find our own peer connection more
        # easily
        self.disconnect_all()

        p2p = self.nodes[0].add_p2p_connection(P2PInterface())
        node = self.nodes[0]

        # Ensure we have a long chain already
        current_height = self.nodes[0].getblockcount()
        if (current_height < 3000):
            self.generatetoaddress(node, 3000-current_height, address, sync_fun=self.no_op)

        # Send a group of 2000 headers, forking from genesis.
        new_blocks = []
        hashPrevBlock = int(node.getblockhash(0), 16)
        for i in range(2000):
            block = create_block(hashprev = hashPrevBlock, tmpl=node.getblocktemplate(NORMAL_GBT_REQUEST_PARAMS))
            block.solve()
            new_blocks.append(block)
            hashPrevBlock = block.sha256

        headers_message = msg_headers()
        headers_message.headers = [CBlockHeader(b) for b in new_blocks]

        #headers_message = msg_headers(headers=new_blocks)
        p2p.send_and_ping(headers_message)

        # getpeerinfo should show a sync in progress
        assert_equal(node.getpeerinfo()[0]['presynced_headers'], 2000)

if __name__ == '__main__':
    PreSyncHeadersTest(__file__).main()
