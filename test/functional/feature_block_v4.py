#!/usr/bin/env python3
# Copyright (c) 2015-2018 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test BIP 34, 65, 66 activation at block 0"""

from test_framework.blocktools import create_coinbase, create_block, create_transaction
from test_framework.messages import msg_block
from test_framework.mininode import mininode_lock, P2PInterface
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal, wait_until

from feature_cltv import cltv_validate, REJECT_OBSOLETE

class BlockV4Test(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 1
        self.extra_args = [['-whitelist=127.0.0.1', '-con_bip34height=0', '-con_bip65height=0', '-con_bip66height=0']]
        self.setup_clean_chain = True

    def run_test(self):
        self.nodes[0].add_p2p_connection(P2PInterface())

        self.nodeaddress = self.nodes[0].getnewaddress()

        self.log.info("Test that blocks past the genesis block must be at least version 4")

        # Create a v3 block
        tip = self.nodes[0].getbestblockhash()
        block_time = self.nodes[0].getblockheader(tip)['mediantime'] + 1
        block = create_block(int(tip, 16), create_coinbase(1), block_time)
        block.nVersion = 3
        block.solve()

        # Send it to the node
        self.nodes[0].p2p.send_and_ping(msg_block(block))

        # The best block should not have changed, because...
        assert_equal(self.nodes[0].getbestblockhash(), tip)

        # ... we rejected it because it is v3
        wait_until(lambda: "reject" in self.nodes[0].p2p.last_message.keys(), lock=mininode_lock)
        with mininode_lock:
            assert_equal(self.nodes[0].p2p.last_message["reject"].code, REJECT_OBSOLETE)
            assert_equal(self.nodes[0].p2p.last_message["reject"].reason, b'bad-version(0x00000003)')
            assert_equal(self.nodes[0].p2p.last_message["reject"].data, block.sha256)
            del self.nodes[0].p2p.last_message["reject"]

        self.log.info("Test that a version 4 block with a valid-according-to-CLTV transaction is accepted")

        # Generate 100 blocks so that first coinbase matures
        generated_blocks = self.nodes[0].generate(100)
        spendable_coinbase_txid = self.nodes[0].getblock(generated_blocks[0])['tx'][0]
        tip = generated_blocks[-1]

        # Construct a v4 block
        block_time = self.nodes[0].getblockheader(tip)['mediantime'] + 1
        block = create_block(int(tip, 16), create_coinbase(len(generated_blocks) + 1), block_time)
        block.nVersion = 4

        # Create a CLTV transaction
        spendtx = create_transaction(self.nodes[0], spendable_coinbase_txid,
                self.nodeaddress, amount=1.0)
        spendtx = cltv_validate(self.nodes[0], spendtx, 1)
        spendtx.rehash()

        # Add the CLTV transaction and prepare for sending
        block.vtx.append(spendtx)
        block.hashMerkleRoot = block.calc_merkle_root()
        block.solve()

        # Send block and check that it becomes new best block
        self.nodes[0].p2p.send_and_ping(msg_block(block))
        assert_equal(int(self.nodes[0].getbestblockhash(), 16), block.sha256)

if __name__ == '__main__':
    BlockV4Test().main()
