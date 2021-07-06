#!/usr/bin/env python3
# Copyright (c) 2015-2018 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test BIP 34, 65, 66, CSV activation at block 0"""

from test_framework.blocktools import create_coinbase, create_block, create_transaction
from test_framework.messages import msg_block
from test_framework.p2p import P2PInterface
from test_framework.script import (
    CScript,
    OP_TRUE,
    OP_DROP,
    OP_CHECKLOCKTIMEVERIFY,
)
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal, softfork_active

class BlockV4Test(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 1
        self.extra_args = [['-whitelist=127.0.0.1', '-con_bip34height=0', '-con_bip65height=0', '-con_bip66height=0', '-con_csv_deploy_start=-1', '-acceptnonstdtxn=1']]
        self.setup_clean_chain = True

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):

        # First, quick check that CSV is ACTIVE at genesis
        assert_equal(self.nodes[0].getblockcount(), 0)
        assert softfork_active(self.nodes[0], 'csv')

        peer = self.nodes[0].add_p2p_connection(P2PInterface())

        self.nodeaddress = self.nodes[0].getnewaddress()

        self.log.info("Test that blocks past the genesis block must be at least version 4")

        # Create a v3 block
        tip = self.nodes[0].getbestblockhash()
        block_time = self.nodes[0].getblockheader(tip)['mediantime'] + 1
        block = create_block(int(tip, 16), create_coinbase(1), block_time)
        block.nVersion = 3
        block.solve()

        # The best block should not have changed, because...
        assert_equal(self.nodes[0].getbestblockhash(), tip)

        # ... we rejected it because it is v3
        with self.nodes[0].assert_debug_log(expected_msgs=['{}, bad-version(0x00000003)'.format(block.hash)]):
            # Send it to the node
            peer.send_and_ping(msg_block(block))

        self.log.info("Test that a version 4 block with a valid-according-to-CLTV transaction is accepted")

        # Generate 100 blocks so that first coinbase matures
        generated_blocks = self.nodes[0].generate(100)
        spendable_coinbase_txid = self.nodes[0].getblock(generated_blocks[0])['tx'][0]
        coinbase_value = self.nodes[0].decoderawtransaction(self.nodes[0].gettransaction(spendable_coinbase_txid)["hex"])["vout"][0]["value"]
        tip = generated_blocks[-1]

        # Construct a v4 block
        block_time = self.nodes[0].getblockheader(tip)['mediantime'] + 1
        block = create_block(int(tip, 16), create_coinbase(len(generated_blocks) + 1), block_time)
        block.nVersion = 4

        # Create a CLTV transaction
        spendtx = create_transaction(self.nodes[0], spendable_coinbase_txid,
                self.nodeaddress, amount=1.0, fee=coinbase_value-1, locktime=1)
        spendtx.nLockTime = 1
        spendtx.vin[0].scriptSig = CScript([OP_TRUE, OP_CHECKLOCKTIMEVERIFY, OP_DROP] + list(CScript(spendtx.vin[0].scriptSig)))
        spendtx.rehash()

        # Add the CLTV transaction and prepare for sending
        block.vtx.append(spendtx)
        block.hashMerkleRoot = block.calc_merkle_root()
        block.solve()

        # Send block and check that it becomes new best block
        peer.send_and_ping(msg_block(block))
        assert_equal(int(self.nodes[0].getbestblockhash(), 16), block.sha256)

if __name__ == '__main__':
    BlockV4Test().main()
