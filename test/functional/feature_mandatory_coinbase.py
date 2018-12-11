#!/usr/bin/env python3
# Copyright (c) 2014-2018 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test mandatory coinbase feature"""

from binascii import b2a_hex

from test_framework.blocktools import create_coinbase
from test_framework.messages import CBlock, CProof
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal, assert_raises_rpc_error

mandatory_privkey = "cNaQCDwmmh4dS9LzCgVtyy1e1xjCJ21GUDHe9K98nzb689JvinGV"
mandatory_address = "n3NkSZqoPMCQN5FENxUBw4qVATbytH6FDK"
mandatory_pubkey = "02fcba7ecf41bc7e1be4ee122d9d22e3333671eb0a3a87b5cdf099d59874e1940f"
mandatory_script = "76a914efc58b838b3153174bf3d1677b7213353a4dccfd88ac"

def b2x(b):
    return b2a_hex(b).decode('ascii')

def assert_template(node, block, expect, rehash=True):
    if rehash:
        block.hashMerkleRoot = block.calc_merkle_root()
    rsp = node.getblocktemplate({'data': b2x(block.serialize()), 'mode': 'proposal'})
    assert_equal(rsp, expect)

class MandatoryCoinbaseTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 2
        self.setup_clean_chain = True
        # Non-zero coinbase outputs *must* match this. Not setting it means anything is allowed
        self.extra_args = [["-con_mandatorycoinbase="+mandatory_script], []]

    def run_test(self):
        node0 = self.nodes[0]
        node1 = self.nodes[1]

        node0.importprivkey(mandatory_privkey)

        self.log.info("generatetoaddress: Making blocks of various kinds, checking for rejection")
        # Create valid blocks to get out of IBD and get some funds (subsidy goes to permitted addr)
        node0.generatetoaddress(101, mandatory_address)

        # Generating for another address will not work
        assert_raises_rpc_error(-1, "CreateNewBlock: TestBlockValidity failed: bad-coinbase-txos", node0.generatetoaddress, 1, node0.getnewaddress())

        # Have non-mandatory node make a template
        self.sync_all()
        tmpl = node1.getblocktemplate()

        # We make a block with OP_TRUE coinbase output that will fail on node0
        coinbase_tx = create_coinbase(height=int(tmpl["height"]))
        # sequence numbers must not be max for nLockTime to have effect
        coinbase_tx.vin[0].nSequence = 2 ** 32 - 2
        coinbase_tx.rehash()

        block = CBlock()
        block.nVersion = tmpl["version"]
        block.hashPrevBlock = int(tmpl["previousblockhash"], 16)
        block.nTime = tmpl["curtime"]
        block.nBits = int(tmpl["bits"], 16)
        block.nNonce = 0
        block.proof = CProof(bytearray.fromhex('51'))
        block.vtx = [coinbase_tx]
        block.block_height = int(tmpl["height"])

        self.log.info("getblocktemplate: Test block on both nodes")
        assert_equal(node0.submitblock(b2x(block.serialize())), 'invalid')
        assert_template(node1, block, None)

        self.log.info("getblocktemplate: Test non-subsidy block on both nodes")
        # Without block reward anything goes, this allows commitment outputs like segwit
        coinbase_tx.vout[0].nValue = 0
        coinbase_tx.rehash()
        block.vtx = [coinbase_tx]
        assert_template(node0, block, None)
        assert_template(node1, block, None)

if __name__ == '__main__':
    MandatoryCoinbaseTest().main()
