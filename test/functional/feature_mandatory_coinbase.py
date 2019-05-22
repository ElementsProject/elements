#!/usr/bin/env python3
# Copyright (c) 2014-2018 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test mandatory coinbase feature"""

from binascii import b2a_hex

from test_framework.blocktools import create_coinbase
from test_framework.messages import CBlock, CProof, CTxOutValue, CTxOut
from test_framework.script import CScript, OP_RETURN
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal, assert_raises_rpc_error

mandatory_privkey = "cQ2nfMkghhdEgRQwcfJmTb6XSenfLRmngpLmWuEBAJnepnKMfznH"
mandatory_address = "XP3bwB9jSxt58frSa3cJismgGL3F57ukUy"
#mandatory_pubkey = "024f0c5cdb8f31d7395bcc83f6adc46f292f6555eca2d24dfa581c3b0845778b2b"
mandatory_script = "a914804b9fd9d6939c2e960b7aa31124a5d532f4e59c87"

def b2x(b):
    return b2a_hex(b).decode('ascii')

def assert_template(node, block, expect, rehash=True):
    if rehash:
        block.hashMerkleRoot = block.calc_merkle_root()
    rsp = node.getblocktemplate({'data': b2x(block.serialize()), 'mode': 'proposal', 'rules': 'segwit'})
    assert_equal(rsp, expect)

class MandatoryCoinbaseTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 2
        self.setup_clean_chain = True
        # Non-zero coinbase outputs *must* match this. Not setting it means anything is allowed
        self.extra_args = [["-con_mandatorycoinbase="+mandatory_script], []]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

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
        tmpl = node1.getblocktemplate({'rules': ['segwit']})

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
        block.hashMerkleRoot = block.calc_merkle_root()

        self.log.info("getblocktemplate: Test block on both nodes")
        assert_template(node1, block, None)
        assert_template(node0, block, 'bad-coinbase-txos')

        self.log.info("getblocktemplate: Test non-subsidy block on both nodes")
        # Without block reward anything goes, this allows commitment outputs like segwit
        coinbase_tx.vout[0].nValue = CTxOutValue(0)
        coinbase_tx.vout[0].scriptPubKey = CScript([OP_RETURN, b'\xff'])
        coinbase_tx.rehash()
        block.vtx = [coinbase_tx]
        assert_template(node0, block, None)
        assert_template(node1, block, None)

        #
        # Also test that coinbases can't have fees.
        self.sync_all()
        tmpl = node1.getblocktemplate({'rules': ['segwit']})
        coinbase_tx = create_coinbase(height=int(tmpl["height"]))
        # sequence numbers must not be max for nLockTime to have effect
        coinbase_tx.vin[0].nSequence = 2 ** 32 - 2
        # Add fee output.
        coinbase_tx.vout[0].nValue.setToAmount(coinbase_tx.vout[0].nValue.getAmount() - 1)
        coinbase_tx.vout.append(CTxOut(1))
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
        block.hashMerkleRoot = block.calc_merkle_root()

        # should not be accepted
        assert_template(node0, block, "bad-cb-fee")
        assert_template(node1, block, "bad-cb-fee")

if __name__ == '__main__':
    MandatoryCoinbaseTest().main()
