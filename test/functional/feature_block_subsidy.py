#!/usr/bin/env python3
# Copyright (c) 2014-2018 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test parameterized block subsidy"""

from binascii import b2a_hex
from decimal import Decimal
from time import time

from test_framework.blocktools import create_coinbase
from test_framework.messages import CBlock, CProof, CTxOutValue
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal

def b2x(b):
    return b2a_hex(b).decode('ascii')

def assert_template(node, block, expect, rehash=True):
    # Re-set the block timestamp before every submission to avoid
    # intermittent "time too old" failures in slow CI boxes
    block.nTime = int(time()) + 1
    if rehash:
        block.hashMerkleRoot = block.calc_merkle_root()
        block.calc_sha256()
    rsp = node.getblocktemplate({'data': b2x(block.serialize()), 'mode': 'proposal'})
    assert_equal(rsp, expect)

class BlockSubsidyTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 2
        self.setup_clean_chain = True
        # 10 satoshi block subsidy at start for one node, none for other
        self.extra_args = [["-con_blocksubsidy=10"], ["-con_blocksubsidy=0", "-txindex=1"]]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):

        # Block will have 10 satoshi output, node 1 will ban
        addr = self.nodes[0].getnewaddress()
        sub_block = self.nodes[0].generatetoaddress(1, addr)
        raw_coinbase = self.nodes[0].getrawtransaction(self.nodes[0].getblock(sub_block[0])["tx"][0], False, sub_block[0])
        decoded_coinbase = self.nodes[0].decoderawtransaction(raw_coinbase)

        found_ten = False
        for vout in decoded_coinbase["vout"]:
            if vout["value"] == Decimal('0.00000010') and found_ten == False:
                found_ten = True
            elif vout["value"] == 0:
                continue
            else:
                raise Exception("Invalid output amount in coinbase")

        assert found_ten

        # Block will have 0 satoshis outputs only at height 1
        no_sub_block = self.nodes[1].generatetoaddress(1, addr)
        raw_coinbase = self.nodes[1].getrawtransaction(self.nodes[1].getblock(no_sub_block[0])["tx"][0], False, no_sub_block[0])
        decoded_coinbase = self.nodes[1].decoderawtransaction(raw_coinbase)
        for vout in decoded_coinbase["vout"]:
            if vout["value"] != 0:
                raise Exception("Invalid output amount in coinbase")

        tmpl = self.nodes[0].getblocktemplate({"rules": ["segwit"]})

        # Template with invalid amount(50*COIN) will be invalid in both
        coinbase_tx = create_coinbase(height=int(tmpl["height"]))

        block = CBlock()
        block.nVersion = tmpl["version"]
        block.hashPrevBlock = int(tmpl["previousblockhash"], 16)
        block.nTime = tmpl["curtime"]
        block.nBits = int(tmpl["bits"], 16)
        block.nNonce = 0
        block.block_height = int(tmpl["height"])
        block.proof = CProof(bytearray.fromhex('51'))
        block.vtx = [coinbase_tx]

        assert_template(self.nodes[0], block, "bad-cb-amount")

        # Set to proper value, resubmit
        block.vtx[0].vout[0].nValue = CTxOutValue(10)
        block.vtx[0].sha256 = None
        assert_template(self.nodes[0], block, None)

        # No subsidy also allowed
        block.vtx[0].vout[0].nValue = CTxOutValue(0)
        block.vtx[0].sha256 = None
        #assert_template(self.nodes[0], block, None) # ELEMENTS: 0-value outputs not allowed

        # Change previous blockhash to other nodes' genesis block and reward to 1, test again
        block.hashPrevBlock = int(self.nodes[1].getblockhash(self.nodes[1].getblockcount()), 16)
        block.vtx[0].vout[0].nValue = CTxOutValue(1)
        block.vtx[0].sha256 = None
        assert_template(self.nodes[1], block, "bad-cb-amount")

        block.vtx[0].vout[0].nValue = CTxOutValue(0)
        block.vtx[0].sha256 = None
        #assert_template(self.nodes[1], block, None) # ELEMENTS: 0-value outputs not allowed

if __name__ == '__main__':
    BlockSubsidyTest().main()
