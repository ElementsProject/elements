#!/usr/bin/env python3
# Copyright (c) 2014-2016 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

#
# Test RPC calls related to blockchain state. Tests correspond to code in
# rpc/blockchain.cpp.
#

from decimal import Decimal
from test_framework.test_framework import BitcoinTestFramework
from test_framework.authproxy import JSONRPCException
from test_framework.util import (
    assert_equal,
    start_nodes,
    assert_raises_jsonrpc,
)


class SignedBlockchainTest(BitcoinTestFramework):
    """
    Test signed-blockchain-related RPC calls:

        - getnewblockhex
        - signblock
        - combineblocksigs
        - submitblock

    """

    def __init__(self):
        super().__init__()
        self.setup_clean_chain = True
        self.num_nodes = 3

    def setup_network(self, split=False):
        # Keys for signing 2-of-3
        pubkeys = ["039560e48d4336e40db447fc136ce24ae1dfdefa5701e4d4e57aa1a1a9f47f3faa", "025a66517c1d85adcd909f9f675bf656708edc4da1f614693e347be6baf0fef4ae", "02ca238faeb3b01d26ae8a39869220dbd84cc8516398afa8958fe613fe4fdf1c04"]
        # Normal multisig scriptPubKey: 1 <33 byte pubkey> <33 byte pubkey> ... 2 OP_CMS
        sign_script = "-signblockscript=5221"+pubkeys[0]+"21"+pubkeys[1]+"21"+pubkeys[2]+"53ae"
        self.nodes = start_nodes(self.num_nodes, self.options.tmpdir, [[sign_script],[sign_script], [sign_script]])
        # nodes are disconnected for this test
        self.is_network_split = True

    def run_test(self):
        keys = ["cRANrxPMceu8jKAA76xzpA9PtTEhBknyZyaaQZ3Z5FnFTGkCAqmT", "cTJRjDBWo1JXdie31B5wv5eXNrPGCAjQKn48umubhmNLjsnj951V", "cVjTXVgKE8PhvCgDowRJVQW68q7j5kSbDGfAT5CUwt9D8dn2cAwf"]
        assert_equal(self.nodes[0].getblockcount(), 0)
        assert_equal(self.nodes[1].getblockcount(), 0)

        block_hex = self.nodes[0].getnewblockhex()

        # Block needs signatures, but valid and extends chaintip otherwise
        assert_equal(self.nodes[0].testproposedblock(block_hex), None)
        assert_equal(self.nodes[1].testproposedblock(block_hex), None)

        assert_equal(self.nodes[0].submitblock(block_hex), "block-proof-invalid")
        assert_equal(self.nodes[1].submitblock(block_hex), "block-proof-invalid")

        assert_equal(self.nodes[0].getblockcount(), 0)
        assert_equal(self.nodes[1].getblockcount(), 0)

        # combineblocksigs only returns true when signatures are appended and enough
        # are included to pass validation
        assert_equal(self.nodes[0].combineblocksigs(block_hex, [])["complete"], False)
        assert_equal(self.nodes[1].combineblocksigs(block_hex, [])["complete"], False)

        # Now we can try to sign, without key
        assert_equal(self.nodes[0].signblock(block_hex), "00")
        assert_equal(self.nodes[1].signblock(block_hex), "00")

        # Import keys
        self.nodes[0].importprivkey(keys[0])
        self.nodes[1].importprivkey(keys[1])
        self.nodes[2].importprivkey(keys[2])

        sig0 = self.nodes[0].signblock(block_hex)
        sig1 = self.nodes[1].signblock(block_hex)

        combined0 = self.nodes[0].combineblocksigs(block_hex, [sig0])
        assert(not combined0["complete"])
        combined1 = self.nodes[0].combineblocksigs(combined0["hex"], [sig1])
        assert(combined1["complete"])

        # Still haven't moved forward
        assert_equal(self.nodes[0].getblockcount(), 0)
        assert_equal(self.nodes[1].getblockcount(), 0)

        self.nodes[0].submitblock(combined1["hex"])
        # Move his chain along for later
        self.nodes[2].submitblock(combined1["hex"])

        assert_equal(self.nodes[0].getblockcount(), 1)
        assert_equal(self.nodes[1].getblockcount(), 0)
        assert_equal(self.nodes[2].getblockcount(), 1)

        block_too_far = self.nodes[0].getnewblockhex()

        assert_raises_jsonrpc,(JSONRPCException, -25, "proposal was not based on our best chain", self.nodes[1].testproposedblock, block_too_far)

        # Finally, submit block
        self.nodes[1].submitblock(combined1["hex"])
        assert_equal(self.nodes[1].getblockcount(), 1)

        # Now proposal is fine, aside from sigs
        assert_equal(self.nodes[1].testproposedblock(block_too_far), None)
        sig0 = self.nodes[0].signblock(block_too_far)
        sig1 = self.nodes[1].signblock(block_too_far)
        sig2 = self.nodes[2].signblock(block_too_far)

        combined0 = self.nodes[0].combineblocksigs(block_too_far, [sig0])
        assert(not combined0["complete"])
        # combining signature from third node this time
        combined1 = self.nodes[0].combineblocksigs(combined0["hex"], [sig2])
        assert(combined1["complete"])

        # TODO stuff with too many signatures or junk data manually

if __name__ == '__main__':
    SignedBlockchainTest().main()
