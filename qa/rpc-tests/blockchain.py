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
    assert_raises,
    assert_is_hex_string,
    assert_is_hash_string,
    start_nodes,
    connect_nodes_bi,
    assert_raises_message,
)


class BlockchainTest(BitcoinTestFramework):
    """
    Test blockchain-related RPC calls:

        - gettxoutsetinfo
        - verifychain

    """

    def __init__(self):
        super().__init__()
        self.setup_clean_chain = False
        self.num_nodes = 2

    def setup_network(self, split=False):
        self.nodes = start_nodes(self.num_nodes, self.options.tmpdir)
        connect_nodes_bi(self.nodes, 0, 1)
        self.is_network_split = False
        self.sync_all()

    def run_test(self):
        self._test_gettxoutsetinfo()
        self._test_getblockheader()
        self._test_getblockheader(getblock=True)
        self._test_getblockchaininfo()
        self._test_getdifficulty()
        self.nodes[0].verifychain(4, 0)

    def _test_getdifficulty(self):
        assert_raises_message(JSONRPCException,
                              "getdifficulty is DEPRECATED for elements (which lacks pow), always returns this error",
                              self.nodes[0].getdifficulty)

    def _test_gettxoutsetinfo(self):
        node = self.nodes[0]
        res = node.gettxoutsetinfo()

        assert 'total_amount' not in res
        assert_equal(res['transactions'], 1)
        assert_equal(res['height'], 200)
        assert_equal(res['txouts'], 1)
        assert_equal(res['bytes_serialized'], 75),
        assert_equal(len(res['bestblock']), 64)
        assert_equal(len(res['hash_serialized']), 64)

    def _test_getblockheader(self, getblock=False):
        node = self.nodes[0]

        assert_raises(
            JSONRPCException, lambda: node.getblockheader('nonsense'))

        besthash = node.getbestblockhash()
        secondbesthash = node.getblockhash(199)
        if getblock:
            header = node.getblock(besthash)
        else:
            header = node.getblockheader(besthash)

        assert_equal(header['hash'], besthash)
        assert_equal(header['height'], 200)
        assert_equal(header['confirmations'], 1)
        assert_equal(header['previousblockhash'], secondbesthash)
        assert_is_hash_string(header['hash'])
        assert_is_hash_string(header['previousblockhash'])
        assert_is_hash_string(header['merkleroot'])
        assert isinstance(header['time'], int)
        assert isinstance(header['mediantime'], int)
        assert isinstance(header['version'], int)
        assert isinstance(int(header['versionHex'], 16), int)
        assert 'nonce' not in header
        assert 'bits' not in header
        assert 'difficulty' not in header
        assert 'chainwork' not in header
        assert 'signblock_witness_asm' in header
        assert 'signblock_witness_hex' in header

    def _test_getblockchaininfo(self):
        besthash = self.nodes[0].getbestblockhash()
        res = self.nodes[0].getblockchaininfo()

        assert_equal(res['chain'], 'elementsregtest')
        assert_equal(res['signblock_asm'], '1')
        assert_equal(res['signblock_hex'], '51')
        assert 'difficulty' not in res
        assert 'chainwork' not in res
        assert_equal(res['blocks'], 200)
        assert_equal(res['headers'], 200)
        assert_equal(res['bestblockhash'], besthash)
        assert isinstance(res['mediantime'], int)
        assert_equal(res['verificationprogress'], 1)
        assert_equal(res['pruned'], False)
        assert 'pruneheight' not in res
        assert 'softforks' not in res
        assert 'bip9_softforks' in res

if __name__ == '__main__':
    BlockchainTest().main()
