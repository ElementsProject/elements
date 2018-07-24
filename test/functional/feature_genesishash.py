#!/usr/bin/env python3
# Copyright (c) 2018-2018 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test genesis block hash
"""

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
)

GENESIS_ARGS_MAP = [

    {
        'memo': 'regtest2_style',
        'genesis': '82ba4b06cffb29f7c5426aa519ecb8e9a2b28b1df11a65c155b5054cca67583d',
        'args': [
                '-con_genesis_style=regtest2_style',
        ],
    },

    {
        'memo': 'default_style',
        'genesis': 'c03f16ae9e2980de2b61fd6dc84af8ac4a37bea928af632166a6b36c5c871ddd',
        'args': [
                '-con_genesis_style=default_style',
        ],
    },

    {
        'memo': 'default_style with blockscript',
        'genesis': 'ac6b1de55f8cb2cffc12c0cab0036d0966a6142fd5f70d0d0ecd96b56f4cb1b6',
        'args': [
                '-con_genesis_style=default_style',
                '-signet_blockscript=512103e464a9f3070da4d3e0b34ce971ff36f3e07c47a8f4beadf32e8ea7e2afa8a82451ae',
        ],
    },

    {
        'memo': 'signet_old',
        'genesis': '7cbf2772cb0e53345b021f34d17b30de42a8952c982b0812e4caca7529009ca5',
        # TODO FIXME Should be
        # 'genesis': '22861f488a5c6cb033a843e476581a8abf5b82a34926babfde1241ed97ba268e',
        'args': [
                '-con_genesis_style=signet_old',
                '-signet_blockscript=512103e464a9f3070da4d3e0b34ce971ff36f3e07c47a8f4beadf32e8ea7e2afa8a82451ae',
        ],
    },
]

class GenesisHashTest(BitcoinTestFramework):

    def set_test_params(self):
        self.chain = 'signet'
        self.setup_clean_chain = True
        self.num_nodes = len(GENESIS_ARGS_MAP)
        self.extra_args = [item['args'] for item in GENESIS_ARGS_MAP]

    def setup_network(self):
        # Don't connect the nodes as they use incompatible chains
        self.add_nodes(self.num_nodes, self.extra_args)
        self.start_nodes()

    def run_test(self):
        for i in range(len(GENESIS_ARGS_MAP)):
            self.log.info('Check genesis style %s...' % GENESIS_ARGS_MAP[i]['memo'])
            assert_equal(self.nodes[i].getblockhash(0), GENESIS_ARGS_MAP[i]['genesis'])

if __name__ == '__main__':
    GenesisHashTest().main()
