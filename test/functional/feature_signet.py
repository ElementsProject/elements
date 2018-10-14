#!/usr/bin/env python3
# Copyright (c) 2018-2018 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test signet

Test chains that use signed blocks instead of pow (signets).
"""

from binascii import hexlify
import os

from test_framework import key, script
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    connect_nodes_bi,
    hex_str_to_bytes,
)

class SignetTest(BitcoinTestFramework):

    def add_options(self, parser):
        parser.add_argument('--config_path', dest='config_path', default='',
                            help='Path to write down the generated config for signet into files.')

    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 3
        self.extra_args = [[
            '-fallbackfee=0.00001',
            '-addresstype=legacy',
            '-deprecatedrpc=validateaddress',
            '-bech32_hrp=sb',
            '-pchmessagestart=F0C7706A',
            '-pubkeyprefix=125',
            '-scriptprefix=87',
            '-secretprefix=217',
            '-extpubkeyprefix=043587CF',
            '-extprvkeyprefix=04358394',
        ]] * 3

    def setup_network(self):

        self.add_nodes(self.num_nodes, self.extra_args)

        self.start_node(2)
        addr = self.nodes[2].getnewaddress()
        k = key.CECKey()
        pub = self.nodes[2].validateaddress(addr)['pubkey']
        k.set_pubkey(hex_str_to_bytes(pub))
        pubkey = key.CPubKey(k.get_pubkey())
        wif = self.nodes[2].dumpprivkey(addr)
        bscript = script.CScript([pubkey, script.OP_CHECKSIG])
        blockscript = hexlify(bscript).decode('ascii')

        if self.options.config_path == '':
            self.log.info('Generated wif %s' % wif)
            self.log.info('Generated blockscript %s' % blockscript)
        else:
            with open(os.path.join(self.options.config_path, 'wif.txt'), 'w', encoding='utf8') as f:
                f.write(wif + '\n')
            with open(os.path.join(self.options.config_path, 'signet_blockscript.txt'), 'w', encoding='utf8') as f:
                f.write(blockscript + '\n')

        for i in range(2):
            self.extra_args[i].append('-signet_blockscript=%s' % blockscript)
            self.start_node(i)
            self.nodes[i].importprivkey(wif)
        for i in range(2):
            connect_nodes_bi(self.nodes, i, i + 1)
        self.sync_all([self.nodes[0:1]])

    def run_test(self):

        self.nodes[0].generate(100)
        self.sync_all([self.nodes[0:1]])
        self.nodes[1].generate(100)
        self.sync_all([self.nodes[0:1]])

        assert_equal(self.nodes[0].getblockcount(), self.nodes[1].getblockcount())

if __name__ == '__main__':
    SignetTest().main()
