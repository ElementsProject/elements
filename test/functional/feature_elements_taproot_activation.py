#!/usr/bin/env python3
# Copyright (c) 2015-2020 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test Taproot soft fork activation for Elements

Unlike Bitcoin, this (a) does not use Speedy Trial, and (b) does use
a pair of new versionbits features which allows Taproot to have its
own signalling period length (128 blocks on regtest) and activation
threshold (100%).

The primary purpose of this test is to confirm that this configuration
works; the actual activation (e.g. how are Taproot-enabled transactions
treated) is covered by other tests and by manual testing.

There is an undocumented option `con_taproot_signal_start` which sets
the block at which signalling starts; otherwise it is set to "always
on" which means that signalling will not occur.
"""

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal

class TaprootActivationTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 1

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def test_activation(self, rpc, activation_height):
        self.log.info("Testing activation at height %d" % activation_height)
        activation_height = 128 * ((activation_height + 127) // 128)

        assert_equal(rpc.getblockcount(), 0)

        blocks = rpc.generatetoaddress(activation_height - 2, rpc.getnewaddress())
        assert_equal(rpc.getblockcount(), activation_height - 2)

        for n, block in enumerate(blocks):
            decode = rpc.getblockheader(block)
            if n < 143:
                assert_equal (decode["versionHex"], "20000000")
            elif n < 431:
                # TESTDUMMY deployment: 144 blocks active, 144 blocks locked in
                assert_equal (decode["versionHex"], "30000000")
            else:
                assert_equal (decode["versionHex"], "20000000")

        assert_equal(rpc.getblockchaininfo()["softforks"]["taproot"]["bip9"]["status"], "defined")
        # The 1023rd block does not signal, but changes the signalling state
        # to "started" from "defined"
        blocks = rpc.generatetoaddress(1, rpc.getnewaddress())
        assert_equal(rpc.getblockchaininfo()["softforks"]["taproot"]["bip9"]["status"], "started")
        assert_equal(rpc.getblockheader(blocks[0])["versionHex"], "20000000")

        blocks = rpc.generatetoaddress(127, rpc.getnewaddress())
        for n, block in enumerate(blocks):
            decode = rpc.getblockheader(block)
            assert_equal (decode["versionHex"], "20000004")
        assert_equal(rpc.getblockchaininfo()["softforks"]["taproot"]["bip9"]["status"], "started")

        # Fail to signal on the 128th block. Since the threshold for Taproot is
        # 100% this will prevent activation. Note that our period is 128, not
        # 144 (the default), as we have overridden the period for Taproot. On
        # the main Liquid chain it is overridden to be one week of signalling.
        block = rpc.getnewblockhex()
        block = block[:1] + "0" + block[2:] # turn off Taproot signal
        rpc.submitblock(block)
        assert_equal(rpc.getblockchaininfo()["softforks"]["taproot"]["bip9"]["status"], "started")

        # Run through another 128 blocks, without failing to signal
        blocks = rpc.generatetoaddress(127, rpc.getnewaddress())
        for n, block in enumerate(blocks):
            decode = rpc.getblockheader(block)
            assert_equal (decode["versionHex"], "20000004")
        assert_equal(rpc.getblockchaininfo()["softforks"]["taproot"]["bip9"]["status"], "started")
        # The 128th block then switches from "started" to "locked_in"
        blocks = rpc.generatetoaddress(1, rpc.getnewaddress())
        assert_equal(rpc.getblockchaininfo()["softforks"]["taproot"]["bip9"]["status"], "locked_in")
        assert_equal(rpc.getblockheader(blocks[0])["versionHex"], "20000004")

        # Run through another 128 blocks, which will go from "locked in" to "active" regardless of signalling
        blocks = rpc.generatetoaddress(127, rpc.getnewaddress())
        for n, block in enumerate(blocks):
            decode = rpc.getblockheader(block)
            assert_equal (decode["versionHex"], "20000004")
        assert_equal(rpc.getblockchaininfo()["softforks"]["taproot"]["bip9"]["status"], "locked_in")
        block = rpc.getnewblockhex()
        block = block[:1] + "0" + block[2:] # turn off Taproot signal
        rpc.submitblock(block)
        assert_equal(rpc.getblockchaininfo()["softforks"]["taproot"]["bip9"]["status"], "active")

        # After the state is "active", signallng stops by default.
        blocks = rpc.generatetoaddress(1, self.nodes[0].getnewaddress())
        assert_equal(rpc.getblockchaininfo()["softforks"]["taproot"]["bip9"]["status"], "active")
        assert_equal(rpc.getblockheader(blocks[0])["versionHex"], "20000000")

    def run_test(self):
        # Test that regtest nodes without -con_taproot_signal_start never signal
        self.log.info("Testing node not configured to activate taproot")
        blocks = self.nodes[0].generatetoaddress(2500, self.nodes[0].getnewaddress())
        assert_equal(self.nodes[0].getblockcount(), 2500)
        for n, block in enumerate(blocks):
            decode = self.nodes[0].getblockheader(block)
            if n < 143:
                assert_equal (decode["versionHex"], "20000000")
            elif n < 431:
                # TESTDUMMY deployment: 144 blocks active, 144 blocks locked in
                assert_equal (decode["versionHex"], "30000000")
            else:
                assert_equal (decode["versionHex"], "20000000")

        # Test activation starting from height 1000
        self.restart_node(0, ["-con_taproot_signal_start=500"])
        self.nodes[0].invalidateblock(self.nodes[0].getblockhash(1))
        self.test_activation(self.nodes[0], 500)

if __name__ == '__main__':
    TaprootActivationTest().main()
