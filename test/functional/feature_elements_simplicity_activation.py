#!/usr/bin/env python3
# Copyright (c) 2015-2020 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test Simplicity soft fork activation for Elements

This is essentially the same as the Taproot activation test.

Like that one, it doesn't try to test the actual activation (which is
tested by feature_taproot.py) but instead makes sure that the parameters
do what we expect.
"""

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal

class SimplicityActivationTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 1
        self.extra_args = [["-evbparams=dynafed:0:::"]]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def test_activation(self, rpc, activation_height):
        self.log.info("Testing activation at height %d" % activation_height)
        activation_height = 128 * ((activation_height + 127) // 128)

        assert_equal(rpc.getblockcount(), 0)

        blocks = self.generatetoaddress(rpc, activation_height - 2, rpc.getnewaddress())
        assert_equal(rpc.getblockcount(), activation_height - 2)

        for n, block in enumerate(blocks):
            decode = rpc.getblockheader(block)
            if n < 143:
                assert_equal (decode["versionHex"], "20000000")
            elif n < 431:
                # TESTDUMMY and DYNAFED deployment: 144 blocks active, 144 blocks locked in
                assert_equal (decode["versionHex"], "32000000")
            else:
                assert_equal (decode["versionHex"], "20000000")

        assert_equal(rpc.getdeploymentinfo()["deployments"]["simplicity"]["bip9"]["status"], "defined")
        # The 1023rd block does not signal, but changes status_next to "started" from "defined"
        # bitcoin PR #23508 changed bip9 status to the current block instead of the next block
        blocks = self.generatetoaddress(rpc, 1, rpc.getnewaddress())
        assert_equal(rpc.getdeploymentinfo()["deployments"]["simplicity"]["bip9"]["status"], "defined")
        assert_equal(rpc.getdeploymentinfo()["deployments"]["simplicity"]["bip9"]["status_next"], "started")
        assert_equal(rpc.getblockheader(blocks[0])["versionHex"], "20000000")

        blocks = self.generatetoaddress(rpc, 127, rpc.getnewaddress())
        for n, block in enumerate(blocks):
            decode = rpc.getblockheader(block)
            assert_equal (decode["versionHex"], "21000000")
        assert_equal(rpc.getdeploymentinfo()["deployments"]["simplicity"]["bip9"]["status"], "started")

        # Fail to signal on the 128th block. Since the threshold for Simplicity is
        # 100% this will prevent activation. Note that our period is 128, not
        # 144 (the default), as we have overridden the period for Simplicity. On
        # the main Liquid chain it is overridden to be one week of signalling.
        block = rpc.getnewblockhex()
        block = block[:7] + "0" + block[8:] # turn off Simplicity signal
        rpc.submitblock(block)
        assert_equal(rpc.getdeploymentinfo()["deployments"]["simplicity"]["bip9"]["status"], "started")

        # Run through another 128 blocks, without failing to signal
        blocks = self.generatetoaddress(rpc, 127, rpc.getnewaddress())
        for n, block in enumerate(blocks):
            decode = rpc.getblockheader(block)
            assert_equal (decode["versionHex"], "21000000")
        assert_equal(rpc.getdeploymentinfo()["deployments"]["simplicity"]["bip9"]["status"], "started")
        # The 128th block then switches from "started" to "locked_in"
        blocks = self.generatetoaddress(rpc, 1, rpc.getnewaddress())
        assert_equal(rpc.getdeploymentinfo()["deployments"]["simplicity"]["bip9"]["status"], "started")
        assert_equal(rpc.getdeploymentinfo()["deployments"]["simplicity"]["bip9"]["status_next"], "locked_in")
        assert_equal(rpc.getblockheader(blocks[0])["versionHex"], "21000000")

        # Run through another 128 blocks, which will go from "locked in" to "active" regardless of signalling
        blocks = self.generatetoaddress(rpc, 127, rpc.getnewaddress())
        for n, block in enumerate(blocks):
            decode = rpc.getblockheader(block)
            assert_equal (decode["versionHex"], "21000000")
        assert_equal(rpc.getdeploymentinfo()["deployments"]["simplicity"]["bip9"]["status"], "locked_in")
        block = rpc.getnewblockhex()
        block = block[:7] + "0" + block[8:] # turn off Simplicity signal
        rpc.submitblock(block)
        assert_equal(rpc.getdeploymentinfo()["deployments"]["simplicity"]["bip9"]["status"], "locked_in")
        assert_equal(rpc.getdeploymentinfo()["deployments"]["simplicity"]["bip9"]["status_next"], "active")

        # After the state is "active", signallng stops by default.
        blocks = self.generatetoaddress(rpc, 1, self.nodes[0].getnewaddress())
        assert_equal(rpc.getdeploymentinfo()["deployments"]["simplicity"]["bip9"]["status"], "active")
        assert_equal(rpc.getblockheader(blocks[0])["versionHex"], "20000000")

    def run_test(self):
        # Test that regtest nodes never signal Simplicity or Simplicity by default
        self.log.info("Testing node not configured to activate Simplicity")
        blocks = self.generatetoaddress(self.nodes[0], 2500, self.nodes[0].getnewaddress())
        assert_equal(self.nodes[0].getblockcount(), 2500)
        for n, block in enumerate(blocks):
            decode = self.nodes[0].getblockheader(block)
            if n < 143:
                assert_equal (decode["versionHex"], "20000000")
            elif n < 431:
                # TESTDUMMY and DYNAFED deployment: 144 blocks active, 144 blocks locked in
                assert_equal (decode["versionHex"], "32000000")
            else:
                assert_equal (decode["versionHex"], "20000000")

        # Test activation starting from height 1000
        # Note that for Simplicity this is an illogical combination (Simplicity without
        # Taproot) but for purposes of this test it's fine.
        self.restart_node(0, ["-evbparams=dynafed:0:::", "-evbparams=simplicity:500:::"])
        self.nodes[0].invalidateblock(self.nodes[0].getblockhash(1))
        self.test_activation(self.nodes[0], 500)

if __name__ == '__main__':
    SimplicityActivationTest().main()
