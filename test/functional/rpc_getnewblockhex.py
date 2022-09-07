#!/usr/bin/env python3
"""Test getnewblockhex
"""
from io import BytesIO

from test_framework.messages import CBlock
from test_framework.p2p import (
    P2PDataStore,
)
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    hex_str_to_bytes,
)

class GetNewBlockHexTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = False
        self.num_nodes = 1

    def run_test(self):
        self.log.info("Starting test...")
        self.bootstrap_p2p()

        node = self.nodes[0]

        height = node.getblockcount()
        assert_equal(height, 200)

        self.log.info("Call getnewblockhex with no args")
        hex = node.getnewblockhex()
        (height, hash) = self.mine_block(hex)
        assert_equal(height, 201)

        self.log.info("Call getnewblockhex with single string commitment")
        hex = node.getnewblockhex(0, None, "1234")
        assert "6a021234" in hex
        (height, hash) = self.mine_block(hex)
        assert_equal(height, 202)
        block = node.getblock(hash, 2)
        vout = block["tx"][0]["vout"]
        assert_equal(vout[0]["scriptPubKey"]["hex"], "6a021234")

        self.log.info("Call getnewblockhex with single string commitment with spaces")
        # ParseHex only validates hex chars, so spaces skipped
        hex = node.getnewblockhex(0, None, "1234 5678")
        assert "6a0412345678" in hex
        (height, hash) = self.mine_block(hex)
        assert_equal(height, 203)
        block = node.getblock(hash, 2)
        vout = block["tx"][0]["vout"]
        assert_equal(vout[0]["scriptPubKey"]["hex"], "6a0412345678")

        self.log.info("Call getnewblockhex with single commitment")
        hex = node.getnewblockhex(0, None, ["1234"])
        assert "6a021234" in hex
        (height, hash) = self.mine_block(hex)
        assert_equal(height, 204)
        block = node.getblock(hash, 2)
        vout = block["tx"][0]["vout"]
        assert_equal(vout[0]["scriptPubKey"]["hex"], "6a021234")

        self.log.info("Call getnewblockhex with multiple commitments")
        hex = node.getnewblockhex(0, None, ["1234", "deadbeef"])
        assert "6a021234" in hex
        assert "6a04deadbeef" in hex
        (height, hash) = self.mine_block(hex)
        assert_equal(height, 205)
        block = node.getblock(hash, 2)
        vout = block["tx"][0]["vout"]
        assert_equal(vout[0]["scriptPubKey"]["hex"], "6a021234")
        assert_equal(vout[1]["scriptPubKey"]["hex"], "6a04deadbeef")

        hex = node.getnewblockhex(0, None, ["1234", "dead", "cafe", "babe"])
        assert "6a021234" in hex
        assert "6a02dead" in hex
        assert "6a02cafe" in hex
        assert "6a02babe" in hex
        (height, hash) = self.mine_block(hex)
        assert_equal(height, 206)
        block = node.getblock(hash, 2)
        vout = block["tx"][0]["vout"]
        assert_equal(vout[0]["scriptPubKey"]["hex"], "6a021234")
        assert_equal(vout[1]["scriptPubKey"]["hex"], "6a02dead")
        assert_equal(vout[2]["scriptPubKey"]["hex"], "6a02cafe")
        assert_equal(vout[3]["scriptPubKey"]["hex"], "6a02babe")

        self.log.info("Done.")

    def mine_block(self, hex):
        """Mine and submit a block from a given hex template.

        Returns a tuple of the new chain height and the block hash."""

        bytes = hex_str_to_bytes(hex)
        block = CBlock()
        block.deserialize(BytesIO(bytes))
        block.solve()
        self.send_blocks([block], success=True)
        height = self.nodes[0].getblockcount()
        return (height, block.hash)

    def bootstrap_p2p(self, timeout=10):
        """Add a P2P connection to the node.

        Helper to connect and wait for version handshake."""
        self.helper_peer = self.nodes[0].add_p2p_connection(P2PDataStore())
        # We need to wait for the initial getheaders from the peer before we
        # start populating our blockstore. If we don't, then we may run ahead
        # to the next subtest before we receive the getheaders. We'd then send
        # an INV for the next block and receive two getheaders - one for the
        # IBD and one for the INV. We'd respond to both and could get
        # unexpectedly disconnected if the DoS score for that error is 50.
        self.helper_peer.wait_for_getheaders(timeout=timeout)

    def reconnect_p2p(self, timeout=60):
        """Tear down and bootstrap the P2P connection to the node.

        The node gets disconnected several times in this test. This helper
        method reconnects the p2p and restarts the network thread."""
        self.nodes[0].disconnect_p2ps()
        self.bootstrap_p2p(timeout=timeout)

    def send_blocks(self, blocks, success=True, reject_reason=None, force_send=False, reconnect=False, timeout=960):
        """Sends blocks to test node. Syncs and verifies that tip has advanced to most recent block.

        Call with success = False if the tip shouldn't advance to the most recent block."""
        self.helper_peer.send_blocks_and_test(blocks, self.nodes[0], success=success, reject_reason=reject_reason, force_send=force_send, timeout=timeout, expect_disconnect=reconnect)

        if reconnect:
            self.reconnect_p2p(timeout=timeout)


if __name__ == '__main__':
    GetNewBlockHexTest().main()
