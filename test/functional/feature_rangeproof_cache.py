#!/usr/bin/env python3
# Copyright (c) 2026 The Elements Core developers
# Distributed under the MIT/X11 software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Regression test: the rangeproof verification cache must bind the
scriptPubKey (and asset generator), not just (proof, value commitment).

A blinded output's rangeproof cryptographically binds its scriptPubKey as
the proof's extra commitment. A cache keyed on (proof, commitment) alone
would accept a previously-seen pair under any script on a cache hit, and
would skip the min_value==0 guard for spendable outputs.
"""

from test_framework.test_framework import BitcoinTestFramework
from test_framework.messages import CTransaction, tx_from_hex
from test_framework.util import assert_equal


class RangeproofCacheTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 1
        self.setup_clean_chain = True
        args = ["-blindedaddresses=1", "-initialfreecoins=2100000000000000",
                "-con_blocksubsidy=0", "-con_connect_genesis_outputs=1",
                "-anyonecanspendaremine=1"]
        self.extra_args = [args]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def add_options(self, parser):
        self.add_wallet_options(parser)

    def run_test(self):
        node = self.nodes[0]
        self.generate(node, 1)

        # A valid blinded transaction; the recipient output carries value
        # commitment C, rangeproof P, and scriptPubKey script_a.
        addr = node.getnewaddress()
        script_a = bytes.fromhex(node.validateaddress(addr)["scriptPubKey"])
        tx_hex = node.createrawtransaction([], [{addr: 1}])
        tx_hex = node.fundrawtransaction(tx_hex)["hex"]
        # Coming from initial free coins: no need to sign
        tx_hex = node.blindrawtransaction(tx_hex)

        # Poisoned copy: identical (C, P) and witnesses, but the blinded
        # output's scriptPubKey is replaced. Balance and surjection proofs
        # still hold; only the rangeproof is invalid under the new script.
        tx = tx_from_hex(tx_hex)
        poison = CTransaction(tx)
        idx = next(i for i, o in enumerate(tx.vout) if o.scriptPubKey == script_a)
        poison.vout[idx].scriptPubKey = b"\x51"  # OP_TRUE
        poison_hex = poison.serialize().hex()

        # Validating the honest tx warms the rangeproof cache. The poisoned
        # copy must still be rejected afterwards.
        assert_equal(node.testmempoolaccept([tx_hex])[0]["allowed"], True)
        res = node.testmempoolaccept([poison_hex])[0]
        assert_equal(res["allowed"], False)
        assert_equal(res["reject-reason"], "bad-txns-in-ne-out")

        # Acceptance must not depend on cache contents: also rejected cold.
        self.restart_node(0)
        res = node.testmempoolaccept([poison_hex])[0]
        assert_equal(res["allowed"], False)
        assert_equal(res["reject-reason"], "bad-txns-in-ne-out")


if __name__ == "__main__":
    RangeproofCacheTest(__file__).main()
