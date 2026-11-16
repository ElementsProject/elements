#!/usr/bin/env python3
# Copyright (c) 2026 The Elements Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test bumpfee and psbtbumpfee on a wallet transaction that spends a blinded (confidential) coin.

The fee bumper summed the input amounts with GetAmount(), which asserts that the amount is explicit,
so bumping such a transaction aborted the node. It must fail with an RPC error instead, as it already
does for a transaction with blinded outputs.
"""

from decimal import Decimal

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_raises_rpc_error

UNBLINDED_ONLY = "bumpfee can only be called on an unblinded transaction"


class BumpFeeBlindedInputTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 1
        self.extra_args = [["-blindedaddresses=1"]]

    def add_options(self, parser):
        self.add_wallet_options(parser)

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):
        node = self.nodes[0]

        self.log.info("Create a blinded coin")
        node.sendtoaddress(node.getnewaddress(), 5)
        self.generate(node, 1)
        coin = next(u for u in node.listunspent() if "amountcommitment" in u)

        self.log.info("Spend it in a replaceable transaction")
        fee = Decimal("0.0001")
        raw = node.createrawtransaction([{"txid": coin["txid"], "vout": coin["vout"]}],
                                        [{node.getnewaddress(): coin["amount"] - fee}, {"fee": fee}],
                                        0, True)
        signed = node.signrawtransactionwithwallet(node.blindrawtransaction(raw))
        assert signed["complete"]
        txid = node.sendrawtransaction(signed["hex"])

        self.log.info("bumpfee and psbtbumpfee fail with an RPC error and the node keeps running")
        assert_raises_rpc_error(-4, UNBLINDED_ONLY, node.bumpfee, txid)
        assert_raises_rpc_error(-4, UNBLINDED_ONLY, node.psbtbumpfee, txid)
        explicit_output = {node.getaddressinfo(node.getnewaddress())["unconfidential"]: coin["amount"] - 2 * fee}
        assert_raises_rpc_error(-4, UNBLINDED_ONLY, node.bumpfee, txid, {"outputs": [explicit_output]})
        assert txid in node.getrawmempool()


if __name__ == '__main__':
    BumpFeeBlindedInputTest(__file__).main()
