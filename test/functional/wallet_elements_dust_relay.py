#!/usr/bin/env python3
# Copyright (c) 2017-2020 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from decimal import Decimal
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    assert_raises_rpc_error,
)

class WalletTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = False
        self.num_nodes = 2
        args = [
            "-blindedaddresses=1",
            "-minrelaytxfee=0.00000100",
        ]
        self.extra_args = [
            args,
            args + ["-dustrelayfee=0.00003000"], # second node uses default upstream dustrelayfee
        ]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def select_unblinded_utxo(self, node):
        for utxo in node.listunspent():
            if utxo["amountblinder"] == "00" * 32:
                return utxo
            else:
                continue
        raise Exception("no unblinded utxo")

    def run_test(self):
        assert_equal(self.nodes[0].getbalance(), {'bitcoin': 1250})
        assert_equal(self.nodes[1].getbalance(), {'bitcoin': 1250})

        addr = self.nodes[0].getnewaddress()

        # test dust threshold for upstream dustrelayfee=3sat/vb
        # 495 sats should succeed for blinded output value
        amt = "0.00000495"
        self.nodes[1].sendtoaddress(address=addr, amount=amt)
        self.generate(self.nodes[1], 1, sync_fun=self.no_op)

        # 494 sats should fail for blinded output value
        amt = "0.00000494"
        assert_raises_rpc_error(-6, "Transaction amount too small", self.nodes[1].sendtoaddress, address=addr, amount=amt)

        addr = self.nodes[1].getnewaddress()

        # test dust threshold for elements default dustrelayfee=0.1sat/vb
        # 17 sats should succeed for blinded output value
        amt = "0.00000017"
        self.nodes[0].sendtoaddress(address=addr, amount=amt)
        self.generate(self.nodes[0], 1, sync_fun=self.no_op)

        # 16 sats should fail for blinded output value
        amt = "0.00000016"
        assert_raises_rpc_error(-6, "Transaction amount too small", self.nodes[0].sendtoaddress, address=addr, amount=amt)

        # a blinded transaction created manually can have an output value as low as 1 sat
        addr = self.nodes[1].getnewaddress()
        changeaddr = self.nodes[0].getnewaddress()
        utxo = self.nodes[0].listunspent()[0]
        amt = Decimal("0.00000001")
        fee = Decimal("0.00000258")
        change = utxo["amount"] - amt - fee
        inputs = [{"txid": utxo["txid"], "vout": utxo["vout"]}]
        outputs = [{addr: amt}, {changeaddr: change}, {"fee": fee}]
        raw = self.nodes[0].createrawtransaction(inputs, outputs)
        blinded = self.nodes[0].blindrawtransaction(raw)
        signed = self.nodes[0].signrawtransactionwithwallet(blinded)
        assert signed["complete"]
        tx = signed["hex"]
        assert self.nodes[1].testmempoolaccept([tx])[0]["allowed"]
        assert self.nodes[0].testmempoolaccept([tx])[0]["allowed"]
        assert_equal(self.nodes[1].sendrawtransaction(tx), self.nodes[0].sendrawtransaction(tx))
        self.generate(self.nodes[0], 1, sync_fun=self.no_op)

        # explicit transactions have slightly smaller outputs
        # node 0 will accept an output value of 14 sats but node 1 will not
        addr = self.nodes[1].getnewaddress(address_type="bech32")
        changeaddr = self.nodes[0].getnewaddress(address_type="bech32")
        utxo = self.select_unblinded_utxo(self.nodes[0])
        amt = Decimal("0.00000014")
        fee = Decimal("0.00000258")
        change = utxo["amount"] - amt - fee
        inputs = [{"txid": utxo["txid"], "vout": utxo["vout"]}]
        outputs = [{addr: amt}, {changeaddr: change}, {"fee": fee}]
        raw = self.nodes[0].createrawtransaction(inputs, outputs)
        signed = self.nodes[0].signrawtransactionwithwallet(raw)
        assert signed["complete"]
        tx = signed["hex"]
        assert self.nodes[0].testmempoolaccept([tx])[0]["allowed"]
        assert not self.nodes[1].testmempoolaccept([tx])[0]["allowed"]
        self.nodes[0].sendrawtransaction(tx)
        assert_raises_rpc_error(-26, "dust", self.nodes[1].sendrawtransaction, tx)
        self.generate(self.nodes[0], 1, sync_fun=self.no_op)

        # neither node will accept an explicit output value of 13 sats
        addr = self.nodes[1].getnewaddress(address_type="bech32")
        changeaddr = self.nodes[0].getnewaddress(address_type="bech32")
        utxo = self.select_unblinded_utxo(self.nodes[0])
        amt = Decimal("0.00000013")
        fee = Decimal("0.00000258")
        change = utxo["amount"] - amt - fee
        inputs = [{"txid": utxo["txid"], "vout": utxo["vout"]}]
        outputs = [{addr: amt}, {changeaddr: change}, {"fee": fee}]
        raw = self.nodes[0].createrawtransaction(inputs, outputs)
        signed = self.nodes[0].signrawtransactionwithwallet(raw)
        assert signed["complete"]
        tx = signed["hex"]
        assert not self.nodes[0].testmempoolaccept([tx])[0]["allowed"]
        assert not self.nodes[1].testmempoolaccept([tx])[0]["allowed"]
        assert_raises_rpc_error(-26, "dust", self.nodes[0].sendrawtransaction, tx)
        assert_raises_rpc_error(-26, "dust", self.nodes[1].sendrawtransaction, tx)

if __name__ == '__main__':
    WalletTest().main()
