#!/usr/bin/env python3
# Copyright (c) 2016 The Bitcoin Core developers
# Distributed under the MIT/X11 software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from decimal import Decimal
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
)

class CTTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 3
        self.setup_clean_chain = True
        args = [
            "-anyonecanspendaremine=1",
            "-con_blocksubsidy=0",
            "-con_connect_genesis_outputs=1",
            "-initialfreecoins=2100000000000000",
            "-txindex=1",
            "-blindedaddresses=1",
            "-minrelaytxfee=0.00000100",
            "-blockmintxfee=0.00000100",
            "-fallbackfee=0.00000100",
        ]
        self.extra_args = [
            # node 0 does not accept nor create discounted CTs
            args + ["-acceptdiscountct=0", "-creatediscountct=0"],
            # node 1 accepts but does not create discounted CTs
            args + ["-acceptdiscountct=1", "-creatediscountct=0"],
            # node 2 both accepts and creates discounted CTs
            # check that 'create' overrides 'accept'
            args + ["-acceptdiscountct=0", "-creatediscountct=1"],
        ]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()
        self.skip_if_no_bdb()

    def run_test(self):
        feerate = 1.0

        node0 = self.nodes[0]
        node1 = self.nodes[1]
        node2 = self.nodes[2]

        self.generate(node0, 101)
        balance = node0.getbalance()
        assert_equal(balance['bitcoin'], 21000000)

        self.log.info("Create UTXOs")
        many = {}
        num = 25
        for i in range(num):
            addr = node0.getnewaddress()
            info = node0.getaddressinfo(addr)
            many[info['unconfidential']] = 1
        for i in range(10):
            addr = node1.getnewaddress()
            info = node1.getaddressinfo(addr)
            many[info['unconfidential']] = 1
        for i in range(10):
            addr = node2.getnewaddress()
            info = node2.getaddressinfo(addr)
            many[info['unconfidential']] = 1

        txid = node0.sendmany("", many)
        self.generate(node0, 1)

        self.log.info("Send explicit tx to node 0")
        addr = node0.getnewaddress()
        info = node0.getaddressinfo(addr)
        txid = node0.sendtoaddress(info['unconfidential'], 1.0, "", "", False, None, None, None, None, None, None, feerate)
        tx = node0.gettransaction(txid, True, True)
        decoded = tx['decoded']
        vin = decoded['vin']
        vout = decoded['vout']
        assert_equal(len(vin), 2)
        assert_equal(len(vout), 3)
        assert_equal(tx['fee']['bitcoin'], Decimal('-0.00000326'))
        assert_equal(decoded['vsize'], 326)
        assert_equal(decoded['weight'], 1302)
        self.generate(node0, 1)
        tx = node1.getrawtransaction(txid, True)
        assert_equal(tx['discountweight'], 1302)
        assert_equal(tx['discountvsize'], 326)

        self.log.info("Send confidential tx to node 0")
        addr = node0.getnewaddress()
        info = node0.getaddressinfo(addr)
        txid = node0.sendtoaddress(info['confidential'], 1.0, "", "", False, None, None, None, None, None, None, feerate)
        tx = node0.gettransaction(txid, True, True)
        decoded = tx['decoded']
        vin = decoded['vin']
        vout = decoded['vout']
        assert_equal(len(vin), 2)
        assert_equal(len(vout), 3)
        assert_equal(tx['fee']['bitcoin'], Decimal('-0.00002575'))
        assert_equal(decoded['vsize'], 2575)
        assert_equal(decoded['weight'], 10300)
        self.generate(node0, 1)
        tx = node1.getrawtransaction(txid, True)
        assert_equal(tx['discountweight'], 1302)
        assert_equal(tx['discountvsize'], 326) # node1 has discountvsize

        self.log.info("Send explicit tx to node 1")
        addr = node1.getnewaddress()
        info = node1.getaddressinfo(addr)
        txid = node0.sendtoaddress(info['unconfidential'], 1.0, "", "", False, None, None, None, None, None, None, feerate)
        tx = node0.gettransaction(txid, True, True)
        decoded = tx['decoded']
        vin = decoded['vin']
        vout = decoded['vout']
        assert_equal(len(vin), 2)
        assert_equal(len(vout), 3)
        assert_equal(tx['fee']['bitcoin'], Decimal('-0.00000326'))
        assert_equal(decoded['vsize'], 326)
        assert_equal(decoded['weight'], 1302)
        self.generate(node0, 1)
        tx = node1.getrawtransaction(txid, True)
        assert_equal(tx['discountweight'], 1302)
        assert_equal(tx['discountvsize'], 326)

        self.log.info("Send confidential (undiscounted) tx to node 1")
        addr = node1.getnewaddress()
        info = node1.getaddressinfo(addr)
        txid = node0.sendtoaddress(info['confidential'], 1.0, "", "", False, None, None, None, None, None, None, feerate)
        tx = node0.gettransaction(txid, True, True)
        decoded = tx['decoded']
        vin = decoded['vin']
        vout = decoded['vout']
        assert_equal(len(vin), 2)
        assert_equal(len(vout), 3)
        assert_equal(tx['fee']['bitcoin'], Decimal('-0.00002575'))
        assert_equal(decoded['vsize'], 2575)
        assert_equal(decoded['weight'], 10300)
        self.generate(node0, 1)
        tx = node1.getrawtransaction(txid, True)
        assert_equal(tx['discountweight'], 1302)
        assert_equal(tx['discountvsize'], 326) # node1 has discountvsize

        self.log.info("Send confidential (discounted) tx to node 1")
        bitcoin = 'b2e15d0d7a0c94e4e2ce0fe6e8691b9e451377f6e46e8045a86f7c4b5d4f0f23'
        addr = node1.getnewaddress()
        info = node1.getaddressinfo(addr)
        txid = node2.sendtoaddress(info['confidential'], 1.0, "", "", False, None, None, None, None, None, None, feerate)
        # node0 won't accept or relay the tx
        self.sync_mempools([node1, node2])
        assert_equal(node0.getrawmempool(), [])
        self.generate(node2, 1, sync_fun=self.sync_blocks)
        for node in [node2, node1]:
            tx = node.gettransaction(txid, True, True)
            decoded = tx['decoded']
            vin = decoded['vin']
            vout = decoded['vout']
            assert_equal(len(vin), 2)
            assert_equal(len(vout), 3)
            if 'bitcoin' in decoded['fee']:
                assert_equal(decoded['fee']['bitcoin'], Decimal('-0.00000326'))
            else:
                assert_equal(decoded['fee'][bitcoin], Decimal('0.00000326'))
            assert_equal(decoded['vsize'], 2575)
            assert_equal(decoded['weight'], 10300)
            assert_equal(decoded['discountweight'], 1302)
            assert_equal(decoded['discountvsize'], 326)

        # node0 only has vsize
        tx = node0.getrawtransaction(txid, True)
        assert_equal(tx['vsize'], 2575)

        # check liquidv1 min feerate
        feerate = 0.1
        self.log.info(f"Send confidential (discounted) tx to node 1 at {feerate} sats/vb")
        addr = node1.getnewaddress()
        info = node1.getaddressinfo(addr)
        txid = node2.sendtoaddress(info['confidential'], 1.0, "", "", False, None, None, None, None, None, None, feerate)
        self.sync_mempools([node1, node2])
        assert_equal(node0.getrawmempool(), [])
        self.generate(node2, 1, sync_fun=self.sync_blocks)
        for node in [node2, node1]:
            tx = node.gettransaction(txid, True, True)
            assert_equal(tx["confirmations"], 1)
            decoded = tx['decoded']
            vin = decoded['vin']
            vout = decoded['vout']
            assert_equal(len(vin), 2)
            assert_equal(len(vout), 3)
            if 'bitcoin' in decoded['fee']:
                assert_equal(decoded['fee']['bitcoin'], Decimal('-0.00000033'))
            else:
                assert_equal(decoded['fee'][bitcoin], Decimal('0.00000033'))
            assert_equal(decoded['vsize'], 2575)
            assert_equal(decoded['weight'], 10300)
            assert_equal(decoded['discountweight'], 1302)
            assert_equal(decoded['discountvsize'], 326)
        # node0 only has vsize
        tx = node0.getrawtransaction(txid, True)
        assert_equal(tx['vsize'], 2575)

        # check transaction package
        self.log.info("Create discounted package")
        addr = node1.getnewaddress()
        addr2 = node1.getnewaddress()
        utxo = node1.listunspent()[0]
        fee = Decimal('0.00000035')
        inputs = [{"txid": utxo["txid"], "vout": utxo["vout"]}]
        change = Decimal('0.00001000')
        amount = utxo["amount"] - change - fee
        outputs = [
            {addr: amount},
            {addr2: change},
            {"fee": fee}
        ]
        raw = node1.createrawtransaction(inputs, outputs)
        blind = node1.blindrawtransaction(raw, False)
        signed = node1.signrawtransactionwithwallet(blind)
        assert_equal(signed["complete"], True)
        test = node1.testmempoolaccept([signed['hex']])
        assert_equal(test[0]["allowed"], True)
        txid = node1.sendrawtransaction(signed['hex'])
        tx = node1.gettransaction(txid, True, True)
        assert_equal(tx['decoded']['discountvsize'], 257)

        for i in range(24):
            self.log.info(f"Add package descendant {i+1}")
            addr = node1.getnewaddress()
            addr2 = node1.getnewaddress()
            fee = Decimal('0.00000035')
            change = Decimal('0.00001000')
            inputs = [{"txid": txid, "vout": 0}]
            amount -= change + fee
            outputs = [
                {addr: amount},
                {addr2: change},
                {"fee": fee}
            ]
            raw = node1.createrawtransaction(inputs, outputs)
            blind = node1.blindrawtransaction(raw, False)
            signed = node1.signrawtransactionwithwallet(blind)
            assert_equal(signed["complete"], True)
            hex = signed["hex"]
            test = node1.testmempoolaccept([hex])
            assert_equal(test[0]["allowed"], True)
            txid = node1.sendrawtransaction(hex)
            tx = node1.gettransaction(txid, True, True)
            assert_equal(tx['decoded']['discountvsize'], 257)
            assert_equal(len(node1.getrawmempool()), i + 2)

        assert_equal(len(node1.getrawmempool()), 25)
        self.log.info("Mine the package")
        self.generate(node1, 1, sync_fun=self.sync_blocks)
        assert_equal(len(node1.getrawmempool()), 0)
        tx = node1.gettransaction(txid, True, True)
        assert_equal(tx["confirmations"], 1)
        self.log.info("Success")

if __name__ == '__main__':
    CTTest().main()
