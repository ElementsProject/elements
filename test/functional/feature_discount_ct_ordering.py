#!/usr/bin/env python3
# Copyright (c) 2016 The Bitcoin Core developers
# Distributed under the MIT/X11 software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from decimal import Decimal
from io import BytesIO
from test_framework.messages import CBlock
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
)

class CTTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 3
        self.setup_clean_chain = True
        self.args = [
            "-anyonecanspendaremine=1",
            "-con_blocksubsidy=0",
            "-con_connect_genesis_outputs=1",
            "-initialfreecoins=2100000000000000",
            "-txindex=1",
        ]
        self.extra_args = [
            # node 0 does not accept nor create discounted CTs
            self.args + ["-acceptdiscountct=0", "-creatediscountct=0"],
            # node 1 accepts but does not create discounted CTs
            self.args + ["-acceptdiscountct=1", "-creatediscountct=0"],
            # node 2 both accepts and creates discounted CTs
            self.args + ["-acceptdiscountct=1", "-creatediscountct=1"],
        ]

    def add_options(self, parser):
        self.add_wallet_options(parser)

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()
        self.skip_if_no_bdb()

    def run_test(self):

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

        feerate = 1.0
        self.log.info(f"Send explicit tx to node 1 at {feerate} sat/vb")
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
        self.sync_mempools([node0, node1])
        tx = node1.getrawtransaction(txid, True)
        assert_equal(tx['discountvsize'], 326)

        feerate = 2.0
        self.log.info(f"Send explicit tx to node 1 at {feerate} sat/vb")
        addr = node1.getnewaddress()
        info = node1.getaddressinfo(addr)
        txid = node0.sendtoaddress(info['unconfidential'], 1.0, "", "", False, None, None, None, None, None, None, feerate)
        tx = node0.gettransaction(txid, True, True)
        decoded = tx['decoded']
        vin = decoded['vin']
        vout = decoded['vout']
        assert_equal(len(vin), 2)
        assert_equal(len(vout), 3)
        assert_equal(tx['fee']['bitcoin'], Decimal('-0.00000652'))
        assert_equal(decoded['vsize'], 326)
        self.sync_mempools([node0, node1])
        tx = node1.getrawtransaction(txid, True)
        assert_equal(tx['discountvsize'], 326)

        feerate = 1.0
        self.log.info(f"Send confidential (undiscounted) tx to node 1 at {feerate} sat/vb")
        addr = node1.getnewaddress()
        info = node1.getaddressinfo(addr)
        txid = node0.sendtoaddress(info['confidential'], 1.0, "", "", False, None, None, None, None, None, None, feerate)
        self.sync_mempools()
        tx = node0.gettransaction(txid, True, True)
        decoded = tx['decoded']
        vin = decoded['vin']
        vout = decoded['vout']
        assert_equal(len(vin), 2)
        assert_equal(len(vout), 3)
        assert_equal(tx['fee']['bitcoin'], Decimal('-0.00002575'))
        assert_equal(decoded['vsize'], 2575)
        self.sync_mempools([node0, node1])
        tx = node1.getrawtransaction(txid, True)
        assert_equal(tx['discountvsize'], 326)

        feerate = 1.0
        self.log.info(f"Send confidential (discounted) tx to node 1 at {feerate} sat/vb")
        bitcoin = 'b2e15d0d7a0c94e4e2ce0fe6e8691b9e451377f6e46e8045a86f7c4b5d4f0f23'
        addr = node1.getnewaddress()
        info = node1.getaddressinfo(addr)
        txid = node2.sendtoaddress(info['confidential'], 1.0, "", "", False, None, None, None, None, None, None, feerate)
        # node0 won't accept or relay the tx
        self.sync_mempools([node1, node2])
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
            assert_equal(decoded['discountvsize'], 326)

        feerate = 2.0
        self.log.info(f"Send confidential (discounted) tx to node 1 at {feerate} sat/vb")
        addr = node1.getnewaddress()
        info = node1.getaddressinfo(addr)
        txid = node2.sendtoaddress(info['confidential'], 1.0, "", "", False, None, None, None, None, None, None, feerate)
        self.sync_mempools([node1, node2])
        tx = node1.gettransaction(txid, True, True)
        decoded = tx['decoded']
        assert_equal(decoded['fee'][bitcoin], Decimal('0.00000652'))

        # check that txs in the block template are in decreasing feerate according to their discount size
        self.log.info("Check tx ordering in block template")
        h = node1.getnewblockhex()
        b = bytes.fromhex(h)
        block = CBlock()
        block.deserialize(BytesIO(b))
        last_feerate = None
        i = 0
        for tx in block.vtx:
            tx.calc_sha256()
            fees = list(filter(lambda o: o.is_fee(), tx.vout))
            # print(f"fees: {fees}")

            if len(fees) > 0:
                print("---")
                txid = tx.hash
                print(f"txid: {txid}")
                t = node1.gettransaction(txid, True, True)
                discountvsize = t['decoded']['discountvsize']
                vsize = tx.get_vsize()
                fee = fees[0].nValue.getAmount()
                print(f"fee: {fee}")
                print(f"vsize: {vsize}")
                print(f"discountvsize: {discountvsize}")
                print(f"actual feerate at vsize : {fee / vsize}")
                feerate = fee / discountvsize
                print(f"feerate at discountvsize: {feerate}")
                # if last_feerate is not None:
                #     assert feerate <= last_feerate
                last_feerate = feerate
                i = i + 1
        print("---")

        # discounted txs are dropped from the mempool on restart if we no longer accept them
        self.log.info("Restart node1 with acceptdiscount=0")
        self.restart_node(1, extra_args = self.args + ["-acceptdiscountct=0", "-creatediscountct=0"])
        self.connect_nodes(0, 1)
        self.sync_mempools([node0, node1])

        # send a few more txs
        feerate = 1.0
        self.log.info(f"Send explicit tx to node 1 at {feerate} sat/vb")
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

        feerate = 2.0
        self.log.info(f"Send explicit tx to node 1 at {feerate} sat/vb")
        addr = node1.getnewaddress()
        info = node1.getaddressinfo(addr)
        txid = node0.sendtoaddress(info['unconfidential'], 1.0, "", "", False, None, None, None, None, None, None, feerate)
        tx = node0.gettransaction(txid, True, True)
        decoded = tx['decoded']
        vin = decoded['vin']
        vout = decoded['vout']
        assert_equal(len(vin), 2)
        assert_equal(len(vout), 3)
        assert_equal(tx['fee']['bitcoin'], Decimal('-0.00000652'))
        assert_equal(decoded['vsize'], 326)

        feerate = 3.0
        self.log.info(f"Send explicit tx to node 1 at {feerate} sat/vb")
        addr = node1.getnewaddress()
        info = node1.getaddressinfo(addr)
        txid = node0.sendtoaddress(info['unconfidential'], 1.0, "", "", False, None, None, None, None, None, None, feerate)
        tx = node0.gettransaction(txid, True, True)
        decoded = tx['decoded']
        vin = decoded['vin']
        vout = decoded['vout']
        assert_equal(len(vin), 2)
        assert_equal(len(vout), 3)
        assert_equal(tx['fee']['bitcoin'], Decimal('-0.00000978'))
        assert_equal(decoded['vsize'], 326)

        feerate = 3.0
        self.log.info(f"Send confidential (undiscounted) tx to node 1 at {feerate} sat/vb")
        addr = node1.getnewaddress()
        info = node1.getaddressinfo(addr)
        txid = node0.sendtoaddress(info['confidential'], 1.0, "", "", False, None, None, None, None, None, None, feerate)
        tx = node0.gettransaction(txid, True, True)
        decoded = tx['decoded']
        vin = decoded['vin']
        vout = decoded['vout']
        assert_equal(len(vin), 2)
        assert_equal(len(vout), 3)
        assert_equal(tx['fee']['bitcoin'], Decimal('-0.00007725'))
        assert_equal(decoded['vsize'], 2575)

        feerate = 2.0
        self.log.info(f"Send confidential (undiscounted) tx to node 1 at {feerate} sat/vb")
        addr = node1.getnewaddress()
        info = node1.getaddressinfo(addr)
        txid = node0.sendtoaddress(info['confidential'], 1.0, "", "", False, None, None, None, None, None, None, feerate)
        tx = node0.gettransaction(txid, True, True)
        decoded = tx['decoded']
        vin = decoded['vin']
        vout = decoded['vout']
        assert_equal(len(vin), 2)
        assert_equal(len(vout), 3)
        assert_equal(tx['fee']['bitcoin'], Decimal('-0.00005150'))
        assert_equal(decoded['vsize'], 2575)

        self.sync_mempools([node0, node1])

        # check that txs in the block template are in decreasing feerate
        self.log.info("Check tx ordering in block template with acceptdiscountct=0")
        h = node0.getnewblockhex()
        b = bytes.fromhex(h)
        block = CBlock()
        block.deserialize(BytesIO(b))
        last_feerate = None
        i = 0
        for tx in block.vtx:
            tx.calc_sha256()
            fees = list(filter(lambda o: o.is_fee(), tx.vout))
            # print(f"fees: {fees}")

            if len(fees) > 0:
                print("---")
                txid = tx.hash
                print(f"txid: {txid}")
                t = node1.gettransaction(txid, True, True)
                vsize = tx.get_vsize()
                fee = fees[0].nValue.getAmount()
                print(f"fee: {fee}")
                print(f"vsize: {vsize}")
                print(f"actual feerate at vsize : {fee / vsize}")
                if last_feerate is not None:
                    assert feerate <= last_feerate
                last_feerate = feerate
                i = i + 1
        print("---")

if __name__ == '__main__':
    CTTest().main()
