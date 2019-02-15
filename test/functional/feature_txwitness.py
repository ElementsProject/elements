#!/usr/bin/env python3
# Copyright (c) 2015-2018 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test the txwitness for elements

1) Make sure python serialization stuff matches whatever the node/wallet creates, signed and unsigned
2) Segwit transactions have witness data still, and is validated correctly
3) Fast merkle root test? (where oh where are we going to find sha2 internals ripped open in python)
4) transaction round-trips through rpc, p2p, inside and outside of blocks
5) make sure non-segwit transactions have no witness data too
6) If we’re not touching all other tests, we’ll need to actually copy our CTransaction python stuff directly into this test, or another adjacent file, otherwise other tests will still break
7) Try to give it some bitcoin serialization transactions, make sure it fails to decode

"""

from test_framework.messages import CTransaction, CBlock, ser_uint256
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal, bytes_to_hex_str, hex_str_to_bytes
from test_framework import util

from io import BytesIO

class TxWitnessTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 2

    def assert_tx_format_also_signed(self, utxo, segwit):
        raw = self.nodes[0].createrawtransaction(
            [{"txid": utxo["txid"], "vout": utxo["vout"]}],
            [{self.unknown_addr: "49.9"}]
        )

        unsigned_decoded = self.nodes[0].decoderawtransaction(raw)
        assert_equal(len(unsigned_decoded["vin"]), 1)
        assert('txinwitness' not in unsigned_decoded["vin"][0])

        # Cross-check python serialization
        tx = CTransaction()
        tx.deserialize(BytesIO(hex_str_to_bytes(raw)))
        assert_equal(tx.vin[0].prevout.hash, int("0x"+utxo["txid"], 0))
        assert_equal(len(tx.vin), len(unsigned_decoded["vin"]))
        assert_equal(len(tx.vout), len(unsigned_decoded["vout"]))
        # assert re-encoding
        serialized = bytes_to_hex_str(tx.serialize())
        assert_equal(serialized, raw)

        # Now sign and repeat tests
        signed_raw = self.nodes[0].signrawtransactionwithwallet(raw)["hex"]
        signed_decoded = self.nodes[0].decoderawtransaction(signed_raw)
        assert_equal(len(signed_decoded["vin"]), 1)
        assert(("txinwitness" in signed_decoded["vin"][0]) == segwit)

        # Cross-check python serialization
        tx = CTransaction()
        tx.deserialize(BytesIO(hex_str_to_bytes(signed_raw)))
        assert_equal(tx.vin[0].prevout.hash, int("0x"+utxo["txid"], 0))
        assert_equal(bytes_to_hex_str(tx.vin[0].scriptSig), signed_decoded["vin"][0]["scriptSig"]["hex"])
        # test witness
        if segwit:
            wit_decoded = signed_decoded["vin"][0]["txinwitness"]
            for i in range(len(wit_decoded)):
                assert_equal(bytes_to_hex_str(tx.wit.vtxinwit[0].scriptWitness.stack[i]), wit_decoded[i])
        # assert re-encoding
        serialized = bytes_to_hex_str(tx.serialize())
        assert_equal(serialized, signed_raw)

        txid = self.nodes[0].sendrawtransaction(serialized)
        nodetx = self.nodes[0].getrawtransaction(txid, 1)
        assert_equal(nodetx["txid"], tx.rehash())
        # cross-check wtxid report from node
        wtxid = bytes_to_hex_str(ser_uint256(tx.calc_sha256(True))[::-1])
        assert_equal(nodetx["wtxid"], wtxid)
        assert_equal(nodetx["hash"], wtxid)

        # witness hash stuff
        assert_equal(nodetx["withash"], bytes_to_hex_str(ser_uint256(tx.calc_witness_hash())[::-1]))
        return (txid, wtxid)

    def test_transaction_serialization(self):
        legacy_addr = self.nodes[0].getnewaddress("", "legacy")
        p2sh_addr = self.nodes[0].getnewaddress("", "p2sh-segwit")
        bech32_addr = self.nodes[0].getnewaddress("", "bech32")
        self.unknown_addr = self.nodes[1].getnewaddress()

        # directly seed types of utxos required
        self.nodes[0].generatetoaddress(1, legacy_addr)
        self.nodes[0].generatetoaddress(1, p2sh_addr)
        self.nodes[0].generatetoaddress(1, bech32_addr)
        self.nodes[0].generatetoaddress(101, self.unknown_addr)

        # grab utxos filtering by age
        legacy_utxo = self.nodes[0].listunspent(104, 104)[0]
        p2sh_utxo = self.nodes[0].listunspent(103, 103)[0]
        bech32_utxo = self.nodes[0].listunspent(102, 102)[0]

        submitted_txids = []
        self.log.info("Testing legacy UTXO")
        submitted_txids.append(self.assert_tx_format_also_signed(legacy_utxo, segwit=False))
        self.log.info("Testing p2sh UTXO")
        submitted_txids.append(self.assert_tx_format_also_signed(p2sh_utxo, segwit=True))
        self.log.info("Testing bech32 UTXO")
        submitted_txids.append(self.assert_tx_format_also_signed(bech32_utxo, segwit=True))

        blockhash = self.nodes[0].generate(1)[0]
        hexblock = self.nodes[0].getblock(blockhash, 0)
        block_details = self.nodes[0].getblock(blockhash, 2)
        block = CBlock()
        block.deserialize(BytesIO(hex_str_to_bytes(hexblock)))
        assert(len(block.vtx) == len(submitted_txids) + 1)
        assert_equal(len(block_details["tx"]), len(block.vtx))
        for tx1, tx2 in zip(block.vtx[1:], block_details["tx"][1:]):
            # no tuple wildcard, just re-used tx2 on first one
            assert((tx1.rehash(), tx2["wtxid"]) in submitted_txids)
            assert((tx2["txid"], tx2["hash"]) in submitted_txids)
            assert((tx2["txid"], tx2["wtxid"]) in submitted_txids)
        block.rehash()
        assert_equal(block.hash, self.nodes[0].getbestblockhash())


    def run_test(self):
        util.node_fastmerkle = self.nodes[0]
        self.test_transaction_serialization()







if __name__ == '__main__':
    TxWitnessTest().main()
