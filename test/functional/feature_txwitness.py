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

from test_framework.messages import CTransaction, CBlock, ser_uint256, from_hex, uint256_from_str, CTxOut, CTxIn, COutPoint, OUTPOINT_ISSUANCE_FLAG, ser_string
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal, hex_str_to_bytes, assert_raises_rpc_error, assert_greater_than
from test_framework import util
from test_framework.blocktools import get_witness_script

from io import BytesIO
import copy
import struct

class TxWitnessTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 2

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def assert_tx_format_also_signed(self, utxo, segwit):
        raw = self.nodes[0].createrawtransaction(
            [{"txid": utxo["txid"], "vout": utxo["vout"]}],
            [{self.unknown_addr: "49.99"}, {"fee": "0.01"}]
        )

        unsigned_decoded = self.nodes[0].decoderawtransaction(raw)
        assert_equal(len(unsigned_decoded["vin"]), 1)
        assert 'txinwitness' not in unsigned_decoded["vin"][0]

        # Cross-check python serialization
        tx = CTransaction()
        tx.deserialize(BytesIO(hex_str_to_bytes(raw)))
        assert_equal(tx.vin[0].prevout.hash, int("0x"+utxo["txid"], 0))
        assert_equal(len(tx.vin), len(unsigned_decoded["vin"]))
        assert_equal(len(tx.vout), len(unsigned_decoded["vout"]))
        # assert re-encoding
        serialized = tx.serialize().hex()
        assert_equal(serialized, raw)

        # Now sign and repeat tests
        signed_raw = self.nodes[0].signrawtransactionwithwallet(raw)["hex"]
        signed_decoded = self.nodes[0].decoderawtransaction(signed_raw)
        assert_equal(len(signed_decoded["vin"]), 1)
        assert ("txinwitness" in signed_decoded["vin"][0]) == segwit

        # Cross-check python serialization
        tx = CTransaction()
        tx.deserialize(BytesIO(hex_str_to_bytes(signed_raw)))
        assert_equal(tx.vin[0].prevout.hash, int("0x"+utxo["txid"], 0))
        assert_equal(tx.vin[0].scriptSig.hex(), signed_decoded["vin"][0]["scriptSig"]["hex"])
        # test witness
        if segwit:
            wit_decoded = signed_decoded["vin"][0]["txinwitness"]
            for i in range(len(wit_decoded)):
                assert_equal(tx.wit.vtxinwit[0].scriptWitness.stack[i].hex(), wit_decoded[i])
        # assert re-encoding
        serialized = tx.serialize().hex()
        assert_equal(serialized, signed_raw)

        txid = self.nodes[0].sendrawtransaction(serialized)
        nodetx = self.nodes[0].getrawtransaction(txid, 1)
        assert_equal(nodetx["txid"], tx.rehash())
        # cross-check wtxid report from node
        wtxid = ser_uint256(tx.calc_sha256(True))[::-1].hex()
        assert_equal(nodetx["wtxid"], wtxid)
        assert_equal(nodetx["hash"], wtxid)

        # witness hash stuff
        assert_equal(nodetx["withash"], tx.calc_witness_hash())
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
        assert len(block.vtx) == len(submitted_txids) + 1
        assert_equal(len(block_details["tx"]), len(block.vtx))
        for tx1, tx2 in zip(block.vtx[1:], block_details["tx"][1:]):
            # no tuple wildcard, just re-used tx2 on first one
            assert (tx1.rehash(), tx2["wtxid"]) in submitted_txids
            assert (tx2["txid"], tx2["hash"]) in submitted_txids
            assert (tx2["txid"], tx2["wtxid"]) in submitted_txids
        block.rehash()
        assert_equal(block.hash, self.nodes[0].getbestblockhash())

    def test_coinbase_witness(self):
        block = self.nodes[0].getnewblockhex()
        block_struct = from_hex(CBlock(), block)

        # Test vanilla block round-trip
        self.nodes[0].testproposedblock(block_struct.serialize(with_witness=True).hex())

        # Assert there's scriptWitness in the coinbase input that is the witness nonce and nothing else
        assert_equal(block_struct.vtx[0].wit.vtxinwit[0].scriptWitness.stack, [b'\x00'*32])
        assert_equal(block_struct.vtx[0].wit.vtxinwit[0].vchIssuanceAmountRangeproof, b'')
        assert_equal(block_struct.vtx[0].wit.vtxinwit[0].vchInflationKeysRangeproof, b'')
        assert_equal(block_struct.vtx[0].wit.vtxinwit[0].peginWitness.stack, [])

        # Add extra witness that isn't covered by witness merkle root, make sure blocks are still valid
        block_witness_stuffed = copy.deepcopy(block_struct)
        block_witness_stuffed.vtx[0].wit.vtxinwit[0].vchIssuanceAmountRangeproof = b'\x00'
        assert_raises_rpc_error(-25, "bad-cb-witness", self.nodes[0].testproposedblock, block_witness_stuffed.serialize(with_witness=True).hex())
        block_witness_stuffed = copy.deepcopy(block_struct)
        block_witness_stuffed.vtx[0].wit.vtxinwit[0].vchInflationKeysRangeproof = b'\x00'
        assert_raises_rpc_error(-25, "bad-cb-witness", self.nodes[0].testproposedblock, block_witness_stuffed.serialize(with_witness=True).hex())
        block_witness_stuffed = copy.deepcopy(block_struct)

        # Let's blow out block weight limit by adding 4MW here
        block_witness_stuffed.vtx[0].wit.vtxinwit[0].peginWitness.stack = [b'\x00'*4000000]
        assert_raises_rpc_error(-25, "bad-cb-witness", self.nodes[0].testproposedblock, block_witness_stuffed.serialize(with_witness=True).hex())

        # Test that node isn't blinded to the block
        # Previously an over-stuffed block >4MW would have been marked permanently bad
        # as it already passes witness merkle and regular merkle root checks
        block_height = self.nodes[0].getblockcount()
        assert_equal(self.nodes[0].submitblock(block_witness_stuffed.serialize(with_witness=True).hex()), "bad-cb-witness")
        assert_equal(block_height, self.nodes[0].getblockcount())
        assert_equal(self.nodes[0].submitblock(block_struct.serialize(with_witness=True).hex()), None)
        assert_equal(block_height+1, self.nodes[0].getblockcount())

        # New block since we used the first one
        block_struct = from_hex(CBlock(), self.nodes[0].getnewblockhex())
        block_witness_stuffed = copy.deepcopy(block_struct)


        # Add extra witness data that is covered by witness merkle root, make sure invalid
        assert_equal(block_witness_stuffed.vtx[0].wit.vtxoutwit[0].vchSurjectionproof, b'')
        assert_equal(block_witness_stuffed.vtx[0].wit.vtxoutwit[0].vchRangeproof, b'')
        block_witness_stuffed.vtx[0].wit.vtxoutwit[0].vchRangeproof = b'\x00'*100000
        block_witness_stuffed.vtx[0].wit.vtxoutwit[0].vchSurjectionproof = b'\x00'*100000
        assert_raises_rpc_error(-25, "bad-witness-merkle-match", self.nodes[0].testproposedblock, block_witness_stuffed.serialize(with_witness=True).hex())
        witness_root_hex = block_witness_stuffed.calc_witness_merkle_root()
        witness_root = uint256_from_str(hex_str_to_bytes(witness_root_hex)[::-1])
        block_witness_stuffed.vtx[0].vout[-1] = CTxOut(0, get_witness_script(witness_root, 0))
        block_witness_stuffed.vtx[0].rehash()
        block_witness_stuffed.hashMerkleRoot = block_witness_stuffed.calc_merkle_root()
        block_witness_stuffed.rehash()
        assert_raises_rpc_error(-25, "bad-cb-amount", self.nodes[0].testproposedblock, block_witness_stuffed.serialize(with_witness=True).hex())
        assert_greater_than(len(block_witness_stuffed.serialize(with_witness=True).hex()), 100000*4) # Make sure the witness data is actually serialized

        # A CTxIn that always serializes the asset issuance, even for coinbases.
        class AlwaysIssuanceCTxIn(CTxIn):
            def serialize(self):
                r = b''
                outpoint = COutPoint()
                outpoint.hash = self.prevout.hash
                outpoint.n = self.prevout.n
                outpoint.n |= OUTPOINT_ISSUANCE_FLAG
                r += outpoint.serialize()
                r += ser_string(self.scriptSig)
                r += struct.pack("<I", self.nSequence)
                r += self.assetIssuance.serialize()
                return r

        # Test that issuance inputs in coinbase don't survive a serialization round-trip
        # (even though this can't cause issuance to occur either way due to VerifyCoinbaseAmount semantics)
        block_witness_stuffed = copy.deepcopy(block_struct)
        coinbase_orig = copy.deepcopy(block_witness_stuffed.vtx[0].vin[0])
        coinbase_ser_size = len(block_witness_stuffed.vtx[0].vin[0].serialize())
        block_witness_stuffed.vtx[0].vin[0] = AlwaysIssuanceCTxIn()
        block_witness_stuffed.vtx[0].vin[0].prevout = coinbase_orig.prevout
        block_witness_stuffed.vtx[0].vin[0].scriptSig = coinbase_orig.scriptSig
        block_witness_stuffed.vtx[0].vin[0].nSequence = coinbase_orig.nSequence
        block_witness_stuffed.vtx[0].vin[0].assetIssuance.nAmount.setToAmount(1)
        bad_coinbase_ser_size = len(block_witness_stuffed.vtx[0].vin[0].serialize())
        # 32+32+9+1 should be serialized for each assetIssuance field
        assert_equal(bad_coinbase_ser_size, coinbase_ser_size+32+32+9+1)
        assert not block_witness_stuffed.vtx[0].vin[0].assetIssuance.isNull()
        assert_raises_rpc_error(-22, "TX decode failed", self.nodes[0].decoderawtransaction, block_witness_stuffed.vtx[0].serialize().hex())

    def run_test(self):
        util.node_fastmerkle = self.nodes[0]
        self.test_coinbase_witness()
        self.test_transaction_serialization()

if __name__ == '__main__':
    TxWitnessTest().main()
