#!/usr/bin/env python3
# Copyright (c) 2014-2016 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

#
# Test for taproot sighash algorithm with pegins and issuances

from test_framework.key import compute_xonly_pubkey, generate_privkey, sign_schnorr, tweak_add_privkey, tweak_add_pubkey, verify_schnorr
from test_framework.messages import COIN, COutPoint, CTransaction, CTxIn, CTxInWitness, CTxOut, CTxOutValue, CTxOutWitness, FromHex, sha256, uint256_from_str
from test_framework.test_framework import BitcoinTestFramework
from test_framework.script import CScript, OP_1, OP_EQUAL, OP_SWAP, OP_SHA256FINALIZE, OP_SHA256INITIALIZE, OP_SHA256UPDATE, TaprootSignatureHash, taproot_construct, SIGHASH_DEFAULT, SIGHASH_ALL, SIGHASH_NONE, SIGHASH_SINGLE, SIGHASH_ANYONECANPAY

import os

VALID_SIGHASHES_ECDSA = [
    SIGHASH_ALL,
    SIGHASH_NONE,
    SIGHASH_SINGLE,
    SIGHASH_ANYONECANPAY + SIGHASH_ALL,
    SIGHASH_ANYONECANPAY + SIGHASH_NONE,
    SIGHASH_ANYONECANPAY + SIGHASH_SINGLE
]

VALID_SIGHASHES_TAPROOT = [SIGHASH_DEFAULT] + VALID_SIGHASHES_ECDSA

class TapHashPeginTest(BitcoinTestFramework):

    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 1
        self.extra_args = [
            ["-initialfreecoins=2100000000000000",
             "-anyonecanspendaremine=1",
            "-blindedaddresses=1",
            "-validatepegin=0",
            "-con_parent_chain_signblockscript=51",
            "-parentscriptprefix=75",
            "-parent_bech32_hrp=ert",
            "-minrelaytxfee=0",
            "-maxtxfee=100.0",
        ]]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def setup_network(self, split=False):
        self.setup_nodes()

    def create_taproot_utxo(self, scripts = None):
        # modify the transaction to add one output that should spend previous taproot
        # Create a taproot prevout
        addr = self.nodes[0].getnewaddress()

        sec = generate_privkey()
        pub = compute_xonly_pubkey(sec)[0]
        tap = taproot_construct(pub, scripts)
        spk = tap.scriptPubKey

        # No need to test blinding in this unit test
        unconf_addr = self.nodes[0].getaddressinfo(addr)['unconfidential']

        raw_tx = self.nodes[0].createrawtransaction([], [{unconf_addr: 1.2}])
        # edit spk directly, no way to get new address.
        # would need to implement bech32m in python
        tx = FromHex(CTransaction(), raw_tx)
        tx.vout[0].scriptPubKey = spk
        tx.vout[0].nValue = CTxOutValue(12*10**7)
        raw_hex = tx.serialize().hex()

        fund_tx = self.nodes[0].fundrawtransaction(raw_hex, False, )["hex"]
        fund_tx = FromHex(CTransaction(), fund_tx)

        # Createrawtransaction might rearrage txouts
        prev_vout = None
        for i, out in enumerate(fund_tx.vout):
            if spk == out.scriptPubKey:
                prev_vout = i

        tx = self.nodes[0].blindrawtransaction(fund_tx.serialize().hex())
        signed_raw_tx = self.nodes[0].signrawtransactionwithwallet(tx)
        _txid = self.nodes[0].sendrawtransaction(signed_raw_tx['hex'])
        tx = FromHex(CTransaction(), signed_raw_tx['hex'])
        tx.rehash()
        self.nodes[0].generate(1)
        last_blk = self.nodes[0].getblock(self.nodes[0].getbestblockhash())
        assert(tx.hash in last_blk['tx'])

        return tx, prev_vout, spk, sec, pub, tap

    def tapscript_satisfy_test(self, script, inputs = []):

        # Create a taproot utxo
        scripts = [("s0", script)]
        prev_tx, prev_vout, spk, sec, pub, tap = self.create_taproot_utxo(scripts)

        # Spend the pegin and taproot tx together
        in_total = prev_tx.vout[prev_vout].nValue.getAmount()
        fees = 1000
        tx = CTransaction()
        tx.vin.append(CTxIn(COutPoint(prev_tx.sha256, prev_vout)))
        tx.vout.append(CTxOut(nValue = CTxOutValue(in_total - fees), scriptPubKey = spk)) # send back to self
        tx.vout.append(CTxOut(CTxOutValue(fees)))

        suffix_annex = []
        control_block = bytes([tap.leaves["s0"].version + tap.negflag]) + tap.inner_pubkey + tap.leaves["s0"].merklebranch
        wit = inputs + [bytes(tap.leaves["s0"].script), control_block] + suffix_annex
        tx.wit.vtxinwit.append(CTxInWitness())
        tx.wit.vtxinwit[0].scriptWitness.stack = wit

        self.nodes[0].sendrawtransaction(hexstring = tx.serialize().hex())
        self.nodes[0].generate(1)
        last_blk = self.nodes[0].getblock(self.nodes[0].getbestblockhash())
        tx.rehash()
        assert(tx.hash in last_blk['tx'])


    def run_test(self):
        self.nodes[0].generate(101)
        self.wait_until(lambda: self.nodes[0].getblockcount() == 101, timeout=5)
        # Test whether the above test framework is working
        self.log.info("Test simple op_1")
        self.tapscript_satisfy_test(CScript([OP_1]))

        # Test streaming sha256
        # All preimages upto len 80 can be filled in a single standard witness element
        # Testing only random even len for speedup
        for k in range(0, 81, 2):
            preimage = os.urandom(k)
            hash = sha256(preimage)
            self.tapscript_satisfy_test(CScript([OP_SHA256INITIALIZE, OP_SWAP, OP_SHA256FINALIZE, hash, OP_EQUAL]), inputs = [bytes(0), preimage])

        # All preimages greater than 80 require Cating the elements
        # But this only works till 520 bytes, streaming opcodes can
        # be when dealing with more than 520 bytes
        # Also adds a test when the sha256 buffer is full
        for pre_len in [64*i for i in range(2, 10)] + [100, 520, 521, 800, 1000, 10000]:
            preimage = os.urandom(pre_len)
            hash = sha256(preimage)
            # Split into chunks of 80
            wit = [preimage[i:min(i + 80, len(preimage))] for i in range(0, len(preimage), 80)]
            script = CScript([OP_SHA256INITIALIZE] + [OP_SWAP, OP_SHA256UPDATE]*(len(wit)-2) + [OP_SWAP, OP_SHA256FINALIZE, hash, OP_EQUAL])
            self.tapscript_satisfy_test(script, wit[::-1])


if __name__ == '__main__':
    TapHashPeginTest().main()