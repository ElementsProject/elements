#!/usr/bin/env python3
# Copyright (c) 2014-2016 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

#
# Test use of assetdir to locally label assets.
# Test listissuances returns a list of all issuances or specific issuances based on asset hex or asset label.
#

from test_framework.script import CScript, OP_CHECKSIG, SIGHASH_ALL, SIGHASH_ANYONECANPAY, SIGHASH_DEFAULT, SIGHASH_NONE, SIGHASH_SINGLE, TaprootSignatureHash, taproot_construct, taproot_pad_sighash_ty
from test_framework.key import ECKey, ECPubKey, compute_xonly_pubkey, generate_privkey, sign_schnorr, tweak_add_privkey, tweak_add_pubkey, verify_schnorr
from test_framework.messages import CAsset, COIN, COutPoint, CTransaction, CTxIn, CTxInWitness, CTxOut, CTxOutNonce, FromHex, ser_uint256, uint256_from_str
from test_framework.test_framework import BitcoinTestFramework, SkipTest
from test_framework.blind import blind_transaction

import sys


VALID_SIGHASHES_ECDSA = [
    SIGHASH_ALL,
    SIGHASH_NONE,
    SIGHASH_SINGLE,
    SIGHASH_ANYONECANPAY + SIGHASH_ALL,
    SIGHASH_ANYONECANPAY + SIGHASH_NONE,
    SIGHASH_ANYONECANPAY + SIGHASH_SINGLE
]

VALID_SIGHASHES_TAPROOT = [SIGHASH_DEFAULT] + VALID_SIGHASHES_ECDSA

class BlindTest(BitcoinTestFramework):
    """
    Check whether a blinded transaction created from testframework is accepted in mempool.
    This works on secp bindings which only work on linux.
    Build with
    ~/secp256k1-zkp$ ./configure --enable-experimental \
                             --enable-module-generator \
                             --enable-module-rangeproof \
                             --enable-module-surjectionproof \
                             --enable-module-ecdh \
                             --enable-module-recovery
    and provide the location of the so file in LD_LIBRARY_PATH variable

    If secp256k1_zkp is built at home, that would be
    export LD_LIBRARY_PATH=$HOME/secp256k1-zkp/.libs/
    """

    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 1
        self.extra_args = [["-initialfreecoins=2100000000000000", "-anyonecanspendaremine=1", "-blindedaddresses=1"]]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def setup_network(self, split=False):
        self.setup_nodes()

    def test_conf_taphash(self, sighash_ty):

        addr = self.nodes[0].getnewaddress()

        sec = generate_privkey()
        pub = compute_xonly_pubkey(sec)[0]
        tap = taproot_construct(pub)
        spk = tap.scriptPubKey
        tweak = tap.tweak

        # unconf_addr = self.nodes[0].getaddressinfo(addr)['unconfidential']

        raw_tx = self.nodes[0].createrawtransaction([], [{addr: 1.2}])
        # edit spk directly, no way to get new address.
        # would need to implement bech32m in python
        tx = FromHex(CTransaction(), raw_tx)
        tx.vout[0].scriptPubKey = spk
        raw_hex = tx.serialize().hex()
        fund_tx = self.nodes[0].fundrawtransaction(raw_hex)["hex"]

        utxos = self.nodes[0].listunspent()
        funded = FromHex(CTransaction(), fund_tx)
        spent = None
        # Coin selection
        for utxo in utxos:
            if utxo["txid"] == ser_uint256(funded.vin[0].prevout.hash)[::-1].hex() and utxo["vout"] == funded.vin[0].prevout.n:
                spent = utxo

        assert(spent is not None)
        assert(len(funded.vin) == 1)

        tx = FromHex(CTransaction(), fund_tx)

        output_pk = ECPubKey()
        output_pk.set(tx.vout[0].nNonce.vchCommitment)
        assert(output_pk.is_valid)

        key = ECKey()
        key.generate()
        output_pk2 = key.get_pubkey()

        in_v_blind = bytes.fromhex(spent['amountblinder'])[::-1]
        in_a_blind = bytes.fromhex(spent["assetblinder"])[::-1]
        in_amount = int(spent['amount']*COIN)
        in_asset = CAsset(bytes.fromhex(spent["asset"])[::-1])

        # Createrawtransaction might rearrage txouts
        prev_vout = None
        spent_value = None
        for i, out in enumerate(tx.vout):
            if spk == out.scriptPubKey:
                prev_vout = i
                spent_value = out.nValue.getAmount()

        # Must have 1 input now.
        (res, v_blind, a_blind) = blind_transaction(tx, input_value_blinding_factors=[in_v_blind], \
            input_asset_blinding_factors = [in_a_blind], \
            input_assets = [in_asset], \
            input_amounts = [in_amount], \
            output_pubkeys =  [output_pk, output_pk2]
            )

        # Check that the transcation is accepted in mempool and can be mined
        signed_raw_tx = self.nodes[0].signrawtransactionwithwallet(tx.serialize().hex())
        self.nodes[0].sendrawtransaction(signed_raw_tx['hex'])
        tx = FromHex(CTransaction(), signed_raw_tx['hex'])
        tx.rehash()
        assert(res == 2), ("blinding failed %d", res)
        self.nodes[0].generate(1)
        last_blk = self.nodes[0].getblock(self.nodes[0].getbestblockhash())
        assert(tx.hash in last_blk['tx'])

        # Create a new transaction spending from this transaction
        # Find vout which has the taproot spk
        assert(prev_vout is not None)
        spent_tx = CTransaction()
        nonce = ECKey()
        nonce.generate()
        prevout = COutPoint(tx.sha256, prev_vout)
        spent_tx.vin.append(CTxIn(prevout))
        spent_tx.vout.append(CTxOut(spent_value - 10000, spk))
        spent_tx.vout.append(CTxOut(10000)) # ELEMENTS: and fee

        (res, _v_blind, _a_blind) = blind_transaction(spent_tx, input_value_blinding_factors=[v_blind[prev_vout]], \
            input_asset_blinding_factors = [a_blind[prev_vout]], \
            input_assets = [in_asset], \
            input_amounts = [spent_value], \
            output_pubkeys =  [nonce.get_pubkey()]
            )
        assert(res == 1)
        genesis_hash = uint256_from_str(bytes.fromhex(self.nodes[0].getblockhash(0))[::-1])
        spent_tx.wit.vtxinwit = [CTxInWitness()]
        msg = TaprootSignatureHash(spent_tx, [tx.vout[prev_vout]], sighash_ty, genesis_hash, 0)

        # compute the tweak
        tweak_sk = tweak_add_privkey(sec, tweak)
        sig = sign_schnorr(tweak_sk, msg)
        spent_tx.wit.vtxinwit[0].scriptWitness.stack = [taproot_pad_sighash_ty(sig, sighash_ty)]
        pub_tweak = tweak_add_pubkey(pub, tweak)[0]
        assert(verify_schnorr(pub_tweak, sig, msg))
        self.nodes[0].sendrawtransaction(spent_tx.serialize().hex())

        self.nodes[0].generate(1)
        last_blk = self.nodes[0].getblock(self.nodes[0].getbestblockhash())
        spent_tx.rehash()
        assert(spent_tx.hash in last_blk['tx'])

    def run_test(self):
        self.log.info("Check for linux")
        if not sys.platform.startswith('linux'):
            raise SkipTest("This test can only be run on linux.")

        self.nodes[0].generate(101)
        self.wait_until(lambda: self.nodes[0].getblockcount() == 101, timeout=5)

        for sighash_ty in VALID_SIGHASHES_TAPROOT:
            self.test_conf_taphash(sighash_ty)

if __name__ == '__main__':
    BlindTest().main()

