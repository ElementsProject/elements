#!/usr/bin/env python3
# Copyright (c) 2014-2016 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

#
# Test for taproot sighash algorithm with pegins and issuances

from test_framework.key import ECKey, ECPubKey, compute_xonly_pubkey, generate_privkey, sign_schnorr, tweak_add_privkey, tweak_add_pubkey, verify_schnorr
from test_framework.messages import COIN, COutPoint, CTransaction, CTxIn, CTxInWitness, CTxOut, CTxOutValue, CTxOutWitness, FromHex, uint256_from_str
from test_framework.test_framework import BitcoinTestFramework, SkipTest
from test_framework.script import TaprootSignatureHash, taproot_construct, taproot_pad_sighash_ty, SIGHASH_DEFAULT, SIGHASH_ALL, SIGHASH_NONE, SIGHASH_SINGLE, SIGHASH_ANYONECANPAY

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

    def create_taproot_utxo(self):
        # modify the transaction to add one output that should spend previous taproot
        # Create a taproot prevout
        addr = self.nodes[0].getnewaddress()

        sec = generate_privkey()
        pub = compute_xonly_pubkey(sec)[0]
        tap = taproot_construct(pub)
        spk = tap.scriptPubKey
        tweak = tap.tweak

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

        return tx, prev_vout, spk, sec, pub, tweak

    def pegin_test(self, sighash_ty):

        # Peg-in prep:
        # Hack: since we're not validating peg-ins in parent chain, just make
        # both the funding and claim tx on same chain (printing money)
        fund_info = self.nodes[0].getpeginaddress()
        peg_id = self.nodes[0].sendtoaddress(fund_info["mainchain_address"], 1)
        raw_peg_tx = self.nodes[0].gettransaction(peg_id)["hex"]
        peg_txid = self.nodes[0].sendrawtransaction(raw_peg_tx)
        self.nodes[0].generate(101)
        peg_prf = self.nodes[0].gettxoutproof([peg_txid])
        claim_script = fund_info["claim_script"]

        # Create a pegin transaction
        # We have to manually supply claim script, otherwise the wallet will pick
        raw_claim = self.nodes[0].createrawpegin(raw_peg_tx, peg_prf, claim_script)
        raw_claim = FromHex(CTransaction(), raw_claim['hex'])

        # Create a taproot utxo
        tx, prev_vout, spk, sec, pub, tweak = self.create_taproot_utxo()

        # Spend the pegin and taproot tx together
        raw_claim.vin.append(CTxIn(COutPoint(tx.sha256, prev_vout)))
        raw_claim.vout.append(CTxOut(nValue = CTxOutValue(12 * 10**7), scriptPubKey = spk)) # send back to self

        signed = self.nodes[0].signrawtransactionwithwallet(raw_claim.serialize().hex())
        raw_claim = FromHex(CTransaction(), signed['hex'])
        genesis_hash = uint256_from_str(bytes.fromhex(self.nodes[0].getblockhash(0))[::-1])
        peg_utxo = CTxOut()
        peg_utxo.from_pegin_witness_data(raw_claim.wit.vtxinwit[0].peginWitness)
        msg = TaprootSignatureHash(raw_claim, [peg_utxo, tx.vout[prev_vout]], sighash_ty, genesis_hash, 1)

        # compute the tweak
        tweak_sk = tweak_add_privkey(sec, tweak)
        sig = sign_schnorr(tweak_sk, msg)
        raw_claim.wit.vtxinwit[1].scriptWitness.stack = [taproot_pad_sighash_ty(sig, sighash_ty)]
        pub_tweak = tweak_add_pubkey(pub, tweak)[0]
        assert(verify_schnorr(pub_tweak, sig, msg))
        # Since we add in/outputs the min feerate is no longer maintained.
        self.nodes[0].sendrawtransaction(hexstring = raw_claim.serialize().hex())
        self.nodes[0].generate(1)
        last_blk = self.nodes[0].getblock(self.nodes[0].getbestblockhash())
        raw_claim.rehash()
        assert(raw_claim.hash in last_blk['tx'])

    def issuance_test(self, sighash_ty):
        tx, prev_vout, spk, sec, pub, tweak = self.create_taproot_utxo()

        blind_addr = self.nodes[0].getnewaddress()
        nonblind_addr = self.nodes[0].validateaddress(blind_addr)['unconfidential']
        raw_tx = self.nodes[0].createrawtransaction([], [{nonblind_addr: 1}])
        raw_tx = FromHex(CTransaction(), raw_tx)

        # Need to taproot outputs later because fundrawtransaction cannot estimate fees
        # prev out has value 1.2 btc
        in_total = tx.vout[prev_vout].nValue.getAmount()
        fees = 100
        raw_tx.vin.append(CTxIn(COutPoint(tx.sha256, prev_vout)))
        raw_tx.vout.append(CTxOut(nValue = CTxOutValue(in_total - fees - 10**8), scriptPubKey = spk)) # send back to self
        raw_tx.vout.append(CTxOut(nValue = CTxOutValue(fees)))

        # issued_tx = raw_tx.serialize().hex()
        blind_addr = self.nodes[0].getnewaddress()
        issue_addr = self.nodes[0].validateaddress(blind_addr)['unconfidential']
        issued_tx = self.nodes[0].rawissueasset(raw_tx.serialize().hex(), [{"asset_amount":2, "asset_address":issue_addr, "blind":False}])[0]["hex"]
        # blind_tx = self.nodes[0].blindrawtransaction(issued_tx) # This is a no-op
        genesis_hash = uint256_from_str(bytes.fromhex(self.nodes[0].getblockhash(0))[::-1])
        issued_tx = FromHex(CTransaction(), issued_tx)
        issued_tx.wit.vtxoutwit = [CTxOutWitness()] * len(issued_tx.vout)
        issued_tx.wit.vtxinwit = [CTxInWitness()] * len(issued_tx.vin)
        msg = TaprootSignatureHash(issued_tx, [tx.vout[prev_vout]], sighash_ty, genesis_hash, 0)

        # compute the tweak
        tweak_sk = tweak_add_privkey(sec, tweak)
        sig = sign_schnorr(tweak_sk, msg)
        issued_tx.wit.vtxinwit[0].scriptWitness.stack = [taproot_pad_sighash_ty(sig, sighash_ty)]
        pub_tweak = tweak_add_pubkey(pub, tweak)[0]
        assert(verify_schnorr(pub_tweak, sig, msg))
        # Since we add in/outputs the min feerate is no longer maintained.
        self.nodes[0].sendrawtransaction(hexstring = issued_tx.serialize().hex())
        self.nodes[0].generate(1)
        last_blk = self.nodes[0].getblock(self.nodes[0].getbestblockhash())
        issued_tx.rehash()
        assert(issued_tx.hash in last_blk['tx'])


    def run_test(self):
        self.nodes[0].generate(101)
        self.wait_until(lambda: self.nodes[0].getblockcount() == 101, timeout=5)
        self.log.info("Testing sighash taproot pegins")
        # Note that this does not test deposit to taproot pegin addresses
        # because there is no support for taproot pegins in rpc. The current rpc assumes
        # to shwsh tweaked address
        for sighash_ty in VALID_SIGHASHES_TAPROOT:
            self.pegin_test(sighash_ty)
        self.log.info("Testing sighash taproot issuances")
        for sighash_ty in VALID_SIGHASHES_TAPROOT:
            self.issuance_test(sighash_ty)


if __name__ == '__main__':
    TapHashPeginTest().main()
