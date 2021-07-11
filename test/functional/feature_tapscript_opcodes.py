#!/usr/bin/env python3
# Copyright (c) 2014-2016 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

#
# Test for taproot sighash algorithm with pegins and issuances

from test_framework.util import BITCOIN_ASSET_BYTES, assert_raises_rpc_error, satoshi_round
from test_framework.key import ECKey, ECPubKey, compute_xonly_pubkey, generate_privkey, sign_schnorr, tweak_add_privkey, tweak_add_pubkey, verify_schnorr
from test_framework.messages import COIN, COutPoint, CTransaction, CTxIn, CTxInWitness, CTxOut, CTxOutNonce, CTxOutValue, CTxOutWitness, FromHex, ser_uint256, sha256, uint256_from_str
from test_framework.test_framework import BitcoinTestFramework
from test_framework.script import CScript, CScriptNum, CScriptOp, OP_0, OP_1, OP_2, OP_3, OP_4, OP_5, OP_6, OP_7, OP_CAT, OP_DROP, OP_DUP, OP_ELSE, OP_EQUAL, OP_EQUALVERIFY, OP_FALSE, OP_FROMALTSTACK, OP_INSPECTINPUTASSET, OP_INSPECTINPUTISSUANCE, OP_INSPECTINPUTOUTPOINT, OP_INSPECTINPUTSCRIPTPUBKEY, OP_INSPECTINPUTSEQUENCE, OP_INSPECTINPUTVALUE, OP_INSPECTLOCKTIME, OP_INSPECTNUMINPUTS, OP_INSPECTNUMOUTPUTS, OP_INSPECTOUTPUTASSET, OP_INSPECTOUTPUTNONCE, OP_INSPECTOUTPUTSCRIPTPUBKEY, OP_INSPECTOUTPUTVALUE, OP_IF, OP_INSPECTVERSION, OP_NOT, OP_NOTIF, OP_PUSHCURRENTINPUTINDEX, OP_SHA256FINALIZE, OP_SHA256INITIALIZE, OP_SHA256UPDATE, OP_SIZE, OP_SWAP, OP_TOALTSTACK, OP_TXWEIGHT, OP_VERIFY, TaprootSignatureHash, taproot_construct, SIGHASH_DEFAULT, SIGHASH_ALL, SIGHASH_NONE, SIGHASH_SINGLE, SIGHASH_ANYONECANPAY

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


    def get_utxo(self, fund_tx, idx):
        spent = None
        # Coin selection
        for utxo in self.nodes[0].listunspent():
            if utxo["txid"] == ser_uint256(fund_tx.vin[idx].prevout.hash)[::-1].hex() and utxo["vout"] == fund_tx.vin[idx].prevout.n:
                spent = utxo

        assert(spent is not None)
        assert(len(fund_tx.vin) == 2)
        return spent

    def create_taproot_utxo(self, scripts = None, blind = False):
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

    def tapscript_satisfy_test(self, script, inputs = [], add_issuance = False,
        add_pegin = False, fail=None, add_prevout=False, add_asset=False,
        add_value=False, add_spk = False, seq = 0, add_out_spk = None,
        add_out_asset = None, add_out_value = None, add_out_nonce = None,
        ver = 2, locktime = 0, add_num_outputs=False, add_weight=False, blind=False):
        # Create a taproot utxo
        scripts = [("s0", script)]
        prev_tx, prev_vout, spk, sec, pub, tap = self.create_taproot_utxo(scripts)

        if add_pegin:
            fund_info = self.nodes[0].getpeginaddress()
            peg_id = self.nodes[0].sendtoaddress(fund_info["mainchain_address"], 1)
            raw_peg_tx = self.nodes[0].gettransaction(peg_id)["hex"]
            peg_txid = self.nodes[0].sendrawtransaction(raw_peg_tx)
            self.nodes[0].generate(101)
            peg_prf = self.nodes[0].gettxoutproof([peg_txid])
            claim_script = fund_info["claim_script"]

            raw_claim = self.nodes[0].createrawpegin(raw_peg_tx, peg_prf, claim_script)
            tx = FromHex(CTransaction(), raw_claim['hex'])
        else:
            tx = CTransaction()

        tx.nVersion = ver
        tx.nLockTime = locktime
        # Spend the pegin and taproot tx together
        in_total = prev_tx.vout[prev_vout].nValue.getAmount()
        fees = 1000
        tap_in_pos = 0

        if blind:
             # Add an unrelated output
            key = ECKey()
            key.generate()
            tx.vout.append(CTxOut(nValue = CTxOutValue(10000), scriptPubKey = spk, nNonce=CTxOutNonce(key.get_pubkey().get_bytes())))

            tx_hex = self.nodes[0].fundrawtransaction(tx.serialize().hex())
            tx = FromHex(CTransaction(), tx_hex['hex'])

        tx.vin.append(CTxIn(COutPoint(prev_tx.sha256, prev_vout), nSequence=seq))
        tx.vout.append(CTxOut(nValue = CTxOutValue(in_total - fees), scriptPubKey = spk)) # send back to self
        tx.vout.append(CTxOut(CTxOutValue(fees)))

        if add_issuance:
            blind_addr = self.nodes[0].getnewaddress()
            issue_addr = self.nodes[0].validateaddress(blind_addr)['unconfidential']
            # Issuances only require one fee output and that output must the last
            # one. However the way, the current code is structured, it is not possible
            # to this in a super clean without special casing.
            if add_pegin:
                tx.vout.pop()
                tx.vout.pop()
                tx.vout.insert(0, CTxOut(nValue = CTxOutValue(in_total), scriptPubKey = spk)) # send back to self)
            issued_tx = self.nodes[0].rawissueasset(tx.serialize().hex(), [{"asset_amount":2, "asset_address":issue_addr, "blind":False}])[0]["hex"]
            tx = FromHex(CTransaction(), issued_tx)
        # Sign inputs
        if add_pegin:
            signed = self.nodes[0].signrawtransactionwithwallet(tx.serialize().hex())
            tx = FromHex(CTransaction(), signed['hex'])
            tap_in_pos += 1
        else:
            # Need to create empty witness when not deserializing from rpc
            tx.wit.vtxinwit.append(CTxInWitness())

        if blind:
            tx.vin[0], tx.vin[1] = tx.vin[1], tx.vin[0]
            utxo = self.get_utxo(tx, 1)
            zero_str = "0"*64
            blinded_raw = self.nodes[0].rawblindrawtransaction(tx.serialize().hex(), [zero_str, utxo["amountblinder"]], [1.2, utxo['amount']], [utxo['asset'], utxo['asset']], [zero_str, utxo['assetblinder']])
            tx = FromHex(CTransaction(), blinded_raw)
            signed_raw_tx = self.nodes[0].signrawtransactionwithwallet(tx.serialize().hex())
            tx = FromHex(CTransaction(), signed_raw_tx['hex'])


        suffix_annex = []
        control_block = bytes([tap.leaves["s0"].version + tap.negflag]) + tap.inner_pubkey + tap.leaves["s0"].merklebranch
        # Add the prevout to the top of inputs. The witness script will check for equality.
        if add_prevout:
            inputs = [prev_vout.to_bytes(4, 'little'), ser_uint256(prev_tx.sha256)]
        if add_asset:
            assert blind # only used with blinding in testing
            utxo = self.nodes[0].gettxout(ser_uint256(tx.vin[1].prevout.hash)[::-1].hex(), tx.vin[1].prevout.n)
            if "assetcommitment" in utxo:
                asset = bytes.fromhex(utxo["assetcommitment"])
            else:
                asset = b"\x01" + bytes.fromhex(utxo["asset"])[::-1]
            inputs = [asset[0:1], asset[1:33]]
        if add_value:
            utxo = self.nodes[0].gettxout(ser_uint256(tx.vin[1].prevout.hash)[::-1].hex(), tx.vin[1].prevout.n)
            if "valuecommitment" in utxo:
                value = bytes.fromhex(utxo["valuecommitment"])
                inputs = [value[0:1], value[1:33]]
            else:
                value = b"\x01" + int(satoshi_round(utxo["value"])*COIN).to_bytes(8, 'little')
                inputs = [value[0:1], value[1:9]]
        if add_spk:
            ver = CScriptOp.decode_op_n(int.from_bytes(spk[0:1], 'little'))
            inputs = [CScriptNum.encode(CScriptNum(ver))[1:], spk[2:len(spk)]] # always segwit

        # Add witness for outputs
        if add_out_asset is not None:
            asset = tx.vout[add_out_asset].nAsset.vchCommitment
            inputs = [asset[0:1], asset[1:33]]
        if add_out_value is not None:
            value = tx.vout[add_out_value].nValue.vchCommitment
            if len(value) == 9:
                inputs = [value[0:1], value[1:9][::-1]]
            else:
                inputs = [value[0:1], value[1:33]]
        if add_out_nonce is not None:
            nonce = tx.vout[add_out_nonce].nNonce.vchCommitment
            if len(nonce) == 1:
                inputs = [b'']
            else:
                inputs = [nonce]
        if add_out_spk is not None:
            out_spk  = tx.vout[add_out_spk].scriptPubKey
            if len(out_spk) == 0:
                # Python upstream encoding CScriptNum interesting behaviour where it also encodes the length
                # This assumes the implicit wallet behaviour of using segwit outputs.
                # This is useful while sending scripts, but not while using CScriptNums in constructing scripts
                inputs = [CScriptNum.encode(CScriptNum(-1))[1:], sha256(out_spk)]
            else:
                ver = CScriptOp.decode_op_n(int.from_bytes(out_spk[0:1], 'little'))
                inputs = [CScriptNum.encode(CScriptNum(ver))[1:], out_spk[2:len(out_spk)]] # always segwit
        if add_num_outputs:
            num_outs = len(tx.vout)
            inputs = [CScriptNum.encode(CScriptNum(num_outs))[1:]]
        if add_weight:
            # Add a dummy input and check the overall weight
            inputs = [int(5).to_bytes(8, 'little')]
            wit = inputs + [bytes(tap.leaves["s0"].script), control_block] + suffix_annex
            tx.wit.vtxinwit[tap_in_pos].scriptWitness.stack = wit

            exp_weight = self.nodes[0].decoderawtransaction(tx.serialize().hex())["weight"]
            inputs = [exp_weight.to_bytes(8, 'little')]
        wit = inputs + [bytes(tap.leaves["s0"].script), control_block] + suffix_annex
        tx.wit.vtxinwit[tap_in_pos].scriptWitness.stack = wit

        if fail:
            assert_raises_rpc_error(-26, fail, self.nodes[0].sendrawtransaction, tx.serialize().hex())
            return


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
        self.log.info("Testing streaming SHA256")
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

        # Test introspection opcodes
        # 1a. No Pegins/issuances
        self.log.info("Instrospection tests: outpoint flag")
        self.tapscript_satisfy_test(CScript([OP_0, OP_INSPECTINPUTOUTPOINT, b'\x00', OP_EQUALVERIFY, OP_DROP, OP_DROP, OP_1]))
        # 1b. Add a pegin (Test pegin input must be 0x40)
        self.tapscript_satisfy_test(CScript([OP_0, OP_INSPECTINPUTOUTPOINT, b'\x40', OP_EQUALVERIFY, OP_DROP, OP_DROP, OP_1]), add_pegin=True)
        # 1c. Add pegin (The non-pegin input must be push 0x00)
        self.tapscript_satisfy_test(CScript([OP_1, OP_INSPECTINPUTOUTPOINT, b'\x00', OP_EQUALVERIFY, OP_DROP, OP_DROP, OP_1]), add_pegin=True)
        # 1d. Add an issuance
        self.tapscript_satisfy_test(CScript([OP_0, OP_INSPECTINPUTOUTPOINT, b'\x80', OP_EQUALVERIFY, OP_DROP, OP_DROP, OP_1]), add_issuance=True)
        # 1e. Both issuance and pegins together
        self.tapscript_satisfy_test(CScript([OP_0, OP_INSPECTINPUTOUTPOINT, b'\xc0', OP_EQUALVERIFY, OP_DROP, OP_DROP, OP_1]), add_pegin = True, add_issuance=True)
        # 1f. Failure test case
        self.tapscript_satisfy_test(CScript([OP_0, OP_INSPECTINPUTOUTPOINT, b'\x00', OP_EQUALVERIFY, OP_DROP, OP_DROP, OP_1]), add_pegin = True, add_issuance=True, fail="Script failed an OP_EQUALVERIFY operation")

        # Test opcode for inspecting prev tx
        self.log.info("Instrospection tests: inputs")
        self.tapscript_satisfy_test(CScript([OP_0, OP_INSPECTINPUTOUTPOINT, b'\x00', OP_EQUALVERIFY, OP_TOALTSTACK, OP_EQUALVERIFY, OP_FROMALTSTACK, OP_EQUAL]), add_prevout=True)

        # Test taproot asset with blinding.
        self.tapscript_satisfy_test(CScript([OP_1]), blind=True)

        # 2 Test asset(explicit and conf)
        self.tapscript_satisfy_test(CScript([OP_0, OP_INSPECTINPUTASSET, 1, OP_EQUALVERIFY, BITCOIN_ASSET_BYTES, OP_EQUAL]))
        for _ in range(5): # run multiple times for wallet to select conf utxos
            self.tapscript_satisfy_test(CScript([OP_1, OP_INSPECTINPUTASSET, OP_TOALTSTACK, OP_EQUALVERIFY, OP_FROMALTSTACK, OP_EQUAL]), blind=True, add_asset=True)

        # 3 Test asset(explicit and conf)
        amt = 12*10**7
        self.tapscript_satisfy_test(CScript([OP_0, OP_INSPECTINPUTVALUE, 1, OP_EQUALVERIFY, amt.to_bytes(8, 'little'), OP_EQUAL]))
        for _ in range(5): # run multiple times for wallet to select conf utxos
            self.tapscript_satisfy_test(CScript([OP_1, OP_INSPECTINPUTVALUE, OP_TOALTSTACK, OP_EQUALVERIFY, OP_FROMALTSTACK, OP_EQUAL]), blind=True, add_value=True)

        # 4 Test scriptpubkey
        self.tapscript_satisfy_test(CScript([OP_0, OP_INSPECTINPUTSCRIPTPUBKEY, OP_TOALTSTACK, OP_EQUALVERIFY, OP_FROMALTSTACK, OP_EQUAL]), add_spk = True)

        # 5 Test nSequence
        one, two = 1, 2
        self.tapscript_satisfy_test(CScript([OP_0, OP_INSPECTINPUTSEQUENCE, one.to_bytes(4, 'little'), OP_EQUAL]), seq = 1)
        self.tapscript_satisfy_test(CScript([OP_0, OP_INSPECTINPUTSEQUENCE, two.to_bytes(4, 'little'), OP_EQUAL]), seq = 1, fail="Script evaluated without error but finished with a false/empty top stack element")

        # 6 Test issuances
        # No issaunce
        self.tapscript_satisfy_test(CScript([OP_0, OP_INSPECTINPUTISSUANCE, OP_FALSE, OP_EQUAL]))
        # Issuance with 2 units
        asset_issue_amount = 2*COIN
        self.tapscript_satisfy_test(CScript([
            OP_0, OP_INSPECTINPUTISSUANCE,
            # Check blinding nonce is zero
            bytes(32), OP_EQUALVERIFY,
            # Check the entropy is 32 bytes
            OP_SIZE, 32, OP_EQUALVERIFY, OP_DROP,
            # Check the explicit issue amount
            1, OP_EQUALVERIFY, asset_issue_amount.to_bytes(8, 'little'), OP_EQUALVERIFY,
            # Last inflation keys is null, check it as explicit `0` LE 8
            1, OP_EQUALVERIFY, int(0).to_bytes(8, 'little'), OP_EQUAL
        ]), add_issuance=True)

        # Input index out of bounds
        self.tapscript_satisfy_test(CScript([120, OP_1, OP_INSPECTINPUTASSET, OP_FALSE, OP_EQUAL]), fail="Introspection index out of bounds")
        self.tapscript_satisfy_test(CScript([-1, OP_1, OP_INSPECTINPUTVALUE, OP_FALSE, OP_EQUAL]), fail="Introspection index out of bounds")

        # Test current input
        self.log.info("Instrospection tests: current input index")
        self.tapscript_satisfy_test(CScript([OP_PUSHCURRENTINPUTINDEX, OP_0, OP_EQUAL]))
        self.tapscript_satisfy_test(CScript([OP_PUSHCURRENTINPUTINDEX, OP_1, OP_EQUAL]), fail="Script evaluated without error but finished with a false/empty top stack element")

        # Test Outputs
        self.log.info("Instrospection tests: outputs")
        for blind in [True, False]:
            for out_pos in [0, 1]:
                self.tapscript_satisfy_test(CScript([out_pos, OP_INSPECTOUTPUTASSET, OP_TOALTSTACK, OP_EQUALVERIFY, OP_FROMALTSTACK, OP_EQUAL]), blind=blind, add_out_asset=out_pos)
                self.tapscript_satisfy_test(CScript([out_pos, OP_INSPECTOUTPUTVALUE, OP_TOALTSTACK, OP_EQUALVERIFY, OP_FROMALTSTACK, OP_EQUAL]), blind=blind, add_out_value=out_pos)
                self.tapscript_satisfy_test(CScript([out_pos, OP_INSPECTOUTPUTNONCE, OP_EQUAL]), blind=blind, add_out_nonce=out_pos)
                self.tapscript_satisfy_test(CScript([out_pos, OP_INSPECTOUTPUTSCRIPTPUBKEY, OP_TOALTSTACK, OP_EQUALVERIFY, OP_FROMALTSTACK, OP_EQUALVERIFY, OP_1]), blind=blind, add_out_spk=out_pos)

        # Test that output index out of bounds fail
        self.tapscript_satisfy_test(CScript([120, OP_INSPECTOUTPUTASSET, OP_FALSE, OP_EQUAL]), fail="Introspection index out of bounds")
        self.tapscript_satisfy_test(CScript([-1, OP_INSPECTOUTPUTVALUE, OP_FALSE, OP_EQUAL]), fail="Introspection index out of bounds")

        # Finally, check the tx instrospection
        self.log.info("Instrospection tests: tx")
        # Test version equality
        self.tapscript_satisfy_test(CScript([OP_INSPECTVERSION, int(2).to_bytes(4, 'little'), OP_EQUAL]), ver = 2)
        self.tapscript_satisfy_test(CScript([OP_INSPECTVERSION, int(5).to_bytes(4, 'little'), OP_EQUAL]), ver = 2, fail="Script evaluated without error but finished with a false/empty top stack element")

        # Test nlocktime
        self.tapscript_satisfy_test(CScript([OP_INSPECTLOCKTIME, int(7).to_bytes(4, 'little'), OP_EQUAL]), locktime = 7)
        self.tapscript_satisfy_test(CScript([OP_INSPECTLOCKTIME, int(7).to_bytes(4, 'little'), OP_EQUAL]), locktime = 10, fail="Script evaluated without error but finished with a false/empty top stack element")

        # Test num_inputs
        self.tapscript_satisfy_test(CScript([OP_INSPECTNUMINPUTS, OP_1, OP_EQUAL]))
        self.tapscript_satisfy_test(CScript([OP_INSPECTNUMINPUTS, OP_2, OP_EQUAL]), fail="Script evaluated without error but finished with a false/empty top stack element")

        # Test num_outputs
        self.tapscript_satisfy_test(CScript([OP_INSPECTNUMOUTPUTS, OP_EQUAL]), add_num_outputs= True)

        # Test tx wieght
        self.tapscript_satisfy_test(CScript([OP_TXWEIGHT, OP_EQUAL]), add_weight= True)

if __name__ == '__main__':
    TapHashPeginTest().main()