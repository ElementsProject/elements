#!/usr/bin/env python3
# Copyright (c) 2015-2021 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test transaction signing using the signrawtransaction* RPCs."""

from test_framework.blocktools import (
    COINBASE_MATURITY,
)
from test_framework.address import (
    script_to_p2sh,
    script_to_p2wsh,
)
from test_framework.key import ECKey
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    assert_raises_rpc_error,
    find_vout_for_address,
)
from test_framework.messages import (
    CTxInWitness,
    tx_from_hex,
)
from test_framework.script import (
    CScript,
    OP_CHECKLOCKTIMEVERIFY,
    OP_CHECKSEQUENCEVERIFY,
    OP_DROP,
    OP_TRUE,
)
from test_framework.script_util import (
    key_to_p2pk_script,
    key_to_p2pkh_script,
    script_to_p2sh_p2wsh_script,
    script_to_p2wsh_script,
)
from test_framework.wallet_util import bytes_to_wif

from decimal import (
    Decimal,
    getcontext,
)

import time # ELEMENTS

class SignRawTransactionsTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 3
        elements_args =  ["-blindedaddresses=1", "-initialfreecoins=2100000000000000", "-con_connect_genesis_outputs=1", "-anyonecanspendaremine=1", "-txindex=1"]
        prefix_args = ["-pubkeyprefix=111", "-scriptprefix=196", "-secretprefix=239", "-extpubkeyprefix=043587CF", "-extprvkeyprefix=04358394" ]
        self.extra_args = [prefix_args, prefix_args, elements_args]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def setup_network(self):
        # Start with split network:
        self.setup_nodes()
        self.connect_nodes(0, 1)
        self.sync_all(self.nodes[:2])
        self.sync_all(self.nodes[2:])

    def successful_signing_test(self):
        """Create and sign a valid raw transaction with one input.

        Expected results:

        1) The transaction has a complete set of signatures
        2) No script verification error occurred"""
        self.log.info("Test valid raw transaction with one input")
        privKeys = ['cUeKHd5orzT3mz8P9pxyREHfsWtVfgsfDjiZZBcjUBAaGk1BTj7N', 'cVKpPfVKSJxKqVpE9awvXNWuLHCa5j5tiE7K6zbUSptFpTEtiFrA']

        inputs = [
            # Valid pay-to-pubkey scripts
            {'txid': '9b907ef1e3c26fc71fe4a4b3580bc75264112f95050014157059c736f0202e71', 'vout': 0,
             'scriptPubKey': '76a91460baa0f494b38ce3c940dea67f3804dc52d1fb9488ac'},
            {'txid': '83a4f6a6b73660e13ee6cb3c6063fa3759c50c9b7521d0536022961898f4fb02', 'vout': 0,
             'scriptPubKey': '76a914669b857c03a5ed269d5d85a1ffac9ed5d663072788ac'},
        ]

        outputs = [{'mpLQjfK79b7CCV4VMJWEWAj5Mpx8Up5zxB': 0.1}]

        rawTx = self.nodes[0].createrawtransaction(inputs, outputs)
        rawTxSigned = self.nodes[0].signrawtransactionwithkey(rawTx, privKeys, inputs)

        # 1) The transaction has a complete set of signatures
        assert rawTxSigned['complete']

        # 2) No script verification error occurred
        assert 'errors' not in rawTxSigned

    def test_with_lock_outputs(self):
        self.log.info("Test correct error reporting when trying to sign a locked output")
        self.nodes[0].encryptwallet("password")

        rawTx = '02000000000156b958f78e3f24e0b2f4e4db1255426b0902027cb37e3ddadb52e37c3557dddb0000000000ffffffff0101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000129b9a6c0001600149a2ee8c77140a053f36018ac8124a6ececc1668a00000000'

        assert_raises_rpc_error(-13, "Please enter the wallet passphrase with walletpassphrase first", self.nodes[0].signrawtransactionwithwallet, rawTx)

    def script_verification_error_test(self):
        """Create and sign a raw transaction with valid (vin 0), invalid (vin 1) and one missing (vin 2) input script.

        Expected results:

        3) The transaction has no complete set of signatures
        4) Two script verification errors occurred
        5) Script verification errors have certain properties ("txid", "vout", "scriptSig", "sequence", "error")
        6) The verification errors refer to the invalid (vin 1) and missing input (vin 2)"""
        self.log.info("Test script verification errors")
        privKeys = ['cUeKHd5orzT3mz8P9pxyREHfsWtVfgsfDjiZZBcjUBAaGk1BTj7N']

        inputs = [
            # Valid pay-to-pubkey script
            {'txid': '9b907ef1e3c26fc71fe4a4b3580bc75264112f95050014157059c736f0202e71', 'vout': 0},
            # Invalid script
            {'txid': '5b8673686910442c644b1f4993d8f7753c7c8fcb5c87ee40d56eaeef25204547', 'vout': 7},
            # Missing scriptPubKey
            {'txid': '9b907ef1e3c26fc71fe4a4b3580bc75264112f95050014157059c736f0202e71', 'vout': 1},
        ]

        scripts = [
            # Valid pay-to-pubkey script
            {'txid': '9b907ef1e3c26fc71fe4a4b3580bc75264112f95050014157059c736f0202e71', 'vout': 0,
             'scriptPubKey': '76a91460baa0f494b38ce3c940dea67f3804dc52d1fb9488ac'},
            # Invalid script
            {'txid': '5b8673686910442c644b1f4993d8f7753c7c8fcb5c87ee40d56eaeef25204547', 'vout': 7,
             'scriptPubKey': 'badbadbadbad'}
        ]

        outputs = [{'mpLQjfK79b7CCV4VMJWEWAj5Mpx8Up5zxB': 0.1}]

        rawTx = self.nodes[0].createrawtransaction(inputs, outputs)

        # Make sure decoderawtransaction is at least marginally sane
        decodedRawTx = self.nodes[0].decoderawtransaction(rawTx)
        for i, inp in enumerate(inputs):
            assert_equal(decodedRawTx["vin"][i]["txid"], inp["txid"])
            assert_equal(decodedRawTx["vin"][i]["vout"], inp["vout"])

        # Make sure decoderawtransaction throws if there is extra data
        assert_raises_rpc_error(-22, "TX decode failed", self.nodes[0].decoderawtransaction, rawTx + "00")

        rawTxSigned = self.nodes[0].signrawtransactionwithkey(rawTx, privKeys, scripts)

        # 3) The transaction has no complete set of signatures
        assert not rawTxSigned['complete']

        # 4) Two script verification errors occurred
        assert 'errors' in rawTxSigned
        assert_equal(len(rawTxSigned['errors']), 2)

        # 5) Script verification errors have certain properties
        assert 'txid' in rawTxSigned['errors'][0]
        assert 'vout' in rawTxSigned['errors'][0]
        assert 'witness' in rawTxSigned['errors'][0]
        assert 'scriptSig' in rawTxSigned['errors'][0]
        assert 'sequence' in rawTxSigned['errors'][0]
        assert 'error' in rawTxSigned['errors'][0]

        # 6) The verification errors refer to the invalid (vin 1) and missing input (vin 2)
        assert_equal(rawTxSigned['errors'][0]['txid'], inputs[1]['txid'])
        assert_equal(rawTxSigned['errors'][0]['vout'], inputs[1]['vout'])
        assert_equal(rawTxSigned['errors'][1]['txid'], inputs[2]['txid'])
        assert_equal(rawTxSigned['errors'][1]['vout'], inputs[2]['vout'])
        assert not rawTxSigned['errors'][0]['witness']

        # Now test signing failure for transaction with input witnesses
        p2wpkh_raw_tx = "010000000102fff7f7881a8099afa6940d42d1e7f6362bec38171ea3edf433541db4e4ad969f00000000494830450221008b9d1dc26ba6a9cb62127b02742fa9d754cd3bebf337f7a55d114c8e5cdd30be022040529b194ba3f9281a99f2b1c0a19c0489bc22ede944ccf4ecbab4cc618ef3ed01eeffffffef51e1b804cc89d182d279655c3aa89e815b1b309fe287d9b2b55d57b90ec68a0100000000ffffffff0201ac2e6a47e85fdc2a5a27334544440f2f5135553a7476f4f5e3b9792da6a58fe0010000000006b22c20001976a9148280b37df378db99f66f85c95a783a76ac7a6d5988ac01ac2e6a47e85fdc2a5a27334544440f2f5135553a7476f4f5e3b9792da6a58fe001000000000d519390001976a9143bde42dbee7e4dbe6a21b2d50ce2f0167faa815988ac110000000000000000000247304402203609e17b84f6a7d30c80bfa610b5b4542f32a8a0d5447a12fb1366d7f01cc44a0220573a954c4518331561406f90300e8f3358f51928d43c212a8caed02de67eebee0121025476c2e83188368da1ff3e292e7acafcdb3566bb0ad253f62fc70f07aeee63570000000000"

        rawTxSigned = self.nodes[0].signrawtransactionwithwallet(p2wpkh_raw_tx)

        # 7) The transaction has no complete set of signatures
        assert not rawTxSigned['complete']

        # 8) Two script verification errors occurred
        assert 'errors' in rawTxSigned
        assert_equal(len(rawTxSigned['errors']), 2)

        # 9) Script verification errors have certain properties
        assert 'txid' in rawTxSigned['errors'][0]
        assert 'vout' in rawTxSigned['errors'][0]
        assert 'witness' in rawTxSigned['errors'][0]
        assert 'scriptSig' in rawTxSigned['errors'][0]
        assert 'sequence' in rawTxSigned['errors'][0]
        assert 'error' in rawTxSigned['errors'][0]

        # Non-empty witness checked here
        assert_equal(rawTxSigned['errors'][1]['witness'], ["304402203609e17b84f6a7d30c80bfa610b5b4542f32a8a0d5447a12fb1366d7f01cc44a0220573a954c4518331561406f90300e8f3358f51928d43c212a8caed02de67eebee01", "025476c2e83188368da1ff3e292e7acafcdb3566bb0ad253f62fc70f07aeee6357"])
        assert not rawTxSigned['errors'][0]['witness']

    def test_fully_signed_tx(self):
        self.log.info("Test signing a fully signed transaction does nothing")
        self.nodes[0].walletpassphrase("password", 9999)
        self.generate(self.nodes[0], COINBASE_MATURITY + 1, sync_fun=self.no_op)
        rawtx = self.nodes[0].createrawtransaction([], [{self.nodes[0].getnewaddress(): 10}])
        fundedtx = self.nodes[0].fundrawtransaction(rawtx)
        signedtx = self.nodes[0].signrawtransactionwithwallet(fundedtx["hex"])
        assert_equal(signedtx["complete"], True)
        signedtx2 = self.nodes[0].signrawtransactionwithwallet(signedtx["hex"])
        assert_equal(signedtx2["complete"], True)
        assert_equal(signedtx["hex"], signedtx2["hex"])
        self.nodes[0].walletlock()

    def witness_script_test(self):
        self.log.info("Test signing transaction to P2SH-P2WSH addresses without wallet")
        # Create a new P2SH-P2WSH 1-of-1 multisig address:
        eckey = ECKey()
        eckey.generate()
        embedded_privkey = bytes_to_wif(eckey.get_bytes())
        embedded_pubkey = eckey.get_pubkey().get_bytes().hex()
        p2sh_p2wsh_address = self.nodes[1].createmultisig(1, [embedded_pubkey], "p2sh-segwit")
        # send transaction to P2SH-P2WSH 1-of-1 multisig address
        self.generate(self.nodes[0], COINBASE_MATURITY + 1, sync_fun=self.no_op)
        self.nodes[0].sendtoaddress(p2sh_p2wsh_address["address"], 49.999)
        self.generate(self.nodes[0], 1, sync_fun=self.no_op)
        # ElEMENTS: allow time for block sync
        time.sleep(1)
        # Get the UTXO info from scantxoutset
        unspent_output = self.nodes[1].scantxoutset('start', [p2sh_p2wsh_address['descriptor']])['unspents'][0]
        spk = script_to_p2sh_p2wsh_script(p2sh_p2wsh_address['redeemScript']).hex()
        unspent_output['witnessScript'] = p2sh_p2wsh_address['redeemScript']
        unspent_output['redeemScript'] = script_to_p2wsh_script(unspent_output['witnessScript']).hex()
        assert_equal(spk, unspent_output['scriptPubKey'])
        # Now create and sign a transaction spending that output on node[0], which doesn't know the scripts or keys
        spending_tx = self.nodes[0].createrawtransaction([unspent_output], [{self.nodes[1].get_wallet_rpc(self.default_wallet_name).getnewaddress(): Decimal("49.998")}])
        spending_tx_signed = self.nodes[0].signrawtransactionwithkey(spending_tx, [embedded_privkey], [unspent_output])
        # Check the signing completed successfully
        assert 'complete' in spending_tx_signed
        assert_equal(spending_tx_signed['complete'], True)

        # Now test with P2PKH and P2PK scripts as the witnessScript
        for tx_type in ['P2PKH', 'P2PK']:  # these tests are order-independent
            self.verify_txn_with_witness_script(tx_type)

    def verify_txn_with_witness_script(self, tx_type):
        self.log.info("Test with a {} script as the witnessScript".format(tx_type))
        eckey = ECKey()
        eckey.generate()
        embedded_privkey = bytes_to_wif(eckey.get_bytes())
        embedded_pubkey = eckey.get_pubkey().get_bytes().hex()
        witness_script = {
            'P2PKH': key_to_p2pkh_script(embedded_pubkey).hex(),
            'P2PK': key_to_p2pk_script(embedded_pubkey).hex()
        }.get(tx_type, "Invalid tx_type")
        redeem_script = script_to_p2wsh_script(witness_script).hex()
        addr = script_to_p2sh(redeem_script, prefix=196)
        script_pub_key = self.nodes[1].validateaddress(addr)['scriptPubKey']
        # Fund that address
        txid = self.nodes[0].sendtoaddress(addr, 10)
        vout = find_vout_for_address(self.nodes[0], txid, addr)
        self.generate(self.nodes[0], 1, sync_fun=self.no_op)
        # Now create and sign a transaction spending that output on node[0], which doesn't know the scripts or keys
        spending_tx = self.nodes[0].createrawtransaction([{'txid': txid, 'vout': vout}], [{self.nodes[1].getnewaddress(): Decimal("9.999")}, {"fee": Decimal("0.001")}])
        spending_tx_signed = self.nodes[0].signrawtransactionwithkey(spending_tx, [embedded_privkey], [{'txid': txid, 'vout': vout, 'scriptPubKey': script_pub_key, 'redeemScript': redeem_script, 'witnessScript': witness_script, 'amount': 10}])
        # Check the signing completed successfully
        assert 'complete' in spending_tx_signed
        assert_equal(spending_tx_signed['complete'], True)
        self.nodes[0].sendrawtransaction(spending_tx_signed['hex'])

    def OP_1NEGATE_test(self):
        self.log.info("Test OP_1NEGATE (0x4f) satisfies BIP62 minimal push standardness rule")
        hex_str = (
            "020000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffff"
            "ffffffffff00000000044f024f9cfdffffff010a12121212121212121212121212"
            "12121212121212121212121212121212121212010000000005f5b9f00023210277"
            "77777777777777777777777777777777777777777777777777777777777777ac66"
            "030000"
        )
        prev_txs = [
            {
                "txid": "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",
                "vout": 0,
                "scriptPubKey": "A914AE44AB6E9AA0B71F1CD2B453B69340E9BFBAEF6087",
                "redeemScript": "4F9C",
                "amount": 1,
            }
        ]
        txn = self.nodes[0].signrawtransactionwithwallet(hex_str, prev_txs)
        assert txn["complete"]

    def test_signing_with_csv(self):
        self.log.info("Test signing a transaction containing a fully signed CSV input")
        self.nodes[0].walletpassphrase("password", 9999)
        getcontext().prec = 10

        # Make sure CSV is active
        assert self.nodes[0].getdeploymentinfo()['deployments']['csv']['active']

        # Create a P2WSH script with CSV
        script = CScript([1, OP_CHECKSEQUENCEVERIFY, OP_DROP])
        address = script_to_p2wsh(script)

        # Fund that address and make the spend
        txid = self.nodes[0].sendtoaddress(address, 1)
        vout = find_vout_for_address(self.nodes[0], txid, address)
        self.generate(self.nodes[0], 1, sync_fun=self.no_op)
        utxo = self.nodes[0].listunspent()[0]
        amt = Decimal(1) + utxo["amount"] - Decimal(0.00001)
        tx = self.nodes[0].createrawtransaction(
            [{"txid": txid, "vout": vout, "sequence": 1},{"txid": utxo["txid"], "vout": utxo["vout"]}],
            [{self.nodes[0].getnewaddress(): amt}, {"fee": 0.00001}],
            self.nodes[0].getblockcount()
        )

        # Set the witness script
        ctx = tx_from_hex(tx)
        ctx.wit.vtxinwit.append(CTxInWitness())
        ctx.wit.vtxinwit[0].scriptWitness.stack = [CScript([OP_TRUE]), script]
        tx = ctx.serialize_with_witness().hex()

        # Sign and send the transaction
        signed = self.nodes[0].signrawtransactionwithwallet(tx)
        assert_equal(signed["complete"], True)
        self.nodes[0].sendrawtransaction(signed["hex"])

    def test_signing_with_cltv(self):
        self.log.info("Test signing a transaction containing a fully signed CLTV input")
        self.nodes[0].walletpassphrase("password", 9999)
        getcontext().prec = 8

        # Make sure CLTV is active
        assert self.nodes[0].getdeploymentinfo()['deployments']['bip65']['active']

        # Create a P2WSH script with CLTV
        script = CScript([100, OP_CHECKLOCKTIMEVERIFY, OP_DROP])
        address = script_to_p2wsh(script)

        # Fund that address and make the spend
        txid = self.nodes[0].sendtoaddress(address, 1)
        vout = find_vout_for_address(self.nodes[0], txid, address)
        self.generate(self.nodes[0], 1, sync_fun=self.no_op)
        utxo = self.nodes[0].listunspent()[0]
        # ELEMENTS:
        # use increased Decimal precision
        # when utxo['amount'] has many decimal places (eg: 50.00005640)
        # then this 'amt' calculation would be incorrect
        # precision  8: 1 + 50.00005640 - 0.00001 = 51.000046
        # precision 10: 1 + 50.00005640 - 0.00001 = 51.00004640
        # which causes the inputs/outputs to not balance
        getcontext().prec = 10
        amt = Decimal(1) + utxo["amount"] - Decimal(0.00001)
        tx = self.nodes[0].createrawtransaction(
            [{"txid": txid, "vout": vout},{"txid": utxo["txid"], "vout": utxo["vout"]}],
            [{self.nodes[0].getnewaddress(): amt}, {"fee": 0.00001}],
            self.nodes[0].getblockcount()
        )

        # Set the witness script
        ctx = tx_from_hex(tx)
        ctx.wit.vtxinwit.append(CTxInWitness())
        ctx.wit.vtxinwit[0].scriptWitness.stack = [CScript([OP_TRUE]), script]
        tx = ctx.serialize_with_witness().hex()

        # Sign and send the transaction
        signed = self.nodes[0].signrawtransactionwithwallet(tx)
        assert_equal(signed["complete"], True)
        self.nodes[0].sendrawtransaction(signed["hex"])

    def witness_blind_pubkey_test(self):
        """Create and compare signatures in multiple ways for a valid raw transaction with one input.

        Expected results:
        1) The transaction has a complete set of signatures
        2) No script verification error occurred
        3) The signature of signrawtransactionwithwallet and
           the signature of signrawtransactionwithkey are equal.
        4) The signature of signrawtransactionwithwallet by inputs and
           the signature of signrawtransactionwithwallet by utxos are equal.
        5) The signed transaction can broadcast."""
        utxo_address = self.nodes[2].getnewaddress('', 'blech32')
        utxo_address_info = self.nodes[2].getaddressinfo(utxo_address)
        uc_addr = utxo_address_info['unconfidential']
        utxo_address_privkey = self.nodes[2].dumpprivkey(uc_addr)
        utxo_script_pk = utxo_address_info['scriptPubKey']
        utxo_amount = 0.1
        utxo_txid = self.nodes[2].sendtoaddress(utxo_address, utxo_amount)
        self.generate(self.nodes[2], 1, sync_fun=self.no_op)

        tx = self.nodes[2].getrawtransaction(utxo_txid, True)
        vout = [v['n'] for v in tx['vout'] if 'scriptPubKey' in v and uc_addr == v['scriptPubKey'].get('address',[])]
        assert len(vout) == 1
        utxo_vout = vout[0]
        assert 'valuecommitment' in tx['vout'][utxo_vout]
        utxo_amountcommitment = tx["vout"][utxo_vout]['valuecommitment']
        assert len(utxo_amountcommitment) == 66

        inputs = [{'txid': utxo_txid, 'vout': utxo_vout}]
        outputs = [{utxo_address: 0.09998}, {'fee': 0.00002}]
        raw_tx = self.nodes[2].createrawtransaction(inputs, outputs)
        raw_blindtx = self.nodes[2].blindrawtransaction(raw_tx)

        privkeys = [utxo_address_privkey]
        scripts = [
            {'txid': utxo_txid, 'vout': utxo_vout, 'scriptPubKey': utxo_script_pk,
             'amountcommitment': utxo_amountcommitment},
        ]
        signed_tx = self.nodes[2].signrawtransactionwithkey(raw_blindtx, privkeys, scripts)
        # 1) The transaction has a complete set of signatures
        assert signed_tx['complete']
        # 2) No script verification error occurred
        assert 'errors' not in signed_tx

        wallet_signed_tx = self.nodes[2].signrawtransactionwithwallet(raw_blindtx, scripts)
        assert wallet_signed_tx['complete']
        assert 'errors' not in wallet_signed_tx

        wallet_signed_tx2 = self.nodes[2].signrawtransactionwithwallet(raw_blindtx)
        assert wallet_signed_tx2['complete']
        assert 'errors' not in wallet_signed_tx2

        # 3) The signature of signrawtransactionwithwallet and
        #    the signature of signrawtransactionwithkey are equal.
        assert signed_tx['hex'] == wallet_signed_tx['hex']
        # 4) The signature of signrawtransactionwithwallet by inputs and
        #    the signature of signrawtransactionwithwallet by utxos are equal.
        assert wallet_signed_tx['hex'] == wallet_signed_tx2['hex']

        # 5) The signed transaction can broadcast.
        txid = self.nodes[2].sendrawtransaction(signed_tx['hex'])
        self.generate(self.nodes[2], 1, sync_fun=self.no_op)

        tx = self.nodes[2].getrawtransaction(txid, True)
        vout = [v['n'] for v in tx['vout'] if 'scriptPubKey' in v and uc_addr == v['scriptPubKey'].get('address',[])]
        assert len(vout) == 1

    def run_test(self):
        self.nodes[0].set_deterministic_priv_key('2Mysp7FKKe52eoC2JmU46irt1dt58TpCvhQ', 'cTNbtVJmhx75RXomhYWSZAafuNNNKPd1cr2ZiUcAeukLNGrHWjvJ')
        self.nodes[0].importprivkey("cTNbtVJmhx75RXomhYWSZAafuNNNKPd1cr2ZiUcAeukLNGrHWjvJ")

        self.successful_signing_test()
        self.script_verification_error_test()
        self.witness_script_test()
        self.OP_1NEGATE_test()
        self.test_with_lock_outputs()
        self.test_fully_signed_tx()
        self.test_signing_with_csv()
        self.test_signing_with_cltv()

        # Blinded descriptors not supported yet
        if not self.options.descriptors:
            self.witness_blind_pubkey_test()


if __name__ == '__main__':
    SignRawTransactionsTest().main()
