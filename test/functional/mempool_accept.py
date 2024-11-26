#!/usr/bin/env python3
# Copyright (c) 2017-2021 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test mempool acceptance of raw transactions."""

from copy import deepcopy
from decimal import Decimal
import math

from test_framework.test_framework import BitcoinTestFramework
from test_framework.key import ECKey
from test_framework.messages import (
    MAX_BIP125_RBF_SEQUENCE,
    COIN,
    COutPoint,
    CTxIn,
    CTxOut,
    CTxOutValue,
    MAX_BLOCK_WEIGHT,
    MAX_MONEY,
    SEQUENCE_FINAL,
    tx_from_hex,
)
from test_framework.script import (
    CScript,
    OP_0,
    OP_HASH160,
    OP_RETURN,
)
from test_framework.script_util import (
    keys_to_multisig_script,
    script_to_p2sh_script,
)
from test_framework.util import (
    assert_equal,
    assert_raises_rpc_error,
)
from test_framework.wallet import MiniWallet


class MempoolAcceptanceTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 1
        self.extra_args = [[
            '-txindex',
            '-txindex','-permitbaremultisig=0',
            '-multi_data_permitted=1', # Elements test
        ]] * self.num_nodes
        self.supports_cli = False

    def check_mempool_result(self, result_expected, *args, **kwargs):
        """Wrapper to check result of testmempoolaccept on node_0's mempool"""
        result_test = self.nodes[0].testmempoolaccept(*args, **kwargs)
        for r in result_test:
            r.pop('wtxid')  # Skip check for now
        assert_equal(result_expected, result_test)
        assert_equal(self.nodes[0].getmempoolinfo()['size'], self.mempool_size)  # Must not change mempool state

    def run_test(self):
        node = self.nodes[0]
        self.wallet = MiniWallet(node)
        self.wallet.rescan_utxos()

        self.log.info('Start with empty mempool, and 200 blocks')
        self.mempool_size = 0
        assert_equal(node.getblockcount(), 200)
        assert_equal(node.getmempoolinfo()['size'], self.mempool_size)

        self.log.info('Should not accept garbage to testmempoolaccept')
        assert_raises_rpc_error(-3, 'JSON value of type string is not of expected type array', lambda: node.testmempoolaccept(rawtxs='ff00baar'))
        assert_raises_rpc_error(-8, 'Array must contain between 1 and 25 transactions.', lambda: node.testmempoolaccept(rawtxs=['ff22']*26))
        assert_raises_rpc_error(-8, 'Array must contain between 1 and 25 transactions.', lambda: node.testmempoolaccept(rawtxs=[]))
        assert_raises_rpc_error(-22, 'TX decode failed', lambda: node.testmempoolaccept(rawtxs=['ff00baar']))

        self.log.info('A transaction already in the blockchain')
        tx = self.wallet.create_self_transfer()['tx']  # Pick a random coin(base) to spend
        tx.vout.append(deepcopy(tx.vout[0]))
        tx.vout[0].nValue.setToAmount(int(0.3 * COIN))
        tx.vout[1].nValue.setToAmount(int(0.7 * COIN)) # ELEMENTS: fee
        tx.vout[2].nValue.setToAmount(int(49 * COIN))
        raw_tx_in_block = tx.serialize().hex()
        txid_in_block = self.wallet.sendrawtransaction(from_node=node, tx_hex=raw_tx_in_block)
        self.generate(node, 1)
        self.mempool_size = 0
        self.check_mempool_result(
            result_expected=[{'txid': txid_in_block, 'allowed': False, 'reject-reason': 'txn-already-known'}],
            rawtxs=[raw_tx_in_block],
        )

        self.log.info('A transaction not in the mempool')
        fee = Decimal('0.000007')
        utxo_to_spend = self.wallet.get_utxo(txid=txid_in_block)  # use 0.3 BTC UTXO
        tx = self.wallet.create_self_transfer(utxo_to_spend=utxo_to_spend, sequence=MAX_BIP125_RBF_SEQUENCE)['tx']
        tx.vout[0].nValue.setToAmount(int((Decimal('0.3') - fee) * COIN))
        tx.vout[1].nValue.setToAmount(int(fee * COIN))
        raw_tx_0 = tx.serialize().hex()
        txid_0 = tx.rehash()
        self.check_mempool_result(
            result_expected=[{'txid': txid_0, 'allowed': True, 'vsize': tx.get_vsize(), 'fees': {'base': fee}}],
            rawtxs=[raw_tx_0],
        )

        self.log.info('A final transaction not in the mempool')
        output_amount = Decimal('0.025')
        tx = self.wallet.create_self_transfer(
            sequence=SEQUENCE_FINAL,
            locktime=node.getblockcount() + 2000,  # Can be anything
        )['tx']
        fee_expected = Decimal('50.0') - output_amount
        tx.vout[0].nValue.setToAmount(int(output_amount * COIN))
        tx.vout[1].nValue.setToAmount(int(fee_expected * COIN))
        raw_tx_final = tx.serialize().hex()
        tx = tx_from_hex(raw_tx_final)
        fee_expected = Decimal('50.0') - output_amount
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': True, 'vsize': tx.get_vsize(), 'fees': {'base': fee_expected}}],
            rawtxs=[tx.serialize().hex()],
            maxfeerate=0,
        )
        node.sendrawtransaction(hexstring=raw_tx_final, maxfeerate=0)
        self.mempool_size += 1

        self.log.info('A transaction in the mempool')
        node.sendrawtransaction(hexstring=raw_tx_0)
        self.mempool_size += 1
        self.check_mempool_result(
            result_expected=[{'txid': txid_0, 'allowed': False, 'reject-reason': 'txn-already-in-mempool'}],
            rawtxs=[raw_tx_0],
        )

        self.log.info('A transaction that replaces a mempool transaction')
        tx = tx_from_hex(raw_tx_0)
        tx.vout[0].nValue.setToAmount(tx.vout[0].nValue.getAmount() - int(fee * COIN))  # Double the fee
        txid_0_out = tx.vout[0].nValue.getAmount()
        tx.vout[1].nValue.setToAmount(tx.vout[1].nValue.getAmount() + int(fee * COIN))
        tx.vin[0].nSequence = MAX_BIP125_RBF_SEQUENCE + 1  # Now, opt out of RBF
        raw_tx_0 = tx.serialize().hex()
        txid_0 = tx.rehash()
        self.check_mempool_result(
            result_expected=[{'txid': txid_0, 'allowed': True, 'vsize': tx.get_vsize(), 'fees': {'base': (2 * fee)}}],
            rawtxs=[raw_tx_0],
        )

        self.log.info('A transaction that conflicts with an unconfirmed tx')
        # Send the transaction that replaces the mempool transaction and opts out of replaceability
        node.sendrawtransaction(hexstring=tx.serialize().hex(), maxfeerate=0)
        # take original raw_tx_0
        tx = tx_from_hex(raw_tx_0)
        tx.vout[0].nValue.setToAmount(tx.vout[0].nValue.getAmount() - int(4 * fee * COIN))  # Set more fee
        tx.vout[1].nValue.setToAmount(tx.vout[1].nValue.getAmount() + int(4 * fee * COIN))
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'txn-mempool-conflict'}],
            rawtxs=[tx.serialize().hex()],
            maxfeerate=0,
        )

        self.log.info('A transaction with missing inputs, that never existed')
        tx = tx_from_hex(raw_tx_0)
        tx.vin[0].prevout = COutPoint(hash=int('ff' * 32, 16), n=14)
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'missing-inputs'}],
            rawtxs=[tx.serialize().hex()],
        )

        self.log.info('A transaction with missing inputs, that existed once in the past')
        tx = tx_from_hex(raw_tx_0)
        tx.vin[0].prevout.n = 2  # ELEMENTS: Set vout to 2, to spend the other outpoint (49 coins) of the in-chain-tx we want to double spend
        tx.vout[1].nValue.setToAmount(int(49 * COIN) - tx.vout[0].nValue.getAmount()) # ELEMENTS: balance tx
        raw_tx_1 = tx.serialize().hex()
        txid_1 = node.sendrawtransaction(hexstring=raw_tx_1, maxfeerate=0)
        txid_1_out = tx.vout[0].nValue.getAmount()
        # Now spend both to "clearly hide" the outputs, ie. remove the coins from the utxo set by spending them
        tx = self.wallet.create_self_transfer()['tx']
        tx.vin.append(deepcopy(tx.vin[0]))
        tx.wit.vtxinwit.append(deepcopy(tx.wit.vtxinwit[0]))
        tx.vin[0].prevout = COutPoint(hash=int(txid_0, 16), n=0)
        tx.vin[1].prevout = COutPoint(hash=int(txid_1, 16), n=0)
        tx.vout[0].nValue.setToAmount(int(0.1 * COIN))
        tx.vout[1].nValue.setToAmount(txid_0_out + txid_1_out - int(0.1 * COIN))
        raw_tx_spend_both = tx.serialize().hex()
        txid_spend_both = self.wallet.sendrawtransaction(from_node=node, tx_hex=raw_tx_spend_both)
        self.generate(node, 1)
        self.mempool_size = 0
        # Now see if we can add the coins back to the utxo set by sending the exact txs again
        self.check_mempool_result(
            result_expected=[{'txid': txid_0, 'allowed': False, 'reject-reason': 'missing-inputs'}],
            rawtxs=[raw_tx_0],
        )
        self.check_mempool_result(
            result_expected=[{'txid': txid_1, 'allowed': False, 'reject-reason': 'missing-inputs'}],
            rawtxs=[raw_tx_1],
        )

        self.log.info('Create a "reference" tx for later use')
        utxo_to_spend = self.wallet.get_utxo(txid=txid_spend_both)
        tx = self.wallet.create_self_transfer(utxo_to_spend=utxo_to_spend, sequence=SEQUENCE_FINAL)['tx']
        tx.vout[0].nValue.setToAmount(int(0.05 * COIN))
        tx.vout[1].nValue.setToAmount(int(utxo_to_spend['value'] * COIN - tx.vout[0].nValue.getAmount()))
        raw_tx_reference = tx.serialize().hex()
        # Reference tx should be valid on itself
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': True, 'vsize': tx.get_vsize(), 'fees': { 'base': Decimal('0.1') - Decimal('0.05')}}],
            rawtxs=[tx.serialize().hex()],
            maxfeerate=0,
        )

        self.log.info('A transaction with no outputs')
        tx = tx_from_hex(raw_tx_reference)
        tx.vout = []
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'bad-txns-vout-empty'}],
            rawtxs=[tx.serialize().hex()],
        )

        self.log.info('A really large transaction')
        tx = tx_from_hex(raw_tx_reference)
        tx.vin = [tx.vin[0]] * math.ceil(MAX_BLOCK_WEIGHT // 4 / len(tx.vin[0].serialize()))
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'bad-txns-oversize'}],
            rawtxs=[tx.serialize().hex()],
        )

        self.log.info('A transaction with negative output value')
        tx = tx_from_hex(raw_tx_reference)
        tx.vout[0].nValue.setToAmount(tx.vout[0].nValue.getAmount() * -1)
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'bad-txns-vout-negative'}],
            rawtxs=[tx.serialize().hex()],
        )

        # The following two validations prevent overflow of the output amounts (see CVE-2010-5139).
        self.log.info('A transaction with too large output value')
        tx = tx_from_hex(raw_tx_reference)
        tx.vout[0].nValue = CTxOutValue(MAX_MONEY + 1)
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'bad-txns-vout-toolarge'}],
            rawtxs=[tx.serialize().hex()],
        )

        self.log.info('A transaction with too large sum of output values')
        tx = tx_from_hex(raw_tx_reference)
        tx.vout = [tx.vout[0]] * 2
        tx.vout[0].nValue = CTxOutValue(MAX_MONEY)
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'bad-txns-txouttotal-toolarge'}],
            rawtxs=[tx.serialize().hex()],
        )

        self.log.info('A transaction with duplicate inputs')
        tx = tx_from_hex(raw_tx_reference)
        tx.vin = [tx.vin[0]] * 2
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'bad-txns-inputs-duplicate'}],
            rawtxs=[tx.serialize().hex()],
        )

        self.log.info('A non-coinbase transaction with coinbase-like outpoint')
        tx = tx_from_hex(raw_tx_reference)
        tx.vin.append(CTxIn(COutPoint(hash=0, n=0xffffffff)))
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'bad-txns-prevout-null'}],
            rawtxs=[tx.serialize().hex()],
        )

        self.log.info('A coinbase transaction')
        # Pick the input of the first tx we created, so it has to be a coinbase tx
        raw_tx_coinbase_spent = node.getrawtransaction(txid=node.decoderawtransaction(hexstring=raw_tx_in_block)['vin'][0]['txid'])
        tx = tx_from_hex(raw_tx_coinbase_spent)
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'coinbase'}],
            rawtxs=[tx.serialize().hex()],
        )

        self.log.info('Some nonstandard transactions')
        tx = tx_from_hex(raw_tx_reference)
        tx.nVersion = 3  # A version currently non-standard
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'version'}],
            rawtxs=[tx.serialize().hex()],
        )
        tx = tx_from_hex(raw_tx_reference)
        tx.vout[0].scriptPubKey = CScript([OP_0])  # Some non-standard script
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'scriptpubkey'}],
            rawtxs=[tx.serialize().hex()],
        )
        tx = tx_from_hex(raw_tx_reference)
        key = ECKey()
        key.generate()
        pubkey = key.get_pubkey().get_bytes()
        tx.vout[0].scriptPubKey = keys_to_multisig_script([pubkey] * 3, k=2)  # Some bare multisig script (2-of-3)
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'bare-multisig'}],
            rawtxs=[tx.serialize().hex()],
        )
        tx = tx_from_hex(raw_tx_reference)
        tx.vin[0].scriptSig = CScript([OP_HASH160])  # Some not-pushonly scriptSig
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'scriptsig-not-pushonly'}],
            rawtxs=[tx.serialize().hex()],
        )
        tx = tx_from_hex(raw_tx_reference)
        tx.vin[0].scriptSig = CScript([b'a' * 1648]) # Some too large scriptSig (>1650 bytes)
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'scriptsig-size'}],
            rawtxs=[tx.serialize().hex()],
        )
        tx = tx_from_hex(raw_tx_reference)
        output_p2sh_burn = CTxOut(nValue=540, scriptPubKey=script_to_p2sh_script(b'burn'))
        num_scripts = 100000 // len(output_p2sh_burn.serialize())  # Use enough outputs to make the tx too large for our policy
        tx.vout = [output_p2sh_burn] * num_scripts
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'tx-size'}],
            rawtxs=[tx.serialize().hex()],
        )
        tx = tx_from_hex(raw_tx_reference)
        tx.vout[0] = output_p2sh_burn
        tx.vout[0].nValue.setToAmount(tx.vout[0].nValue.getAmount() - 1)  # Make output smaller, such that it is dust for our policy
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'dust'}],
            rawtxs=[tx.serialize().hex()],
        )
        # Elements: We allow multi op_return outputs by default. This still fails because relay fee isn't met
        tx = tx_from_hex(raw_tx_reference)
        tx.vout[0].scriptPubKey = CScript([OP_RETURN, b'\xff'])
        tx.vout = [tx.vout[0]] * 2
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'min relay fee not met'}],
            rawtxs=[tx.serialize().hex()],
        )

        self.log.info('A timelocked transaction')
        tx = tx_from_hex(raw_tx_reference)
        tx.vin[0].nSequence -= 1  # Should be non-max, so locktime is not ignored
        tx.nLockTime = node.getblockcount() + 1
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'non-final'}],
            rawtxs=[tx.serialize().hex()],
        )

        self.log.info('A transaction that is locked by BIP68 sequence logic')
        tx = tx_from_hex(raw_tx_reference)
        tx.vin[0].nSequence = 2  # We could include it in the second block mined from now, but not the very next one
        self.check_mempool_result(
            result_expected=[{'txid': tx.rehash(), 'allowed': False, 'reject-reason': 'non-BIP68-final'}],
            rawtxs=[tx.serialize().hex()],
            maxfeerate=0,
        )


if __name__ == '__main__':
    MempoolAcceptanceTest().main()
