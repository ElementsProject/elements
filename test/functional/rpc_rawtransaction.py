#!/usr/bin/env python3
# Copyright (c) 2014-2022 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test the rawtransaction RPCs.

Test the following RPCs:
   - getrawtransaction
   - createrawtransaction
   - signrawtransactionwithwallet
   - sendrawtransaction
   - decoderawtransaction
"""

from decimal import Decimal
from itertools import product
from typing import Dict

from test_framework.messages import (
    MAX_BIP125_RBF_SEQUENCE,
    COIN,
    CTransaction,
    CTxOut,
    tx_from_hex,
)
from test_framework.script import (
    CScript,
    OP_FALSE,
    OP_INVALIDOPCODE,
    OP_RETURN,
)
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    assert_raises_rpc_error,
)
from test_framework.wallet import (
    getnewdestination,
    MiniWallet,
)


TXID = "1d1d4e24ed99057e84c3f80fd8fbec79ed9e1acee37da269356ecea000000000"


class multidict(dict):
    """Dictionary that allows duplicate keys.

    Constructed with a list of (key, value) tuples. When dumped by the json module,
    will output invalid json with repeated keys, eg:
    >>> json.dumps(multidict([(1,2),(1,2)])
    '{"1": 2, "1": 2}'

    Used to test calls to rpc methods with repeated keys in the json object."""

    def __init__(self, x):
        dict.__init__(self, x)
        self.x = x

    def items(self):
        return self.x


class RawTransactionsTest(BitcoinTestFramework):
    def add_options(self, parser):
        self.add_wallet_options(parser, descriptors=False)

    def set_test_params(self):
        self.num_nodes = 3
        self.extra_args = [
            ["-txindex"],
            ["-txindex"],
            [],
        ]
        # whitelist all peers to speed up tx relay / mempool sync
        for args in self.extra_args:
            args.append("-whitelist=noban@127.0.0.1")
        self.supports_cli = False

    def setup_network(self):
        super().setup_network()
        self.connect_nodes(0, 2)

    def run_test(self):
        self.wallet = MiniWallet(self.nodes[0])

        self.getrawtransaction_tests()
        self.getrawtransaction_verbosity_tests()
        self.createrawtransaction_tests()
        self.sendrawtransaction_tests()
        self.sendrawtransaction_testmempoolaccept_tests()
        self.decoderawtransaction_tests()
        self.transaction_version_number_tests()
        if self.is_specified_wallet_compiled() and not self.options.descriptors:
            self.import_deterministic_coinbase_privkeys()
            self.raw_multisig_transaction_legacy_tests()

    def getrawtransaction_tests(self):
        tx = self.wallet.send_self_transfer(from_node=self.nodes[0])
        self.generate(self.nodes[0], 1)
        txId = tx['txid']
        err_msg = (
            "No such mempool transaction. Use -txindex or provide a block hash to enable"
            " blockchain transaction queries. Use gettransaction for wallet transactions."
        )

        for n in [0, 2]:
            self.log.info(f"Test getrawtransaction {'with' if n == 0 else 'without'} -txindex")

            if n == 0:
                # With -txindex.
                # 1. valid parameters - only supply txid
                assert_equal(self.nodes[n].getrawtransaction(txId), tx['hex'])

                # 2. valid parameters - supply txid and 0 for non-verbose
                assert_equal(self.nodes[n].getrawtransaction(txId, 0), tx['hex'])

                # 3. valid parameters - supply txid and False for non-verbose
                assert_equal(self.nodes[n].getrawtransaction(txId, False), tx['hex'])

                # 4. valid parameters - supply txid and 1 for verbose.
                # We only check the "hex" field of the output so we don't need to update this test every time the output format changes.
                assert_equal(self.nodes[n].getrawtransaction(txId, 1)["hex"], tx['hex'])
                assert_equal(self.nodes[n].getrawtransaction(txId, 2)["hex"], tx['hex'])

                # 5. valid parameters - supply txid and True for non-verbose
                assert_equal(self.nodes[n].getrawtransaction(txId, True)["hex"], tx['hex'])
            else:
                # Without -txindex, expect to raise.
                for verbose in [None, 0, False, 1, True]:
                    assert_raises_rpc_error(-5, err_msg, self.nodes[n].getrawtransaction, txId, verbose)

            # 6. invalid parameters - supply txid and invalid boolean values (strings) for verbose
            for value in ["True", "False"]:
                assert_raises_rpc_error(-3, "not of expected type number", self.nodes[n].getrawtransaction, txid=txId, verbose=value)
                assert_raises_rpc_error(-3, "not of expected type number", self.nodes[n].getrawtransaction, txid=txId, verbosity=value)

            # 7. invalid parameters - supply txid and empty array
            assert_raises_rpc_error(-3, "not of expected type number", self.nodes[n].getrawtransaction, txId, [])

            # 8. invalid parameters - supply txid and empty dict
            assert_raises_rpc_error(-3, "not of expected type number", self.nodes[n].getrawtransaction, txId, {})

        # Make a tx by sending, then generate 2 blocks; block1 has the tx in it
        tx = self.wallet.send_self_transfer(from_node=self.nodes[2])['txid']
        block1, block2 = self.generate(self.nodes[2], 2)
        for n in [0, 2]:
            self.log.info(f"Test getrawtransaction {'with' if n == 0 else 'without'} -txindex, with blockhash")
            # We should be able to get the raw transaction by providing the correct block
            gottx = self.nodes[n].getrawtransaction(txid=tx, verbose=True, blockhash=block1)
            assert_equal(gottx['txid'], tx)
            assert_equal(gottx['in_active_chain'], True)
            if n == 0:
                self.log.info("Test getrawtransaction with -txindex, without blockhash: 'in_active_chain' should be absent")
                for v in [1,2]:
                    gottx = self.nodes[n].getrawtransaction(txid=tx, verbosity=v)
                    assert_equal(gottx['txid'], tx)
                    assert 'in_active_chain' not in gottx
            else:
                self.log.info("Test getrawtransaction without -txindex, without blockhash: expect the call to raise")
                assert_raises_rpc_error(-5, err_msg, self.nodes[n].getrawtransaction, txid=tx, verbose=True)
            # We should not get the tx if we provide an unrelated block
            assert_raises_rpc_error(-5, "No such transaction found", self.nodes[n].getrawtransaction, txid=tx, blockhash=block2)
            # An invalid block hash should raise the correct errors
            assert_raises_rpc_error(-3, "JSON value of type bool is not of expected type string", self.nodes[n].getrawtransaction, txid=tx, blockhash=True)
            assert_raises_rpc_error(-8, "parameter 3 must be of length 64 (not 6, for 'foobar')", self.nodes[n].getrawtransaction, txid=tx, blockhash="foobar")
            assert_raises_rpc_error(-8, "parameter 3 must be of length 64 (not 8, for 'abcd1234')", self.nodes[n].getrawtransaction, txid=tx, blockhash="abcd1234")
            foo = "ZZZ0000000000000000000000000000000000000000000000000000000000000"
            assert_raises_rpc_error(-8, f"parameter 3 must be hexadecimal string (not '{foo}')", self.nodes[n].getrawtransaction, txid=tx, blockhash=foo)
            bar = "0000000000000000000000000000000000000000000000000000000000000000"
            assert_raises_rpc_error(-5, "Block hash not found", self.nodes[n].getrawtransaction, txid=tx, blockhash=bar)
            # Undo the blocks and verify that "in_active_chain" is false.
            self.nodes[n].invalidateblock(block1)
            gottx = self.nodes[n].getrawtransaction(txid=tx, verbose=True, blockhash=block1)
            assert_equal(gottx['in_active_chain'], False)
            self.nodes[n].reconsiderblock(block1)
            assert_equal(self.nodes[n].getbestblockhash(), block2)

        self.log.info("Test getrawtransaction on genesis block coinbase returns an error")
        block = self.nodes[0].getblock(self.nodes[0].getblockhash(0))
        assert_raises_rpc_error(-5, "The genesis block coinbase is not considered an ordinary transaction", self.nodes[0].getrawtransaction, block['merkleroot'])

    def getrawtransaction_verbosity_tests(self):
        tx = self.wallet.send_self_transfer(from_node=self.nodes[1])['txid']
        [block1] = self.generate(self.nodes[1], 1)
        fields = [
            'blockhash',
            'blocktime',
            'confirmations',
            'hash',
            'hex',
            'in_active_chain',
            'locktime',
            'size',
            'time',
            'txid',
            'vin',
            'vout',
            'vsize',
            'weight',
        ]
        prevout_fields = [
            'generated',
            'height',
            'value',
            'scriptPubKey',
        ]
        script_pub_key_fields = [
            'address',
            'asm',
            'hex',
            'type',
        ]
        # node 0 & 2 with verbosity 1 & 2
        for n, v in product([0, 2], [1, 2]):
            self.log.info(f"Test getrawtransaction_verbosity {v} {'with' if n == 0 else 'without'} -txindex, with blockhash")
            gottx = self.nodes[n].getrawtransaction(txid=tx, verbosity=v, blockhash=block1)
            missing_fields = set(fields).difference(gottx.keys())
            if missing_fields:
                raise AssertionError(f"fields {', '.join(missing_fields)} are not in transaction")

            assert len(gottx['vin']) > 0
            if v == 1:
                # assert 'fee' not in gottx # ELEMENTS: our verbose=1 does include fee
                assert 'prevout' not in gottx['vin'][0]
            if v == 2:
                assert isinstance(gottx['fee'], Dict) # ELEMENTS: our fee instance is a map
                assert 'prevout' in gottx['vin'][0]
                prevout = gottx['vin'][0]['prevout']
                script_pub_key = prevout['scriptPubKey']

                missing_fields = set(prevout_fields).difference(prevout.keys())
                if missing_fields:
                    raise AssertionError(f"fields {', '.join(missing_fields)} are not in transaction")

                missing_fields = set(script_pub_key_fields).difference(script_pub_key.keys())
                if missing_fields:
                    raise AssertionError(f"fields {', '.join(missing_fields)} are not in transaction")

        # check verbosity 2 without blockhash but with txindex
        assert 'fee' in self.nodes[0].getrawtransaction(txid=tx, verbosity=2)
        # check that coinbase has no fee or does not throw any errors for verbosity 2
        coin_base = self.nodes[1].getblock(block1)['tx'][0]
        gottx = self.nodes[1].getrawtransaction(txid=coin_base, verbosity=2, blockhash=block1)
        assert_equal(gottx['fee'], {}) # ELEMENTS: we always have a fee object

    def createrawtransaction_tests(self):
        self.log.info("Test createrawtransaction")
        # Test `createrawtransaction` required parameters
        assert_raises_rpc_error(-1, "createrawtransaction", self.nodes[0].createrawtransaction)
        assert_raises_rpc_error(-1, "createrawtransaction", self.nodes[0].createrawtransaction, [])

        # Test `createrawtransaction` invalid extra parameters
        # ELEMENTS: we have extra elements arguments
        assert_raises_rpc_error(-1, "createrawtransaction", self.nodes[0].createrawtransaction, [], [], 0, False, 'foo')

        # Test `createrawtransaction` invalid `inputs`
        assert_raises_rpc_error(-3, "JSON value of type string is not of expected type array", self.nodes[0].createrawtransaction, 'foo', [])
        assert_raises_rpc_error(-3, "JSON value of type string is not of expected type object", self.nodes[0].createrawtransaction, ['foo'], [])
        assert_raises_rpc_error(-3, "JSON value of type null is not of expected type string", self.nodes[0].createrawtransaction, [{}], [])
        assert_raises_rpc_error(-8, "txid must be of length 64 (not 3, for 'foo')", self.nodes[0].createrawtransaction, [{'txid': 'foo'}], [])
        txid = "ZZZ7bb8b1697ea987f3b223ba7819250cae33efacb068d23dc24859824a77844"
        assert_raises_rpc_error(-8, f"txid must be hexadecimal string (not '{txid}')", self.nodes[0].createrawtransaction, [{'txid': txid, 'vout': 0}], [{}])
        # ELEMENTS: these are rejected because txid is not hex
        # assert_raises_rpc_error(-8, "Invalid parameter, missing vout key", self.nodes[0].createrawtransaction, [{'txid': txid}], [])
        # assert_raises_rpc_error(-8, "Invalid parameter, missing vout key", self.nodes[0].createrawtransaction, [{'txid': txid, 'vout': 'foo'}], [])
        # assert_raises_rpc_error(-8, "Invalid parameter, vout cannot be negative", self.nodes[0].createrawtransaction, [{'txid': txid, 'vout': -1}], [])
        # sequence number out of range
        for invalid_seq in [-1, 4294967296]:
            inputs = [{'txid': TXID, 'vout': 1, 'sequence': invalid_seq}]
            address = getnewdestination()[2]
            outputs = [{address: 1}]
            assert_raises_rpc_error(-8, 'Invalid parameter, sequence number is out of range',
                                    self.nodes[0].createrawtransaction, inputs, outputs)
        # with valid sequence number
        for valid_seq in [1000, 4294967294]:
            inputs = [{'txid': TXID, 'vout': 1, 'sequence': valid_seq}]
            address = getnewdestination()[2]
            outputs = [{address: 1}]
            rawtx = self.nodes[0].createrawtransaction(inputs, outputs)
            decrawtx = self.nodes[0].decoderawtransaction(rawtx)
            assert_equal(decrawtx['vin'][0]['sequence'], valid_seq)

        # Test `createrawtransaction` invalid `outputs`
        address = getnewdestination()[2]
        # assert_raises_rpc_error(-3, "JSON value of type string is not of expected type array", self.nodes[0].createrawtransaction, [], 'foo') # ELEMENTS: expects array
        # self.nodes[0].createrawtransaction(inputs=[], outputs={})  # Should not throw for backwards compatibility # ELEMENTS: n/a
        self.nodes[0].createrawtransaction(inputs=[], outputs=[])
        assert_raises_rpc_error(-8, "Data must be hexadecimal string", self.nodes[0].createrawtransaction, [], [{'data': 'foo'}])
        assert_raises_rpc_error(-5, "Invalid Bitcoin address", self.nodes[0].createrawtransaction, [], [{'foo': 0}])
        assert_raises_rpc_error(-3, "Invalid amount", self.nodes[0].createrawtransaction, [], [{address: 'foo'}])
        assert_raises_rpc_error(-3, "Amount out of range", self.nodes[0].createrawtransaction, [], [{address: -1}])
        # assert_raises_rpc_error(-8, "Invalid parameter, duplicated address: %s" % address, self.nodes[0].createrawtransaction, [], multidict([(address, 1), (address, 1)])) # ELEMENTS: n/a
        assert_raises_rpc_error(-8, "Invalid parameter, duplicated address: %s" % address, self.nodes[0].createrawtransaction, [], [{address: 1}, {address: 1}])
        assert_raises_rpc_error(-8, "Invalid parameter, duplicate key: data", self.nodes[0].createrawtransaction, [], [{"data": 'aa'}, {"data": "bb"}])
        assert_raises_rpc_error(-3, "JSON value of type array is not of expected type object", self.nodes[0].createrawtransaction, [], [['key-value pair1'], ['2']])

        # Test `createrawtransaction` mismatch between sequence number(s) and `replaceable` option
        assert_raises_rpc_error(-8, "Invalid parameter combination: Sequence number(s) contradict replaceable option",
                                self.nodes[0].createrawtransaction, [{'txid': TXID, 'vout': 0, 'sequence': MAX_BIP125_RBF_SEQUENCE+1}], [{}], 0, True)

        # Test `createrawtransaction` invalid `locktime`
        assert_raises_rpc_error(-3, "JSON value of type string is not of expected type number", self.nodes[0].createrawtransaction, [], [], 'foo')
        assert_raises_rpc_error(-8, "Invalid parameter, locktime out of range", self.nodes[0].createrawtransaction, [], [], -1)
        assert_raises_rpc_error(-8, "Invalid parameter, locktime out of range", self.nodes[0].createrawtransaction, [], [], 4294967296)

        # Test `createrawtransaction` invalid `replaceable`
        assert_raises_rpc_error(-3, "JSON value of type string is not of expected type bool", self.nodes[0].createrawtransaction, [], [], 0, 'foo')

        # Test that createrawtransaction accepts an array and object as outputs
        # One output
        tx = tx_from_hex(self.nodes[2].createrawtransaction(inputs=[{'txid': TXID, 'vout': 9}], outputs=[{address: 99}]))
        assert_equal(len(tx.vout), 1)
        assert_equal(
            tx.serialize().hex(),
            self.nodes[2].createrawtransaction(inputs=[{'txid': TXID, 'vout': 9}], outputs=[{address: 99}]),
        )
        # Two outputs
        address2 = getnewdestination()[2]
        tx = tx_from_hex(self.nodes[2].createrawtransaction(inputs=[{'txid': TXID, 'vout': 9}], outputs=[{address: 99}, {address2: 99}]))
        assert_equal(len(tx.vout), 2)
        assert_equal(
            tx.serialize().hex(),
            self.nodes[2].createrawtransaction(inputs=[{'txid': TXID, 'vout': 9}], outputs=[{address: 99}, {address2: 99}]),
        )
        # Multiple mixed outputs
        tx = tx_from_hex(self.nodes[2].createrawtransaction(inputs=[{'txid': TXID, 'vout': 9}], outputs=[{address: 99}, {address2: 99}, {'data': '99'}]))
        assert_equal(len(tx.vout), 3)
        assert_equal(
            tx.serialize().hex(),
            self.nodes[2].createrawtransaction(inputs=[{'txid': TXID, 'vout': 9}], outputs=[{address: 99}, {address2: 99}, {'data': '99'}]),
        )

    def sendrawtransaction_tests(self):
        self.log.info('Test sendrawtransaction with missing input')
        inputs  = [ {'txid' : "1d1d4e24ed99057e84c3f80fd8fbec79ed9e1acee37da269356ecea000000000", 'vout' : 1}] #won't exists
        address = getnewdestination()[2]
        outputs = [{address: 4.998}]
        rawtx = self.nodes[2].createrawtransaction(inputs, outputs)
        assert_raises_rpc_error(-25, "bad-txns-inputs-missingorspent", self.nodes[2].sendrawtransaction, rawtx)

        self.log.info("Test sendrawtransaction exceeding, falling short of, and equaling maxburnamount")
        max_burn_exceeded = "Unspendable output exceeds maximum configured by user (maxburnamount)"


        # Test that spendable transaction with default maxburnamount (0) gets sent
        tx = self.wallet.create_self_transfer()['tx']
        tx_hex = tx.serialize().hex()
        self.nodes[2].sendrawtransaction(hexstring=tx_hex)

        # Test that datacarrier transaction with default maxburnamount (0) does not get sent
        tx = self.wallet.create_self_transfer()['tx']
        tx_val = 0.001
        tx.vout = [CTxOut(int(Decimal(tx_val) * COIN), CScript([OP_RETURN] + [OP_FALSE] * 30))]
        tx_hex = tx.serialize().hex()
        assert_raises_rpc_error(-25, max_burn_exceeded, self.nodes[2].sendrawtransaction, tx_hex)

        # Test that oversized script gets rejected by sendrawtransaction
        tx = self.wallet.create_self_transfer()['tx']
        tx_val = 0.001
        tx.vout = [CTxOut(int(Decimal(tx_val) * COIN), CScript([OP_FALSE] * 10001))]
        tx_hex = tx.serialize().hex()
        assert_raises_rpc_error(-25, max_burn_exceeded, self.nodes[2].sendrawtransaction, tx_hex)

        # Test that script containing invalid opcode gets rejected by sendrawtransaction
        tx = self.wallet.create_self_transfer()['tx']
        tx_val = 0.01
        tx.vout = [CTxOut(int(Decimal(tx_val) * COIN), CScript([OP_INVALIDOPCODE]))]
        tx_hex = tx.serialize().hex()
        assert_raises_rpc_error(-25, max_burn_exceeded, self.nodes[2].sendrawtransaction, tx_hex)

        # Test a transaction where our burn exceeds maxburnamount
        tx = self.wallet.create_self_transfer()['tx']
        tx_val = 0.001
        tx.vout = [CTxOut(int(Decimal(tx_val) * COIN), CScript([OP_RETURN] + [OP_FALSE] * 30))]
        tx_hex = tx.serialize().hex()
        assert_raises_rpc_error(-25, max_burn_exceeded, self.nodes[2].sendrawtransaction, tx_hex, 0, 0.0009)

        # Test a transaction where our burn falls short of maxburnamount
        tx = self.wallet.create_self_transfer()['tx']
        tx_val = 0.001
        tx.vout = [CTxOut(int(Decimal(tx_val) * COIN), CScript([OP_RETURN] + [OP_FALSE] * 30))]
        tx_hex = tx.serialize().hex()
        assert_raises_rpc_error(-26, "bad-txns-in-ne-out", self.nodes[2].sendrawtransaction, tx_hex, 0, 0.0011)

        # Test a transaction where our burn equals maxburnamount
        tx = self.wallet.create_self_transfer()['tx']
        tx_val = 0.001
        tx.vout = [CTxOut(int(Decimal(tx_val) * COIN), CScript([OP_RETURN] + [OP_FALSE] * 30))]
        tx_hex = tx.serialize().hex()
        assert_raises_rpc_error(-26, "bad-txns-in-ne-out", self.nodes[2].sendrawtransaction, tx_hex, 0, 0.001)

    def sendrawtransaction_testmempoolaccept_tests(self):
        self.log.info("Test sendrawtransaction/testmempoolaccept with maxfeerate")
        fee_exceeds_max = "Fee exceeds maximum configured by user (e.g. -maxtxfee, maxfeerate)"

        # Test a transaction with a small fee.
        # Fee rate is 0.00100000 BTC/kvB
        tx = self.wallet.create_self_transfer(fee_rate=Decimal('0.00100000'))
        # Thus, testmempoolaccept should reject
        testres = self.nodes[2].testmempoolaccept([tx['hex']], 0.00001000)[0]
        assert_equal(testres['allowed'], False)
        assert_equal(testres['reject-reason'], 'max-fee-exceeded')
        # and sendrawtransaction should throw
        assert_raises_rpc_error(-25, fee_exceeds_max, self.nodes[2].sendrawtransaction, tx['hex'], 0.00001000)
        # and the following calls should both succeed
        testres = self.nodes[2].testmempoolaccept(rawtxs=[tx['hex']])[0]
        assert_equal(testres['allowed'], True)
        self.nodes[2].sendrawtransaction(hexstring=tx['hex'])

        # Test a transaction with a large fee.
        # Fee rate is 0.20000000 BTC/kvB
        tx = self.wallet.create_self_transfer(fee_rate=Decimal("0.20000000"))
        # Thus, testmempoolaccept should reject
        testres = self.nodes[2].testmempoolaccept([tx['hex']])[0]
        assert_equal(testres['allowed'], False)
        assert_equal(testres['reject-reason'], 'max-fee-exceeded')
        # and sendrawtransaction should throw
        assert_raises_rpc_error(-25, fee_exceeds_max, self.nodes[2].sendrawtransaction, tx['hex'])
        # and the following calls should both succeed
        testres = self.nodes[2].testmempoolaccept(rawtxs=[tx['hex']], maxfeerate='0.20000000')[0]
        assert_equal(testres['allowed'], True)
        self.nodes[2].sendrawtransaction(hexstring=tx['hex'], maxfeerate='0.20000000')

        self.log.info("Test sendrawtransaction/testmempoolaccept with tx already in the chain")
        self.generate(self.nodes[2], 1)
        for node in self.nodes:
            testres = node.testmempoolaccept([tx['hex']])[0]
            assert_equal(testres['allowed'], False)
            assert_equal(testres['reject-reason'], 'txn-already-known')
            assert_raises_rpc_error(-27, 'Transaction already in block chain', node.sendrawtransaction, tx['hex'])

    def decoderawtransaction_tests(self):
        self.log.info("Test decoderawtransaction")
        # witness transaction
        # new in core:
        #encrawtx = "010000000001010000000000000072c1a6a246ae63f74f931e8365e15a089c68d61900000000000000000000ffffffff0100e1f50500000000000102616100000000"
        encrawtx = "0100000001010000000000000072c1a6a246ae63f74f931e8365e15a089c68d61900000000000000000000ffffffff0101ac2e6a47e85fdc2a5a27334544440f2f5135553a7476f4f5e3b9792da6a58fe0010000000005f5e100000000000000000001026161000000"
        decrawtx = self.nodes[0].decoderawtransaction(encrawtx, True)  # decode as witness transaction
        assert_equal(decrawtx['vout'][0]['value'], Decimal('1.00000000'))

    def transaction_version_number_tests(self):
        self.log.info("Test transaction version numbers")

        # Test the minimum transaction version number that fits in a signed 32-bit integer.
        # As transaction version is unsigned, this should convert to its unsigned equivalent.
        tx = CTransaction()
        tx.nVersion = -0x80000000
        rawtx = tx.serialize().hex()
        decrawtx = self.nodes[0].decoderawtransaction(rawtx)
        assert_equal(decrawtx['version'], 0x80000000)

        # Test the maximum transaction version number that fits in a signed 32-bit integer.
        tx = CTransaction()
        tx.nVersion = 0x7fffffff
        rawtx = tx.serialize().hex()
        decrawtx = self.nodes[0].decoderawtransaction(rawtx)
        assert_equal(decrawtx['version'], 0x7fffffff)

    def raw_multisig_transaction_legacy_tests(self):
        self.log.info("Test raw multisig transactions (legacy)")
        # The traditional multisig workflow does not work with descriptor wallets so these are legacy only.
        # The multisig workflow with descriptor wallets uses PSBTs and is tested elsewhere, no need to do them here.

        # 2of2 test
        addr1 = self.nodes[2].getnewaddress()
        addr2 = self.nodes[2].getnewaddress()

        addr1Obj = self.nodes[2].getaddressinfo(addr1)
        addr2Obj = self.nodes[2].getaddressinfo(addr2)

        # Tests for createmultisig and addmultisigaddress
        assert_raises_rpc_error(-5, "Invalid public key", self.nodes[0].createmultisig, 1, ["01020304"])
        # createmultisig can only take public keys
        self.nodes[0].createmultisig(2, [addr1Obj['pubkey'], addr2Obj['pubkey']])
        # addmultisigaddress can take both pubkeys and addresses so long as they are in the wallet, which is tested here
        assert_raises_rpc_error(-5, "Invalid public key", self.nodes[0].createmultisig, 2, [addr1Obj['pubkey'], addr1])

        mSigObj = self.nodes[2].addmultisigaddress(2, [addr1Obj['pubkey'], addr1])['address']

        # use balance deltas instead of absolute values
        bal = self.nodes[2].getbalance()

        # send 1.2 BTC to msig adr
        txId = self.nodes[0].sendtoaddress(mSigObj, 1.2)
        self.sync_all()
        self.generate(self.nodes[0], 1)
        # node2 has both keys of the 2of2 ms addr, tx should affect the balance
        assert_equal(self.nodes[2].getbalance()['bitcoin'], bal['bitcoin'] + Decimal('1.20000000'))


        # 2of3 test from different nodes
        bal = self.nodes[2].getbalance()
        addr1 = self.nodes[1].getnewaddress()
        addr2 = self.nodes[2].getnewaddress()
        addr3 = self.nodes[2].getnewaddress()

        addr1Obj = self.nodes[1].getaddressinfo(addr1)
        addr2Obj = self.nodes[2].getaddressinfo(addr2)
        addr3Obj = self.nodes[2].getaddressinfo(addr3)

        mSigObj = self.nodes[2].addmultisigaddress(2, [addr1Obj['pubkey'], addr2Obj['pubkey'], addr3Obj['pubkey']])['address']

        txId = self.nodes[0].sendtoaddress(mSigObj, 2.2)
        decTx = self.nodes[0].gettransaction(txId)
        rawTx = self.nodes[0].decoderawtransaction(decTx['hex'])
        self.sync_all()
        self.generate(self.nodes[0], 1)

        # THIS IS AN INCOMPLETE FEATURE
        # NODE2 HAS TWO OF THREE KEYS AND THE FUNDS SHOULD BE SPENDABLE AND COUNT AT BALANCE CALCULATION
        assert_equal(self.nodes[2].getbalance(), bal)  # for now, assume the funds of a 2of3 multisig tx are not marked as spendable

        txDetails = self.nodes[0].gettransaction(txId, True)
        rawTx = self.nodes[0].decoderawtransaction(txDetails['hex'])
        vout = next(o for o in rawTx['vout'] if o['value'] == Decimal('2.20000000'))

        bal = self.nodes[0].getbalance()
        inputs = [{"txid": txId, "vout": vout['n'], "scriptPubKey": vout['scriptPubKey']['hex'], "amount": vout['value']}]
        outputs = [{self.nodes[0].getnewaddress(): 2.19}, {"fee": 0.01}]
        rawTx = self.nodes[2].createrawtransaction(inputs, outputs)
        rawTxPartialSigned = self.nodes[1].signrawtransactionwithwallet(rawTx, inputs)
        assert_equal(rawTxPartialSigned['complete'], False)  # node1 only has one key, can't comp. sign the tx

        rawTxSigned = self.nodes[2].signrawtransactionwithwallet(rawTx, inputs)
        assert_equal(rawTxSigned['complete'], True)  # node2 can sign the tx compl., own two of three keys
        self.nodes[2].sendrawtransaction(rawTxSigned['hex'])
        rawTx = self.nodes[0].decoderawtransaction(rawTxSigned['hex'])
        self.sync_all()
        self.generate(self.nodes[0], 1)
        assert_equal(self.nodes[0].getbalance()['bitcoin'], bal['bitcoin'] + Decimal('50.00000000') + Decimal('2.19000000'))  # block reward + tx

        # 2of2 test for combining transactions
        bal = self.nodes[2].getbalance()
        addr1 = self.nodes[1].getnewaddress()
        addr2 = self.nodes[2].getnewaddress()

        addr1Obj = self.nodes[1].getaddressinfo(addr1)
        addr2Obj = self.nodes[2].getaddressinfo(addr2)

        self.nodes[1].addmultisigaddress(2, [addr1Obj['pubkey'], addr2Obj['pubkey']])['address']
        mSigObj = self.nodes[2].addmultisigaddress(2, [addr1Obj['pubkey'], addr2Obj['pubkey']])['address']
        mSigObjValid = self.nodes[2].getaddressinfo(mSigObj)

        txId = self.nodes[0].sendtoaddress(mSigObj, 2.2)
        decTx = self.nodes[0].gettransaction(txId)
        rawTx2 = self.nodes[0].decoderawtransaction(decTx['hex'])
        self.sync_all()
        self.generate(self.nodes[0], 1)

        assert_equal(self.nodes[2].getbalance(), bal)  # the funds of a 2of2 multisig tx should not be marked as spendable

        txDetails = self.nodes[0].gettransaction(txId, True)
        rawTx2 = self.nodes[0].decoderawtransaction(txDetails['hex'])
        vout = next(o for o in rawTx2['vout'] if o['value'] == Decimal('2.20000000'))

        bal = self.nodes[0].getbalance()
        inputs = [{"txid": txId, "vout": vout['n'], "scriptPubKey": vout['scriptPubKey']['hex'], "redeemScript": mSigObjValid['hex'], "amount": vout['value']}]
        outputs = [{self.nodes[0].getnewaddress(): 2.19}, {"fee": 0.01}]
        rawTx2 = self.nodes[2].createrawtransaction(inputs, outputs)
        rawTxPartialSigned1 = self.nodes[1].signrawtransactionwithwallet(rawTx2, inputs)
        self.log.debug(rawTxPartialSigned1)
        assert_equal(rawTxPartialSigned1['complete'], False)  # node1 only has one key, can't comp. sign the tx

        rawTxPartialSigned2 = self.nodes[2].signrawtransactionwithwallet(rawTx2, inputs)
        self.log.debug(rawTxPartialSigned2)
        assert_equal(rawTxPartialSigned2['complete'], False)  # node2 only has one key, can't comp. sign the tx
        rawTxComb = self.nodes[2].combinerawtransaction([rawTxPartialSigned1['hex'], rawTxPartialSigned2['hex']])
        self.log.debug(rawTxComb)
        self.nodes[2].sendrawtransaction(rawTxComb)
        rawTx2 = self.nodes[0].decoderawtransaction(rawTxComb)
        self.sync_all()
        self.generate(self.nodes[0], 1)
        assert_equal(self.nodes[0].getbalance()['bitcoin'], bal['bitcoin'] + Decimal('50.00000000') + Decimal('2.19000000'))  # block reward + tx


if __name__ == '__main__':
    RawTransactionsTest().main()
