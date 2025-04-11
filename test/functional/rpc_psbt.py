#!/usr/bin/env python3
# Copyright (c) 2018-2022 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test the Partially Signed Transaction RPCs.
"""
from decimal import Decimal
from itertools import product

from test_framework.descriptors import descsum_create
from test_framework.key import ECKey, H_POINT
from test_framework.messages import (
    # COutPoint,
    # CTransaction,
    # CTxIn,
    # CTxOut,
    MAX_BIP125_RBF_SEQUENCE,
    WITNESS_SCALE_FACTOR,
    ser_compact_size,
)
from test_framework.psbt import (
    PSBT,
    PSBTMap,
    PSBT_GLOBAL_UNSIGNED_TX,
    PSBT_IN_RIPEMD160,
    PSBT_IN_SHA256,
    PSBT_IN_HASH160,
    PSBT_IN_HASH256,
    PSBT_IN_NON_WITNESS_UTXO,
    PSBT_IN_WITNESS_UTXO,
    PSBT_OUT_TAP_TREE,
)
from test_framework.script import CScript, OP_TRUE
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    # assert_approx,
    assert_equal,
    assert_greater_than,
    assert_greater_than_or_equal,
    assert_raises_rpc_error,
    find_output,
    find_vout_for_address,
    # random_bytes,
)
from test_framework.wallet_util import bytes_to_wif

# These imports are used by commented-out tests.
"""
import json
import os
"""


# Utility function to extract info from outputs for use in assert_equal
# Returns a set of tuples (address, is blinded, is OP_RETURN). (It would
# feel nicer to return a set of dicts, but you can't do that in Python.)
def outputs_info(outputs):
    return {(
        x["script"].get("address"),
        x.get("blinding_pubkey") is not None,
        x["script"]["asm"] == "OP_RETURN",
    ) for x in outputs}


class PSBTTest(BitcoinTestFramework):
    def add_options(self, parser):
        self.add_wallet_options(parser)

    def set_test_params(self):
        self.num_nodes = 3
        self.extra_args = [
            ["-walletrbf=1", "-addresstype=bech32", "-changetype=bech32"], #TODO: Remove address type restrictions once taproot has psbt extensions
            ["-walletrbf=0", "-changetype=legacy"],
            []
        ]
        # whitelist peers to speed up tx relay / mempool sync
        for args in self.extra_args:
            args.append("-whitelist=noban@127.0.0.1")
        self.supports_cli = False

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def test_utxo_conversion(self):
        self.log.info("Check that non-witness UTXOs are removed for segwit v1+ inputs")
        mining_node = self.nodes[2]
        offline_node = self.nodes[0]
        online_node = self.nodes[1]

        # Disconnect offline node from others
        # Topology of test network is linear, so this one call is enough
        self.disconnect_nodes(0, 1)

        # Create watchonly on online_node
        online_node.createwallet(wallet_name='wonline', disable_private_keys=True)
        wonline = online_node.get_wallet_rpc('wonline')
        w2 = online_node.get_wallet_rpc(self.default_wallet_name)

        # Mine a transaction that credits the offline address
        offline_addr = offline_node.getnewaddress(address_type="bech32m")
        online_addr = w2.getnewaddress(address_type="bech32m")
        wonline.importaddress(offline_addr, "", False)
        mining_wallet = mining_node.get_wallet_rpc(self.default_wallet_name)
        mining_wallet.sendtoaddress(address=offline_addr, amount=1.0)
        self.generate(mining_node, nblocks=1, sync_fun=lambda: self.sync_all([online_node, mining_node]))

        # Construct an unsigned PSBT on the online node
        utxos = wonline.listunspent(addresses=[offline_addr])
        raw = wonline.createrawtransaction([{"txid":utxos[0]["txid"], "vout":utxos[0]["vout"]}],[{online_addr:0.9999},{"fee":0.0001}])
        psbt = wonline.walletprocesspsbt(online_node.converttopsbt(raw))["psbt"]
        assert not "not_witness_utxo" in mining_node.decodepsbt(psbt)["inputs"][0]

        # ELEMENTS FIXME: psbt parsing
        # add non-witness UTXO manually
        # psbt_new = PSBT.from_base64(psbt)
        # prev_tx = wonline.gettransaction(utxos[0]["txid"])["hex"]
        # psbt_new.i[0].map[PSBT_IN_NON_WITNESS_UTXO] = bytes.fromhex(prev_tx)
        # assert "non_witness_utxo" in mining_node.decodepsbt(psbt_new.to_base64())["inputs"][0]

        # # Have the offline node sign the PSBT (which will remove the non-witness UTXO)
        # signed_psbt = offline_node.walletprocesspsbt(psbt_new.to_base64())["psbt"]
        # assert not "non_witness_utxo" in mining_node.decodepsbt(signed_psbt)["inputs"][0]

        # # Make sure we can mine the resulting transaction
        # txid = mining_node.sendrawtransaction(mining_node.finalizepsbt(signed_psbt)["hex"])
        # self.generate(mining_node, nblocks=1, sync_fun=lambda: self.sync_all([online_node, mining_node]))
        # assert_equal(online_node.gettxout(txid,0)["confirmations"], 1)

        wonline.unloadwallet()

        # Reconnect
        self.connect_nodes(1, 0)
        self.connect_nodes(0, 2)

    def get_address(self, confidential, node_num, addr_mode=None):
        if (addr_mode):
            addr = self.nodes[node_num].getnewaddress()
        else:
            addr = self.nodes[node_num].getnewaddress("", addr_mode)

        if confidential:
            addr = self.nodes[node_num].getaddressinfo(addr)['confidential']
        else:
            addr = self.nodes[node_num].getaddressinfo(addr)['unconfidential']

        return addr

    def to_unconf_addr(self, node_num, addr):
        return self.nodes[node_num].getaddressinfo(addr)['unconfidential']

    def num_blinded_outputs(self, tx):
        result = 0
        decoded = self.nodes[0].decoderawtransaction(tx)
        for out in decoded["vout"]:
            if out["scriptPubKey"]["type"] == "fee":
                pass
            if "valuecommitment" in out:
                result += 1
        return result

    def test_input_confs_control(self):
        self.nodes[0].createwallet("minconf")
        wallet = self.nodes[0].get_wallet_rpc("minconf")

        # Fund the wallet with different chain heights
        for _ in range(2):
            self.nodes[1].sendmany("", {wallet.getnewaddress():1, wallet.getnewaddress():1})
            self.generate(self.nodes[1], 1)

        unconfirmed_txid = wallet.sendtoaddress(wallet.getnewaddress(), 0.5)

        self.log.info("Crafting PSBT using an unconfirmed input")
        target_address = self.nodes[1].getnewaddress()
        psbtx1 = wallet.walletcreatefundedpsbt([], [{target_address: 0.1}], 0, {'fee_rate': 1, 'maxconf': 0})['psbt']

        # Make sure we only had the one input
        tx1_inputs = self.nodes[0].decodepsbt(psbtx1)['inputs']
        assert_equal(len(tx1_inputs), 1)

        utxo1 = tx1_inputs[0]
        assert_equal(unconfirmed_txid, utxo1['previous_txid'])

        signed_tx1 = wallet.walletprocesspsbt(psbtx1)['psbt']
        final_tx1 = wallet.finalizepsbt(signed_tx1)['hex']
        txid1 = self.nodes[0].sendrawtransaction(final_tx1)

        mempool = self.nodes[0].getrawmempool()
        assert txid1 in mempool

        self.log.info("Fail to craft a new PSBT that sends more funds with add_inputs = False")
        assert_raises_rpc_error(-4, "The preselected coins total amount does not cover the transaction target. Please allow other inputs to be automatically selected or include more coins manually", wallet.walletcreatefundedpsbt, [{'txid': utxo1['previous_txid'], 'vout': utxo1['previous_vout']}], [{target_address: 1}], 0, {'add_inputs': False})

        self.log.info("Fail to craft a new PSBT with minconf above highest one")
        assert_raises_rpc_error(-4, "Insufficient funds", wallet.walletcreatefundedpsbt, [{'txid': utxo1['previous_txid'], 'vout': utxo1['previous_vout']}], [{target_address: 1}], 0, {'add_inputs': True, 'minconf': 3, 'fee_rate': 10})

        self.log.info("Fail to broadcast a new PSBT with maxconf 0 due to BIP125 rules to verify it actually chose unconfirmed outputs")
        psbt_invalid = wallet.walletcreatefundedpsbt([{'txid': utxo1['previous_txid'], 'vout': utxo1['previous_vout']}], [{target_address: 1}], 0, {'add_inputs': True, 'maxconf': 0, 'fee_rate': 10})['psbt']
        signed_invalid = wallet.walletprocesspsbt(psbt_invalid)['psbt']
        final_invalid = wallet.finalizepsbt(signed_invalid)['hex']
        assert_raises_rpc_error(-26, "bad-txns-spends-conflicting-tx", self.nodes[0].sendrawtransaction, final_invalid)

        self.log.info("Craft a replacement adding inputs with highest confs possible")
        psbtx2 = wallet.walletcreatefundedpsbt([{'txid': utxo1['previous_txid'], 'vout': utxo1['previous_vout']}], [{target_address: 1}], 0, {'add_inputs': True, 'minconf': 2, 'fee_rate': 10})['psbt']
        tx2_inputs = self.nodes[0].decodepsbt(psbtx2)['inputs']
        assert_greater_than_or_equal(len(tx2_inputs), 2)
        for vin in tx2_inputs:
            if vin['previous_txid'] != unconfirmed_txid:
                assert_greater_than_or_equal(self.nodes[0].gettxout(vin['previous_txid'], vin['previous_vout'])['confirmations'], 2)

        signed_tx2 = wallet.walletprocesspsbt(psbtx2)['psbt']
        final_tx2 = wallet.finalizepsbt(signed_tx2)['hex']
        txid2 = self.nodes[0].sendrawtransaction(final_tx2)

        mempool = self.nodes[0].getrawmempool()
        assert txid1 not in mempool
        assert txid2 in mempool

        wallet.unloadwallet()

    def assert_change_type(self, psbtx, expected_type):
        """Assert that the given PSBT has a change output with the given type."""

        # The decodepsbt RPC is stateless and independent of any settings, we can always just call it on the first node
        decoded_psbt = self.nodes[0].decodepsbt(psbtx["psbt"])
        changepos = psbtx["changepos"]
        assert_equal(decoded_psbt["outputs"][changepos]["script"]["type"], expected_type)

    def run_basic_tests(self, confidential):
        starting_n_unspent = len(self.nodes[0].listlockunspent()) # ELEMENTS
        # Create and fund a raw tx for sending 10 BTC
        psbtx1 = self.nodes[0].walletcreatefundedpsbt([], [{self.get_address(confidential, 2):10}])['psbt']

        # If inputs are specified, do not automatically add more:
        utxo1 = self.nodes[0].listunspent()[0]
        assert_raises_rpc_error(-4, "The preselected coins total amount does not cover the transaction target. "
                                    "Please allow other inputs to be automatically selected or include more coins manually",
                                self.nodes[0].walletcreatefundedpsbt, [{"txid": utxo1['txid'], "vout": utxo1['vout']}], [{self.nodes[2].getnewaddress():90}])

        psbtx1 = self.nodes[0].walletcreatefundedpsbt([{"txid": utxo1['txid'], "vout": utxo1['vout']}], [{self.get_address(confidential, 2):90}], 0, {"add_inputs": True})['psbt']
        # ELEMENTS: we are on the edge between 2 and 3 inputs; don't check exact value,
        #  just make sure that we added at least one input
        assert len(self.nodes[0].decodepsbt(psbtx1)["inputs"]) > 1

        # Inputs argument can be null
        self.nodes[0].walletcreatefundedpsbt(None, [{self.nodes[2].getnewaddress():10}])

        # Node 1 should not be able to add anything to it but still return the psbtx same as before
        psbtx = self.nodes[1].walletprocesspsbt(psbtx1)['psbt']
        assert_equal(psbtx1, psbtx)

        # ELEMENTS: FIXME failing asserts
        # Node 0 should not be able to sign the transaction with the wallet is locked
        # self.nodes[0].encryptwallet("password")
        # assert_raises_rpc_error(-13, "Please enter the wallet passphrase with walletpassphrase first", self.nodes[0].walletprocesspsbt, psbtx)

        # Node 0 should be able to process without signing though
        unsigned_tx = self.nodes[0].walletprocesspsbt(psbtx, False)
        assert_equal(unsigned_tx['complete'], False)

        # self.nodes[0].walletpassphrase(passphrase="password", timeout=1000000)

        # Sign the transaction and send
        signed_tx = self.nodes[0].walletprocesspsbt(psbt=psbtx, finalize=False)['psbt']
        finalized_tx = self.nodes[0].walletprocesspsbt(psbt=psbtx, finalize=True)['psbt']
        assert signed_tx != finalized_tx
        final_tx = self.nodes[0].finalizepsbt(signed_tx)['hex']
        if confidential:
            # Can't use assert_equal because there may or may not be change
            assert(self.num_blinded_outputs(final_tx) > 0)
        self.nodes[0].sendrawtransaction(final_tx)

        # Manually selected inputs can be locked:
        assert_equal(len(self.nodes[0].listlockunspent()), starting_n_unspent)
        utxo1 = self.nodes[0].listunspent()[0]
        psbtx1 = self.nodes[0].walletcreatefundedpsbt([{"txid": utxo1['txid'], "vout": utxo1['vout']}], [{self.get_address(confidential, 2):1}], 0,{"lockUnspents": True})["psbt"]
        assert_equal(len(self.nodes[0].listlockunspent()), starting_n_unspent + 1)

        # Locks are ignored for manually selected inputs
        self.nodes[0].walletcreatefundedpsbt([{"txid": utxo1['txid'], "vout": utxo1['vout']}], [{self.get_address(confidential, 2):1}], 0)

        # Create p2sh, p2wpkh, and p2wsh addresses
        pubkey0 = self.nodes[0].getaddressinfo(self.get_address(confidential, 0))['pubkey']
        pubkey1 = self.nodes[1].getaddressinfo(self.get_address(confidential, 1))['pubkey']
        pubkey2 = self.nodes[2].getaddressinfo(self.get_address(confidential, 2))['pubkey']

        # Setup watchonly wallets
        if confidential:
            self.nodes[2].createwallet(wallet_name='wmulti_conf', disable_private_keys=True)
            wmulti = self.nodes[2].get_wallet_rpc('wmulti_conf')
        else:
            self.nodes[2].createwallet(wallet_name='wmulti', disable_private_keys=True)
            wmulti = self.nodes[2].get_wallet_rpc('wmulti')

        # Create all the addresses
        p2sh = wmulti.addmultisigaddress(2, [pubkey0, pubkey1, pubkey2], "", "legacy")['address']
        p2sh_unconf = self.to_unconf_addr(1, p2sh)
        p2wsh = wmulti.addmultisigaddress(2, [pubkey0, pubkey1, pubkey2], "", "bech32")['address']
        p2wsh_unconf = self.to_unconf_addr(1, p2wsh)
        p2sh_p2wsh = wmulti.addmultisigaddress(2, [pubkey0, pubkey1, pubkey2], "", "p2sh-segwit")['address']
        p2sh_p2wsh_unconf = self.to_unconf_addr(1, p2sh_p2wsh)
        if not self.options.descriptors:
            wmulti.importaddress(p2sh)
            wmulti.importaddress(p2wsh)
            wmulti.importaddress(p2sh_p2wsh)
        p2wpkh = self.get_address(confidential, 1, "bech32")
        p2wpkh_unconf = self.to_unconf_addr(1, p2wpkh)
        p2pkh = self.get_address(confidential, 1, "legacy")
        p2pkh_unconf = self.to_unconf_addr(1, p2pkh)
        p2sh_p2wpkh = self.get_address(confidential, 1, "p2sh-segwit")
        p2sh_p2wpkh_unconf = self.to_unconf_addr(1, p2sh_p2wpkh)

        # fund those addresses
        rawtx = self.nodes[0].createrawtransaction([], [{p2sh:10}, {p2wsh:10}, {p2wpkh:10}, {p2sh_p2wsh:10}, {p2sh_p2wpkh:10}, {p2pkh:10}])
        rawtx = self.nodes[0].fundrawtransaction(rawtx, {"changePosition":3})
        rawtx = self.nodes[0].blindrawtransaction(rawtx['hex'])
        signed_tx = self.nodes[0].signrawtransactionwithwallet(rawtx)['hex']
        txid = self.nodes[0].sendrawtransaction(signed_tx)

        self.generate(self.nodes[0], 6)

        # Find the output pos
        p2sh_pos = -1
        p2wsh_pos = -1
        p2wpkh_pos = -1
        p2pkh_pos = -1
        p2sh_p2wsh_pos = -1
        p2sh_p2wpkh_pos = -1
        decoded = self.nodes[0].decoderawtransaction(signed_tx)
        for out in decoded['vout']:
            if out['scriptPubKey']['type'] == 'fee':
                next
            elif out['scriptPubKey']['address'] == p2sh_unconf:
                p2sh_pos = out['n']
            elif out['scriptPubKey']['address'] == p2wsh_unconf:
                p2wsh_pos = out['n']
            elif out['scriptPubKey']['address'] == p2wpkh_unconf:
                p2wpkh_pos = out['n']
            elif out['scriptPubKey']['address'] == p2sh_p2wsh_unconf:
                p2sh_p2wsh_pos = out['n']
            elif out['scriptPubKey']['address'] == p2sh_p2wpkh_unconf:
                p2sh_p2wpkh_pos = out['n']
            elif out['scriptPubKey']['address'] == p2pkh_unconf:
                p2pkh_pos = out['n']

        inputs = [{"txid": txid, "vout": p2wpkh_pos}, {"txid": txid, "vout": p2sh_p2wpkh_pos}, {"txid": txid, "vout": p2pkh_pos}]
        outputs = [{self.get_address(confidential, 1): 29.99}]

        # spend single key from node 1
        created_psbt = self.nodes[1].walletcreatefundedpsbt(inputs, outputs)
        walletsignpsbt_out = self.nodes[1].walletprocesspsbt(created_psbt["psbt"])
        # Make sure it has both types of UTXOs
        decoded = self.nodes[1].decodepsbt(walletsignpsbt_out['psbt'])
        assert 'non_witness_utxo' in decoded['inputs'][0]
        assert 'witness_utxo' in decoded['inputs'][0]
        if 'asset' in decoded['inputs'][0]['witness_utxo']:
            assert_equal(decoded['inputs'][0]['witness_utxo']['asset'], 'b2e15d0d7a0c94e4e2ce0fe6e8691b9e451377f6e46e8045a86f7c4b5d4f0f23')
        else:
            assert 'assetcommitment' in decoded['inputs'][0]['witness_utxo']
        # Check decodepsbt fee calculation (input values shall only be counted once per UTXO)
        #assert_equal(decoded['fee'], created_psbt['fee']) # ELEMENTS: we do not have this field. Should be fixed by #900
        assert_equal(walletsignpsbt_out['complete'], True)
        self.nodes[1].sendrawtransaction(self.nodes[1].finalizepsbt(walletsignpsbt_out['psbt'])['hex'])

        if confidential:
            fee_rate_sb = 2000
        else:
            fee_rate_sb = 10000

        self.log.info("Test walletcreatefundedpsbt fee rate of 10000 sat/vB and 0.1 BTC/kvB produces a total fee at or slightly below -maxtxfee (~0.05290000)")
        #res1 =
        self.nodes[1].walletcreatefundedpsbt(inputs, outputs, 0, {"fee_rate": fee_rate_sb, "add_inputs": True})
        #assert_approx(res1["fee"], 0.055, 0.005) # ELEMENTS: no "fee" field
        #res2 =
        self.nodes[1].walletcreatefundedpsbt(inputs, outputs, 0, {"feeRate": fee_rate_sb / 100000.0, "add_inputs": True})
        #assert_approx(res2["fee"], 0.055, 0.005) # ELEMENTS: no "fee" field

        self.log.info("Test min fee rate checks with walletcreatefundedpsbt are bypassed, e.g. a fee_rate under 1 sat/vB is allowed")
        #res3 =
        self.nodes[1].walletcreatefundedpsbt(inputs, outputs, 0, {"fee_rate": "0.999", "add_inputs": True})
        #assert_approx(res3["fee"], 0.00000381, 0.0000001)
        #res4 =
        self.nodes[1].walletcreatefundedpsbt(inputs, outputs, 0, {"feeRate": 0.00000999, "add_inputs": True})
        #assert_approx(res4["fee"], 0.00000381, 0.0000001)

        self.log.info("Test min fee rate checks with walletcreatefundedpsbt are bypassed and that funding non-standard 'zero-fee' transactions is valid")
        for param, zero_value in product(["fee_rate", "feeRate"], [0, 0.000, 0.00000000, "0", "0.000", "0.00000000"]):
            assert_equal(0, self.nodes[1].walletcreatefundedpsbt(inputs, outputs, 0, {param: zero_value, "add_inputs": True})["fee"])

        self.log.info("Test invalid fee rate settings")
        for param, value in {("fee_rate", 100000), ("feeRate", 1)}:
            assert_raises_rpc_error(-4, "Fee exceeds maximum configured by user (e.g. -maxtxfee, maxfeerate)",
                self.nodes[1].walletcreatefundedpsbt, inputs, outputs, 0, {param: value, "add_inputs": True})
            assert_raises_rpc_error(-3, "Amount out of range",
                self.nodes[1].walletcreatefundedpsbt, inputs, outputs, 0, {param: -1, "add_inputs": True})
            assert_raises_rpc_error(-3, "Amount is not a number or string",
                self.nodes[1].walletcreatefundedpsbt, inputs, outputs, 0, {param: {"foo": "bar"}, "add_inputs": True})
            # Test fee rate values that don't pass fixed-point parsing checks.
            for invalid_value in ["", 0.000000001, 1e-09, 1.111111111, 1111111111111111, "31.999999999999999999999"]:
                assert_raises_rpc_error(-3, "Invalid amount",
                    self.nodes[1].walletcreatefundedpsbt, inputs, outputs, 0, {param: invalid_value, "add_inputs": True})
        # Test fee_rate values that cannot be represented in sat/vB.
        for invalid_value in [0.0001, 0.00000001, 0.00099999, 31.99999999, "0.0001", "0.00000001", "0.00099999", "31.99999999"]:
            assert_raises_rpc_error(-3, "Invalid amount",
                self.nodes[1].walletcreatefundedpsbt, inputs, outputs, 0, {"fee_rate": invalid_value, "add_inputs": True})

        self.log.info("- raises RPC error if both feeRate and fee_rate are passed")
        assert_raises_rpc_error(-8, "Cannot specify both fee_rate (sat/vB) and feeRate (BTC/kvB)",
            self.nodes[1].walletcreatefundedpsbt, inputs, outputs, 0, {"fee_rate": 0.1, "feeRate": 0.1, "add_inputs": True})

        self.log.info("- raises RPC error if both feeRate and estimate_mode passed")
        assert_raises_rpc_error(-8, "Cannot specify both estimate_mode and feeRate",
            self.nodes[1].walletcreatefundedpsbt, inputs, outputs, 0, {"estimate_mode": "economical", "feeRate": 0.1, "add_inputs": True})

        for param in ["feeRate", "fee_rate"]:
            self.log.info("- raises RPC error if both {} and conf_target are passed".format(param))
            assert_raises_rpc_error(-8, "Cannot specify both conf_target and {}. Please provide either a confirmation "
                "target in blocks for automatic fee estimation, or an explicit fee rate.".format(param),
                self.nodes[1].walletcreatefundedpsbt ,inputs, outputs, 0, {param: 1, "conf_target": 1, "add_inputs": True})

        self.log.info("- raises RPC error if both fee_rate and estimate_mode are passed")
        assert_raises_rpc_error(-8, "Cannot specify both estimate_mode and fee_rate",
            self.nodes[1].walletcreatefundedpsbt ,inputs, outputs, 0, {"fee_rate": 1, "estimate_mode": "economical", "add_inputs": True})

        self.log.info("- raises RPC error with invalid estimate_mode settings")
        for k, v in {"number": 42, "object": {"foo": "bar"}}.items():
            assert_raises_rpc_error(-3, f"JSON value of type {k} for field estimate_mode is not of expected type string",
                self.nodes[1].walletcreatefundedpsbt, inputs, outputs, 0, {"estimate_mode": v, "conf_target": 0.1, "add_inputs": True})
        for mode in ["", "foo", Decimal("3.141592")]:
            assert_raises_rpc_error(-8, 'Invalid estimate_mode parameter, must be one of: "unset", "economical", "conservative"',
                self.nodes[1].walletcreatefundedpsbt, inputs, outputs, 0, {"estimate_mode": mode, "conf_target": 0.1, "add_inputs": True})

        self.log.info("- raises RPC error with invalid conf_target settings")
        for mode in ["unset", "economical", "conservative"]:
            self.log.debug("{}".format(mode))
            for k, v in {"string": "", "object": {"foo": "bar"}}.items():
                assert_raises_rpc_error(-3, f"JSON value of type {k} for field conf_target is not of expected type number",
                    self.nodes[1].walletcreatefundedpsbt, inputs, outputs, 0, {"estimate_mode": mode, "conf_target": v, "add_inputs": True})
            for n in [-1, 0, 1009]:
                assert_raises_rpc_error(-8, "Invalid conf_target, must be between 1 and 1008",  # max value of 1008 per src/policy/fees.h
                    self.nodes[1].walletcreatefundedpsbt, inputs, outputs, 0, {"estimate_mode": mode, "conf_target": n, "add_inputs": True})

        self.log.info("Test walletcreatefundedpsbt with too-high fee rate produces total fee well above -maxtxfee and raises RPC error")
        # previously this was silently capped at -maxtxfee
        for bool_add, outputs_array in {True: outputs, False: [{self.nodes[1].getnewaddress(): 1}]}.items():
            msg = "Fee exceeds maximum configured by user (e.g. -maxtxfee, maxfeerate)"
            assert_raises_rpc_error(-4, msg, self.nodes[1].walletcreatefundedpsbt, inputs, outputs_array, 0, {"fee_rate": 1000000, "add_inputs": bool_add})
            assert_raises_rpc_error(-4, msg, self.nodes[1].walletcreatefundedpsbt, inputs, outputs_array, 0, {"feeRate": 1, "add_inputs": bool_add})

        self.log.info("Test various PSBT operations")
        addr = self.get_address(confidential, 1)
        unconf_addr = self.nodes[1].getaddressinfo(addr)['unconfidential']
        change_addr = self.nodes[1].getrawchangeaddress()
        conf_change_addr = self.nodes[1].getaddressinfo(change_addr)['confidential']
        unconf_change_addr = self.nodes[1].getaddressinfo(change_addr)['unconfidential']
        # partially sign multisig things with node 1
        psbtx = wmulti.walletcreatefundedpsbt(inputs=[{"txid":txid,"vout":p2wsh_pos},{"txid":txid,"vout":p2sh_pos},{"txid":txid,"vout":p2sh_p2wsh_pos}], outputs=[{addr:29.99}], options={'changeAddress': unconf_change_addr})['psbt']
        filled = wmulti.walletprocesspsbt(psbtx)
        # have both nodes fill before we try to blind and sign
        walletprocesspsbt_out = self.nodes[1].walletprocesspsbt(filled["psbt"])
        psbtx = walletprocesspsbt_out['psbt']
        assert_equal(walletprocesspsbt_out['complete'], False)
        # check that the unblinded change address led to unblinded change
        assert_equal(
            outputs_info(self.nodes[1].decodepsbt(psbtx)["outputs"]),
            {
                (unconf_addr, confidential, False),
                (unconf_change_addr, False, False),
                (None, False, False), # fee
            },
        )

        # Repeat the above, with a confidential change address
        psbtx = wmulti.walletcreatefundedpsbt(inputs=[{"txid":txid,"vout":p2wsh_pos},{"txid":txid,"vout":p2sh_pos},{"txid":txid,"vout":p2sh_p2wsh_pos}], outputs=[{addr:29.99}], options={'changeAddress': conf_change_addr})['psbt']
        filled = wmulti.walletprocesspsbt(psbtx)
        # have both nodes fill before we try to blind and sign
        walletprocesspsbt_out = self.nodes[1].walletprocesspsbt(filled["psbt"])
        psbtx = walletprocesspsbt_out['psbt']
        assert_equal(walletprocesspsbt_out['complete'], False)
        # check that the blinded change address led to blinded change (and below,
        # when we call `walletprocesspsbt` with nodes[2], it will make sure that
        # node 2 is able to unblind this change, even though wmulti created it).
        # Notice that if `confidential` is False, the change is not blinded. This
        # is a quirk of the wallet.cpp blinding logic and will go away when we
        # overhaul this.
        assert_equal(
            outputs_info(self.nodes[1].decodepsbt(psbtx)["outputs"]),
            {
                (unconf_addr, confidential, False),
                (unconf_change_addr, confidential, False),
                (None, False, False), # fee
            },
        )

        # Unload wmulti, we don't need it anymore
        wmulti.unloadwallet()

        # partially sign with node 2. This should be complete and sendable
        walletsignpsbt_out = self.nodes[2].walletprocesspsbt(psbtx)
        assert_equal(walletsignpsbt_out['complete'], True)
        hex_tx = self.nodes[2].finalizepsbt(walletsignpsbt_out['psbt'])['hex']
        if confidential:
            # Can't use assert_equal because there may or may not be change
            assert(self.num_blinded_outputs(hex_tx) > 0)
        self.nodes[2].sendrawtransaction(hex_tx)

        # check that walletprocesspsbt fails to decode a non-psbt
        rawtx = self.nodes[1].createrawtransaction([{"txid":txid,"vout":p2wpkh_pos}], [{self.get_address(confidential, 1):9.99}])
        assert_raises_rpc_error(-22, "TX decode failed", self.nodes[1].walletprocesspsbt, rawtx)

        # Convert a non-psbt to psbt and make sure we can decode it
        rawtx = self.nodes[0].createrawtransaction([], [{self.get_address(confidential, 1):10}])
        rawtx = self.nodes[0].fundrawtransaction(rawtx)
        new_psbt = self.nodes[0].converttopsbt(rawtx['hex'])
        self.nodes[0].decodepsbt(new_psbt)

        # Make sure that a non-psbt with signatures cannot be converted
        # Error could be either "TX decode failed" (segwit inputs causes parsing to fail) or "Inputs must not have scriptSigs and scriptWitnesses"
        # We must set iswitness=True because the serialized transaction has inputs and is therefore a witness transaction
        signedtx = self.nodes[0].signrawtransactionwithwallet(rawtx['hex'])
        # Can be either a scriptSig or a scriptWitness that it yells about, depending on which UTXOs are selected for the TX
        assert_raises_rpc_error(-22, "Inputs must not have", self.nodes[0].converttopsbt, signedtx['hex'], False)
        assert_raises_rpc_error(-22, "Inputs must not have", self.nodes[0].converttopsbt, signedtx['hex'])
        assert_raises_rpc_error(-22, "", self.nodes[0].converttopsbt, hexstring=signedtx['hex'], iswitness=True)
        assert_raises_rpc_error(-22, "", self.nodes[0].converttopsbt, hexstring=signedtx['hex'], permitsigdata=False, iswitness=True)
        # Unless we allow it to convert and strip signatures
        self.nodes[0].converttopsbt(signedtx['hex'], True)

        # Explicitly allow converting non-empty txs
        new_psbt = self.nodes[0].converttopsbt(rawtx['hex'])
        self.nodes[0].decodepsbt(new_psbt)

        # Create outputs to nodes 1 and 2
        # We do a whole song-and-dance here (instead of calling sendtoaddress) to get access to the unblinded transaction data to find our outputs
        node1_addr = self.get_address(confidential, 1)
        node1_unconf_addr = self.to_unconf_addr(1, node1_addr)
        node2_addr = self.get_address(confidential, 2)
        node2_unconf_addr = self.to_unconf_addr(2, node2_addr)
        rt1 = self.nodes[0].createrawtransaction([], [{node1_addr:13}])
        rt1 = self.nodes[0].fundrawtransaction(rt1)
        rt1 = self.nodes[0].blindrawtransaction(rt1['hex'])
        rt1 = self.nodes[0].signrawtransactionwithwallet(rt1)
        txid1 = self.nodes[0].sendrawtransaction(rt1['hex'])
        rt1 = self.nodes[0].decoderawtransaction(rt1['hex'])

        rt2 = self.nodes[0].createrawtransaction([], [{node2_addr:13}])
        rt2 = self.nodes[0].fundrawtransaction(rt2)
        rt2 = self.nodes[0].blindrawtransaction(rt2['hex'])
        rt2 = self.nodes[0].signrawtransactionwithwallet(rt2)
        txid2 = self.nodes[0].sendrawtransaction(rt2['hex'])
        rt2 = self.nodes[0].decoderawtransaction(rt2['hex'])

        self.generate(self.nodes[0], 6)

        for out in rt1['vout']:
            if out['scriptPubKey']['type'] == "fee":
                pass
            elif out['scriptPubKey']['address'] == node1_unconf_addr:
                vout1 = out['n']

        for out in rt2['vout']:
            if out['scriptPubKey']['type'] == "fee":
                pass
            elif out['scriptPubKey']['address'] == node2_unconf_addr:
                vout2 = out['n']

        # This test doesn't work with Confidential Assets yet.
        if not confidential:
            # Create a psbt spending outputs from nodes 1 and 2
            psbt_orig = self.nodes[0].createpsbt([{"txid":txid1,  "vout":vout1}, {"txid":txid2, "vout":vout2}], [{self.get_address(confidential, 0):25.999}, {"fee":0.001}])

            # Update psbts, should only have data for one input and not the other
            psbt1 = self.nodes[1].walletprocesspsbt(psbt_orig, False, "ALL")['psbt']
            psbt1_decoded = self.nodes[0].decodepsbt(psbt1)
            assert len(psbt1_decoded["inputs"][0].keys()) > 3
            assert len(psbt1_decoded["inputs"][1].keys()) == 3
            # Check that BIP32 path was added
            assert "bip32_derivs" in psbt1_decoded['inputs'][0]
            psbt2 = self.nodes[2].walletprocesspsbt(psbt_orig, False, "ALL", False)['psbt']
            psbt2_decoded = self.nodes[0].decodepsbt(psbt2)
            assert len(psbt2_decoded["inputs"][0].keys()) == 3
            assert len(psbt2_decoded["inputs"][1].keys()) > 3
            # Check that BIP32 paths were not added
            assert "bip32_derivs" not in psbt2_decoded['inputs'][1]

            # Fill PSBTs (workaround issue #18039)
            psbt1 = self.nodes[1].walletprocesspsbt(psbt_orig, False)['psbt']
            psbt2 = self.nodes[2].walletprocesspsbt(psbt_orig, False)['psbt']

            # Combine and sign
            combined = self.nodes[0].combinepsbt([psbt1, psbt2])
            psbt1 = self.nodes[1].walletprocesspsbt(combined, True)['psbt']
            psbt2 = self.nodes[2].walletprocesspsbt(combined, True)['psbt']

            # Combine again, finalize, sign, and send the psbts
            combined = self.nodes[0].combinepsbt([psbt1, psbt2])
            finalized = self.nodes[0].finalizepsbt(combined)['hex']
            self.nodes[0].sendrawtransaction(finalized)

            self.generate(self.nodes[0], 6)
            self.sync_all()

        # Test additional args in walletcreatepsbt
        # Make sure both pre-included and funded inputs
        # have the correct sequence numbers based on
        # replaceable arg
        block_height = self.nodes[0].getblockcount()
        unspent = self.nodes[0].listunspent()[0]
        psbtx_info = self.nodes[0].walletcreatefundedpsbt([{"txid":unspent["txid"], "vout":unspent["vout"]}], [{self.get_address(confidential, 2):unspent["amount"]+1}], block_height+2, {"replaceable": False, "add_inputs": True}, False)
        decoded_psbt = self.nodes[0].decodepsbt(psbtx_info["psbt"])
        for psbt_in in decoded_psbt["inputs"]:
            assert_greater_than(psbt_in["sequence"], MAX_BIP125_RBF_SEQUENCE)
            assert "bip32_derivs" not in psbt_in
        assert_equal(decoded_psbt["fallback_locktime"], block_height+2)

        # Same construction with only locktime set and RBF explicitly enabled
        psbtx_info = self.nodes[0].walletcreatefundedpsbt([{"txid":unspent["txid"], "vout":unspent["vout"]}], [{self.get_address(confidential, 2):unspent["amount"]+1}], block_height, {"replaceable": True, "add_inputs": True}, True)
        decoded_psbt = self.nodes[0].decodepsbt(psbtx_info["psbt"])
        for psbt_in in decoded_psbt["inputs"]:
            assert_equal(psbt_in["sequence"], MAX_BIP125_RBF_SEQUENCE)
            assert "bip32_derivs" in psbt_in
        assert_equal(decoded_psbt["fallback_locktime"], block_height)

        # Same construction without optional arguments
        psbtx_info = self.nodes[0].walletcreatefundedpsbt([], [{self.get_address(confidential, 2):unspent["amount"]+1}])
        decoded_psbt = self.nodes[0].decodepsbt(psbtx_info["psbt"])
        for psbt_in in decoded_psbt["inputs"]:
            assert_equal(psbt_in["sequence"], MAX_BIP125_RBF_SEQUENCE)
            assert "bip32_derivs" in psbt_in
        assert_equal(decoded_psbt["fallback_locktime"], 0)

        # Same construction without optional arguments, for a node with -walletrbf=0
        unspent1 = self.nodes[1].listunspent()[0]
        psbtx_info = self.nodes[1].walletcreatefundedpsbt([{"txid":unspent1["txid"], "vout":unspent1["vout"]}], [{self.nodes[2].getnewaddress():unspent1["amount"]+1}], block_height, {"add_inputs": True})
        decoded_psbt = self.nodes[1].decodepsbt(psbtx_info["psbt"])
        for psbt_in in decoded_psbt["inputs"]:
            assert_greater_than(psbt_in["sequence"], MAX_BIP125_RBF_SEQUENCE)
            assert "bip32_derivs" in psbt_in

        # Make sure change address wallet does not have P2SH innerscript access to results in success
        # when attempting BnB coin selection
        self.nodes[0].walletcreatefundedpsbt([], [{self.nodes[2].getnewaddress():unspent["amount"]+1}], block_height+2, {"changeAddress":self.nodes[1].getnewaddress()}, False)

        # Make sure the wallet's change type is respected by default
        small_output = {self.nodes[0].getnewaddress():0.1}
        psbtx_native = self.nodes[0].walletcreatefundedpsbt([], [small_output])
        self.assert_change_type(psbtx_native, "witness_v0_keyhash")
        psbtx_legacy = self.nodes[1].walletcreatefundedpsbt([], [small_output])
        self.assert_change_type(psbtx_legacy, "pubkeyhash")

        # Make sure the change type of the wallet can also be overwritten
        psbtx_np2wkh = self.nodes[1].walletcreatefundedpsbt([], [small_output], 0, {"change_type":"p2sh-segwit"})
        self.assert_change_type(psbtx_np2wkh, "scripthash")

        # Make sure the change type cannot be specified if a change address is given
        invalid_options = {"change_type":"legacy","changeAddress":self.nodes[0].getnewaddress()}
        assert_raises_rpc_error(-8, "both change address and address type options", self.nodes[0].walletcreatefundedpsbt, [], [small_output], 0, invalid_options)

        # Regression test for 14473 (mishandling of already-signed witness transaction):
        psbtx_info = self.nodes[0].walletcreatefundedpsbt([{"txid":unspent["txid"], "vout":unspent["vout"]}], [{self.get_address(confidential, 2):unspent["amount"]+1}], 0, {"add_inputs": True})
        signed = self.nodes[0].walletprocesspsbt(psbtx_info["psbt"])
        signed_again = self.nodes[0].walletprocesspsbt(signed["psbt"])
        assert_equal(signed, signed_again)
        # We don't care about the decode result, but decoding must succeed.
        self.nodes[0].decodepsbt(signed["psbt"])


    def run_unsafe_tests(self):
        # Make sure unsafe inputs are included if specified
        self.nodes[2].createwallet(wallet_name="unsafe")
        wunsafe = self.nodes[2].get_wallet_rpc("unsafe")
        self.nodes[0].sendtoaddress(wunsafe.getnewaddress(), 2)
        self.sync_mempools()
        assert_raises_rpc_error(-4, "Insufficient funds", wunsafe.walletcreatefundedpsbt, [], [{self.nodes[0].getnewaddress(): 1}])
        wunsafe.walletcreatefundedpsbt([], [{self.nodes[0].getnewaddress(): 1}], 0, {"include_unsafe": True})


    # BIP 174 tests are disabled because they don't work with CA yet. Comment the function so it doesn't flag lint as unused.
    """
    def run_bip174_tests(self):
        # BIP 174 Test Vectors

        # Check that unknown values are just passed through
        unknown_psbt = "cHNidP8BAD8CAAAAAf//////////////////////////////////////////AAAAAAD/////AQAAAAAAAAAAA2oBAAAAAAAACvABAgMEBQYHCAkPAQIDBAUGBwgJCgsMDQ4PAAA="
        unknown_out = self.nodes[0].walletprocesspsbt(unknown_psbt)['psbt']
        assert_equal(unknown_psbt, unknown_out)

        # Open the data file
        with open(os.path.join(os.path.dirname(os.path.realpath(__file__)), 'data/rpc_psbt.json'), encoding='utf-8') as f:
            d = json.load(f)
            invalids = d['invalid']
            invalid_with_msgs = d["invalid_with_msg"]
            valids = d['valid']
            creators = d['creator']
            signers = d['signer']
            combiners = d['combiner']
            finalizers = d['finalizer']
            extractors = d['extractor']

        # Invalid PSBTs
        for invalid in invalids:
            assert_raises_rpc_error(-22, "TX decode failed", self.nodes[0].decodepsbt, invalid)
        for invalid in invalid_with_msgs:
            psbt, msg = invalid
            assert_raises_rpc_error(-22, f"TX decode failed {msg}", self.nodes[0].decodepsbt, psbt)

        # Valid PSBTs
        for valid in valids:
            self.nodes[0].decodepsbt(valid)

        # Creator Tests
        for creator in creators:
            created_tx = self.nodes[0].createpsbt(inputs=creator['inputs'], outputs=creator['outputs'], psbt_version=creator['version'], replaceable=False)
            assert_equal(created_tx, creator['result'])

        # Signer tests
        for i, signer in enumerate(signers):
            self.nodes[2].createwallet(wallet_name="wallet{}".format(i))
            wrpc = self.nodes[2].get_wallet_rpc("wallet{}".format(i))
            for key in signer['privkeys']:
                wrpc.importprivkey(key)
            signed_tx = wrpc.walletprocesspsbt(signer['psbt'], True, "ALL")['psbt']
            assert_equal(signed_tx, signer['result'])

        # Combiner test
        for combiner in combiners:
            combined = self.nodes[2].combinepsbt(combiner['combine'])
            assert_equal(combined, combiner['result'])

        # Empty combiner test
        assert_raises_rpc_error(-8, "Parameter 'txs' cannot be empty", self.nodes[0].combinepsbt, [])

        # Finalizer test
        for finalizer in finalizers:
            finalized = self.nodes[2].finalizepsbt(finalizer['finalize'], False)['psbt']
            assert_equal(finalized, finalizer['result'])

        # Extractor test
        for extractor in extractors:
            extracted = self.nodes[2].finalizepsbt(extractor['extract'], True)['hex']
            assert_equal(extracted, extractor['result'])

        # Unload extra wallets
        for i, signer in enumerate(signers):
            self.nodes[2].unloadwallet("wallet{}".format(i))
    """

    def run_ca_tests(self):
        # Confidential Assets tests

        # Start by sending some coins to a nonconf address
        unconf_addr_0 = self.get_address(False, 0)
        unconf_addr_1 = self.get_address(False, 0)
        unconf_addr_4 = self.get_address(False, 0)
        rawtx = self.nodes[0].createrawtransaction([], [{unconf_addr_0:50}, {unconf_addr_1:50}, {unconf_addr_4:50}])
        rawtx = self.nodes[0].fundrawtransaction(rawtx, {"changePosition":3})  # our outputs will be 0, 1, 2
        rawtx = self.nodes[0].blindrawtransaction(rawtx['hex'])
        signed_tx = self.nodes[0].signrawtransactionwithwallet(rawtx)['hex']
        txid_nonconf = self.nodes[0].sendrawtransaction(signed_tx)
        self.generate(self.nodes[0], 1)
        self.sync_all()

        # Now use PSBT to send some coins nonconf->nonconf
        unconf_addr_2 = self.get_address(False, 1)
        psbt = self.nodes[0].createpsbt([{"txid": txid_nonconf, "vout": 0}], [{unconf_addr_2: 49.999}, {"fee": 0.001}])
        psbt = self.nodes[0].walletprocesspsbt(psbt)["psbt"]
        tx_hex = self.nodes[0].finalizepsbt(psbt)['hex']
        self.nodes[0].sendrawtransaction(tx_hex)
        self.generate(self.nodes[0], 1)
        self.sync_all()

        # Now send nonconf->conf (with two outputs, blinding succeeds)
        conf_addr_1 = self.get_address(True, 2)
        conf_addr_2 = self.get_address(True, 2)
        psbt = self.nodes[0].createpsbt([{"txid": txid_nonconf, "vout": 1}], [{conf_addr_1: 24.999, "blinder_index": 0}, {conf_addr_2: 24.999, "blinder_index": 0}, {"fee": 0.002}])
        psbt = self.nodes[0].walletprocesspsbt(psbt)['psbt']
        hex_tx = self.nodes[0].finalizepsbt(psbt)['hex']
        assert_equal(self.num_blinded_outputs(hex_tx), 2)
        txid_conf_2 = self.nodes[0].sendrawtransaction(hex_tx)
        self.generate(self.nodes[0], 1)
        self.sync_all()

        # Try to send conf->nonconf: This will fail because we can't balance the blinders
        unconf_addr_3 = self.get_address(False, 0)
        psbt = self.nodes[2].createpsbt([{"txid": txid_conf_2, "vout": 0}], [{unconf_addr_3: 24.998}, {"fee": 0.001}])
        #assert_raises_rpc_error(-25, "Transaction values or blinders are not balanced", self.nodes[2].walletprocesspsbt, psbt)

        # Try to send conf->(nonconf + conf), so we have a conf output to balance blinders
        conf_addr_3 = self.get_address(True, 0)
        psbt = self.nodes[2].createpsbt([{"txid": txid_conf_2, "vout": 0}], [{unconf_addr_3: 10}, {conf_addr_3: 14.998, "blinder_index": 0}, {"fee": 0.001}])
        psbt = self.nodes[2].walletprocesspsbt(psbt)['psbt']
        hex_tx = self.nodes[2].finalizepsbt(psbt)['hex']
        assert_equal(self.num_blinded_outputs(hex_tx), 1)
        self.nodes[2].sendrawtransaction(hex_tx)
        self.generate(self.nodes[0], 1)
        self.sync_all()

        # Check include_explicit option
        psbt = self.nodes[2].walletcreatefundedpsbt([{"txid": txid_conf_2, "vout": 1}], [{self.get_address(True, 0): 24.998, "blinder_index": 0}, {"fee": 0.001}], 0, {"include_explicit": True})["psbt"]
        decoded = self.nodes[1].decodepsbt(psbt)
        assert "explicit_value" in decoded["inputs"][0]
        assert "value_proof" in decoded["inputs"][0]
        assert "explicit_asset" in decoded["inputs"][0]
        assert "asset_proof" in decoded["inputs"][0]

        # Try to send conf->conf
        conf_addr_4 = self.get_address(True, 0)
        psbt = self.nodes[2].createpsbt([{"txid": txid_conf_2, "vout": 1}], [{conf_addr_4: 24.998, "blinder_index": 0}, {"fee": 0.001}])
        psbt = self.nodes[2].walletprocesspsbt(psbt)['psbt']
        decoded = self.nodes[1].decodepsbt(psbt)
        assert "blind_value_proof" in decoded["outputs"][0]
        assert "blind_asset_proof" in decoded["outputs"][0]
        hex_tx = self.nodes[2].finalizepsbt(psbt)['hex']
        assert_equal(self.num_blinded_outputs(hex_tx), 1)
        self.nodes[2].sendrawtransaction(hex_tx)
        self.generate(self.nodes[0], 1)
        self.sync_all()

        # Try to send nonconf->(nonconf + conf + conf) -- two conf to make blinders balance
        nonconf_addr_5 = self.get_address(False, 1)
        conf_addr_5 = self.get_address(True, 1)
        conf_addr_6 = self.get_address(True, 2)
        psbt = self.nodes[0].createpsbt([{"txid": txid_nonconf, "vout": 2}], [{nonconf_addr_5: 24.999}, {conf_addr_5: 14.999, "blinder_index": 0}, {conf_addr_6: 10, "blinder_index": 0}, {"fee": 0.002}])
        psbt = self.nodes[0].walletprocesspsbt(psbt)['psbt']
        hex_tx = self.nodes[0].finalizepsbt(psbt)['hex']
        assert_equal(self.num_blinded_outputs(hex_tx), 2)
        self.nodes[0].sendrawtransaction(hex_tx)
        self.generate(self.nodes[0], 1)
        self.sync_all()

        # Try a multiparty blinded tx
        # Prepare wallets and UTXOs for inputs
        self.nodes[2].createwallet("w1")
        w1 = self.nodes[2].get_wallet_rpc("w1")
        self.nodes[2].createwallet("w2")
        w2 = self.nodes[2].get_wallet_rpc("w2")
        self.nodes[2].createwallet("w3")
        w3 = self.nodes[2].get_wallet_rpc("w3")
        w1_addr = w1.getaddressinfo(w1.getnewaddress())["confidential"]
        w2_addr = w2.getaddressinfo(w2.getnewaddress())["confidential"]
        w3_addr = w3.getaddressinfo(w3.getnewaddress())["confidential"]
        txid1 = self.nodes[0].sendtoaddress(w1_addr, 10)
        txid2 = self.nodes[0].sendtoaddress(w2_addr, 10)
        txid3 = self.nodes[0].sendtoaddress(w3_addr, 10)
        self.sync_all()
        vout1 = find_vout_for_address(self.nodes[2], txid1, w1_addr)
        vout2 = find_vout_for_address(self.nodes[2], txid2, w2_addr)
        vout3 = find_vout_for_address(self.nodes[2], txid3, w3_addr)
        self.generate(self.nodes[0], 1)
        self.sync_all()
        # Check that a walletprocesspsbt fails if the wallet has a blind input but no blind outputs
        created_psbt = self.nodes[0].createpsbt(
            [
                {"txid": txid1, "vout": vout1},
                {"txid": txid2, "vout": vout2},
            ],
            [
                {self.get_address(True, 0): Decimal("19.999"), "blinder_index": 0},
                {"fee": Decimal("0.001")}
            ]
        )
        up_psbt1 = w1.walletprocesspsbt(psbt=created_psbt, sign=False)["psbt"]
        assert_raises_rpc_error(-4, "Transaction has blind inputs belonging to this blinder but does not have outputs to blind", w2.walletprocesspsbt, up_psbt1, False)
        # Make the PSBT
        created_psbt = self.nodes[0].createpsbt(
            [
                {"txid": txid1, "vout": vout1},
                {"txid": txid2, "vout": vout2},
                {"txid": txid3, "vout": vout3},
            ],
            [
                {self.get_address(True, 0): Decimal("9.999"), "blinder_index": 0},
                {self.get_address(True, 0): Decimal("9.999"), "blinder_index": 1},
                {self.get_address(True, 0): Decimal("9.999"), "blinder_index": 2},
                {"fee": Decimal("0.003")}
            ]
        )
        # Update all but don't blind
        up_psbt1 = w1.walletprocesspsbt(psbt=created_psbt, sign=False)["psbt"]
        up_psbt2 = w2.walletprocesspsbt(psbt=created_psbt, sign=False)["psbt"]
        up_psbt3 = w3.walletprocesspsbt(psbt=created_psbt, sign=False)["psbt"]
        # Combine updated
        comb_psbt1 = self.nodes[0].combinepsbt([up_psbt1, up_psbt2, up_psbt3])
        # 1 and 2 blind
        blind_psbt1 = w1.walletprocesspsbt(psbt=comb_psbt1, sign=False)["psbt"]
        blind_psbt2 = w2.walletprocesspsbt(psbt=comb_psbt1, sign=False)["psbt"]
        # Check that trying to blind a PSET where our inputs are already blinded results in no change
        re_blind_psbt2 = w2.walletprocesspsbt(psbt=blind_psbt2, sign=False)["psbt"]
        assert_equal(blind_psbt2, re_blind_psbt2)
        # Make sure combinepsbt does not work if the result would have imbalanced values and blinders
        blind_psbt3 = w3.walletprocesspsbt(psbt=comb_psbt1, sign=False)["psbt"]
        assert_raises_rpc_error(-22, "Cannot combine PSETs as the values and blinders would become imbalanced", self.nodes[0].combinepsbt, [blind_psbt1, blind_psbt2, blind_psbt3])
        # Combine 1 and 2 blinded
        comb_psbt2 = self.nodes[0].combinepsbt([blind_psbt1, blind_psbt2])
        # 3 Updates and blinds combined
        blind_psbt = w3.walletprocesspsbt(psbt=comb_psbt2, sign=False)["psbt"]
        # All sign
        sign_psbt1 = w1.walletprocesspsbt(psbt=blind_psbt)["psbt"]
        sign_psbt2 = w2.walletprocesspsbt(psbt=blind_psbt)["psbt"]
        sign_psbt3 = w3.walletprocesspsbt(psbt=blind_psbt)["psbt"]
        # Combine sigs
        comb_psbt2 = self.nodes[0].combinepsbt([sign_psbt1, sign_psbt2, sign_psbt3])
        # Finalize and send
        tx = self.nodes[0].finalizepsbt(comb_psbt2)["hex"]
        self.nodes[0].sendrawtransaction(tx)
        self.generate(self.nodes[0], 1)
        self.sync_all()

        # Regression for #1049
        # 1. Create a one-blinded-output PSET and check that it is blinded correctly
        addr = self.nodes[0].getnewaddress()
        conf_addr = self.nodes[0].getaddressinfo(addr)['confidential']
        unconf_addr = self.nodes[0].getaddressinfo(addr)['unconfidential']
        # 1a. Funding should succeed and *not* add a OP_RETURN output
        funded = self.nodes[1].walletcreatefundedpsbt([], [{conf_addr: self.nodes[1].getbalance()['bitcoin']}], 0, {"subtractFeeFromOutputs": [0]})["psbt"]
        assert_equal(
            outputs_info(self.nodes[1].decodepsbt(funded)["outputs"]),
            {
                (unconf_addr, True, False),
                (None, False, False), # fee
            },
        )
        # 1b. `walletprocesspsbt` should then succeed in creating a full transaction
        signed = self.nodes[1].walletprocesspsbt(funded)["psbt"]
        tx = self.nodes[1].finalizepsbt(signed)["hex"]
        assert self.nodes[1].testmempoolaccept([tx])[0]['allowed']
        # 2. Create a one-unblinded-output PSET and check that it is blinded correctly
        # 2a. Funding should succeed and add a OP_RETURN output
        funded = self.nodes[1].walletcreatefundedpsbt([], [{unconf_addr: self.nodes[1].getbalance()['bitcoin']}], 0, {"subtractFeeFromOutputs": [0]})["psbt"]
        assert_equal(
            outputs_info(self.nodes[1].decodepsbt(funded)["outputs"]),
            {
                (unconf_addr, False, False),
                (None, True, True), # blinded OP_RETURN
                (None, False, False), # fee
            },
        )
        # 2b. `walletprocesspsbt` should then succeed in creating a full transaction
        signed = self.nodes[1].walletprocesspsbt(funded)["psbt"]
        tx = self.nodes[1].finalizepsbt(signed)["hex"]
        assert self.nodes[1].testmempoolaccept([tx])[0]['allowed']

    def pset_confidential_proofs(self):
        UNBLINDED = "cHNldP8BAgQCAAAAAQMEAAAAAAEEAQEBBQECAfsEAgAAAAABAP1UAQIAAAAAASopobdl5W15RSedscp/8bxEXKuKIMOZw+JTqgD8qJEKBAAAAAD9////Awrye7Xu4kI5VnpTDeGaq8sYdXP3qdzYaHrLDRzaC8y51ggl1U8hJxSo+8GcTzHv926wsqTTkOrdBnJo8qcLwLQauQKktt71EJU7HTH5HsgG4kJV/tC32F992/WgieIPRkUkmxYAFPrs/iioimRS5hoJKl/hua83d7rwC1uuuLvfuQh38wHS+0Vg2ecXzypsUabYofOFaGSrICByCKvjgTF6TdHNp2el7Cwi+94dy4qMDrEh/25Aqnc+5qABAqWPEY9ZNCz7m64pANrr04bVgPxaWCr7LvvWGH5FLzvRFgAU96wAzcLFRah7B8gq17sVY9Uso18BIw9PXUt8b6hFgG7k9ncTRZ4baejmD87i5JQMeg1d4bIBAAAAAAAAKfQAAAAAAAABAXoK8nu17uJCOVZ6Uw3hmqvLGHVz96nc2Gh6yw0c2gvMudYIJdVPIScUqPvBnE8x7/dusLKk05Dq3QZyaPKnC8C0GrkCpLbe9RCVOx0x+R7IBuJCVf7Qt9hffdv1oIniD0ZFJJsWABT67P4oqIpkUuYaCSpf4bmvN3e68CIGA3pgD7iheh1WkyCWvviXQBa9KOJk6JBeYxEpPuxiRBOvEElHIxkAAACAAQAAgAMAAIABDiB25bQww62kp1L1uQVb7MxEVoem8kCzSmM5DW09I9V6DQEPBAAAAAABEAT/////B/wEcHNldA79CwFgAgAHY7+9IRzxAXWemL7C9M7CBAqQoSrXRoxI5/YnMLV6nV/GBMEhmvoDFJcNzRXI/LrIRMLZFvNrP5IupN8OZ+4q+++aJTnuYCZIDR1pssb0JHA0z2UXkEYdHv26qoW26RbLf2LNh29yVIOHG3jqqc7+L7F4UELZmjlEs6R1sulqQ0ePCUUgAsqURkdnNKtl0nORiyLN/9JfqGGTC30WhsdXifWRmqOfkWil0Va1bDYumMU7zJdW/go83ODuZ5VZVWFsBLFSn9HxF1SaFCGt197qo8dr+vhPZwb72k13A72D+5Lx7UKoYqamRJsoAZdUZ/oVd9GRlPbAmRPV7iOxmPYf+t9AQiEd0Z4AIgICuujF5+Lk/uCeX9+RWtJ8ioG51rogGduwt+iY1tZFtjUQSUcjGQAAAIAAAACACwAAgAEDCAC/fEgYCQAAAQQWABSD7wBNJDxW82D5YkC7B5ebqReUWQf8BHBzZXQCICMPT11LfG+oRYBu5PZ3E0WeG2no5g/O4uSUDHoNXeGyB/wEcHNldAYhAwxmNPa94Vg9u/nZBWC/8IYTgnp85V5TMOEFWTTAcF2pB/wEcHNldAgEAAAAAAABAwgA4fUFAAAAAAEEAAf8BHBzZXQCICMPT11LfG+oRYBu5PZ3E0WeG2no5g/O4uSUDHoNXeGyB/wEcHNldAgEAAAAAAA="
        BLINDED = "cHNldP8BAgQCAAAAAQMEAAAAAAEEAQEBBQECAfsEAgAAAAABAP1UAQIAAAAAASopobdl5W15RSedscp/8bxEXKuKIMOZw+JTqgD8qJEKBAAAAAD9////Awrye7Xu4kI5VnpTDeGaq8sYdXP3qdzYaHrLDRzaC8y51ggl1U8hJxSo+8GcTzHv926wsqTTkOrdBnJo8qcLwLQauQKktt71EJU7HTH5HsgG4kJV/tC32F992/WgieIPRkUkmxYAFPrs/iioimRS5hoJKl/hua83d7rwC1uuuLvfuQh38wHS+0Vg2ecXzypsUabYofOFaGSrICByCKvjgTF6TdHNp2el7Cwi+94dy4qMDrEh/25Aqnc+5qABAqWPEY9ZNCz7m64pANrr04bVgPxaWCr7LvvWGH5FLzvRFgAU96wAzcLFRah7B8gq17sVY9Uso18BIw9PXUt8b6hFgG7k9ncTRZ4baejmD87i5JQMeg1d4bIBAAAAAAAAKfQAAAAAAAABAXoK8nu17uJCOVZ6Uw3hmqvLGHVz96nc2Gh6yw0c2gvMudYIJdVPIScUqPvBnE8x7/dusLKk05Dq3QZyaPKnC8C0GrkCpLbe9RCVOx0x+R7IBuJCVf7Qt9hffdv1oIniD0ZFJJsWABT67P4oqIpkUuYaCSpf4bmvN3e68CIGA3pgD7iheh1WkyCWvviXQBa9KOJk6JBeYxEpPuxiRBOvEElHIxkAAACAAQAAgAMAAIABDiB25bQww62kp1L1uQVb7MxEVoem8kCzSmM5DW09I9V6DQEPBAAAAAABEAT/////B/wEcHNldA79CwFgAgAHY7+9IRzxAXWemL7C9M7CBAqQoSrXRoxI5/YnMLV6nV/GBMEhmvoDFJcNzRXI/LrIRMLZFvNrP5IupN8OZ+4q+++aJTnuYCZIDR1pssb0JHA0z2UXkEYdHv26qoW26RbLf2LNh29yVIOHG3jqqc7+L7F4UELZmjlEs6R1sulqQ0ePCUUgAsqURkdnNKtl0nORiyLN/9JfqGGTC30WhsdXifWRmqOfkWil0Va1bDYumMU7zJdW/go83ODuZ5VZVWFsBLFSn9HxF1SaFCGt197qo8dr+vhPZwb72k13A72D+5Lx7UKoYqamRJsoAZdUZ/oVd9GRlPbAmRPV7iOxmPYf+t9AQiEd0Z4AIgICuujF5+Lk/uCeX9+RWtJ8ioG51rogGduwt+iY1tZFtjUQSUcjGQAAAIAAAACACwAAgAEDCAC/fEgYCQAAAQQWABSD7wBNJDxW82D5YkC7B5ebqReUWQf8BHBzZXQBIQgGgfEKdAooxyl0pgId27fqPNDTNJzj2ga4NCXs2+6zeAf8BHBzZXQCICMPT11LfG+oRYBu5PZ3E0WeG2no5g/O4uSUDHoNXeGyB/wEcHNldAMhCy5VZJhP9SRRur+Fix1a6ijcBFLLkrt7//fqHxCGN0pEB/wEcHNldAT9CwFgAgAACRhIfL75AJaUOCJ2q+YnbnYTFqluECvtDoJFGcrYvu5VsxPdASJNduFIJRBglnPdW73QRjqt+r3KlxBQ3XUWTce6is6cGED9eySEVJwBXz4Mt8SjqM2GsyUfqC+Ey3+APGgh54MYLt+HHKmt6ibcvE1DDU/UGpVo+I3cY/kgKJzrWMG6y/jDm/CHcF49L8EBtYC7iSrBhwzmDk7DmiViiQFCTUDfIqilX/piqS9ZlO4JNydA5kmLqXkj/xtR2hKt57wknqqvM7/car1S4Do8VljtG9lCzvSOBtBvijSwpFY1KaVFjpj0UZI9XJQ2eEbMrqC0qygNBi1f+ULyZFccNSGpXaZnrZAH/ARwc2V0BUMBAAECnwdoJ4rVnGgLT0He5GaLEhDnGqCKcH0nlTi1T53tBYMI8InonQGT61IAjoLcRxOqzMLgEC3KXg7yW8x6d6VmB/wEcHNldAYhAwxmNPa94Vg9u/nZBWC/8IYTgnp85V5TMOEFWTTAcF2pB/wEcHNldAchAitGVbG/bZNcV2ifjimuh04FOwRlxNrNPva66U6/RiHFB/wEcHNldAgEAAAAAAf8BHBzZXQJSSAAAAkYSHy/AIN6lvAUJ1o6ZQK5i/ewcpqRz4eW8zMzXFO/ZlNvAomxweIBD8YyywTguhBMI0BdLs2VeS5mc5e1oR0R27YAUccH/ARwc2V0CkMBAAGJm91DfvVBUOaEFZ0uH1RbT2cgI9MN9k1lE1hlWc2AtALpMJ17khkivt8F7dgCAVdBvcHFaw138ZsVfiD7g480AAEDCADh9QUAAAAAAQQAB/wEcHNldAIgIw9PXUt8b6hFgG7k9ncTRZ4baejmD87i5JQMeg1d4bIH/ARwc2V0CAQAAAAAAA=="
        NO_VALUE_PROOF = "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"
        BAD_VALUE_PROOF = "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"
        NO_ASSET_PROOF = "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"
        BAD_ASSET_PROOF = "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"
        ONLY_BLIND = "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"
        INPUT_ALL_PROOFS = "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"
        INPUT_BAD_VALUE = "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"
        INPUT_BAD_VALUE_PROOF = "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"
        INPUT_BAD_ASSET = "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"
        INPUT_BAD_ASSET_PROOF = "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"
        INPUT_MISSING_VALUE = "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"
        INPUT_MISSING_VALUE_PROOF = "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"
        INPUT_MISSING_ASSET = "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"
        INPUT_MISSING_ASSET_PROOF = "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"

        # Check warnings for PSETs
        stats = [output.get("status") for output in self.nodes[0].decodepsbt(UNBLINDED)["outputs"]]
        assert_equal(stats, ["needs blinding", None])
        stats = [output for output in self.nodes[0].analyzepsbt(UNBLINDED)["outputs"]]
        assert_equal(stats, [
            {"blind": True, "status": "unblinded" },
            {"blind": False, "status": "done" },
        ])

        for output in self.nodes[0].decodepsbt(BLINDED)["outputs"]:
            assert "status" not in output
        for output in self.nodes[0].analyzepsbt(BLINDED)["outputs"]:
            assert_equal (output["status"], "done")

        stats = [output.get("status") for output in self.nodes[0].decodepsbt(NO_VALUE_PROOF)["outputs"]]
        assert_equal(stats, [
            "WARNING: has confidential and explicit values but no proof connecting them",
            None,
        ])
        stats = [output for output in self.nodes[0].analyzepsbt(NO_VALUE_PROOF)["outputs"]]
        assert_equal(stats, [
            {"blind": True, "status": "WARNING: has confidential and explicit values but no proof connecting them" },
            {"blind": False, "status": "done" },
        ])

        stats = [output.get("status") for output in self.nodes[0].decodepsbt(BAD_VALUE_PROOF)["outputs"]]
        assert_equal(stats, [
            "ERROR: has invalid value proof, the value may be a lie!",
            None,
        ])
        stats = [output for output in self.nodes[0].analyzepsbt(BAD_VALUE_PROOF)["outputs"]]
        assert_equal(stats, [
            {"blind": True, "status": "ERROR: has invalid value proof, the value may be a lie!" },
            {"blind": False, "status": "done" },
        ])

        stats = [output.get("status") for output in self.nodes[0].decodepsbt(NO_ASSET_PROOF)["outputs"]]
        assert_equal(stats, [
            "WARNING: has confidential and explicit assets but no proof connecting them",
            None,
        ])
        stats = [output for output in self.nodes[0].analyzepsbt(NO_ASSET_PROOF)["outputs"]]
        assert_equal(stats, [
            {"blind": True, "status": "WARNING: has confidential and explicit assets but no proof connecting them" },
            {"blind": False, "status": "done" },
        ])

        stats = [output.get("status") for output in self.nodes[0].decodepsbt(BAD_ASSET_PROOF)["outputs"]]
        assert_equal(stats, [
            "ERROR: has invalid asset proof, the asset may be a lie!",
            None,
        ])
        stats = [output for output in self.nodes[0].analyzepsbt(BAD_ASSET_PROOF)["outputs"]]
        assert_equal(stats, [
            {"blind": True, "status": "ERROR: has invalid asset proof, the asset may be a lie!" },
            {"blind": False, "status": "done" },
        ])

        stats = [output.get("status") for output in self.nodes[0].decodepsbt(ONLY_BLIND)["outputs"]]
        assert_equal(stats, [None, None])
        stats = [output for output in self.nodes[0].analyzepsbt(ONLY_BLIND)["outputs"]]
        assert_equal(stats, [
            {"blind": True, "status": "done" },
            {"blind": False, "status": "done" },
        ])

        assert "status" not in self.nodes[0].decodepsbt(INPUT_ALL_PROOFS)["inputs"][0]
        assert_equal("ERROR: has invalid value proof, the value may be a lie!", self.nodes[0].decodepsbt(INPUT_BAD_VALUE)["inputs"][0]["status"])
        assert_equal("ERROR: has invalid value proof, the value may be a lie!", self.nodes[0].decodepsbt(INPUT_BAD_VALUE_PROOF)["inputs"][0]["status"])
        assert_equal("ERROR: has invalid asset proof, the asset may be a lie!", self.nodes[0].decodepsbt(INPUT_BAD_ASSET)["inputs"][0]["status"])
        assert_equal("ERROR: has invalid asset proof, the asset may be a lie!", self.nodes[0].decodepsbt(INPUT_BAD_ASSET_PROOF)["inputs"][0]["status"])
        assert_raises_rpc_error(-22, "TX decode failed Input explicit value and value proof must be provided together", self.nodes[0].decodepsbt, INPUT_MISSING_VALUE)
        assert_raises_rpc_error(-22, "TX decode failed Input explicit value and value proof must be provided together", self.nodes[0].decodepsbt, INPUT_MISSING_VALUE_PROOF)
        assert_raises_rpc_error(-22, "TX decode failed Input explicit asset and asset proof must be provided together", self.nodes[0].decodepsbt, INPUT_MISSING_ASSET)
        assert_raises_rpc_error(-22, "TX decode failed Input explicit asset and asset proof must be provided together", self.nodes[0].decodepsbt, INPUT_MISSING_ASSET_PROOF)

        # The fully-blinded (with proofs) PSET will combine with the blinded one,
        # and will copy the blinded data
        assert_equal (self.nodes[0].combinepsbt([UNBLINDED, BLINDED]), BLINDED)
        assert_equal (self.nodes[0].combinepsbt([BLINDED, UNBLINDED]), BLINDED)
        # When combining, "bad proofs" are the same as blinded data. So these transactions
        # will be interpreted as partially blinded (exp asset blind value, or vice-versa),
        # and will combine accordingly. These details are not so important, but what *IS*
        # important is that you cannot combine any of the bad-proof PSETs with the
        # unblinded one.
        self.nodes[0].combinepsbt([NO_VALUE_PROOF, BAD_VALUE_PROOF])
        self.nodes[0].combinepsbt([NO_ASSET_PROOF, BAD_ASSET_PROOF])
        assert_raises_rpc_error(-8, "PSBTs not compatible (different transactions)", self.nodes[0].combinepsbt, [BAD_VALUE_PROOF, BAD_ASSET_PROOF])
        for bad_pset in [ NO_VALUE_PROOF, BAD_VALUE_PROOF, NO_ASSET_PROOF, BAD_ASSET_PROOF ]:
            assert_raises_rpc_error(-8, "PSBTs not compatible (different transactions)", self.nodes[0].combinepsbt, [UNBLINDED, bad_pset])
            assert_raises_rpc_error(-8, "PSBTs not compatible (different transactions)", self.nodes[0].combinepsbt, [ONLY_BLIND, bad_pset])
            assert_raises_rpc_error(-8, "PSBTs not compatible (different transactions)", self.nodes[0].combinepsbt, [BLINDED, bad_pset])

    def run_test(self):
        self.generate(self.nodes[0], 200)
        self.sync_all()

        # Run all the pre-Elements, tests first with non-confidential addresses, then again with confidential addresses
        self.run_basic_tests(False)
        self.run_basic_tests(True)

        # BIP 174 test vectors are disabled, because they have embedded serialized CTransactions, and
        #   the transaction serialization format changed in Elements so none of them work
        #self.run_bip174_tests()

        # Some Confidential-Assets-specific tests
        self.run_ca_tests()
        self.run_unsafe_tests()

        if self.options.descriptors:
            self.test_utxo_conversion()

        self.test_input_confs_control()

        # Test that psbts with p2pkh outputs are created properly
        p2pkh = self.nodes[0].getnewaddress(address_type='legacy')
        psbt = self.nodes[1].walletcreatefundedpsbt([], [{p2pkh : 1}], 0, {"includeWatching" : True}, True)
        self.nodes[0].decodepsbt(psbt['psbt'])

        # Test decoding error: invalid base64
        assert_raises_rpc_error(-22, "TX decode failed invalid base64", self.nodes[0].decodepsbt, ";definitely not base64;")

        # Test serialisation acceptance of PSBT_ELEMENTS_GLOBAL_SCALAR
        old_serialization = 'cHNldP8B+wQCAAAAAQIEAgAAAAEEAQABBQEAJ/wEcHNldAABAgMEBQYHCAkKCwwNDg8QERITFBUWFxgZGhscHR4fIAEAAA=='
        new_serialization = 'cHNldP8B+wQCAAAAAQIEAgAAAAEEAQABBQEAJ/wEcHNldAABAgMEBQYHCAkKCwwNDg8QERITFBUWFxgZGhscHR4fIAAA'
        assert_equal(self.nodes[1].decodepsbt(old_serialization), self.nodes[1].decodepsbt(new_serialization))

        # Send to all types of addresses
        addr1 = self.nodes[1].getnewaddress("", "bech32")
        txid1 = self.nodes[0].sendtoaddress(addr1, 11)
        vout1 = find_output(self.nodes[0], txid1, 11)
        addr2 = self.nodes[1].getnewaddress("", "legacy")
        txid2 = self.nodes[0].sendtoaddress(addr2, 11)
        vout2 = find_output(self.nodes[0], txid2, 11)
        addr3 = self.nodes[1].getnewaddress("", "p2sh-segwit")
        txid3 = self.nodes[0].sendtoaddress(addr3, 11)
        vout3 = find_output(self.nodes[0], txid3, 11)
        self.sync_all()

        psbt_v2_required_keys = ["previous_vout", "sequence", "previous_txid"]

        def test_psbt_input_keys(psbt_input, keys):
            """Check that the psbt input has only the expected keys."""
            assert_equal(set(keys), set(psbt_input.keys()))

        # Create a PSBT. None of the inputs are filled initially
        psbt = self.nodes[1].createpsbt([{"txid":txid1, "vout":vout1},{"txid":txid2, "vout":vout2},{"txid":txid3, "vout":vout3}], [{self.nodes[0].getnewaddress():32.999}])
        decoded = self.nodes[1].decodepsbt(psbt)
        test_psbt_input_keys(decoded['inputs'][0], psbt_v2_required_keys)
        test_psbt_input_keys(decoded['inputs'][1], psbt_v2_required_keys)
        test_psbt_input_keys(decoded['inputs'][2], psbt_v2_required_keys)

        # Update a PSBT with UTXOs from the node
        # Bech32 inputs should be filled with witness UTXO. Other inputs should not be filled because they are non-witness
        updated = self.nodes[1].utxoupdatepsbt(psbt)
        decoded = self.nodes[1].decodepsbt(updated)
        test_psbt_input_keys(decoded['inputs'][0], psbt_v2_required_keys + ['witness_utxo'])
        test_psbt_input_keys(decoded['inputs'][1], psbt_v2_required_keys)
        test_psbt_input_keys(decoded['inputs'][2], psbt_v2_required_keys)

        # Try again, now while providing descriptors, making P2SH-segwit work, and causing bip32_derivs and redeem_script to be filled in
        descs = [self.nodes[1].getaddressinfo(addr)['desc'] for addr in [addr1,addr2,addr3]]
        updated = self.nodes[1].utxoupdatepsbt(psbt=psbt, descriptors=descs)
        decoded = self.nodes[1].decodepsbt(updated)
        test_psbt_input_keys(decoded['inputs'][0], psbt_v2_required_keys + ['witness_utxo', 'bip32_derivs'])
        test_psbt_input_keys(decoded['inputs'][1], psbt_v2_required_keys)
        test_psbt_input_keys(decoded['inputs'][2], psbt_v2_required_keys + ['witness_utxo', 'bip32_derivs', 'redeem_script'])

        # Cannot create PSBTv0
        assert_raises_rpc_error(-8, "The PSBT version can only be 2", self.nodes[0].createpsbt, [{"txid":txid1, "vout":vout1}], [{self.nodes[0].getnewaddress():Decimal('10.999')}], 0, True, 0)

        """
        # TODO: joinpsbts is disabled for PSBTv2s
        # Cannot join PSBTv2s
        psbt1 = self.nodes[1].createpsbt(inputs=[{"txid":txid1, "vout":vout1}], outputs=[{self.nodes[0].getnewaddress():Decimal('10.999')}], psbt_version=0)
        psbt2 = self.nodes[1].createpsbt(inputs=[{"txid":txid1, "vout":vout1}], outputs=[{self.nodes[0].getnewaddress():Decimal('10.999')}], psbt_version=2)
        assert_raises_rpc_error(-8, "joinpsbts only operates on version 0 PSBTs", self.nodes[1].joinpsbts, [psbt1, psbt2])

        # Two PSBTs with a common input should not be joinable
        psbt2 = self.nodes[1].createpsbt(inputs=[{"txid":txid1, "vout":vout1}], outputs=[{self.nodes[0].getnewaddress():Decimal('10.999')}], psbt_version=0)
        assert_raises_rpc_error(-8, "exists in multiple PSBTs", self.nodes[1].joinpsbts, [psbt1, psbt2])

        # Join two distinct PSBTs
        psbt1 = self.nodes[1].createpsbt(inputs=[{"txid":txid1, "vout":vout1},{"txid":txid2, "vout":vout2},{"txid":txid3, "vout":vout3}], outputs=[{self.nodes[0].getnewaddress():32.999}], psbt_version=0)
        addr4 = self.nodes[1].getnewaddress("", "p2sh-segwit")
        txid4 = self.nodes[0].sendtoaddress(addr4, 5)
        vout4 = find_output(self.nodes[0], txid4, 5)
        self.generate(self.nodes[0], 6)
        psbt2 = self.nodes[1].createpsbt(inputs=[{"txid":txid4, "vout":vout4}], outputs=[{self.nodes[0].getnewaddress():Decimal('4.999')}], psbt_version=0)
        psbt2 = self.nodes[1].walletprocesspsbt(psbt2)['psbt']
        psbt2_decoded = self.nodes[0].decodepsbt(psbt2)
        assert "final_scriptwitness" in psbt2_decoded['inputs'][0] and "final_scriptSig" in psbt2_decoded['inputs'][0]
        joined = self.nodes[0].joinpsbts([psbt1, psbt2])
        joined_decoded = self.nodes[0].decodepsbt(joined)
        assert_equal(len(joined_decoded['inputs']), 4)
        assert_equal(len(joined_decoded['outputs']), 2)
        assert "final_scriptwitness" not in joined_decoded['inputs'][3]
        assert "final_scriptSig" not in joined_decoded['inputs'][3]

        # Check that joining shuffles the inputs and outputs
        # 10 attempts should be enough to get a shuffled join
        shuffled = False
        for _ in range(10):
            shuffled_joined = self.nodes[0].joinpsbts([psbt1, psbt2])
            shuffled |= joined != shuffled_joined
            if shuffled:
                break
        assert shuffled
        """

        # Newly created PSBT needs UTXOs and updating
        addr = self.nodes[1].getnewaddress("", "p2sh-segwit")
        txid = self.nodes[0].sendtoaddress(addr, 7)
        addrinfo = self.nodes[1].getaddressinfo(addr)
        blockhash = self.generate(self.nodes[0], 6)[0]
        vout = find_output(self.nodes[0], txid, 7, blockhash=blockhash)
        psbt = self.nodes[1].createpsbt([{"txid":txid, "vout":vout}], [{self.nodes[0].getnewaddress("", "p2sh-segwit"):Decimal('6.999')}, {"fee": 0.001}])
        analyzed = self.nodes[0].analyzepsbt(psbt)
        assert not analyzed['inputs'][0]['has_utxo'] and not analyzed['inputs'][0]['is_final'] and analyzed['inputs'][0]['next'] == 'updater' and analyzed['next'] == 'updater'

        # After update with wallet, only needs signing
        updated = self.nodes[1].walletprocesspsbt(psbt, False, 'ALL', True)['psbt']
        analyzed = self.nodes[0].analyzepsbt(updated)
        assert analyzed['inputs'][0]['has_utxo'] and not analyzed['inputs'][0]['is_final'] and analyzed['inputs'][0]['next'] == 'signer' and analyzed['next'] == 'signer' and analyzed['inputs'][0]['missing']['signatures'][0] == addrinfo['embedded']['witness_program']

        # Check fee and size things
        assert_equal(analyzed['fee'], Decimal('0.001'))
        assert_equal(analyzed['estimated_vsize'], 215)
        assert_equal(analyzed['estimated_feerate'], Decimal('0.00465116'))

        # After signing and finalizing, needs extracting
        signed = self.nodes[1].walletprocesspsbt(updated)['psbt']
        analyzed = self.nodes[0].analyzepsbt(signed)
        assert analyzed['inputs'][0]['has_utxo'] and analyzed['inputs'][0]['is_final'] and analyzed['next'] == 'extractor'

        self.log.info("PSBT spending unspendable outputs should have error message and Creator as next")
        analysis = self.nodes[0].analyzepsbt("cHNldP8BAgQCAAAAAQMEAAAAAAEEAQIBBQEDAfsEAgAAAAABAUMBAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABAAAAAAvrwgAAF2oUt/X69ELjeX2nTof+fZ10l+OyAokDAQ4gWOh6IbVtrwwjvo5wcEVsM298uqXIdXkk9UWIe7Kr3XUBDwQAAAAAARAE/////wABAUMBAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABAAAAAAvrwgAAF2oUt/X69ELjeX2nTof+fZ10l+OyAokDAQ4gg40EJ9DsZQpoqka7CwmK6kQiwHGyyng1Kgd5WdB86h0BDwQBAAAAARAE/////wABAwgA4fUFAAAAAAEEAwAAAAf8BHBzZXQCICMPT11LfG+oRYBu5PZ3E0WeG2no5g/O4uSUDHoNXeGyAAEDCADh9QUAAAAAAQQD/1EAB/wEcHNldAIgIw9PXUt8b6hFgG7k9ncTRZ4baejmD87i5JQMeg1d4bIAAQMIAOH1BQAAAAABBAAH/ARwc2V0AiAjD09dS3xvqEWAbuT2dxNFnhtp6OYPzuLklAx6DV3hsgA=")
        assert_equal(analysis['next'], 'creator')
        assert_equal(analysis['error'], 'PSBT is not valid. Input 0 spends unspendable output')

        self.log.info("PSBT with invalid values should have error message and Creator as next")
        analysis = self.nodes[0].analyzepsbt("cHNldP8BAgQCAAAAAQMEAAAAAAEEAQEBBQEDAfsEAgAAAAABAUIBAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABAAfQ42qBgAAAFgAUlQO3F/Y8ejrjUcQ4E4Ai8Uw1OvYBDiDwNNARYAJurafOkaMMB+gTCJkDS+c11HE0/e16Cxs9AQEPBAAAAAABEAT/////AAEDCAD5ApUAAAAAAQQWABQo3DTHwdFy0CCa+h6+bi7VJs3tcgf8BHBzZXQCICMPT11LfG+oRYBu5PZ3E0WeG2no5g/O4uSUDHoNXeGyAAEDCPztApUAAAAAAQQWABT3JOIBe4i+DS+MLX0QCoEG4IYk1Af8BHBzZXQCICMPT11LfG+oRYBu5PZ3E0WeG2no5g/O4uSUDHoNXeGyAAEDCBAnAAAAAAAAAQQAB/wEcHNldAIgIw9PXUt8b6hFgG7k9ncTRZ4baejmD87i5JQMeg1d4bIA")
        assert_equal(analysis['next'], 'creator')
        assert_equal(analysis['error'], 'PSBT is not valid. Input 0 has invalid value')

        self.log.info("PSBT with signed, but not finalized, inputs should have Finalizer as next")
        analysis = self.nodes[0].analyzepsbt("cHNldP8BAgQCAAAAAQMEAAAAAAEEAQEBBQECAfsEAgAAAAABAP1GAQIAAAAAAtpPG2HNaQ7g1RhD88FfUIfJC09s/JOG0O51k1yf+BOGAAAAAAD9////B3dy8WfLRW/bNMpUigt/fepavcJqGEcCLA5HiRruhoABAAAAAP3///8DASMPT11LfG+oRYBu5PZ3E0WeG2no5g/O4uSUDHoNXeGyAQAAAAApuScAABepFI3c8Pl2L3+zDBFaVnU/fbC7u8YXhwrU7XTaIgX0Ui+O3yyCMz3qIu5eWWqhkpvPSTFUT4FBmQmTF2BnoPq5+0AfEsZypoPR7bm/U3+hxwcRJf4goV/3qwNo5VLiic5ce1dZCSUfff5XpRUYgb+WVEDRuomG9fTTbhYAFMThhARjTBZ+SqXAUJy8DC2ynay7ASMPT11LfG+oRYBu5PZ3E0WeG2no5g/O4uSUDHoNXeGyAQAAAAAAAHFwAAC0AQAAAQFDASMPT11LfG+oRYBu5PZ3E0WeG2no5g/O4uSUDHoNXeGyAQAAAAApuScAABepFI3c8Pl2L3+zDBFaVnU/fbC7u8YXhyICAsCxi4vc5vAaJ2S51LhmUQvRlbzhefuG3oE+dDVoas8YRzBEAiAO0A9CdWAlaTY1B8KOdngrWAkfzbNZ8lo+cxjGkGFTXAIgAy5K1VQsg5Gc+4ux4k8uEEs3NzMPvbCoHOLsaMYyep8BAQQWABQ1lhF0QZDAcsVXaiYPLLHEDZEmOAEOINut3V3yAGie+x4icl/6hWw9TuDiUk5fuXQWHKy14+ARAQ8EAAAAAAEQBP////8AAQMIYKC3KQAAAAABBBepFISnksGRURiWNA4SzGESWQAM3sn6hwf8BHBzZXQCICMPT11LfG+oRYBu5PZ3E0WeG2no5g/O4uSUDHoNXeGyAAEDCKCGAQAAAAAAAQQAB/wEcHNldAIgIw9PXUt8b6hFgG7k9ncTRZ4baejmD87i5JQMeg1d4bIA")
        assert_equal(analysis['next'], 'finalizer')

        analysis = self.nodes[0].analyzepsbt("cHNldP8BAgQCAAAAAQMEAAAAAAEEAQEBBQEDAfsEAgAAAAABDiDwNNARYAJurafOkaMMB+gTCJkDS+c11HE0/e16Cxs9AQEPBAAAAAABEAT/////AAEDCACAgWrj0AcAAQQWABQo3DTHwdFy0CCa+h6+bi7VJs3tcgf8BHBzZXQCICMPT11LfG+oRYBu5PZ3E0WeG2no5g/O4uSUDHoNXeGyAAEDCPztApUAAAAAAQQWABT3JOIBe4i+DS+MLX0QCoEG4IYk1Af8BHBzZXQCICMPT11LfG+oRYBu5PZ3E0WeG2no5g/O4uSUDHoNXeGyAAEDCBAnAAAAAAAAAQQAB/wEcHNldAIgIw9PXUt8b6hFgG7k9ncTRZ4baejmD87i5JQMeg1d4bIA")
        assert_equal(analysis['next'], 'creator')
        assert_equal(analysis['error'], 'PSBT is not valid. Output amount invalid')

        analysis = self.nodes[0].analyzepsbt("cHNldP8BAgQCAAAAAQMEAAAAAAEEAQEBBQEDAfsEAgAAAAABAKICAAAAAAHH6k+xEgicvmA3NdivY741Mkb1NOcXWr0NNl6hrR/WbgAAAEAA/////wIBIw9PXUt8b6hFgG7k9ncTRZ4baejmD87i5JQMeg1d4bIBAAAAAlQLx/QAFgAUTwXL7rzz4++YOM52QVixAcDETlwBIw9PXUt8b6hFgG7k9ncTRZ4baejmD87i5JQMeg1d4bIBAAAAAAAAHAwAAAAAAAABAUIBIw9PXUt8b6hFgG7k9ncTRZ4baejmD87i5JQMeg1d4bIBAAAAAlQLx/QAFgAUTwXL7rzz4++YOM52QVixAcDETlwBDiBzQYOL5jKoCOgksiRTvw0zfNZ+6QwsBsCZRoqc3PHoygEPBAIAAAABEAT9////ACICAt/pWo4sGJOHmHcQ8znTQCNWAZbCdkdGx3JaRfNNtbr6EAm9XegAAACAAQAAgEgAAIABAwjMugi/AQAAAAEEFgAUK4O/jgxELlCP5V61uOh6JJRLmncH/ARwc2V0AiAjD09dS3xvqEWAbuT2dxNFnhtp6OYPzuLklAx6DV3hsgf8BHBzZXQIBAAAAAAAAQMIAPkClQAAAAABBBYAFI0krONpRve47GLGy+HUYYTd9bvNB/wEcHNldAIgIw9PXUt8b6hFgG7k9ncTRZ4baejmD87i5JQMeg1d4bIH/ARwc2V0CAQAAAAAAAEDCCgUAAAAAAAAAQQAB/wEcHNldAIgIw9PXUt8b6hFgG7k9ncTRZ4baejmD87i5JQMeg1d4bIH/ARwc2V0CAQAAAAAAA==")
        assert_equal(analysis['next'], 'creator')
        assert_equal(analysis['error'], 'PSBT is not valid. Input 0 specifies invalid prevout')

        assert_raises_rpc_error(-25, 'Inputs missing or spent', self.nodes[0].walletprocesspsbt, "cHNldP8BAgQCAAAAAQMEAAAAAAEEAQEBBQEDAfsEAgAAAAABAKICAAAAAAHH6k+xEgicvmA3NdivY741Mkb1NOcXWr0NNl6hrR/WbgAAAEAA/////wIBIw9PXUt8b6hFgG7k9ncTRZ4baejmD87i5JQMeg1d4bIBAAAAAlQLx/QAFgAUTwXL7rzz4++YOM52QVixAcDETlwBIw9PXUt8b6hFgG7k9ncTRZ4baejmD87i5JQMeg1d4bIBAAAAAAAAHAwAAAAAAAABDiBzQYOL5jKoCOgksiRTvw0zfNZ+6QwsBsCZRoqc3PHoygEPBAIAAAABEAT9////ACICAt/pWo4sGJOHmHcQ8znTQCNWAZbCdkdGx3JaRfNNtbr6EAm9XegAAACAAQAAgEgAAIABAwjMugi/AQAAAAEEFgAUK4O/jgxELlCP5V61uOh6JJRLmncH/ARwc2V0AiAjD09dS3xvqEWAbuT2dxNFnhtp6OYPzuLklAx6DV3hsgf8BHBzZXQIBAAAAAAAAQMIAPkClQAAAAABBBYAFI0krONpRve47GLGy+HUYYTd9bvNB/wEcHNldAIgIw9PXUt8b6hFgG7k9ncTRZ4baejmD87i5JQMeg1d4bIH/ARwc2V0CAQAAAAAAAEDCCgUAAAAAAAAAQQAB/wEcHNldAIgIw9PXUt8b6hFgG7k9ncTRZ4baejmD87i5JQMeg1d4bIH/ARwc2V0CAQAAAAAAA==")

        self.log.info("Try decoding and combining transactions in various states of blindedness")
        self.pset_confidential_proofs()

        self.log.info("Test that we can fund psbts with external inputs specified")

        eckey = ECKey()
        eckey.generate()
        privkey = bytes_to_wif(eckey.get_bytes())

        self.nodes[1].createwallet("extfund")
        wallet = self.nodes[1].get_wallet_rpc("extfund")

        # Make a weird but signable script. sh(wsh(pkh())) descriptor accomplishes this
        desc = descsum_create("sh(wsh(pkh({})))".format(privkey))
        if self.options.descriptors:
            res = self.nodes[0].importdescriptors([{"desc": desc, "timestamp": "now"}])
        else:
            res = self.nodes[0].importmulti([{"desc": desc, "timestamp": "now"}])
        assert res[0]["success"]
        addr = self.nodes[0].deriveaddresses(desc)[0]
        addr_info = self.nodes[0].getaddressinfo(addr)

        self.nodes[0].sendtoaddress(addr, 10)
        self.nodes[0].sendtoaddress(wallet.getnewaddress(), 10)
        self.generate(self.nodes[0], 6)
        ext_utxo = self.nodes[0].listunspent(addresses=[addr])[0]

        # An external input without solving data should result in an error
        assert_raises_rpc_error(-4, "Not solvable pre-selected input COutPoint(%s, %s)" % (ext_utxo["txid"][0:10], ext_utxo["vout"]), wallet.walletcreatefundedpsbt, [ext_utxo], [{self.nodes[0].getnewaddress(): 15}])

        # But funding should work when the solving data is provided
        psbt = wallet.walletcreatefundedpsbt([ext_utxo], [{self.nodes[0].getnewaddress(): 15}], 0, {"add_inputs": True, "solving_data": {"pubkeys": [addr_info['pubkey']], "scripts": [addr_info["embedded"]["scriptPubKey"], addr_info["embedded"]["embedded"]["scriptPubKey"]]}})
        signed = wallet.walletprocesspsbt(psbt['psbt'])
        assert not signed['complete']
        signed = self.nodes[0].walletprocesspsbt(signed['psbt'])
        assert signed['complete']
        self.nodes[0].finalizepsbt(signed['psbt'])

        psbt = wallet.walletcreatefundedpsbt([ext_utxo], [{self.nodes[0].getnewaddress(): 15}], 0, {"add_inputs": True, "solving_data":{"descriptors": [desc]}})
        signed = wallet.walletprocesspsbt(psbt['psbt'])
        assert not signed['complete']
        signed = self.nodes[0].walletprocesspsbt(signed['psbt'])
        assert signed['complete']
        final = self.nodes[0].finalizepsbt(signed['psbt'], False)

        dec = self.nodes[0].decodepsbt(signed["psbt"])
        for i, txin in enumerate(dec["inputs"]):
            if txin["previous_txid"] == ext_utxo["txid"] and txin["previous_vout"] == ext_utxo["vout"]:
                input_idx = i
                break
        psbt_in = dec["inputs"][input_idx]
        # Calculate the input weight
        # (prevout + sequence + length of scriptSig + scriptsig + 1 byte buffer) * WITNESS_SCALE_FACTOR + num scriptWitness stack items + (length of stack item + stack item) * N stack items + 1 byte buffer
        len_scriptsig = len(psbt_in["final_scriptSig"]["hex"]) // 2 if "final_scriptSig" in psbt_in else 0
        len_scriptsig += len(ser_compact_size(len_scriptsig)) + 1
        len_scriptwitness = (sum([(len(x) // 2) + len(ser_compact_size(len(x) // 2)) for x in psbt_in["final_scriptwitness"]]) + len(psbt_in["final_scriptwitness"]) + 1) if "final_scriptwitness" in psbt_in else 0
        input_weight = ((40 + len_scriptsig) * WITNESS_SCALE_FACTOR) + len_scriptwitness
        low_input_weight = input_weight // 2
        high_input_weight = input_weight * 2

        # Input weight error conditions
        assert_raises_rpc_error(
            -8,
            "Input weights should be specified in inputs rather than in options.",
            wallet.walletcreatefundedpsbt,
            inputs=[ext_utxo],
            outputs=[{self.nodes[0].getnewaddress(): 15}],
            options={"input_weights": [{"txid": ext_utxo["txid"], "vout": ext_utxo["vout"], "weight": 1000}]}
        )

        # Funding should also work if the input weight is provided
        psbt = wallet.walletcreatefundedpsbt(
            inputs=[{"txid": ext_utxo["txid"], "vout": ext_utxo["vout"], "weight": input_weight}],
            outputs=[{self.nodes[0].getnewaddress(): 15}],
            options={"add_inputs": True}
        )
        signed = wallet.walletprocesspsbt(psbt["psbt"])
        signed = self.nodes[0].walletprocesspsbt(signed["psbt"])
        final = self.nodes[0].finalizepsbt(signed["psbt"])
        assert self.nodes[0].testmempoolaccept([final["hex"]])[0]["allowed"]
        # Reducing the weight should have a lower fee
        psbt2 = wallet.walletcreatefundedpsbt(
            inputs=[{"txid": ext_utxo["txid"], "vout": ext_utxo["vout"], "weight": low_input_weight}],
            outputs=[{self.nodes[0].getnewaddress(): 15}],
            options={"add_inputs": True}
        )
        assert_greater_than(psbt["fee"], psbt2["fee"])
        # Increasing the weight should have a higher fee
        psbt2 = wallet.walletcreatefundedpsbt(
            inputs=[{"txid": ext_utxo["txid"], "vout": ext_utxo["vout"], "weight": high_input_weight}],
            outputs=[{self.nodes[0].getnewaddress(): 15}],
            options={"add_inputs": True}
        )
        assert_greater_than(psbt2["fee"], psbt["fee"])
        # The provided weight should override the calculated weight when solving data is provided
        psbt3 = wallet.walletcreatefundedpsbt(
            inputs=[{"txid": ext_utxo["txid"], "vout": ext_utxo["vout"], "weight": high_input_weight}],
            outputs=[{self.nodes[0].getnewaddress(): 15}],
            options={'add_inputs': True, "solving_data":{"descriptors": [desc]}}
        )
        assert_equal(psbt2["fee"], psbt3["fee"])

        # Import the external utxo descriptor so that we can sign for it from the test wallet
        if self.options.descriptors:
            res = wallet.importdescriptors([{"desc": desc, "timestamp": "now"}])
        else:
            res = wallet.importmulti([{"desc": desc, "timestamp": "now"}])
        assert res[0]["success"]
        # The provided weight should override the calculated weight for a wallet input
        psbt3 = wallet.walletcreatefundedpsbt(
            inputs=[{"txid": ext_utxo["txid"], "vout": ext_utxo["vout"], "weight": high_input_weight}],
            outputs=[{self.nodes[0].getnewaddress(): 15}],
            options={"add_inputs": True}
        )
        assert_equal(psbt2["fee"], psbt3["fee"])

        self.log.info("Test signing inputs that the wallet has keys for but is not watching the scripts")
        self.nodes[1].createwallet(wallet_name="scriptwatchonly", disable_private_keys=True)
        watchonly = self.nodes[1].get_wallet_rpc("scriptwatchonly")

        eckey = ECKey()
        eckey.generate()
        privkey = bytes_to_wif(eckey.get_bytes())

        desc = descsum_create("wsh(pkh({}))".format(eckey.get_pubkey().get_bytes().hex()))
        if self.options.descriptors:
            res = watchonly.importdescriptors([{"desc": desc, "timestamp": "now"}])
        else:
            res = watchonly.importmulti([{"desc": desc, "timestamp": "now"}])
        assert res[0]["success"]
        addr = self.nodes[0].deriveaddresses(desc)[0]
        self.nodes[0].sendtoaddress(addr, 10)
        self.generate(self.nodes[0], 1)
        self.nodes[0].importprivkey(privkey)

        psbt = watchonly.walletcreatefundedpsbt([], [{wallet.getnewaddress(): watchonly.getbalance()['bitcoin']}], None, {"subtractFeeFromOutputs": [0]})['psbt']
        psbt = self.nodes[0].walletprocesspsbt(psbt)["psbt"]
        self.nodes[0].sendrawtransaction(self.nodes[0].finalizepsbt(psbt)["hex"])

        # Same test but for taproot
        if self.options.descriptors:
            eckey = ECKey()
            eckey.generate()
            privkey = bytes_to_wif(eckey.get_bytes())

            desc = descsum_create("tr({},pk({}))".format(H_POINT, eckey.get_pubkey().get_bytes().hex()))
            res = watchonly.importdescriptors([{"desc": desc, "timestamp": "now"}])
            assert res[0]["success"]
            addr = self.nodes[0].deriveaddresses(desc)[0]
            self.nodes[0].sendtoaddress(addr, 10)
            self.generate(self.nodes[0], 1)
            self.nodes[0].importdescriptors([{"desc": descsum_create("tr({})".format(privkey)), "timestamp":"now"}])

            # psbt = watchonly.walletcreatefundedpsbt([], [{wallet.getnewaddress(): watchonly.getbalance()['bitcoin']}], None, {"subtractFeeFromOutputs": [0]})['psbt']
            # ELEMENTS: FIXME
            # psbt = watchonly.sendall([wallet.getnewaddress(), addr])["psbt"]
            # psbt = self.nodes[0].walletprocesspsbt(psbt)["psbt"]
            # txid = self.nodes[0].sendrawtransaction(self.nodes[0].finalizepsbt(psbt)["hex"])
            # vout = find_vout_for_address(self.nodes[0], txid, addr)

            # # Make sure tap tree is in psbt
            # parsed_psbt = PSBT.from_base64(psbt)
            # assert_greater_than(len(parsed_psbt.o[vout].map[PSBT_OUT_TAP_TREE]), 0)
            # assert "taproot_tree" in self.nodes[0].decodepsbt(psbt)["outputs"][vout]
            # parsed_psbt.make_blank()
            # comb_psbt = self.nodes[0].combinepsbt([psbt, parsed_psbt.to_base64()])
            # assert_equal(comb_psbt, psbt)

            self.log.info("Test that walletprocesspsbt both updates and signs a non-updated psbt containing Taproot inputs")
            addr = self.nodes[0].getnewaddress("", "bech32m")
            txid = self.nodes[0].sendtoaddress(addr, 1)
            vout = find_vout_for_address(self.nodes[0], txid, addr)
            psbt = self.nodes[0].createpsbt([{"txid": txid, "vout": vout}], [{self.nodes[0].getnewaddress(): 0.9999}, {"fee": 0.0001}])
            signed = self.nodes[0].walletprocesspsbt(psbt)
            rawtx = self.nodes[0].finalizepsbt(signed["psbt"])["hex"]
            self.nodes[0].sendrawtransaction(rawtx)
            self.generate(self.nodes[0], 1)

            # Make sure tap tree is not in psbt
            # ELEMENTS: FIXME
            # parsed_psbt = PSBT.from_base64(psbt)
            # assert PSBT_OUT_TAP_TREE not in parsed_psbt.o[0].map
            # assert "taproot_tree" not in self.nodes[0].decodepsbt(psbt)["outputs"][0]
            # parsed_psbt.make_blank()
            # comb_psbt = self.nodes[0].combinepsbt([psbt, parsed_psbt.to_base64()])
            # assert_equal(comb_psbt, psbt)

        # ELEMENTS FIXME
        # self.log.info("Test decoding PSBT with per-input preimage types")
        # # note that the decodepsbt RPC doesn't check whether preimages and hashes match
        # hash_ripemd160, preimage_ripemd160 = random_bytes(20), random_bytes(50)
        # hash_sha256, preimage_sha256 = random_bytes(32), random_bytes(50)
        # hash_hash160, preimage_hash160 = random_bytes(20), random_bytes(50)
        # hash_hash256, preimage_hash256 = random_bytes(32), random_bytes(50)

        # tx = CTransaction()
        # tx.vin = [CTxIn(outpoint=COutPoint(hash=int('aa' * 32, 16), n=0), scriptSig=b""),
        #           CTxIn(outpoint=COutPoint(hash=int('bb' * 32, 16), n=0), scriptSig=b""),
        #           CTxIn(outpoint=COutPoint(hash=int('cc' * 32, 16), n=0), scriptSig=b""),
        #           CTxIn(outpoint=COutPoint(hash=int('dd' * 32, 16), n=0), scriptSig=b"")]
        # tx.vout = [CTxOut(nValue=0, scriptPubKey=b"")]
        # psbt = PSBT()
        # psbt.g = PSBTMap({PSBT_GLOBAL_UNSIGNED_TX: tx.serialize()})
        # psbt.i = [PSBTMap({bytes([PSBT_IN_RIPEMD160]) + hash_ripemd160: preimage_ripemd160}),
        #           PSBTMap({bytes([PSBT_IN_SHA256]) + hash_sha256: preimage_sha256}),
        #           PSBTMap({bytes([PSBT_IN_HASH160]) + hash_hash160: preimage_hash160}),
        #           PSBTMap({bytes([PSBT_IN_HASH256]) + hash_hash256: preimage_hash256})]
        # psbt.o = [PSBTMap()]
        # res_inputs = self.nodes[0].decodepsbt(psbt.to_base64())["inputs"]
        # assert_equal(len(res_inputs), 4)
        # preimage_keys = ["ripemd160_preimages", "sha256_preimages", "hash160_preimages", "hash256_preimages"]
        # expected_hashes = [hash_ripemd160, hash_sha256, hash_hash160, hash_hash256]
        # expected_preimages = [preimage_ripemd160, preimage_sha256, preimage_hash160, preimage_hash256]
        # for res_input, preimage_key, hash, preimage in zip(res_inputs, preimage_keys, expected_hashes, expected_preimages):
        #     assert preimage_key in res_input
        #     assert_equal(len(res_input[preimage_key]), 1)
        #     assert hash.hex() in res_input[preimage_key]
        #     assert_equal(res_input[preimage_key][hash.hex()], preimage.hex())

        # ELEMENTS FIXME
        # self.log.info("Test that combining PSBTs with different transactions fails")
        # tx = CTransaction()
        # tx.vin = [CTxIn(outpoint=COutPoint(hash=int('aa' * 32, 16), n=0), scriptSig=b"")]
        # tx.vout = [CTxOut(nValue=0, scriptPubKey=b"")]
        # psbt1 = PSBT(g=PSBTMap({PSBT_GLOBAL_UNSIGNED_TX: tx.serialize()}), i=[PSBTMap()], o=[PSBTMap()]).to_base64()
        # tx.vout[0].nValue += 1  # slightly modify tx
        # psbt2 = PSBT(g=PSBTMap({PSBT_GLOBAL_UNSIGNED_TX: tx.serialize()}), i=[PSBTMap()], o=[PSBTMap()]).to_base64()
        # assert_raises_rpc_error(-8, "PSBTs not compatible (different transactions)", self.nodes[0].combinepsbt, [psbt1, psbt2])
        # assert_equal(self.nodes[0].combinepsbt([psbt1, psbt1]), psbt1)

        # ELEMENTS FIXME
        # self.log.info("Test that PSBT inputs are being checked via script execution")
        # acs_prevout = CTxOut(nValue=0, scriptPubKey=CScript([OP_TRUE]))
        # tx = CTransaction()
        # tx.vin = [CTxIn(outpoint=COutPoint(hash=int('dd' * 32, 16), n=0), scriptSig=b"")]
        # tx.vout = [CTxOut(nValue=0, scriptPubKey=b"")]
        # psbt = PSBT()
        # psbt.g = PSBTMap({PSBT_GLOBAL_UNSIGNED_TX: tx.serialize()})
        # psbt.i = [PSBTMap({bytes([PSBT_IN_WITNESS_UTXO]) : acs_prevout.serialize()})]
        # psbt.o = [PSBTMap()]
        # assert_equal(self.nodes[0].finalizepsbt(psbt.to_base64()),
        #     {'hex': '0200000001dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd0000000000000000000100000000000000000000000000', 'complete': True})


if __name__ == '__main__':
    PSBTTest().main()
