#!/usr/bin/env python3
# Copyright (c) 2016-2021 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test the bumpfee RPC.

Verifies that the bumpfee RPC creates replacement transactions successfully when
its preconditions are met, and returns appropriate errors in other cases.

This module consists of around a dozen individual test cases implemented in the
top-level functions named as test_<test_case_description>. The test functions
can be disabled or reordered if needed for debugging. If new test cases are
added in the future, they should try to follow the same convention and not
make assumptions about execution order.
"""
from decimal import Decimal

from test_framework.blocktools import (
    COINBASE_MATURITY,
    add_witness_commitment,
    create_block,
    create_coinbase,
    send_to_witness,
)
from test_framework.messages import (
    MAX_BIP125_RBF_SEQUENCE,
)
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    assert_greater_than,
    assert_raises_rpc_error,
)
from test_framework import util
from test_framework.wallet import MiniWallet


WALLET_PASSPHRASE = "test"
WALLET_PASSPHRASE_TIMEOUT = 3600

# Fee rates (sat/vB)
INSUFFICIENT =      1
ECONOMICAL   =     50
NORMAL       =    100
HIGH         =    800
TOO_HIGH     = 100000


class BumpFeeTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 2
        self.setup_clean_chain = True
        self.extra_args = [[
            "-walletrbf={}".format(i),
            "-mintxfee=0.00002",
            "-addresstype=bech32",
            "-whitelist=noban@127.0.0.1",
        ] for i in range(self.num_nodes)]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def clear_mempool(self):
        # Clear mempool between subtests. The subtests may only depend on chainstate (utxos)
        self.generate(self.nodes[1], 1)

    def run_test(self):
        util.node_fastmerkle = self.nodes[0]
        # Encrypt wallet for test_locked_wallet_fails test
        self.nodes[1].encryptwallet(WALLET_PASSPHRASE)
        self.nodes[1].walletpassphrase(WALLET_PASSPHRASE, WALLET_PASSPHRASE_TIMEOUT)

        peer_node, rbf_node = self.nodes
        rbf_node_address = rbf_node.getnewaddress()

        # fund rbf node with 10 coins of 0.001 btc (100,000 satoshis)
        self.log.info("Mining blocks...")
        self.generate(peer_node, 110)
        for _ in range(100):
            peer_node.sendtoaddress(rbf_node_address, 0.001)
        self.sync_all()
        self.generate(peer_node, 1)
        assert_equal(rbf_node.getbalance()['bitcoin'], Decimal("0.1"))

        self.log.info("Running tests")
        dest_address = peer_node.getnewaddress()
        for mode in ["default", "fee_rate"]:
            test_simple_bumpfee_succeeds(self, mode, rbf_node, peer_node, dest_address)
        self.test_invalid_parameters(rbf_node, peer_node, dest_address)
        test_segwit_bumpfee_succeeds(self, rbf_node, dest_address)
        test_nonrbf_bumpfee_fails(self, peer_node, dest_address)
        test_notmine_bumpfee(self, rbf_node, peer_node, dest_address)
        test_bumpfee_with_descendant_fails(self, rbf_node, rbf_node_address, dest_address)
        test_dust_to_fee(self, rbf_node, dest_address)
        test_watchonly_psbt(self, peer_node, rbf_node, dest_address)

        test_rebumping(self, rbf_node, dest_address)
        test_rebumping_not_replaceable(self, rbf_node, dest_address)
        test_unconfirmed_not_spendable(self, rbf_node, rbf_node_address)
        test_bumpfee_metadata(self, rbf_node, dest_address)
        test_locked_wallet_fails(self, rbf_node, dest_address)
        test_change_script_match(self, rbf_node, dest_address)
        test_settxfee(self, rbf_node, dest_address)
        test_maxtxfee_fails(self, rbf_node, dest_address)

        # These tests wipe out a number of utxos that are expected in other tests
        test_small_output_with_feerate_succeeds(self, rbf_node, dest_address)
        test_no_more_inputs_fails(self, rbf_node, dest_address)

    def test_invalid_parameters(self, rbf_node, peer_node, dest_address):
        self.log.info('Test invalid parameters')
        rbfid = spend_one_input(rbf_node, dest_address)
        self.sync_mempools((rbf_node, peer_node))
        assert rbfid in rbf_node.getrawmempool() and rbfid in peer_node.getrawmempool()

        for key in ["totalFee", "feeRate"]:
            assert_raises_rpc_error(-3, "Unexpected key {}".format(key), rbf_node.bumpfee, rbfid, {key: NORMAL})

        # Bumping to just above minrelay should fail to increase the total fee enough.
        assert_raises_rpc_error(-8, "Insufficient total fee 0.00000257", rbf_node.bumpfee, rbfid, {"fee_rate": INSUFFICIENT})

        self.log.info("Test invalid fee rate settings")
        assert_raises_rpc_error(-4, "Specified or calculated fee 0.257 is too high (cannot be higher than -maxtxfee 0.10",
            rbf_node.bumpfee, rbfid, {"fee_rate": TOO_HIGH})
        # Test fee_rate with zero values.
        msg = "Insufficient total fee 0.00"
        for zero_value in [0, 0.000, 0.00000000, "0", "0.000", "0.00000000"]:
            assert_raises_rpc_error(-8, msg, rbf_node.bumpfee, rbfid, {"fee_rate": zero_value})
        msg = "Invalid amount"
        # Test fee_rate values that don't pass fixed-point parsing checks.
        for invalid_value in ["", 0.000000001, 1e-09, 1.111111111, 1111111111111111, "31.999999999999999999999"]:
            assert_raises_rpc_error(-3, msg, rbf_node.bumpfee, rbfid, {"fee_rate": invalid_value})
        # Test fee_rate values that cannot be represented in sat/vB.
        for invalid_value in [0.0001, 0.00000001, 0.00099999, 31.99999999, "0.0001", "0.00000001", "0.00099999", "31.99999999"]:
            assert_raises_rpc_error(-3, msg, rbf_node.bumpfee, rbfid, {"fee_rate": invalid_value})
        # Test fee_rate out of range (negative number).
        assert_raises_rpc_error(-3, "Amount out of range", rbf_node.bumpfee, rbfid, {"fee_rate": -1})
        # Test type error.
        for value in [{"foo": "bar"}, True]:
            assert_raises_rpc_error(-3, "Amount is not a number or string", rbf_node.bumpfee, rbfid, {"fee_rate": value})

        self.log.info("Test explicit fee rate raises RPC error if both fee_rate and conf_target are passed")
        assert_raises_rpc_error(-8, "Cannot specify both conf_target and fee_rate. Please provide either a confirmation "
            "target in blocks for automatic fee estimation, or an explicit fee rate.",
            rbf_node.bumpfee, rbfid, {"conf_target": NORMAL, "fee_rate": NORMAL})

        self.log.info("Test explicit fee rate raises RPC error if both fee_rate and estimate_mode are passed")
        assert_raises_rpc_error(-8, "Cannot specify both estimate_mode and fee_rate",
            rbf_node.bumpfee, rbfid, {"estimate_mode": "economical", "fee_rate": NORMAL})

        self.log.info("Test invalid conf_target settings")
        assert_raises_rpc_error(-8, "confTarget and conf_target options should not both be set",
            rbf_node.bumpfee, rbfid, {"confTarget": 123, "conf_target": 456})

        self.log.info("Test invalid estimate_mode settings")
        for k, v in {"number": 42, "object": {"foo": "bar"}}.items():
            assert_raises_rpc_error(-3, "Expected type string for estimate_mode, got {}".format(k),
                rbf_node.bumpfee, rbfid, {"estimate_mode": v})
        for mode in ["foo", Decimal("3.1415"), "sat/B", "BTC/kB"]:
            assert_raises_rpc_error(-8, 'Invalid estimate_mode parameter, must be one of: "unset", "economical", "conservative"',
                rbf_node.bumpfee, rbfid, {"estimate_mode": mode})

        self.clear_mempool()


def test_simple_bumpfee_succeeds(self, mode, rbf_node, peer_node, dest_address):
    self.log.info('Test simple bumpfee: {}'.format(mode))
    rbfid = spend_one_input(rbf_node, dest_address)
    rbftx = rbf_node.gettransaction(rbfid)
    self.sync_mempools((rbf_node, peer_node))
    assert rbfid in rbf_node.getrawmempool() and rbfid in peer_node.getrawmempool()
    if mode == "fee_rate":
        bumped_psbt = rbf_node.psbtbumpfee(rbfid, {"fee_rate": str(NORMAL)})
        bumped_tx = rbf_node.bumpfee(rbfid, {"fee_rate": NORMAL})
    else:
        bumped_psbt = rbf_node.psbtbumpfee(rbfid)
        bumped_tx = rbf_node.bumpfee(rbfid)
    assert_equal(bumped_tx["errors"], [])
    assert bumped_tx["fee"] > -rbftx["fee"]['bitcoin']
    assert_equal(bumped_tx["origfee"], -rbftx["fee"]['bitcoin'])
    assert "psbt" not in bumped_tx
    assert_equal(bumped_psbt["errors"], [])
    assert bumped_psbt["fee"] > -rbftx["fee"]['bitcoin']
    assert_equal(bumped_psbt["origfee"], -rbftx["fee"]['bitcoin'])
    assert "psbt" in bumped_psbt
    # check that bumped_tx propagates, original tx was evicted and has a wallet conflict
    self.sync_mempools((rbf_node, peer_node))
    assert bumped_tx["txid"] in rbf_node.getrawmempool()
    assert bumped_tx["txid"] in peer_node.getrawmempool()
    assert rbfid not in rbf_node.getrawmempool()
    assert rbfid not in peer_node.getrawmempool()
    oldwtx = rbf_node.gettransaction(rbfid)
    assert len(oldwtx["walletconflicts"]) > 0
    # check wallet transaction replaces and replaced_by values
    bumpedwtx = rbf_node.gettransaction(bumped_tx["txid"])
    assert_equal(oldwtx["replaced_by_txid"], bumped_tx["txid"])
    assert_equal(bumpedwtx["replaces_txid"], rbfid)
    self.clear_mempool()


def test_segwit_bumpfee_succeeds(self, rbf_node, dest_address):
    self.log.info('Test that segwit-sourcing bumpfee works')
    # Create a transaction with segwit output, then create an RBF transaction
    # which spends it, and make sure bumpfee can be called on it.

    segwit_in = next(u for u in rbf_node.listunspent() if u["amount"] == Decimal("0.001"))
    segwit_out = rbf_node.getaddressinfo(rbf_node.getnewaddress(address_type='bech32'))
    segwitid = send_to_witness(
        use_p2wsh=False,
        node=rbf_node,
        utxo=segwit_in,
        pubkey=segwit_out["pubkey"],
        encode_p2sh=False,
        amount=Decimal("0.0009"),
        sign=True)

    rbfraw = rbf_node.createrawtransaction([{
        'txid': segwitid,
        'vout': 0,
        "sequence": MAX_BIP125_RBF_SEQUENCE
    }], [{dest_address: Decimal("0.0005")},
        {rbf_node.getrawchangeaddress(): Decimal("0.0003")},
        {"fee": "0.0001"}])
    rbfsigned = rbf_node.signrawtransactionwithwallet(rbfraw)
    rbfid = rbf_node.sendrawtransaction(rbfsigned["hex"])
    assert rbfid in rbf_node.getrawmempool()

    bumped_tx = rbf_node.bumpfee(rbfid)
    assert bumped_tx["txid"] in rbf_node.getrawmempool()
    assert rbfid not in rbf_node.getrawmempool()
    self.clear_mempool()


def test_nonrbf_bumpfee_fails(self, peer_node, dest_address):
    self.log.info('Test that we cannot replace a non RBF transaction')
    not_rbfid = peer_node.sendtoaddress(dest_address, Decimal("0.00090000"))
    assert_raises_rpc_error(-4, "not BIP 125 replaceable", peer_node.bumpfee, not_rbfid)
    self.clear_mempool()


def test_notmine_bumpfee(self, rbf_node, peer_node, dest_address):
    self.log.info('Test that it cannot bump fee if non-owned inputs are included')
    # here, the rbftx has a peer_node coin and then adds a rbf_node input
    # Note that this test depends upon the RPC code checking input ownership prior to change outputs
    # (since it can't use fundrawtransaction, it lacks a proper change output)
    fee = Decimal("0.001")
    utxos = [node.listunspent(query_options={'minimumAmount': fee})[-1] for node in (rbf_node, peer_node)]
    inputs = [{
        "txid": utxo["txid"],
        "vout": utxo["vout"],
        "address": utxo["address"],
        "sequence": MAX_BIP125_RBF_SEQUENCE
    } for utxo in utxos]
    output_val = sum(utxo["amount"] for utxo in utxos) - fee
    rawtx = rbf_node.createrawtransaction(inputs, [{dest_address: output_val}, {"fee": fee}])
    signedtx = rbf_node.signrawtransactionwithwallet(rawtx)
    signedtx = peer_node.signrawtransactionwithwallet(signedtx["hex"])
    rbfid = rbf_node.sendrawtransaction(signedtx["hex"])
    entry = rbf_node.getmempoolentry(rbfid)
    old_fee = entry["fees"]["base"]
    old_feerate = int(old_fee / entry["vsize"] * Decimal(1e8))
    print(old_feerate) # ELEMENTS FIXME lint
    assert_raises_rpc_error(-4, "Transaction contains inputs that don't belong to this wallet",
                            rbf_node.bumpfee, rbfid)

    def finish_psbtbumpfee(psbt):
        psbt = rbf_node.walletprocesspsbt(psbt)
        psbt = peer_node.walletprocesspsbt(psbt["psbt"])
        final = rbf_node.finalizepsbt(psbt["psbt"])
        res = rbf_node.testmempoolaccept([final["hex"]])
        assert res[0]["allowed"]
        assert_greater_than(res[0]["fees"]["base"], old_fee)

    # ELEMENTS FIXME: insufficient funds
    # self.log.info("Test that psbtbumpfee works for non-owned inputs")
    # psbt = rbf_node.psbtbumpfee(txid=rbfid)
    # finish_psbtbumpfee(psbt["psbt"])

    # psbt = rbf_node.psbtbumpfee(txid=rbfid, options={"fee_rate": old_feerate + 10})
    # finish_psbtbumpfee(psbt["psbt"])

    self.clear_mempool()


def test_bumpfee_with_descendant_fails(self, rbf_node, rbf_node_address, dest_address):
    self.log.info('Test that fee cannot be bumped when it has descendant')
    # parent is send-to-self, so we don't have to check which output is change when creating the child tx
    parent_id = spend_one_input(rbf_node, rbf_node_address)
    input_val = rbf_node.getrawtransaction(parent_id, 1)["vout"][0]["value"]
    tx = rbf_node.createrawtransaction([{"txid": parent_id, "vout": 0}], [{dest_address: "0.0002"}, {"fee": input_val-Decimal("0.0002")}])
    tx = rbf_node.signrawtransactionwithwallet(tx)
    rbf_node.sendrawtransaction(tx["hex"])
    assert_raises_rpc_error(-8, "Transaction has descendants in the wallet", rbf_node.bumpfee, parent_id)

    # create tx with descendant in the mempool by using MiniWallet
    miniwallet = MiniWallet(rbf_node)
    parent_id = spend_one_input(rbf_node, miniwallet.get_address())
    tx = rbf_node.gettransaction(txid=parent_id, verbose=True)['decoded']
    miniwallet.scan_tx(tx)
    miniwallet.send_self_transfer(from_node=rbf_node, fee_rate=Decimal(0.001)) # ELEMENTS: reduce fee rate
    assert_raises_rpc_error(-8, "Transaction has descendants in the mempool", rbf_node.bumpfee, parent_id)
    self.clear_mempool()


def test_small_output_with_feerate_succeeds(self, rbf_node, dest_address):
    self.log.info('Testing small output with feerate bump succeeds')

    # Make sure additional inputs exist
    self.generatetoaddress(rbf_node, COINBASE_MATURITY + 1, rbf_node.getnewaddress())
    rbfid = spend_one_input(rbf_node, dest_address)
    input_list = rbf_node.getrawtransaction(rbfid, 1)["vin"]
    assert_equal(len(input_list), 1)
    original_txin = input_list[0]
    self.log.info('Keep bumping until transaction fee out-spends non-destination value')
    tx_fee = 0
    while True:
        input_list = rbf_node.getrawtransaction(rbfid, 1)["vin"]
        new_item = list(input_list)[0]
        assert_equal(len(input_list), 1)
        assert_equal(original_txin["txid"], new_item["txid"])
        assert_equal(original_txin["vout"], new_item["vout"])
        rbfid_new_details = rbf_node.bumpfee(rbfid)
        rbfid_new = rbfid_new_details["txid"]
        raw_pool = rbf_node.getrawmempool()
        assert rbfid not in raw_pool
        assert rbfid_new in raw_pool
        rbfid = rbfid_new
        tx_fee = rbfid_new_details["fee"]

        # Total value from input not going to destination
        if tx_fee > Decimal('0.00040000'): # ELEMENTS FIXME: this was 0.00050000 in bitcoin (since spend_one_input leaves 0.0005 for the fee)
            break

    # input(s) have been added
    final_input_list = rbf_node.getrawtransaction(rbfid, 1)["vin"]
    if len(final_input_list) != 1: # ELEMENTS: allow it to be equal
        assert_greater_than(len(final_input_list), 1)
    # Original input is in final set
    assert [txin for txin in final_input_list
            if txin["txid"] == original_txin["txid"]
            and txin["vout"] == original_txin["vout"]]

    self.generatetoaddress(rbf_node, 1, rbf_node.getnewaddress())
    assert_equal(rbf_node.gettransaction(rbfid)["confirmations"], 1)
    self.clear_mempool()


def test_dust_to_fee(self, rbf_node, dest_address):
    self.log.info('Test that bumped output that is dust is dropped to fee')
    rbfid = spend_one_input(rbf_node, dest_address)
    fulltx = rbf_node.getrawtransaction(rbfid, 1)
    # The DER formatting used by Bitcoin to serialize ECDSA signatures means that signatures can have a
    # variable size of 70-72 bytes (or possibly even less), with most being 71 or 72 bytes. The signature
    # in the witness is divided by 4 for the vsize, so this variance can take the weight across a 4-byte
    # boundary
    # ELEMENTS: 116 vbytes added (9 for fee spk+value, 99 for assets, 3 for value tags, 3 for null nonces, 2 for elements tx encoding)
    # size of transaction (p2wpkh, 1 input, 3 outputs): 257 vbytes
    if not 140 + 116 <= fulltx["vsize"] <= 141 + 116:
        raise AssertionError("Invalid tx vsize of {} (256-257 expected), full tx: {}".format(fulltx["vsize"], fulltx))
    # Bump with fee_rate of 350.25 sat/vB vbytes to create dust.
    # ELEMENTS: Expected bump fee of 257 vbytes * fee_rate 0.00190000 BTC / 1000 vbytes = 0.00048830 BTC
    # Expected fee is 141 vbytes * fee_rate 0.00350250 BTC / 1000 vbytes = 0.00049385 BTC.
    # or occasionally 140 vbytes * fee_rate 0.00350250 BTC / 1000 vbytes = 0.00049035 BTC.
    # Dust should be dropped to the fee, so actual bump fee is 0.00050000 BTC.
    bumped_tx = rbf_node.bumpfee(rbfid, {"fee_rate": 190.00})
    full_bumped_tx = rbf_node.getrawtransaction(bumped_tx["txid"], 1)
    assert_equal(bumped_tx["fee"], Decimal("0.00050000"))
    assert_equal(len(fulltx["vout"]), 3)
    assert_equal(len(full_bumped_tx["vout"]), 2)  #change output is eliminated
    assert_equal(full_bumped_tx["vout"][0]['value'], Decimal("0.00050000"))
    self.clear_mempool()


def test_settxfee(self, rbf_node, dest_address):
    self.log.info('Test settxfee')
    assert_raises_rpc_error(-8, "txfee cannot be less than min relay tx fee", rbf_node.settxfee, Decimal('0.000005'))
    assert_raises_rpc_error(-8, "txfee cannot be less than wallet min fee", rbf_node.settxfee, Decimal('0.000015'))
    # check that bumpfee reacts correctly to the use of settxfee (paytxfee)
    rbfid = spend_one_input(rbf_node, dest_address)
    requested_feerate = Decimal("0.00025000")
    rbf_node.settxfee(requested_feerate)
    bumped_tx = rbf_node.bumpfee(rbfid)
    actual_feerate = bumped_tx["fee"] * 1000 / rbf_node.getrawtransaction(bumped_tx["txid"], True)["vsize"]
    # Assert that the difference between the requested feerate and the actual
    # feerate of the bumped transaction is small.
    assert_greater_than(Decimal("0.001000"), abs(requested_feerate - actual_feerate))
    rbf_node.settxfee(Decimal("0.00000000"))  # unset paytxfee

    # check that settxfee respects -maxtxfee
    self.restart_node(1, ['-maxtxfee=0.000025'] + self.extra_args[1])
    assert_raises_rpc_error(-8, "txfee cannot be more than wallet max tx fee", rbf_node.settxfee, Decimal('0.00003'))
    self.restart_node(1, self.extra_args[1])
    rbf_node.walletpassphrase(WALLET_PASSPHRASE, WALLET_PASSPHRASE_TIMEOUT)
    self.connect_nodes(1, 0)
    self.clear_mempool()


def test_maxtxfee_fails(self, rbf_node, dest_address):
    self.log.info('Test that bumpfee fails when it hits -maxtxfee')
    # size of bumped transaction (p2wpkh, 1 input, 2 outputs): 141 vbytes
    # expected bump fee of 141 vbytes * 0.00200000 BTC / 1000 vbytes = 0.00002820 BTC
    # which exceeds maxtxfee and is expected to raise
    self.restart_node(1, ['-maxtxfee=0.000025'] + self.extra_args[1])
    rbf_node.walletpassphrase(WALLET_PASSPHRASE, WALLET_PASSPHRASE_TIMEOUT)
    rbfid = spend_one_input(rbf_node, dest_address)
    assert_raises_rpc_error(-4, "Unable to create transaction. Fee exceeds maximum configured by user (e.g. -maxtxfee, maxfeerate)", rbf_node.bumpfee, rbfid)
    self.restart_node(1, self.extra_args[1])
    rbf_node.walletpassphrase(WALLET_PASSPHRASE, WALLET_PASSPHRASE_TIMEOUT)
    self.connect_nodes(1, 0)
    self.clear_mempool()


def test_watchonly_psbt(self, peer_node, rbf_node, dest_address):
    self.log.info('Test that PSBT is returned for bumpfee in watchonly wallets')
    priv_rec_desc = "wpkh([00000001/84'/1'/0']tprv8ZgxMBicQKsPd7Uf69XL1XwhmjHopUGep8GuEiJDZmbQz6o58LninorQAfcKZWARbtRtfnLcJ5MQ2AtHcQJCCRUcMRvmDUjyEmNUWwx8UbK/0/*)#rweraev0"
    pub_rec_desc = rbf_node.getdescriptorinfo(priv_rec_desc)["descriptor"]
    priv_change_desc = "wpkh([00000001/84'/1'/0']tprv8ZgxMBicQKsPd7Uf69XL1XwhmjHopUGep8GuEiJDZmbQz6o58LninorQAfcKZWARbtRtfnLcJ5MQ2AtHcQJCCRUcMRvmDUjyEmNUWwx8UbK/1/*)#j6uzqvuh"
    pub_change_desc = rbf_node.getdescriptorinfo(priv_change_desc)["descriptor"]
    # Create a wallet with private keys that can sign PSBTs
    rbf_node.createwallet(wallet_name="signer", disable_private_keys=False, blank=True)
    signer = rbf_node.get_wallet_rpc("signer")
    assert signer.getwalletinfo()['private_keys_enabled']
    reqs = [{
        "desc": priv_rec_desc,
        "timestamp": 0,
        "range": [0,1],
        "internal": False,
        "keypool": False # Keys can only be imported to the keypool when private keys are disabled
    },
    {
        "desc": priv_change_desc,
        "timestamp": 0,
        "range": [0, 0],
        "internal": True,
        "keypool": False
    }]
    if self.options.descriptors:
        result = signer.importdescriptors(reqs)
    else:
        result = signer.importmulti(reqs)
    assert_equal(result, [{'success': True}, {'success': True}])

    # Create another wallet with just the public keys, which creates PSBTs
    rbf_node.createwallet(wallet_name="watcher", disable_private_keys=True, blank=True)
    watcher = rbf_node.get_wallet_rpc("watcher")
    assert not watcher.getwalletinfo()['private_keys_enabled']

    reqs = [{
        "desc": pub_rec_desc,
        "timestamp": 0,
        "range": [0, 10],
        "internal": False,
        "keypool": True,
        "watchonly": True,
        "active": True,
    }, {
        "desc": pub_change_desc,
        "timestamp": 0,
        "range": [0, 10],
        "internal": True,
        "keypool": True,
        "watchonly": True,
        "active": True,
    }]
    if self.options.descriptors:
        result = watcher.importdescriptors(reqs)
    else:
        result = watcher.importmulti(reqs)
    assert_equal(result, [{'success': True}, {'success': True}])

    funding_address1 = watcher.getnewaddress(address_type='bech32')
    funding_address2 = watcher.getnewaddress(address_type='bech32')
    # ELEMENTS: start with more funds since our transaction will be 688 bytes vs 444 in Bitcoin
    peer_node.sendmany("", {funding_address1: 0.001, funding_address2: 0.005})
    self.generate(peer_node, 1)

    # Create single-input PSBT for transaction to be bumped
    # Ensure the payment amount + change can be fully funded using one of the 0.001BTC inputs.
    psbt = watcher.walletcreatefundedpsbt([watcher.listunspent()[0]], [{dest_address: 0.0005}], 0,
            {"fee_rate": 1, "add_inputs": False}, True)['psbt']
    psbt_signed = signer.walletprocesspsbt(psbt=psbt, sign=True, sighashtype="ALL", bip32derivs=True)
    psbt_final = watcher.finalizepsbt(psbt_signed["psbt"])
    original_txid = watcher.sendrawtransaction(psbt_final["hex"])
    assert_equal(len(watcher.decodepsbt(psbt)["inputs"]), 1)

    # bumpfee can't be used on watchonly wallets
    assert_raises_rpc_error(-4, "bumpfee is not available with wallets that have private keys disabled. Use psbtbumpfee instead.", watcher.bumpfee, original_txid)

    # Bump fee, obnoxiously high to add additional watchonly input
    bumped_psbt = watcher.psbtbumpfee(original_txid, {"fee_rate": HIGH}) # ELEMENTS: made it higher than HIGH
    # ELEMENTS: sometimes greater than 1, sometimes equal to 1
    if len(watcher.decodepsbt(bumped_psbt['psbt'])["inputs"]) != 1:
        assert_greater_than(len(watcher.decodepsbt(bumped_psbt['psbt'])["inputs"]), 1)
    assert "txid" not in bumped_psbt
    assert_equal(bumped_psbt["origfee"], -watcher.gettransaction(original_txid)["fee"]['bitcoin'])
    assert not watcher.finalizepsbt(bumped_psbt["psbt"])["complete"]

    # Sign bumped transaction
    bumped_psbt_signed = signer.walletprocesspsbt(psbt=bumped_psbt["psbt"], sign=True, sighashtype="ALL", bip32derivs=True)
    bumped_psbt_final = watcher.finalizepsbt(bumped_psbt_signed["psbt"])
    assert bumped_psbt_final["complete"]

    # Broadcast bumped transaction
    bumped_txid = watcher.sendrawtransaction(bumped_psbt_final["hex"])
    assert bumped_txid in rbf_node.getrawmempool()
    assert original_txid not in rbf_node.getrawmempool()

    rbf_node.unloadwallet("watcher")
    rbf_node.unloadwallet("signer")
    self.clear_mempool()


def test_rebumping(self, rbf_node, dest_address):
    self.log.info('Test that re-bumping the original tx fails, but bumping successor works')
    rbfid = spend_one_input(rbf_node, dest_address)
    bumped = rbf_node.bumpfee(rbfid, {"fee_rate": ECONOMICAL})
    assert_raises_rpc_error(-4, "already bumped", rbf_node.bumpfee, rbfid, {"fee_rate": ECONOMICAL})
    rbf_node.bumpfee(bumped["txid"], {"fee_rate": NORMAL})
    self.clear_mempool()


def test_rebumping_not_replaceable(self, rbf_node, dest_address):
    self.log.info('Test that re-bumping non-replaceable fails')
    rbfid = spend_one_input(rbf_node, dest_address)
    bumped = rbf_node.bumpfee(rbfid, {"fee_rate": ECONOMICAL, "replaceable": False})
    assert_raises_rpc_error(-4, "Transaction is not BIP 125 replaceable", rbf_node.bumpfee, bumped["txid"],
                            {"fee_rate": NORMAL})
    self.clear_mempool()


def test_unconfirmed_not_spendable(self, rbf_node, rbf_node_address):
    self.log.info('Test that unconfirmed outputs from bumped txns are not spendable')
    rbfid = spend_one_input(rbf_node, rbf_node_address)
    rbftx = rbf_node.gettransaction(rbfid)["hex"]
    assert rbfid in rbf_node.getrawmempool()
    bumpid = rbf_node.bumpfee(rbfid)["txid"]
    assert bumpid in rbf_node.getrawmempool()
    assert rbfid not in rbf_node.getrawmempool()

    # check that outputs from the bump transaction are not spendable
    # due to the replaces_txid check in CWallet::AvailableCoins
    assert_equal([t for t in rbf_node.listunspent(minconf=0, include_unsafe=False) if t["txid"] == bumpid], [])

    # submit a block with the rbf tx to clear the bump tx out of the mempool,
    # then invalidate the block so the rbf tx will be put back in the mempool.
    # This makes it possible to check whether the rbf tx outputs are
    # spendable before the rbf tx is confirmed.
    block = submit_block_with_tx(rbf_node, rbftx)
    # Can not abandon conflicted tx
    assert_raises_rpc_error(-5, 'Transaction not eligible for abandonment', lambda: rbf_node.abandontransaction(txid=bumpid))
    rbf_node.invalidateblock(block.hash)
    # Call abandon to make sure the wallet doesn't attempt to resubmit
    # the bump tx and hope the wallet does not rebroadcast before we call.
    rbf_node.abandontransaction(bumpid)
    assert bumpid not in rbf_node.getrawmempool()
    assert rbfid in rbf_node.getrawmempool()

    # check that outputs from the rbf tx are not spendable before the
    # transaction is confirmed, due to the replaced_by_txid check in
    # CWallet::AvailableCoins
    assert_equal([t for t in rbf_node.listunspent(minconf=0, include_unsafe=False) if t["txid"] == rbfid], [])

    # check that the main output from the rbf tx is spendable after confirmed
    self.generate(rbf_node, 1, sync_fun=self.no_op)
    rbf_node_address_unconfidential = rbf_node.getaddressinfo(rbf_node_address)["unconfidential"]
    assert_equal(
        sum(1 for t in rbf_node.listunspent(minconf=0, include_unsafe=False)
            if t["txid"] == rbfid and t["address"] == rbf_node_address_unconfidential and t["spendable"]), 1)
    self.clear_mempool()


def test_bumpfee_metadata(self, rbf_node, dest_address):
    self.log.info('Test that bumped txn metadata persists to new txn record')
    assert(rbf_node.getbalance()["bitcoin"] < 49)
    self.generatetoaddress(rbf_node, 101, rbf_node.getnewaddress())
    rbfid = rbf_node.sendtoaddress(dest_address, 49, "comment value", "to value")
    bumped_tx = rbf_node.bumpfee(rbfid)
    bumped_wtx = rbf_node.gettransaction(bumped_tx["txid"])
    assert_equal(bumped_wtx["comment"], "comment value")
    assert_equal(bumped_wtx["to"], "to value")
    self.clear_mempool()


def test_locked_wallet_fails(self, rbf_node, dest_address):
    self.log.info('Test that locked wallet cannot bump txn')
    rbfid = spend_one_input(rbf_node, dest_address)
    rbf_node.walletlock()
    assert_raises_rpc_error(-13, "Please enter the wallet passphrase with walletpassphrase first.",
                            rbf_node.bumpfee, rbfid)
    rbf_node.walletpassphrase(WALLET_PASSPHRASE, WALLET_PASSPHRASE_TIMEOUT)
    self.clear_mempool()


def test_change_script_match(self, rbf_node, dest_address):
    self.log.info('Test that the same change addresses is used for the replacement transaction when possible')

    def get_change_address(tx):
        tx_details = rbf_node.getrawtransaction(tx, 1)
        txout_addresses = [txout['scriptPubKey']['address'] for txout in tx_details["vout"] if txout['scriptPubKey']['type'] != 'fee']
        return [address for address in txout_addresses if rbf_node.getaddressinfo(address)["ischange"]]

    # Check that there is only one change output
    rbfid = spend_one_input(rbf_node, dest_address)
    change_addresses = get_change_address(rbfid)
    assert_equal(len(change_addresses), 1)

    # Now find that address in each subsequent tx, and no other change
    bumped_total_tx = rbf_node.bumpfee(rbfid, {"fee_rate": ECONOMICAL})
    assert_equal(change_addresses, get_change_address(bumped_total_tx['txid']))
    bumped_rate_tx = rbf_node.bumpfee(bumped_total_tx["txid"])
    assert_equal(change_addresses, get_change_address(bumped_rate_tx['txid']))
    self.clear_mempool()


def spend_one_input(node, dest_address, change_size=Decimal("0.0004000")):
    tx_input = dict(
        sequence=MAX_BIP125_RBF_SEQUENCE, **next(u for u in node.listunspent() if u["amount"] == Decimal("0.00100000")))
    destinations = [{dest_address: Decimal("0.00050000")}]
    if change_size > 0:
        destinations.append({node.getrawchangeaddress(): change_size})
    destinations.append({"fee": Decimal("0.0001")})
    rawtx = node.createrawtransaction([tx_input], destinations)
    signedtx = node.signrawtransactionwithwallet(rawtx)
    txid = node.sendrawtransaction(signedtx["hex"])
    return txid


def submit_block_with_tx(node, tx):
    tip = node.getbestblockhash()
    height = node.getblockcount() + 1
    block_time = node.getblockheader(tip)["mediantime"] + 1
    block = create_block(int(tip, 16), create_coinbase(height), block_time, txlist=[tx])
    add_witness_commitment(block)
    block.solve()
    node.submitblock(block.serialize().hex())
    return block


def test_no_more_inputs_fails(self, rbf_node, dest_address):
    self.log.info('Test that bumpfee fails when there are no available confirmed outputs')
    # feerate rbf requires confirmed outputs when change output doesn't exist or is insufficient
    self.generatetoaddress(rbf_node, 1, dest_address)
    # spend all funds, no change output
    rbfid = rbf_node.sendall(recipients=[rbf_node.getnewaddress()])['txid']
    assert_equal(rbf_node.getbalance()['bitcoin'], 0) # ELEMENTS
    assert_raises_rpc_error(-4, "bumpfee can only be called on an unblinded transaction", rbf_node.bumpfee, rbfid) # ELEMENTS
    self.clear_mempool()


if __name__ == "__main__":
    BumpFeeTest().main()
