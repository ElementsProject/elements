#!/usr/bin/env python3
# Copyright (c) 2018-2019 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test the Partially Signed Transaction RPCs.
"""

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    assert_greater_than,
    assert_raises_rpc_error,
    connect_nodes,
    disconnect_nodes,
    find_output,
)
from decimal import Decimal

# These imports are used by commented-out tests.
"""
import json
import os
"""

MAX_BIP125_RBF_SEQUENCE = 0xfffffffd

# Create one-input, one-output, no-fee transaction:
class PSBTTest(BitcoinTestFramework):

    def set_test_params(self):
        self.setup_clean_chain = False
        self.num_nodes = 3
        self.extra_args = [
            ["-walletrbf=1"],
            ["-walletrbf=0"],
            []
        ]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def test_utxo_conversion(self):
        mining_node = self.nodes[2]
        offline_node = self.nodes[0]
        online_node = self.nodes[1]

        # Disconnect offline node from others
        disconnect_nodes(offline_node, 1)
        disconnect_nodes(online_node, 0)
        disconnect_nodes(offline_node, 2)
        disconnect_nodes(mining_node, 0)

        # Mine a transaction that credits the offline address
        offline_addr = offline_node.getnewaddress(address_type="p2sh-segwit")
        online_addr = online_node.getnewaddress(address_type="p2sh-segwit")
        online_node.importaddress(offline_addr, "", False)
        mining_node.sendtoaddress(address=offline_addr, amount=1.0)
        mining_node.generate(nblocks=1)
        self.sync_blocks([mining_node, online_node])

        # Construct an unsigned PSBT on the online node (who doesn't know the output is Segwit, so will include a non-witness UTXO)
        utxos = online_node.listunspent(addresses=[offline_addr])
        raw = online_node.createrawtransaction([{"txid":utxos[0]["txid"], "vout":utxos[0]["vout"]}],[{online_addr:0.9999},{"fee":0.0001}])
        psbt = online_node.walletprocesspsbt(online_node.converttopsbt(raw))["psbt"]
        assert "non_witness_utxo" in mining_node.decodepsbt(psbt)["inputs"][0]

        # Have the offline node sign the PSBT (which will update the UTXO to segwit)
        signed_psbt = offline_node.walletprocesspsbt(psbt)["psbt"]
        assert "witness_utxo" in mining_node.decodepsbt(signed_psbt)["inputs"][0]

        # Make sure we can mine the resulting transaction
        txid = mining_node.sendrawtransaction(mining_node.finalizepsbt(signed_psbt)["hex"])
        mining_node.generate(1)
        self.sync_blocks([mining_node, online_node])
        assert_equal(online_node.gettxout(txid,0)["confirmations"], 1)

        # Reconnect
        connect_nodes(self.nodes[0], 1)
        connect_nodes(self.nodes[0], 2)

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

    def run_basic_tests(self, confidential):
        # Create and fund a raw tx for sending 10 BTC
        psbtx1 = self.nodes[0].walletcreatefundedpsbt([], {self.get_address(confidential, 2):10})['psbt']

        # Node 1 should not be able to add anything to it but still return the psbtx same as before
        psbtx = self.nodes[1].walletfillpsbtdata(psbtx1)['psbt']
        assert_equal(psbtx1, psbtx)

        # Sign the transaction and send
        filled_tx = self.nodes[0].walletfillpsbtdata(psbtx)['psbt']
        blinded_tx = self.nodes[0].blindpsbt(filled_tx)
        signed_tx = self.nodes[0].walletsignpsbt(blinded_tx)['psbt']
        final_tx = self.nodes[0].finalizepsbt(signed_tx)['hex']
        if confidential:
            # Can't use assert_equal because there may or may not be change
            assert(self.num_blinded_outputs(final_tx) > 0)
        self.nodes[0].sendrawtransaction(final_tx)

        # Create p2sh, p2wpkh, and p2wsh addresses
        pubkey0 = self.nodes[0].getaddressinfo(self.get_address(confidential, 0))['pubkey']
        pubkey1 = self.nodes[1].getaddressinfo(self.get_address(confidential, 1))['pubkey']
        pubkey2 = self.nodes[2].getaddressinfo(self.get_address(confidential, 2))['pubkey']
        p2sh = self.nodes[1].addmultisigaddress(2, [pubkey0, pubkey1, pubkey2], "", "legacy")['address']
        p2sh_unconf = self.to_unconf_addr(1, p2sh)
        p2wsh = self.nodes[1].addmultisigaddress(2, [pubkey0, pubkey1, pubkey2], "", "bech32")['address']
        p2wsh_unconf = self.to_unconf_addr(1, p2wsh)
        p2sh_p2wsh = self.nodes[1].addmultisigaddress(2, [pubkey0, pubkey1, pubkey2], "", "p2sh-segwit")['address']
        p2sh_p2wsh_unconf = self.to_unconf_addr(1, p2sh_p2wsh)
        p2wpkh = self.get_address(confidential, 1, "bech32")
        p2wpkh_unconf = self.to_unconf_addr(1, p2wpkh)
        p2pkh = self.get_address(confidential, 1, "legacy")
        p2pkh_unconf = self.to_unconf_addr(1, p2pkh)
        p2sh_p2wpkh = self.get_address(confidential, 1, "p2sh-segwit")
        p2sh_p2wpkh_unconf = self.to_unconf_addr(1, p2sh_p2wpkh)

        # fund those addresses
        rawtx = self.nodes[0].createrawtransaction([], {p2sh:10, p2wsh:10, p2wpkh:10, p2sh_p2wsh:10, p2sh_p2wpkh:10, p2pkh:10})
        rawtx = self.nodes[0].fundrawtransaction(rawtx, {"changePosition":3})
        rawtx = self.nodes[0].blindrawtransaction(rawtx['hex'])
        signed_tx = self.nodes[0].signrawtransactionwithwallet(rawtx)['hex']
        txid = self.nodes[0].sendrawtransaction(signed_tx)

        self.nodes[0].generate(6)
        self.sync_all()

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
            elif out['scriptPubKey']['addresses'][0] == p2sh_unconf:
                p2sh_pos = out['n']
            elif out['scriptPubKey']['addresses'][0] == p2wsh_unconf:
                p2wsh_pos = out['n']
            elif out['scriptPubKey']['addresses'][0] == p2wpkh_unconf:
                p2wpkh_pos = out['n']
            elif out['scriptPubKey']['addresses'][0] == p2sh_p2wsh_unconf:
                p2sh_p2wsh_pos = out['n']
            elif out['scriptPubKey']['addresses'][0] == p2sh_p2wpkh_unconf:
                p2sh_p2wpkh_pos = out['n']
            elif out['scriptPubKey']['addresses'][0] == p2pkh_unconf:
                p2pkh_pos = out['n']

        # spend single key from node 1
        rawtx = self.nodes[1].walletcreatefundedpsbt([{"txid":txid,"vout":p2wpkh_pos},{"txid":txid,"vout":p2sh_p2wpkh_pos},{"txid":txid,"vout":p2pkh_pos}], {self.get_address(confidential, 1):29.99})['psbt']
        filled = self.nodes[1].walletfillpsbtdata(rawtx)['psbt']
        blinded = self.nodes[1].blindpsbt(filled)
        walletsignpsbt_out = self.nodes[1].walletsignpsbt(blinded)
        assert_equal(walletsignpsbt_out['complete'], True)
        hex_tx = self.nodes[1].finalizepsbt(walletsignpsbt_out['psbt'])['hex']
        if confidential:
            # Can't use assert_equal because there may or may not be change
            assert(self.num_blinded_outputs(hex_tx) > 0)
        self.nodes[1].sendrawtransaction(hex_tx)

        # feeRate of 0.1 BTC / KB produces a total fee slightly below -maxtxfee (~0.05420000):
        if confidential:
            fee_rate = 0.04
        else:
            fee_rate = 0.1
        res = self.nodes[1].walletcreatefundedpsbt([{"txid":txid,"vout":p2wpkh_pos},{"txid":txid,"vout":p2sh_p2wpkh_pos},{"txid":txid,"vout":p2pkh_pos}], {self.nodes[1].getnewaddress():29.99}, 0, {"feeRate": fee_rate})
        assert_greater_than(res["fee"], 0.05)
        assert_greater_than(0.06, res["fee"])

        # feeRate of 10 BTC / KB produces a total fee well above -maxtxfee
        # previously this was silently capped at -maxtxfee
        assert_raises_rpc_error(-4, "Fee exceeds maximum configured by -maxtxfee", self.nodes[1].walletcreatefundedpsbt, [{"txid":txid,"vout":p2wpkh_pos},{"txid":txid,"vout":p2sh_p2wpkh_pos},{"txid":txid,"vout":p2pkh_pos}], {self.nodes[1].getnewaddress():29.99}, 0, {"feeRate": 10})

        # partially sign multisig things with node 1
        psbtx = self.nodes[1].walletcreatefundedpsbt([{"txid":txid,"vout":p2wsh_pos},{"txid":txid,"vout":p2sh_pos},{"txid":txid,"vout":p2sh_p2wsh_pos}], {self.get_address(confidential, 1):29.99})['psbt']
        filled = self.nodes[1].walletfillpsbtdata(psbtx)['psbt']
        # have both nodes fill before we try to blind and sign
        filled = self.nodes[2].walletfillpsbtdata(filled)['psbt']
        blinded = self.nodes[1].blindpsbt(filled)
        walletsignpsbt_out = self.nodes[1].walletsignpsbt(blinded)
        psbtx = walletsignpsbt_out['psbt']
        assert_equal(walletsignpsbt_out['complete'], False)

        # partially sign with node 2. This should be complete and sendable
        walletsignpsbt_out = self.nodes[2].walletsignpsbt(psbtx)
        assert_equal(walletsignpsbt_out['complete'], True)
        hex_tx = self.nodes[2].finalizepsbt(walletsignpsbt_out['psbt'])['hex']
        if confidential:
            # Can't use assert_equal because there may or may not be change
            assert(self.num_blinded_outputs(hex_tx) > 0)
        self.nodes[2].sendrawtransaction(hex_tx)

        # check that walletprocesspsbt fails to decode a non-psbt
        rawtx = self.nodes[1].createrawtransaction([{"txid":txid,"vout":p2wpkh_pos}], {self.get_address(confidential, 1):9.99})
        assert_raises_rpc_error(-22, "TX decode failed", self.nodes[1].walletprocesspsbt, rawtx)

        # Convert a non-psbt to psbt and make sure we can decode it
        rawtx = self.nodes[0].createrawtransaction([], {self.get_address(confidential, 1):10})
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
        rt1 = self.nodes[0].createrawtransaction([], {node1_addr:13})
        rt1 = self.nodes[0].fundrawtransaction(rt1)
        rt1 = self.nodes[0].blindrawtransaction(rt1['hex'])
        rt1 = self.nodes[0].signrawtransactionwithwallet(rt1)
        txid1 = self.nodes[0].sendrawtransaction(rt1['hex'])
        rt1 = self.nodes[0].decoderawtransaction(rt1['hex'])

        rt2 = self.nodes[0].createrawtransaction([], {node2_addr:13})
        rt2 = self.nodes[0].fundrawtransaction(rt2)
        rt2 = self.nodes[0].blindrawtransaction(rt2['hex'])
        rt2 = self.nodes[0].signrawtransactionwithwallet(rt2)
        txid2 = self.nodes[0].sendrawtransaction(rt2['hex'])
        rt2 = self.nodes[0].decoderawtransaction(rt2['hex'])

        self.nodes[0].generate(6)
        self.sync_all()

        for out in rt1['vout']:
            if out['scriptPubKey']['type'] == "fee":
                pass
            elif out['scriptPubKey']['addresses'][0] == node1_unconf_addr:
                vout1 = out['n']

        for out in rt2['vout']:
            if out['scriptPubKey']['type'] == "fee":
                pass
            elif out['scriptPubKey']['addresses'][0] == node2_unconf_addr:
                vout2 = out['n']

        # This test doesn't work with Confidential Assets yet.
        if not confidential:
            # Create a psbt spending outputs from nodes 1 and 2
            psbt_orig = self.nodes[0].createpsbt([{"txid":txid1,  "vout":vout1}, {"txid":txid2, "vout":vout2}], [{self.get_address(confidential, 0):25.999}, {"fee":0.001}])

            # Update psbts, should only have data for one input and not the other
            psbt1 = self.nodes[1].walletprocesspsbt(psbt_orig)['psbt']
            psbt1_decoded = self.nodes[0].decodepsbt(psbt1)
            assert psbt1_decoded['inputs'][0] and not psbt1_decoded['inputs'][1]
            psbt1 = self.nodes[1].walletsignpsbt(psbt1, "ALL", True)['psbt'] # Allow signing incomplete tx
            psbt2 = self.nodes[2].walletprocesspsbt(psbt_orig)['psbt']
            psbt2_decoded = self.nodes[0].decodepsbt(psbt2)
            assert not psbt2_decoded['inputs'][0] and psbt2_decoded['inputs'][1]
            psbt2 = self.nodes[2].walletsignpsbt(psbt2, "ALL", True)['psbt'] # Allow signing incomplete tx

            # Combine, finalize, and send the psbts
            combined = self.nodes[0].combinepsbt([psbt1, psbt2])
            finalized = self.nodes[0].finalizepsbt(combined)['hex']
            self.nodes[0].sendrawtransaction(finalized)
            self.nodes[0].generate(6)
            self.sync_all()

        # Test additional args in walletcreatepsbt
        # Make sure both pre-included and funded inputs
        # have the correct sequence numbers based on
        # replaceable arg
        block_height = self.nodes[0].getblockcount()
        unspent = self.nodes[0].listunspent()[0]
        psbtx_info = self.nodes[0].walletcreatefundedpsbt([{"txid":unspent["txid"], "vout":unspent["vout"]}], [{self.get_address(confidential, 2):unspent["amount"]+1}], block_height+2, {"replaceable": False}, False)
        decoded_psbt = self.nodes[0].decodepsbt(psbtx_info["psbt"])
        for tx_in, psbt_in in zip(decoded_psbt["tx"]["vin"], decoded_psbt["inputs"]):
            assert_greater_than(tx_in["sequence"], MAX_BIP125_RBF_SEQUENCE)
            assert "bip32_derivs" not in psbt_in
        assert_equal(decoded_psbt["tx"]["locktime"], block_height+2)

        # Same construction with only locktime set and RBF explicitly enabled
        psbtx_info = self.nodes[0].walletcreatefundedpsbt([{"txid":unspent["txid"], "vout":unspent["vout"]}], [{self.get_address(confidential, 2):unspent["amount"]+1}], block_height, {"replaceable": True}, True)
        decoded_psbt = self.nodes[0].decodepsbt(psbtx_info["psbt"])
        for tx_in, psbt_in in zip(decoded_psbt["tx"]["vin"], decoded_psbt["inputs"]):
            assert_equal(tx_in["sequence"], MAX_BIP125_RBF_SEQUENCE)
            assert "bip32_derivs" in psbt_in
        assert_equal(decoded_psbt["tx"]["locktime"], block_height)

        # Same construction without optional arguments
        psbtx_info = self.nodes[0].walletcreatefundedpsbt([{"txid":unspent["txid"], "vout":unspent["vout"]}], [{self.get_address(confidential, 2):unspent["amount"]+1}])
        decoded_psbt = self.nodes[0].decodepsbt(psbtx_info["psbt"])
        for tx_in in decoded_psbt["tx"]["vin"]:
            assert_equal(tx_in["sequence"], MAX_BIP125_RBF_SEQUENCE)
        assert_equal(decoded_psbt["tx"]["locktime"], 0)

        # Same construction without optional arguments, for a node with -walletrbf=0
        unspent1 = self.nodes[1].listunspent()[0]
        psbtx_info = self.nodes[1].walletcreatefundedpsbt([{"txid":unspent1["txid"], "vout":unspent1["vout"]}], [{self.nodes[2].getnewaddress():unspent1["amount"]+1}], block_height)
        decoded_psbt = self.nodes[1].decodepsbt(psbtx_info["psbt"])
        for tx_in in decoded_psbt["tx"]["vin"]:
            assert_greater_than(tx_in["sequence"], MAX_BIP125_RBF_SEQUENCE)

        # Make sure change address wallet does not have P2SH innerscript access to results in success
        # when attempting BnB coin selection
        self.nodes[0].walletcreatefundedpsbt([], [{self.nodes[2].getnewaddress():unspent["amount"]+1}], block_height+2, {"changeAddress":self.nodes[1].getnewaddress()}, False)

        # Regression test for 14473 (mishandling of already-signed witness transaction):
        psbtx_info = self.nodes[0].walletcreatefundedpsbt([{"txid":unspent["txid"], "vout":unspent["vout"]}], [{self.nodes[2].getnewaddress():unspent["amount"]+1}])
        filled = self.nodes[0].walletfillpsbtdata(psbtx_info["psbt"])
        blinded = self.nodes[0].blindpsbt(filled["psbt"])
        signed = self.nodes[0].walletsignpsbt(blinded)
        signed_again = self.nodes[0].walletsignpsbt(signed["psbt"])
        assert_equal(signed, signed_again)
        # We don't care about the decode result, but decoding must succeed.
        self.nodes[0].decodepsbt(signed["psbt"])

        # Test the imbalance_ok argument of walletsignpsbt by manually constructing a psbt that doesn't balance.
        node1_addr = self.get_address(confidential, 1)
        node1_unconf_addr = self.to_unconf_addr(1, node1_addr)
        rt1 = self.nodes[0].createrawtransaction([], {node1_addr:11.11})
        rt1 = self.nodes[0].fundrawtransaction(rt1)
        rt1 = self.nodes[0].blindrawtransaction(rt1['hex'])
        rt1 = self.nodes[0].signrawtransactionwithwallet(rt1)
        txid1 = self.nodes[0].sendrawtransaction(rt1['hex'])
        rt1 = self.nodes[0].decoderawtransaction(rt1['hex'])

        self.nodes[0].generate(6)
        self.sync_all()

        for out in rt1['vout']:
            if out['scriptPubKey']['type'] == "fee":
                pass
            elif out['scriptPubKey']['addresses'][0] == node1_unconf_addr:
                vout1 = out['n']

        psbt = self.nodes[1].createpsbt([{"txid":txid1, "vout":vout1}], [{self.get_address(confidential, 2):1}, {"fee":0.001}])
        psbt = self.nodes[1].walletfillpsbtdata(psbt)
        psbt = self.nodes[1].blindpsbt(psbt["psbt"])
        # If imbalance_ok is false, should fail
        assert_raises_rpc_error(-25, "Transaction values or blinders are not balanced", self.nodes[1].walletsignpsbt, psbt, "ALL", False)
        # If imbalance_ok is true, should succeed
        psbt = self.nodes[1].walletsignpsbt(psbt, "ALL", True)
        psbt = self.nodes[1].finalizepsbt(psbt["psbt"])
        # ... but you still can't send it.
        assert_raises_rpc_error(-26, "bad-txns-in-ne-out, value in != value out (code 16)", self.nodes[1].sendrawtransaction, psbt['hex'])


    # BIP 174 tests are disabled because they don't work with CA yet. Comment the function so it doesn't flag lint as unused.
    """
    def run_bip174_tests(self):
        # BIP 174 Test Vectors

        # Check that unknown values are just passed through
        unknown_psbt = "cHNidP8BAD8CAAAAAf//////////////////////////////////////////AAAAAAD/////AQAAAAAAAAAAA2oBAAAAAAAACg8BAgMEBQYHCAkPAQIDBAUGBwgJCgsMDQ4PAAA="
        unknown_out = self.nodes[0].walletprocesspsbt(unknown_psbt)['psbt']
        assert_equal(unknown_psbt, unknown_out)

        # Open the data file
        with open(os.path.join(os.path.dirname(os.path.realpath(__file__)), 'data/rpc_psbt.json'), encoding='utf-8') as f:
            d = json.load(f)
            invalids = d['invalid']
            valids = d['valid']
            creators = d['creator']
            signers = d['signer']
            combiners = d['combiner']
            finalizers = d['finalizer']
            extractors = d['extractor']

        # Invalid PSBTs
        for invalid in invalids:
            assert_raises_rpc_error(-22, "TX decode failed", self.nodes[0].decodepsbt, invalid)

        # Valid PSBTs
        for valid in valids:
            self.nodes[0].decodepsbt(valid)

        # Creator Tests
        for creator in creators:
            created_tx = self.nodes[0].createpsbt(creator['inputs'], creator['outputs'])
            assert_equal(created_tx, creator['result'])

        # Signer tests
        for i, signer in enumerate(signers):
            self.nodes[2].createwallet("wallet{}".format(i))
            wrpc = self.nodes[2].get_wallet_rpc("wallet{}".format(i))
            for key in signer['privkeys']:
                wrpc.importprivkey(key)
            signed_tx = wrpc.walletprocesspsbt(signer['psbt'])['psbt']
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
        rawtx = self.nodes[0].createrawtransaction([], {unconf_addr_0:50, unconf_addr_1:50, unconf_addr_4:50})
        rawtx = self.nodes[0].fundrawtransaction(rawtx, {"changePosition":3})  # our outputs will be 0, 1, 2
        rawtx = self.nodes[0].blindrawtransaction(rawtx['hex'])
        signed_tx = self.nodes[0].signrawtransactionwithwallet(rawtx)['hex']
        txid_nonconf = self.nodes[0].sendrawtransaction(signed_tx)
        self.nodes[0].generate(1)
        self.sync_all()

        # Now use PSBT to send some coins nonconf->nonconf
        unconf_addr_2 = self.get_address(False, 1)
        psbt = self.nodes[0].createpsbt([{"txid": txid_nonconf, "vout": 0}], [{unconf_addr_2: 49.999}, {"fee": 0.001}])
        psbt = self.nodes[0].walletfillpsbtdata(psbt)['psbt']
        psbt = self.nodes[0].walletsignpsbt(psbt)['psbt']
        tx_hex = self.nodes[0].finalizepsbt(psbt)['hex']
        txid_nonconf_2 = self.nodes[0].sendrawtransaction(tx_hex)
        self.nodes[0].generate(1)
        self.sync_all()

        # Now send nonconf->conf
        conf_addr = self.get_address(True, 2)
        psbt = self.nodes[1].createpsbt([{"txid": txid_nonconf_2, "vout": 0}], [{conf_addr: 49.998}, {"fee": 0.001}])
        psbt = self.nodes[1].walletfillpsbtdata(psbt)['psbt']
        # Currently can't blind a transaction like this, so it fails
        assert_raises_rpc_error(-8, "Unable to blind transaction: Add another output to blind in order to complete the blinding.", self.nodes[1].blindpsbt, psbt, False)
        # Signing without blinding should not work either.
        assert_raises_rpc_error(-25, "Transaction is not yet fully blinded", self.nodes[1].walletsignpsbt, psbt)
        # If we pass "ignore_blind_fail", then it succeeds in this case without blinding.
        psbt = self.nodes[1].blindpsbt(psbt, True)
        psbt = self.nodes[1].walletsignpsbt(psbt)['psbt']
        hex_tx = self.nodes[1].finalizepsbt(psbt)['hex']
        self.nodes[1].sendrawtransaction(hex_tx)
        self.nodes[0].generate(1)
        self.sync_all()

        # Now send nonconf->conf (with two outputs, blinding succeeds)
        conf_addr_1 = self.get_address(True, 2)
        conf_addr_2 = self.get_address(True, 2)
        psbt = self.nodes[0].createpsbt([{"txid": txid_nonconf, "vout": 1}], [{conf_addr_1: 24.999}, {conf_addr_2: 24.999}, {"fee": 0.002}])
        psbt = self.nodes[0].walletfillpsbtdata(psbt)['psbt']
        psbt = self.nodes[0].blindpsbt(psbt, False)
        psbt = self.nodes[0].walletsignpsbt(psbt)['psbt']
        hex_tx = self.nodes[0].finalizepsbt(psbt)['hex']
        assert_equal(self.num_blinded_outputs(hex_tx), 2)
        txid_conf_2 = self.nodes[0].sendrawtransaction(hex_tx)
        self.nodes[0].generate(1)
        self.sync_all()

        # Try to send conf->nonconf: This will fail because we can't balance the blinders
        unconf_addr_3 = self.get_address(False, 0)
        psbt = self.nodes[2].createpsbt([{"txid": txid_conf_2, "vout": 0}], [{unconf_addr_3: 24.998}, {"fee": 0.001}])
        psbt = self.nodes[2].walletfillpsbtdata(psbt)['psbt']
        assert_raises_rpc_error(-8, "Unable to blind transaction: Add another output to blind in order to complete the blinding.", self.nodes[2].blindpsbt, psbt, False)

        # Try to send conf->(nonconf + conf), so we have a conf output to balance blinders
        conf_addr_3 = self.get_address(True, 0)
        psbt = self.nodes[2].createpsbt([{"txid": txid_conf_2, "vout": 0}], [{unconf_addr_3: 10}, {conf_addr_3: 14.998}, {"fee": 0.001}])
        psbt = self.nodes[2].walletfillpsbtdata(psbt)['psbt']
        psbt = self.nodes[2].blindpsbt(psbt, False)
        psbt = self.nodes[2].walletsignpsbt(psbt)['psbt']
        hex_tx = self.nodes[2].finalizepsbt(psbt)['hex']
        assert_equal(self.num_blinded_outputs(hex_tx), 1)
        self.nodes[2].sendrawtransaction(hex_tx)
        self.nodes[0].generate(1)
        self.sync_all()

        # Try to send conf->conf
        conf_addr_4 = self.get_address(True, 0)
        psbt = self.nodes[2].createpsbt([{"txid": txid_conf_2, "vout": 1}], [{conf_addr_4: 24.998}, {"fee": 0.001}])
        psbt = self.nodes[2].walletfillpsbtdata(psbt)['psbt']
        psbt = self.nodes[2].blindpsbt(psbt, False)
        psbt = self.nodes[2].walletsignpsbt(psbt)['psbt']
        hex_tx = self.nodes[2].finalizepsbt(psbt)['hex']
        assert_equal(self.num_blinded_outputs(hex_tx), 1)
        self.nodes[2].sendrawtransaction(hex_tx)
        self.nodes[0].generate(1)
        self.sync_all()

        # Try to send nonconf->(nonconf + conf + conf) -- two conf to make blinders balance
        nonconf_addr_5 = self.get_address(False, 1)
        conf_addr_5 = self.get_address(True, 1)
        conf_addr_6 = self.get_address(True, 2)
        psbt = self.nodes[0].createpsbt([{"txid": txid_nonconf, "vout": 2}], [{nonconf_addr_5: 24.999}, {conf_addr_5: 14.999}, {conf_addr_6: 10}, {"fee": 0.002}])
        psbt = self.nodes[0].walletfillpsbtdata(psbt)['psbt']
        psbt = self.nodes[0].blindpsbt(psbt, False)
        psbt = self.nodes[0].walletsignpsbt(psbt)['psbt']
        hex_tx = self.nodes[0].finalizepsbt(psbt)['hex']
        assert_equal(self.num_blinded_outputs(hex_tx), 2)
        self.nodes[0].sendrawtransaction(hex_tx)
        self.nodes[0].generate(1)
        self.sync_all()

    def run_test(self):
        self.nodes[0].generate(200)
        self.sync_all()

        # Run all the pre-Elements, tests first with non-confidential addresses, then again with confidential addresses
        self.run_basic_tests(False)
        self.run_basic_tests(True)

        # BIP 174 test vectors are disabled, because they have embedded serialized CTransactions, and
        #   the transaction serialization format changed in Elements so none of them work
        #self.run_bip174_tests()

        # Some Confidential-Assets-specific tests
        self.run_ca_tests()

        # Check that peg-ins are disallowed
        assert_raises_rpc_error(-8, 'pegin_ arguments provided but this command does not support peg-ins', self.nodes[0].createpsbt, [{"txid": "0000000000000000000000000000000000000000000000000000000000000000", "vout": 0, "pegin_bitcoin_tx": "00"}], [{self.nodes[0].getnewaddress(): 1}])
        assert_raises_rpc_error(-8, 'pegin_ arguments provided but this command does not support peg-ins', self.nodes[0].createpsbt, [{"txid": "0000000000000000000000000000000000000000000000000000000000000000", "vout": 0, "pegin_txout_proof": "00"}], [{self.nodes[0].getnewaddress(): 1}])
        assert_raises_rpc_error(-8, 'pegin_ arguments provided but this command does not support peg-ins', self.nodes[0].createpsbt, [{"txid": "0000000000000000000000000000000000000000000000000000000000000000", "vout": 0, "pegin_claim_script": "00"}], [{self.nodes[0].getnewaddress(): 1}])
        assert_raises_rpc_error(-8, 'pegin_ arguments provided but this command does not support peg-ins', self.nodes[0].walletcreatefundedpsbt, [{"txid": "0000000000000000000000000000000000000000000000000000000000000000", "vout": 0, "pegin_bitcoin_tx": "00"}], [{self.nodes[0].getnewaddress(): 1}])
        assert_raises_rpc_error(-8, 'pegin_ arguments provided but this command does not support peg-ins', self.nodes[0].walletcreatefundedpsbt, [{"txid": "0000000000000000000000000000000000000000000000000000000000000000", "vout": 0, "pegin_txout_proof": "00"}], [{self.nodes[0].getnewaddress(): 1}])
        assert_raises_rpc_error(-8, 'pegin_ arguments provided but this command does not support peg-ins', self.nodes[0].walletcreatefundedpsbt, [{"txid": "0000000000000000000000000000000000000000000000000000000000000000", "vout": 0, "pegin_claim_script": "00"}], [{self.nodes[0].getnewaddress(): 1}])

        self.test_utxo_conversion()

        # Test that psbts with p2pkh outputs are created properly
        p2pkh = self.nodes[0].getnewaddress(address_type='legacy')
        psbt = self.nodes[1].walletcreatefundedpsbt([], [{p2pkh : 1}], 0, {"includeWatching" : True}, True)
        self.nodes[0].decodepsbt(psbt['psbt'])

        # Test decoding error: invalid base64
        assert_raises_rpc_error(-22, "TX decode failed invalid base64", self.nodes[0].decodepsbt, ";definitely not base64;")

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

        def test_psbt_input_keys(psbt_input, keys):
            """Check that the psbt input has only the expected keys."""
            assert_equal(set(keys), set(psbt_input.keys()))

        # Create a PSBT. None of the inputs are filled initially
        psbt = self.nodes[1].createpsbt([{"txid":txid1, "vout":vout1},{"txid":txid2, "vout":vout2},{"txid":txid3, "vout":vout3}], {self.nodes[0].getnewaddress():32.999})
        decoded = self.nodes[1].decodepsbt(psbt)
        test_psbt_input_keys(decoded['inputs'][0], [])
        test_psbt_input_keys(decoded['inputs'][1], [])
        test_psbt_input_keys(decoded['inputs'][2], [])

        # Update a PSBT with UTXOs from the node
        # Bech32 inputs should be filled with witness UTXO. Other inputs should not be filled because they are non-witness
        updated = self.nodes[1].utxoupdatepsbt(psbt)
        decoded = self.nodes[1].decodepsbt(updated)
        test_psbt_input_keys(decoded['inputs'][0], ['witness_utxo'])
        test_psbt_input_keys(decoded['inputs'][1], [])
        test_psbt_input_keys(decoded['inputs'][2], [])

        # Try again, now while providing descriptors, making P2SH-segwit work, and causing bip32_derivs and redeem_script to be filled in
        descs = [self.nodes[1].getaddressinfo(addr)['desc'] for addr in [addr1,addr2,addr3]]
        updated = self.nodes[1].utxoupdatepsbt(psbt=psbt, descriptors=descs)
        decoded = self.nodes[1].decodepsbt(updated)
        test_psbt_input_keys(decoded['inputs'][0], ['witness_utxo', 'bip32_derivs'])
        test_psbt_input_keys(decoded['inputs'][1], [])
        test_psbt_input_keys(decoded['inputs'][2], ['witness_utxo', 'bip32_derivs', 'redeem_script'])

        # Two PSBTs with a common input should not be joinable
        psbt1 = self.nodes[1].createpsbt([{"txid":txid1, "vout":vout1}], {self.nodes[0].getnewaddress():Decimal('10.999')})
        assert_raises_rpc_error(-8, "exists in multiple PSBTs", self.nodes[1].joinpsbts, [psbt1, updated])

        # Join two distinct PSBTs
        addr4 = self.nodes[1].getnewaddress("", "p2sh-segwit")
        txid4 = self.nodes[0].sendtoaddress(addr4, 5)
        vout4 = find_output(self.nodes[0], txid4, 5)
        self.nodes[0].generate(6)
        self.sync_all()
        psbt2 = self.nodes[1].createpsbt([{"txid":txid4, "vout":vout4}], {self.nodes[0].getnewaddress():Decimal('4.999')})
        psbt2 = self.nodes[1].walletprocesspsbt(psbt2)['psbt']
        psbt2_decoded = self.nodes[0].decodepsbt(psbt2)
        assert "final_scriptwitness" in psbt2_decoded['inputs'][0] and "final_scriptSig" in psbt2_decoded['inputs'][0]
        joined = self.nodes[0].joinpsbts([psbt, psbt2])
        joined_decoded = self.nodes[0].decodepsbt(joined)
        assert len(joined_decoded['inputs']) == 4 and len(joined_decoded['outputs']) == 2 and "final_scriptwitness" not in joined_decoded['inputs'][3] and "final_scriptSig" not in joined_decoded['inputs'][3]

        # Check that joining shuffles the inputs and outputs
        # 10 attempts should be enough to get a shuffled join
        shuffled = False
        for i in range(0, 10):
            shuffled_joined = self.nodes[0].joinpsbts([psbt, psbt2])
            shuffled |= joined != shuffled_joined
            if shuffled:
                break
        assert shuffled

        # Newly created PSBT needs UTXOs and updating
        addr = self.nodes[1].getnewaddress("", "p2sh-segwit")
        txid = self.nodes[0].sendtoaddress(addr, 7)
        addrinfo = self.nodes[1].getaddressinfo(addr)
        blockhash = self.nodes[0].generate(6)[0]
        self.sync_all()
        vout = find_output(self.nodes[0], txid, 7, blockhash=blockhash)
        psbt = self.nodes[1].createpsbt([{"txid":txid, "vout":vout}], {self.nodes[0].getnewaddress("", "p2sh-segwit"):Decimal('6.999')})
        analyzed = self.nodes[0].analyzepsbt(psbt)
        assert not analyzed['inputs'][0]['has_utxo'] and not analyzed['inputs'][0]['is_final'] and analyzed['inputs'][0]['next'] == 'updater' and analyzed['next'] == 'updater'

        # After update with wallet, only needs signing
        updated = self.nodes[1].walletprocesspsbt(psbt, False, 'ALL', True)['psbt']
        analyzed = self.nodes[0].analyzepsbt(updated)
        assert analyzed['inputs'][0]['has_utxo'] and not analyzed['inputs'][0]['is_final'] and analyzed['inputs'][0]['next'] == 'signer' and analyzed['next'] == 'signer' and analyzed['inputs'][0]['missing']['signatures'][0] == addrinfo['embedded']['witness_program']

        # Check fee and size things
        assert_equal(analyzed['fee']['bitcoin'], Decimal('0.001'))
        assert_equal(analyzed['estimated_vsize'], 170)
        assert_equal(analyzed['estimated_feerate'], Decimal('0.00588235'))

        # After signing and finalizing, needs extracting
        signed = self.nodes[1].walletprocesspsbt(updated)['psbt']
        analyzed = self.nodes[0].analyzepsbt(signed)
        assert analyzed['inputs'][0]['has_utxo'] and analyzed['inputs'][0]['is_final'] and analyzed['next'] == 'extractor'

if __name__ == '__main__':
    PSBTTest().main()
