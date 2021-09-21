#!/usr/bin/env python3
# Copyright (c) 2016 The Bitcoin Core developers
# Distributed under the MIT/X11 software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

import io

from decimal import Decimal
from test_framework.test_framework import BitcoinTestFramework
from test_framework.authproxy import JSONRPCException
from test_framework.messages import (
    COIN,
    CTransaction,
    CTxOut,
    CTxOutAsset,
    CTxOutValue,
    CTxInWitness,
    CTxOutWitness,
    tx_from_hex,
)
from test_framework.util import (
    assert_equal,
    hex_str_to_bytes,
    BITCOIN_ASSET_OUT,
    assert_raises_rpc_error,
)
import os
import re

from test_framework.liquid_addr import (
    encode,
    decode,
)

class CTTest (BitcoinTestFramework):

    def set_test_params(self):
        self.num_nodes = 3
        self.setup_clean_chain = True
        args = ["-blindedaddresses=1", "-initialfreecoins=2100000000000000", "-con_blocksubsidy=0", "-con_connect_genesis_outputs=1"]
        self.extra_args = [args] * self.num_nodes
        self.extra_args[0].append("-anyonecanspendaremine=1") # first node gets the coins

    def setup_network(self, split=False):
        self.setup_nodes()
        self.connect_nodes(0, 1)
        self.connect_nodes(1, 2)
        self.connect_nodes(0, 2)
        self.sync_all()

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def test_wallet_recovery(self):
        file_path = "/tmp/blind_details"
        try:
            os.remove(file_path)
        except OSError:
            pass

        # Wallet recovery requires more than just seed, but also master blinding key
        # which currently is not derived from seed, see
        # https://github.com/ElementsProject/elements/pull/232
        blind_addr = self.nodes[0].getnewaddress()

        self.nodes[0].dumpwallet(file_path)

        found_seed = False
        found_blind = False
        with open(file_path, encoding="utf8") as f:
            for line in f:
                if "hdseed=1" in line:
                    split = re.split(" ", line)
                    found_seed = split[0]
                split = re.split("Master private blinding key: ", line)
                if len(split) == 2:
                    assert_equal(len(split[1].rstrip()), 64)
                    found_blind = split[1].rstrip()

        assert_equal(found_blind, self.nodes[0].dumpmasterblindingkey())

        # Create new wallet
        self.nodes[0].createwallet("recover")
        rec = self.nodes[0].get_wallet_rpc("recover")
        wrong_info = rec.getaddressinfo(blind_addr)
        assert "pubkey" not in wrong_info
        assert_equal(wrong_info["ismine"], False)

        # Setting seed should get us more info, still not "ours" until blinding key
        rec.generatetoaddress(1, rec.getnewaddress()) # get out of IBD
        rec.sethdseed(True, found_seed)

        wrong_blind_info = rec.getaddressinfo(blind_addr)
        assert "pubkey" in wrong_blind_info
        assert_equal(wrong_blind_info["ismine"], False)

        # Now import master blinding key
        rec.importmasterblindingkey(found_blind)
        assert_equal(rec.dumpmasterblindingkey(), found_blind)
        blind_info = rec.getaddressinfo(blind_addr)
        assert "pubkey" in blind_info
        assert_equal(blind_info["ismine"], True)
        assert_equal(rec.getaddressinfo(blind_info["unconfidential"])["confidential"], blind_addr)
        self.nodes[0].unloadwallet("recover")

    def test_null_rangeproof_enforcement(self):
        self.nodes[0].generate(1)

        # 1. Produce a transaction. This is coming out of initialfreecoins so
        #    no signatures are needed, which slightly simplifies the test
        unfunded_tx = self.nodes[0].createrawtransaction([], [{self.nodes[1].getnewaddress(): 1000}])
        unblinded_tx = self.nodes[0].fundrawtransaction(unfunded_tx)['hex']
        unsigned_tx = self.nodes[0].blindrawtransaction(unblinded_tx)
        assert_equal(self.nodes[0].testmempoolaccept([unsigned_tx])[0]['allowed'], True) # tx is ok before we malleate it
        tx = tx_from_hex(unsigned_tx)
        assert tx.wit.vtxinwit[0].vchIssuanceAmountRangeproof == b''
        assert tx.wit.vtxinwit[0].vchInflationKeysRangeproof == b''

        # 1a. Add an issuance with null amounts but rangeproofs
        tx.wit.vtxinwit = [CTxInWitness()]
        tx.wit.vtxinwit[0].vchIssuanceAmountRangeproof = b'this should not be allowed'
        hex_tx = tx.serialize(with_witness=True).hex()
        assert_equal(self.nodes[0].testmempoolaccept([hex_tx])[0]['allowed'], False)

        tx.wit.vtxinwit[0].vchIssuanceAmountRangeproof = b''
        tx.wit.vtxinwit[0].vchInflationKeysRangeproof = b'and neither should this'
        hex_tx = tx.serialize(with_witness=True).hex()
        assert_equal(self.nodes[0].testmempoolaccept([hex_tx])[0]['allowed'], False)

        # 2. Create an issuance tx with no tokens
        issuance_tx = self.nodes[0].rawissueasset(unblinded_tx, [{"asset_amount": 2, "asset_address": self.nodes[1].getnewaddress()}])[0]['hex']
        issuance_tx = self.nodes[0].blindrawtransaction(issuance_tx)
        assert_equal(self.nodes[0].testmempoolaccept([issuance_tx])[0]['allowed'], True) # tx is ok before we malleate it
        tx = tx_from_hex(issuance_tx)
        assert tx.wit.vtxinwit[0].vchIssuanceAmountRangeproof != b''
        assert tx.wit.vtxinwit[0].vchInflationKeysRangeproof == b''
        # 2a. Attach a rangeproof to the (null) reissuance token amount
        tx.wit.vtxinwit[0].vchInflationKeysRangeproof = b'and this also should not be allowed'
        hex_tx = tx.serialize(with_witness=True).hex()
        assert_equal(self.nodes[0].testmempoolaccept([hex_tx])[0]['allowed'], False)

        # 3. Create an issuance tx with tokens but no issuance. This time we do an
        #    explicit issuance because we want to null out the issuance amount, and
        #    `rawissueasset` would want to put a confidential 0 rather than a null.
        blinded_addr = self.nodes[1].getnewaddress()
        unblinded_addr = self.nodes[1].validateaddress(blinded_addr)['unconfidential']
        issuance_tx = self.nodes[0].rawissueasset(unblinded_tx, [{"token_amount": 2, "token_address": unblinded_addr, "blind": False }])[0]['hex']
        issuance_tx = self.nodes[0].blindrawtransaction(issuance_tx, False, [], False)
        assert_equal(self.nodes[0].testmempoolaccept([issuance_tx])[0]['allowed'], True) # tx is ok before we malleate it
        tx = tx_from_hex(issuance_tx)
        assert tx.wit.vtxinwit[0].vchIssuanceAmountRangeproof == b''
        assert tx.wit.vtxinwit[0].vchInflationKeysRangeproof == b''
        # 3a. Attach a rangeproof to the (null) issuance amount
        tx.wit.vtxinwit[0].vchIssuanceAmountRangeproof = b'this also should not be allowed'
        hex_tx = tx.serialize(with_witness=True).hex()
        assert_equal(self.nodes[0].testmempoolaccept([hex_tx])[0]['allowed'], False)

    def run_test(self):

        print("Testing that null issuances must have null rangeproofs")
        self.test_null_rangeproof_enforcement()

        print("Testing wallet secret recovery")
        self.test_wallet_recovery()

        print("Test blech32 python roundtrip")
        # blech/bech are aliased, both are blech32
        for addrtype in ["bech32", "blech32"]:
            addr_to_rt = self.nodes[0].getnewaddress("", addrtype)
            hrp = addr_to_rt[:2]
            assert_equal(hrp, "el")
            (witver, witprog) = decode(hrp, addr_to_rt)
            assert_equal(encode(hrp, witver, witprog), addr_to_rt)

        # Test that "blech32" gives a blinded segwit address.
        blech32_addr = self.nodes[0].getnewaddress("", "blech32")
        blech32_addr_info = self.nodes[0].getaddressinfo(blech32_addr)
        assert_equal(blech32_addr_info["iswitness"], True)
        assert_equal(blech32_addr_info["confidential"], blech32_addr)

        print("General Confidential tests")
        # Running balances
        node0 = self.nodes[0].getbalance()["bitcoin"]
        assert_equal(node0, 21000000) # just making sure initialfreecoins is working
        node1 = 0
        node2 = 0

        self.nodes[0].generate(101)
        txid = self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), node0, "", "", True)
        self.nodes[0].generate(101)
        self.sync_all()
        assert_equal(self.nodes[0].getbalance()["bitcoin"], node0)
        assert_equal(self.nodes[1].getbalance("*", 1, False, False, "bitcoin"), node1)
        assert_equal(self.nodes[2].getbalance("*", 1, False, False, "bitcoin"), node2)

        # Send 3 BTC from 0 to a new unconfidential address of 2 with
        # the sendtoaddress call
        address = self.nodes[2].getnewaddress()
        unconfidential_address = self.nodes[2].validateaddress(address)["unconfidential"]
        value0 = 3
        self.nodes[0].sendtoaddress(unconfidential_address, value0)
        self.nodes[0].generate(101)
        self.sync_all()

        node0 = node0 - value0
        node2 = node2 + value0

        assert_equal(self.nodes[0].getbalance()["bitcoin"], node0)
        assert_equal(self.nodes[1].getbalance("*", 1, False, False, "bitcoin"), node1)
        assert_equal(self.nodes[2].getbalance()["bitcoin"], node2)

        # Send 5 BTC from 0 to a new address of 2 with the sendtoaddress call
        address2 = self.nodes[2].getnewaddress()
        unconfidential_address2 = self.nodes[2].validateaddress(address2)["unconfidential"]
        value1 = 5
        confidential_tx_id = self.nodes[0].sendtoaddress(address2, value1)
        self.nodes[0].generate(101)
        self.sync_all()

        node0 = node0 - value1
        node2 = node2 + value1

        assert_equal(self.nodes[0].getbalance()["bitcoin"], node0)
        assert_equal(self.nodes[1].getbalance("*", 1, False, False, "bitcoin"), node1)
        assert_equal(self.nodes[2].getbalance()["bitcoin"], node2)

        # Send 7 BTC from 0 to the unconfidential address of 2 and 11 BTC to the
        # confidential address using the raw transaction interface
        change_address = self.nodes[0].getnewaddress()
        value2 = 7
        value3 = 11
        value23 = value2 + value3
        unspent = self.nodes[0].listunspent(1, 9999999, [], True, {"asset": "bitcoin"})
        unspent = [i for i in unspent if i['amount'] > value23]
        assert_equal(len(unspent), 1)
        fee = Decimal('0.0001')
        tx = self.nodes[0].createrawtransaction([{"txid": unspent[0]["txid"],
                                                  "vout": unspent[0]["vout"],
                                                  "nValue": unspent[0]["amount"]}],
                                                [{unconfidential_address: value2}, {address2: value3},
                                                {change_address: unspent[0]["amount"] - value2 - value3 - fee}, {"fee":fee}])
        tx = self.nodes[0].blindrawtransaction(tx)
        tx_signed = self.nodes[0].signrawtransactionwithwallet(tx)
        raw_tx_id = self.nodes[0].sendrawtransaction(tx_signed['hex'])
        self.nodes[0].generate(101)
        self.sync_all()

        node0 -= (value2 + value3)
        node2 += value2 + value3

        assert_equal(self.nodes[0].getbalance()["bitcoin"], node0)
        assert_equal(self.nodes[1].getbalance("*", 1, False, False, "bitcoin"), node1)
        assert_equal(self.nodes[2].getbalance()["bitcoin"], node2)

        # Check 2's listreceivedbyaddress
        received_by_address = self.nodes[2].listreceivedbyaddress(0, False, False, "", "bitcoin")
        validate_by_address = [(address2, value1 + value3), (address, value0 + value2)]
        assert_equal(sorted([(ele['address'], ele['amount']) for ele in received_by_address], key=lambda t: t[0]),
                sorted(validate_by_address, key = lambda t: t[0]))
        received_by_address = self.nodes[2].listreceivedbyaddress(0, False, False, "")
        validate_by_address = [(address2, {"bitcoin": value1 + value3}), (address, {"bitcoin": value0 + value2})]
        assert_equal(sorted([(ele['address'], ele['amount']) for ele in received_by_address], key=lambda t: t[0]),
                sorted(validate_by_address, key = lambda t: t[0]))

        # Give an auditor (node 1) a blinding key to allow her to look at
        # transaction values
        self.nodes[1].importaddress(address2)
        received_by_address = self.nodes[1].listreceivedbyaddress(1, False, True)
        #Node sees nothing unless it understands the values
        assert_equal(len(received_by_address), 0)
        assert_equal(len(self.nodes[1].listunspent(1, 9999999, [], True, {"asset": "bitcoin"})), 0)

        # Import the blinding key
        blindingkey = self.nodes[2].dumpblindingkey(address2)
        self.nodes[1].importblindingkey(address2, blindingkey)
        # Check the auditor's gettransaction and listreceivedbyaddress
        # Needs rescan to update wallet txns
        conf_tx = self.nodes[1].gettransaction(confidential_tx_id, True)
        assert_equal(conf_tx['amount']["bitcoin"], value1)

        # Make sure wallet can now deblind part of transaction
        deblinded_tx = self.nodes[1].unblindrawtransaction(conf_tx['hex'])['hex']
        for output in self.nodes[1].decoderawtransaction(deblinded_tx)["vout"]:
            if "value" in output and output["scriptPubKey"]["type"] != "fee":
                assert_equal(output["scriptPubKey"]["address"], self.nodes[1].validateaddress(address2)['unconfidential'])
                found_unblinded = True
        assert found_unblinded

        assert_equal(self.nodes[1].gettransaction(raw_tx_id, True)['amount']["bitcoin"], value3)
        assert_equal(self.nodes[1].gettransaction(raw_tx_id, True, False, "bitcoin")['amount'], value3)
        list_unspent = self.nodes[1].listunspent(1, 9999999, [], True, {"asset": "bitcoin"})
        assert_equal(list_unspent[0]['amount']+list_unspent[1]['amount'], value1+value3)
        received_by_address = self.nodes[1].listreceivedbyaddress(1, False, True)
        assert_equal(len(received_by_address), 1)
        assert_equal((received_by_address[0]['address'], received_by_address[0]['amount']['bitcoin']),
                     (unconfidential_address2, value1 + value3))

        # Spending a single confidential output and sending it to a
        # unconfidential output is not possible with CT. Test the
        # correct behavior of blindrawtransaction.
        unspent = self.nodes[0].listunspent(1, 9999999, [], True, {"asset": "bitcoin"})
        unspent = [i for i in unspent if i['amount'] > value23]
        assert_equal(len(unspent), 1)
        tx = self.nodes[0].createrawtransaction([{"txid": unspent[0]["txid"],
                                                  "vout": unspent[0]["vout"],
                                                  "nValue": unspent[0]["amount"]}],
                                                  [{unconfidential_address: unspent[0]["amount"] - fee}, {"fee":fee}])

        # Test that blindrawtransaction adds an OP_RETURN output to balance blinders
        temptx = self.nodes[0].blindrawtransaction(tx)
        decodedtx = self.nodes[0].decoderawtransaction(temptx)
        assert_equal(decodedtx["vout"][-1]["scriptPubKey"]["asm"], "OP_RETURN")
        assert_equal(len(decodedtx["vout"]), 3)

        # Create same transaction but with a change/dummy output.
        # It should pass the blinding step.
        value4 = 17
        change_address = self.nodes[0].getrawchangeaddress()
        tx = self.nodes[0].createrawtransaction([{"txid": unspent[0]["txid"],
                                                  "vout": unspent[0]["vout"],
                                                  "nValue": unspent[0]["amount"]}],
                                                  [{unconfidential_address: value4},
                                                   {change_address: unspent[0]["amount"] - value4 - fee}, {"fee":fee}])
        tx = self.nodes[0].blindrawtransaction(tx)
        tx_signed = self.nodes[0].signrawtransactionwithwallet(tx)
        txid = self.nodes[0].sendrawtransaction(tx_signed['hex'])
        decodedtx = self.nodes[0].decoderawtransaction(tx_signed["hex"])
        self.nodes[0].generate(101)
        self.sync_all()

        unblindfound = False
        for i in range(len(decodedtx["vout"])):
            txout = self.nodes[0].gettxout(txid, i)
            if txout is not None and "asset" in txout:
                unblindfound = True

        if unblindfound == False:
            raise Exception("No unconfidential output detected when one should exist")

        node0 -= value4
        node2 += value4
        assert_equal(self.nodes[0].getbalance()["bitcoin"], node0)
        assert_equal(self.nodes[1].getbalance("*", 1, False, False, "bitcoin"), node1)
        assert_equal(self.nodes[2].getbalance()["bitcoin"], node2)

        # Testing wallet's ability to deblind its own outputs
        addr = self.nodes[0].getnewaddress()
        addr2 = self.nodes[0].getnewaddress()
        # We add two to-blind outputs, fundraw adds an already-blinded change output
        # If we only add one, the newly blinded will be 0-blinded because input = -output
        raw = self.nodes[0].createrawtransaction([], [{addr:Decimal('1.1')}, {addr2:1}])
        funded = self.nodes[0].fundrawtransaction(raw)
        # fund again to make sure no blinded outputs were created (would fail)
        funded = self.nodes[0].fundrawtransaction(funded["hex"])
        blinded = self.nodes[0].blindrawtransaction(funded["hex"])
        # blind again to make sure we know output blinders
        blinded2 = self.nodes[0].blindrawtransaction(blinded)
        # then sign and send
        signed = self.nodes[0].signrawtransactionwithwallet(blinded2)
        self.nodes[0].sendrawtransaction(signed["hex"])

        # Aside: Check all outputs after fundraw are properly marked for blinding
        fund_decode = self.nodes[0].decoderawtransaction(funded["hex"])
        for output in fund_decode["vout"][:-1]:
            assert "asset" in output
            assert "value" in output
            assert output["scriptPubKey"]["type"] != "fee"
            assert output["commitmentnonce_fully_valid"]
        assert fund_decode["vout"][-1]["scriptPubKey"]["type"] == "fee"
        assert not fund_decode["vout"][-1]["commitmentnonce_fully_valid"]

        # Also check that all fundraw outputs marked for blinding are blinded later
        for blind_tx in [blinded, blinded2]:
            blind_decode = self.nodes[0].decoderawtransaction(blind_tx)
            for output in blind_decode["vout"][:-1]:
                assert "asset" not in output
                assert "value" not in output
                assert output["scriptPubKey"]["type"] != "fee"
                assert output["commitmentnonce_fully_valid"]
            assert blind_decode["vout"][-1]["scriptPubKey"]["type"] == "fee"
            assert "asset" in blind_decode["vout"][-1]
            assert "value" in blind_decode["vout"][-1]
            assert not blind_decode["vout"][-1]["commitmentnonce_fully_valid"]

        # Check createblindedaddress functionality
        blinded_addr = self.nodes[0].getnewaddress()
        validated_addr = self.nodes[0].validateaddress(blinded_addr)
        blinding_pubkey = self.nodes[0].validateaddress(blinded_addr)["confidential_key"]
        blinding_key = self.nodes[0].dumpblindingkey(blinded_addr)
        assert_equal(blinded_addr, self.nodes[1].createblindedaddress(validated_addr["unconfidential"], blinding_pubkey))

        # If a blinding key is over-ridden by a newly imported one, funds may be unaccounted for
        new_addr = self.nodes[0].getnewaddress()
        new_validated = self.nodes[0].validateaddress(new_addr)
        self.nodes[2].sendtoaddress(new_addr, 1)
        self.sync_all()
        diff_blind = self.nodes[1].createblindedaddress(new_validated["unconfidential"], blinding_pubkey)
        assert_equal(len(self.nodes[0].listunspent(0, 0, [new_validated["unconfidential"]])), 1)
        self.nodes[0].importblindingkey(diff_blind, blinding_key)
        # CT values for this wallet transaction  have been cached via importblindingkey
        # therefore result will be same even though we change blinding keys
        assert_equal(len(self.nodes[0].listunspent(0, 0, [new_validated["unconfidential"]])), 1)

        # Confidential Assets Tests

        print("Assets tests...")

        # Bitcoin is the first issuance
        assert_equal(self.nodes[0].listissuances()[0]["assetlabel"], "bitcoin")
        assert_equal(len(self.nodes[0].listissuances()), 1)

        # Unblinded issuance of asset
        issued = self.nodes[0].issueasset(1, 1, False)
        self.nodes[0].reissueasset(issued["asset"], 1)

        # Compare resulting fields with getrawtransaction
        raw_details = self.nodes[0].getrawtransaction(issued["txid"], 1)
        assert_equal(issued["entropy"], raw_details["vin"][issued["vin"]]["issuance"]["assetEntropy"])
        assert_equal(issued["asset"], raw_details["vin"][issued["vin"]]["issuance"]["asset"])
        assert_equal(issued["token"], raw_details["vin"][issued["vin"]]["issuance"]["token"])

        self.nodes[0].generate(1)
        self.sync_all()

        issued2 = self.nodes[0].issueasset(2, 1)
        test_asset = issued2["asset"]
        assert_equal(self.nodes[0].getwalletinfo()['balance'][test_asset], Decimal(2))
        assert test_asset not in self.nodes[1].getwalletinfo()['balance']

        # Assets balance checking, note that accounts are completely ignored because
        # balance queries with accounts are horrifically broken upstream
        assert_equal(self.nodes[0].getbalance("*", 0, False, False, "bitcoin"), self.nodes[0].getbalance("*", 0, False, False, "bitcoin"))
        assert_equal(self.nodes[0].getbalance("*", 0, False, False)["bitcoin"], self.nodes[0].getbalance("*", 0, False, False, "bitcoin"))
        assert_equal(self.nodes[0].getwalletinfo()['balance']['bitcoin'], self.nodes[0].getbalance("*", 0, False, False, "bitcoin"))

        # Send some bitcoin and other assets over as well to fund wallet
        addr = self.nodes[2].getnewaddress()
        txid = self.nodes[0].sendtoaddress(addr, 5)
        # Make sure we're doing 52 bits of hiding which covers 21M BTC worth
        assert_equal(self.nodes[0].getrawtransaction(txid, 1)["vout"][0]["ct-bits"], 52)
        self.nodes[0].sendmany("", {addr: 1, self.nodes[2].getnewaddress(): 13}, 0, "", [], False, 1, "UNSET", {addr: test_asset})

        self.sync_all()

        # Should have exactly 1 in change(trusted, though not confirmed) after sending one off
        assert_equal(self.nodes[0].getbalance("*", 0, False, False, test_asset), 1)
        assert_equal(self.nodes[2].getunconfirmedbalance()[test_asset], Decimal(1))

        b_utxos = self.nodes[2].listunspent(0, 0, [], True, {"asset": "bitcoin"})
        t_utxos = self.nodes[2].listunspent(0, 0, [], True, {"asset": test_asset})

        assert_equal(len(self.nodes[2].listunspent(0, 0, [])), len(b_utxos)+len(t_utxos))

        # Now craft a blinded transaction via raw api
        rawaddrs = []
        for i in range(2):
            rawaddrs.append(self.nodes[1].getnewaddress())
        raw_assets = self.nodes[2].createrawtransaction(
                [
                    {"txid":b_utxos[0]['txid'], "vout":b_utxos[0]['vout'], "nValue":b_utxos[0]['amount']},
                    {"txid":b_utxos[1]['txid'], "vout":b_utxos[1]['vout'], "nValue":b_utxos[1]['amount'], "asset":b_utxos[1]['asset']},
                    {"txid":t_utxos[0]['txid'], "vout":t_utxos[0]['vout'], "nValue":t_utxos[0]['amount'], "asset":t_utxos[0]['asset']}
                ],
                [
                    {rawaddrs[1]:Decimal(t_utxos[0]['amount']), "asset": t_utxos[0]["asset"]},
                    {rawaddrs[0]:Decimal(b_utxos[0]['amount']+b_utxos[1]['amount']-Decimal("0.01")), "asset": b_utxos[0]["asset"]},
                    {"fee":Decimal("0.01"), "asset": b_utxos[0]["asset"]}
                ],
                0,
                False)

        # Sign unblinded, then blinded
        signed_assets = self.nodes[2].signrawtransactionwithwallet(raw_assets)
        blind_assets = self.nodes[2].blindrawtransaction(raw_assets)
        signed_assets = self.nodes[2].signrawtransactionwithwallet(blind_assets)

        # And finally send
        self.nodes[2].sendrawtransaction(signed_assets['hex'])
        self.nodes[2].generate(101)
        self.sync_all()

        issuancedata = self.nodes[2].issueasset(0, Decimal('0.00000006')) #0 of asset, 6 reissuance token

        # Node 2 will send node 1 a reissuance token, both will generate assets
        self.nodes[2].sendtoaddress(self.nodes[1].getnewaddress(), Decimal('0.00000001'), "", "", False, False, 1, "UNSET", False, issuancedata["token"])
        # node 1 needs to know about a (re)issuance to reissue itself
        self.nodes[1].importaddress(self.nodes[2].gettransaction(issuancedata["txid"])["details"][0]["address"])
        # also send some bitcoin
        self.nodes[2].generate(1)
        self.sync_all()

        self.nodes[1].reissueasset(issuancedata["asset"], Decimal('0.05'))
        self.nodes[2].reissueasset(issuancedata["asset"], Decimal('0.025'))
        self.nodes[1].generate(1)
        self.sync_all()

        # Check for value accounting when asset issuance is null but token not, ie unblinded
        # HACK: Self-send to sweep up bitcoin inputs into blinded output.
        # We were hitting https://github.com/ElementsProject/elements/issues/473 for the following issuance
        self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), self.nodes[0].getwalletinfo()["balance"]["bitcoin"], "", "", True)
        issued = self.nodes[0].issueasset(0, 1, False)
        walletinfo = self.nodes[0].getwalletinfo()
        assert issued["asset"] not in walletinfo["balance"]
        assert_equal(walletinfo["balance"][issued["token"]], Decimal(1))
        assert issued["asset"] not in walletinfo["unconfirmed_balance"]
        assert issued["token"] not in walletinfo["unconfirmed_balance"]

        # Check for value when receiving different assets by same address.
        self.nodes[0].sendtoaddress(unconfidential_address2, Decimal('0.00000001'), "", "", False, False, 1, "UNSET", False, test_asset)
        self.nodes[0].sendtoaddress(unconfidential_address2, Decimal('0.00000002'), "", "", False, False, 1, "UNSET", False, test_asset)
        self.nodes[0].generate(1)
        self.sync_all()
        received_by_address = self.nodes[1].listreceivedbyaddress(0, False, True)
        multi_asset_amount = [x for x in received_by_address if x['address'] == unconfidential_address2][0]['amount']
        assert_equal(multi_asset_amount['bitcoin'], value1 + value3)
        assert_equal(multi_asset_amount[test_asset], Decimal('0.00000003'))

        # Check blinded multisig functionality and partial blinding functionality

        # Get two pubkeys
        blinded_addr = self.nodes[0].getnewaddress()
        pubkey = self.nodes[0].getaddressinfo(blinded_addr)["pubkey"]
        blinded_addr2 = self.nodes[1].getnewaddress()
        pubkey2 = self.nodes[1].getaddressinfo(blinded_addr2)["pubkey"]
        pubkeys = [pubkey, pubkey2]
        # Add multisig address
        unconfidential_addr = self.nodes[0].addmultisigaddress(2, pubkeys)["address"]
        self.nodes[1].addmultisigaddress(2, pubkeys)
        self.nodes[0].importaddress(unconfidential_addr)
        self.nodes[1].importaddress(unconfidential_addr)
        # Use blinding key from node 0's original getnewaddress call
        blinding_pubkey = self.nodes[0].getaddressinfo(blinded_addr)["confidential_key"]
        blinding_key = self.nodes[0].dumpblindingkey(blinded_addr)
        # Create blinded address from p2sh address and import corresponding privkey
        blinded_multisig_addr = self.nodes[0].createblindedaddress(unconfidential_addr, blinding_pubkey)
        self.nodes[0].importblindingkey(blinded_multisig_addr, blinding_key)

        # Issue new asset, to use different assets in one transaction when doing
        # partial blinding. Just to make these tests a bit more elaborate :-)
        issued3 = self.nodes[2].issueasset(1, 0)
        self.nodes[2].generate(1)
        self.sync_all()
        node2_balance = self.nodes[2].getbalance()
        assert issued3['asset'] in node2_balance
        assert_equal(node2_balance[issued3['asset']], Decimal(1))

        # Send asset to blinded multisig address and check that it was received
        self.nodes[2].sendtoaddress(address=blinded_multisig_addr, amount=1, assetlabel=issued3['asset'])
        self.sync_all()
        # We will use this multisig UTXO in our partially-blinded transaction,
        # and will also check that multisig UTXO can be successfully spent
        # after the transaction is signed by node1 and node0 in succession.
        unspent_asset = self.nodes[0].listunspent(0, 0, [unconfidential_addr], True, {"asset":issued3['asset']})
        assert_equal(len(unspent_asset), 1)
        assert issued3['asset'] not in self.nodes[2].getbalance()

        # Create new UTXO on node0 to be used in our partially-blinded transaction
        blinded_addr = self.nodes[0].getnewaddress()
        addr = self.nodes[0].validateaddress(blinded_addr)["unconfidential"]
        self.nodes[0].sendtoaddress(blinded_addr, 0.1)
        unspent = self.nodes[0].listunspent(0, 0, [addr])
        assert_equal(len(unspent), 1)

        # Create new UTXO on node1 to be used in our partially-blinded transaction
        blinded_addr2 = self.nodes[1].getnewaddress()
        addr2 = self.nodes[1].validateaddress(blinded_addr2)["unconfidential"]
        self.nodes[1].sendtoaddress(blinded_addr2, 0.11)
        unspent2 = self.nodes[1].listunspent(0, 0, [addr2])
        assert_equal(len(unspent2), 1)

        # The transaction will have three non-fee outputs
        dst_addr = self.nodes[0].getnewaddress()
        dst_addr2 = self.nodes[1].getnewaddress()
        dst_addr3 = self.nodes[2].getnewaddress()

        # Inputs are selected up front
        inputs = [{"txid": unspent2[0]["txid"], "vout": unspent2[0]["vout"]}, {"txid": unspent[0]["txid"], "vout": unspent[0]["vout"]}, {"txid": unspent_asset[0]["txid"], "vout": unspent_asset[0]["vout"]}]

        # Create one part of the transaction to partially blind
        rawtx = self.nodes[0].createrawtransaction(
            inputs[:1], [{dst_addr2: Decimal("0.01")}])

        # Create another part of the transaction to partially blind
        rawtx2 = self.nodes[0].createrawtransaction(
            inputs[1:],
            [{dst_addr: Decimal("0.1"), "asset": unspent[0]["asset"]}, {dst_addr3: Decimal("1.0"), "asset": unspent_asset[0]["asset"]}],
            0,
            False)

        sum_i = unspent2[0]["amount"] + unspent[0]["amount"]
        sum_o = 0.01 + 0.10 + 0.1
        assert_equal(int(round(sum_i*COIN)), int(round(sum_o*COIN)))

        # Blind the first part of the transaction - we need to supply the
        # assetcommmitments for all of the inputs, for the surjectionproof
        # to be valid after we combine the transactions
        blindtx = self.nodes[1].blindrawtransaction(
            rawtx, True, [
                unspent2[0]['assetcommitment'],
                unspent[0]['assetcommitment'],
                unspent_asset[0]['assetcommitment']
            ])

        # Combine the transactions

        # Blinded, but incomplete transaction.
        # 1 inputs and 1 output, but no fee output, and
        # it was blinded with 3 asset commitments, that means
        # the final transaction should have 3 inputs.
        btx = CTransaction()
        btx.deserialize(io.BytesIO(hex_str_to_bytes(blindtx)))

        # Unblinded transaction, with 2 inputs and 2 outputs.
        # We will add them to the other transaction to make it complete.
        ubtx = CTransaction()
        ubtx.deserialize(io.BytesIO(hex_str_to_bytes(rawtx2)))

        # We will add outputs of unblinded transaction
        # on top of inputs and outputs of the blinded, but incomplete transaction.
        # We also append empty witness instances to make witness arrays match
        # vin/vout arrays
        btx.vin.append(ubtx.vin[0])
        btx.wit.vtxinwit.append(CTxInWitness())
        btx.vout.append(ubtx.vout[0])
        btx.wit.vtxoutwit.append(CTxOutWitness())
        btx.vin.append(ubtx.vin[1])
        btx.wit.vtxinwit.append(CTxInWitness())
        btx.vout.append(ubtx.vout[1])
        btx.wit.vtxoutwit.append(CTxOutWitness())
        # Add explicit fee output
        btx.vout.append(CTxOut(nValue=CTxOutValue(10000000),
                               nAsset=CTxOutAsset(BITCOIN_ASSET_OUT)))
        btx.wit.vtxoutwit.append(CTxOutWitness())

        # Input 0 is bitcoin asset (already blinded)
        # Input 1 is also bitcoin asset
        # Input 2 is our new asset

        # Blind with wrong order of assetcommitments - such transaction should be rejected
        blindtx = self.nodes[0].blindrawtransaction(
            btx.serialize().hex(), True, [
                unspent_asset[0]['assetcommitment'],
                unspent[0]['assetcommitment'],
                unspent2[0]['assetcommitment']
            ])

        stx2 = self.nodes[1].signrawtransactionwithwallet(blindtx)
        stx = self.nodes[0].signrawtransactionwithwallet(stx2['hex'])
        self.sync_all()

        assert_raises_rpc_error(-26, "bad-txns-in-ne-out", self.nodes[2].sendrawtransaction, stx['hex'])

        # Blind with correct order of assetcommitments
        blindtx = self.nodes[0].blindrawtransaction(
            btx.serialize().hex(), True, [
                unspent2[0]['assetcommitment'],
                unspent[0]['assetcommitment'],
                unspent_asset[0]['assetcommitment']
            ])

        stx2 = self.nodes[1].signrawtransactionwithwallet(blindtx)
        stx = self.nodes[0].signrawtransactionwithwallet(stx2['hex'])
        txid = self.nodes[2].sendrawtransaction(stx['hex'])
        self.nodes[2].generate(1)
        assert self.nodes[2].gettransaction(txid)['confirmations'] == 1
        self.sync_all()

        # Check that the sent asset has reached its destination
        unconfidential_dst_addr3 = self.nodes[2].validateaddress(dst_addr3)["unconfidential"]
        unspent_asset2 = self.nodes[2].listunspent(1, 1, [unconfidential_dst_addr3], True, {"asset":issued3['asset']})
        assert_equal(len(unspent_asset2), 1)
        assert_equal(unspent_asset2[0]['amount'], Decimal(1))
        # And that the balance was correctly updated
        assert_equal(self.nodes[2].getbalance()[issued3['asset']], Decimal(1))

        # Basic checks of rawblindrawtransaction functionality
        blinded_addr = self.nodes[0].getnewaddress()
        addr = self.nodes[0].validateaddress(blinded_addr)["unconfidential"]
        self.nodes[0].sendtoaddress(blinded_addr, 1)
        self.nodes[0].sendtoaddress(blinded_addr, 3)
        unspent = self.nodes[0].listunspent(0, 0)
        rawtx = self.nodes[0].createrawtransaction(
                [
                    {"txid":unspent[0]["txid"], "vout":unspent[0]["vout"]},
                    {"txid":unspent[1]["txid"], "vout":unspent[1]["vout"]}
                ],
                [
                    {addr:unspent[0]["amount"]+unspent[1]["amount"]-Decimal("0.2")},
                    {"fee":Decimal("0.2")}
                ])
        # Blinding will fail with 2 blinded inputs and 0 blinded outputs
        # since it has no notion of a wallet to fill in a 0-value OP_RETURN output
        try:
            self.nodes[0].rawblindrawtransaction(rawtx, [unspent[0]["amountblinder"], unspent[1]["amountblinder"]], [unspent[0]["amount"], unspent[1]["amount"]], [unspent[0]["asset"], unspent[1]["asset"]], [unspent[0]["assetblinder"], unspent[1]["assetblinder"]])
            raise AssertionError("Shouldn't be able to blind 2 input 0 output transaction via rawblindraw")
        except JSONRPCException:
            pass

        # Blinded destination added, can blind, sign and send
        rawtx = self.nodes[0].createrawtransaction(
                [
                    {"txid":unspent[0]["txid"], "vout":unspent[0]["vout"]},
                    {"txid":unspent[1]["txid"], "vout":unspent[1]["vout"]}
                ],
                [
                    {blinded_addr:unspent[0]["amount"]+unspent[1]["amount"]-Decimal("0.002")},
                    {"fee":Decimal("0.002")}
                ])
        signtx = self.nodes[0].signrawtransactionwithwallet(rawtx)

        try:
            self.nodes[0].sendrawtransaction(signtx["hex"])
            raise AssertionError("Shouldn't be able to send unblinded tx with emplaced pubkey in output without additional argument")
        except JSONRPCException:
            pass

        # Make sure RPC throws when an invalid blinding factor is provided.
        bad_blinder = 'FF'*32
        assert_raises_rpc_error(-8, "Unable to blind transaction: Are you sure each asset type to blind is represented in the inputs?", self.nodes[0].rawblindrawtransaction, rawtx, [unspent[0]["amountblinder"], bad_blinder], [unspent[0]["amount"], unspent[1]["amount"]], [unspent[0]["asset"], unspent[1]["asset"]], [unspent[0]["assetblinder"], unspent[1]["assetblinder"]])
        assert_raises_rpc_error(-8, "Unable to blind transaction: Are you sure each asset type to blind is represented in the inputs?", self.nodes[0].rawblindrawtransaction, rawtx, [unspent[0]["amountblinder"], unspent[1]["amountblinder"]], [unspent[0]["amount"], unspent[1]["amount"]], [unspent[0]["asset"], unspent[1]["asset"]], [unspent[0]["assetblinder"], bad_blinder])

        blindtx = self.nodes[0].rawblindrawtransaction(rawtx, [unspent[0]["amountblinder"], unspent[1]["amountblinder"]], [unspent[0]["amount"], unspent[1]["amount"]], [unspent[0]["asset"], unspent[1]["asset"]], [unspent[0]["assetblinder"], unspent[1]["assetblinder"]])
        signtx = self.nodes[0].signrawtransactionwithwallet(blindtx)
        txid = self.nodes[0].sendrawtransaction(signtx["hex"])
        for output in self.nodes[0].decoderawtransaction(blindtx)["vout"]:
            if "asset" in output and output["scriptPubKey"]["type"] != "fee":
                raise AssertionError("An unblinded output exists")

        # Test fundrawtransaction with multiple assets
        issue = self.nodes[0].issueasset(1, 0)
        assetaddr = self.nodes[0].getnewaddress()
        rawtx = self.nodes[0].createrawtransaction([], [{assetaddr:1, "asset": issue["asset"]}, {self.nodes[0].getnewaddress():2}], 0, False)
        funded = self.nodes[0].fundrawtransaction(rawtx)
        blinded = self.nodes[0].blindrawtransaction(funded["hex"])
        signed = self.nodes[0].signrawtransactionwithwallet(blinded)
        txid = self.nodes[0].sendrawtransaction(signed["hex"])

        # Test fundrawtransaction with multiple inputs, creating > vout.size change
        rawtx = self.nodes[0].createrawtransaction([{"txid":txid, "vout":0}, {"txid":txid, "vout":1}], [{self.nodes[0].getnewaddress():5}])
        funded = self.nodes[0].fundrawtransaction(rawtx)
        blinded = self.nodes[0].blindrawtransaction(funded["hex"])
        signed = self.nodes[0].signrawtransactionwithwallet(blinded)
        txid = self.nodes[0].sendrawtransaction(signed["hex"])

        # Test corner case where wallet appends a OP_RETURN output, yet doesn't blind it
        # due to the fact that the output value is 0-value and input pedersen commitments
        # self-balance. This is rare corner case, but ok.
        unblinded = self.nodes[0].validateaddress(self.nodes[0].getnewaddress())["unconfidential"]
        self.nodes[0].sendtoaddress(unblinded, self.nodes[0].getbalance()["bitcoin"], "", "", True)
        # Make tx with blinded destination and change outputs only
        self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), self.nodes[0].getbalance()["bitcoin"]/2)
        # Send back again, this transaction should have 3 outputs, all unblinded
        txid = self.nodes[0].sendtoaddress(unblinded, self.nodes[0].getbalance()["bitcoin"], "", "", True)
        outputs = self.nodes[0].getrawtransaction(txid, 1)["vout"]
        assert_equal(len(outputs), 3)
        assert "value" in outputs[0] and "value" in outputs[1] and "value" in outputs[2]
        assert_equal(outputs[2]["scriptPubKey"]["type"], 'nulldata')

        # Test burn argument in createrawtransaction
        raw_burn1 = self.nodes[0].createrawtransaction([], [{self.nodes[0].getnewaddress():1}, {"burn":2}])
        decode_burn1 = self.nodes[0].decoderawtransaction(raw_burn1)
        assert_equal(len(decode_burn1["vout"]), 2)
        found_pay = False
        found_burn = False
        for output in decode_burn1["vout"]:
            if output["scriptPubKey"]["asm"] == "OP_RETURN":
                found_burn = True
                if output["asset"] != self.nodes[0].dumpassetlabels()["bitcoin"]:
                    raise Exception("Burn should have been bitcoin(policyAsset)")
            if output["scriptPubKey"]["type"] == "witness_v0_keyhash":
                found_pay = True
        assert found_pay and found_burn

        raw_burn2 = self.nodes[0].createrawtransaction([], [{self.nodes[0].getnewaddress():1}, {"burn":2, "asset": "deadbeef"*8}], 101, False)
        decode_burn2 = self.nodes[0].decoderawtransaction(raw_burn2)
        assert_equal(len(decode_burn2["vout"]), 2)
        found_pay = False
        found_burn = False
        for output in decode_burn2["vout"]:
            if output["scriptPubKey"]["asm"] == "OP_RETURN":
                found_burn = True
                if output["asset"] != "deadbeef"*8:
                    raise Exception("Burn should have been deadbeef")
            if output["scriptPubKey"]["type"] == "witness_v0_keyhash":
                found_pay = True
        assert found_pay and found_burn

        # TODO: signrawtransactionwith{wallet, key} with confidential segwit input given as previous transaction arg

if __name__ == '__main__':
    CTTest ().main ()
