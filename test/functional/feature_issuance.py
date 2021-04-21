#!/usr/bin/env python3
# Copyright (c) 2016 The Bitcoin Core developers
# Distributed under the MIT/X11 software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal, assert_greater_than_or_equal, assert_raises_rpc_error
from test_framework.authproxy import JSONRPCException
from decimal import Decimal

" Tests issued assets functionality including (re)issuance, and de-issuance "

# Creates a raw issuance transaction based on the passed in list, checking important details after
def process_raw_issuance(node, issuance_list):
    if len(issuance_list) > 5:
        raise Exception('Issuance list too long')
    # Make enough outputs for any subsequent spend
    next_destinations = []
    output_values = Decimal('%.8f' % ((node.getbalance()['bitcoin']-1)/5))
    for i in range(5):
        next_destinations.append({node.getnewaddress(): output_values})

    raw_tx = node.createrawtransaction([], next_destinations)
    # We "over-fund" these transactions to 50 sat/vbyte since issuances aren't baked in yet
    # Otherwise huge multi-issuances may fail min-relay
    funded_tx = node.fundrawtransaction(raw_tx, {"feeRate":Decimal('0.00050000')})['hex']
    issued_call_details = node.rawissueasset(funded_tx, issuance_list)
    issued_tx = issued_call_details[-1]["hex"] # Get hex from end
    # don't accept blinding fail, and blind all issuances or none at all
    blind_tx = node.blindrawtransaction(issued_tx, False, [], issuance_list[0]["blind"])
    signed_tx = node.signrawtransactionwithwallet(blind_tx)
    tx_id = node.sendrawtransaction(signed_tx['hex'])
    node.generate(1)
    assert_equal(node.gettransaction(tx_id)["confirmations"], 1)
    num_issuance = 0
    decoded_tx = node.decoderawtransaction(signed_tx['hex'])
    decoded_unblind_tx = node.decoderawtransaction(issued_tx)
    for i, (issuance_req, tx_input, issuance_result) in enumerate(zip(issuance_list, decoded_tx["vin"], issued_call_details)):
        if "issuance" not in tx_input:
            break

        num_issuance += 1
        issuance_details = tx_input["issuance"]
        if "blind" not in issuance_req or issuance_req["blind"] == True:

            assert "assetamount" not in issuance_details
            assert "tokenamount" not in issuance_details
            assert_equal(issuance_details["assetBlindingNonce"], "00"*32)
            if "asset_amount" in issuance_req:
                assert "assetamountcommitment" in issuance_details
            if "token_amount" in issuance_req:
                assert "tokenamountcommitment" in issuance_details
        else:
            if "asset_amount" in issuance_req:
                assert_equal(issuance_details["assetamount"], issuance_req["asset_amount"])
            if "token_amount" in issuance_req:
                assert_equal(issuance_details["tokenamount"], issuance_req["token_amount"])

        # Cross-check RPC call result details with raw details
        assert_equal(issuance_result["vin"], i)
        assert_equal(issuance_result["entropy"], issuance_details["assetEntropy"])
        if "asset" in issuance_details:
            assert_equal(issuance_result["asset"], issuance_details["asset"])
        if "token" in issuance_details:
            assert_equal(issuance_result["token"], issuance_details["token"])

        # Look for outputs assets where we expect them, or not, initial issuance first then token
        for issuance_type in ["asset", "token"]:
            blind_dest = issuance_type+"_address" not in issuance_req or node.validateaddress(issuance_req[issuance_type+"_address"])["confidential_key"] != ""
            if blind_dest:
                # We should not find any the issuances we made since the addresses confidential
                for output in decoded_tx["vout"]:
                    if "asset" in output and output["asset"] == issuance_details[issuance_type]:
                        raise Exception("Found asset in plaintext that should be confidential!")

            # Now scan unblinded version of issuance outputs
            asset_found = False
            for output in decoded_unblind_tx["vout"]:
                if "asset" in output and output["asset"] == issuance_details[issuance_type]:
                    if issuance_type+"_address" not in issuance_req:
                        raise Exception("Found asset type not requested")
                    if "value" in output and output["value"] == issuance_req[issuance_type+"_amount"]:
                        asset_found = True

            # Find the asset type if it was created
            assert asset_found if issuance_type+"_address" in issuance_req else True

    assert_equal(num_issuance, len(issuance_list))

class IssuanceTest(BitcoinTestFramework):

    def set_test_params(self):
        self.num_nodes = 3
        self.extra_args = [["-blindedaddresses=1"]] * self.num_nodes
        self.setup_clean_chain = True

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def setup_network(self, split=False):
        self.setup_nodes()
        self.connect_nodes(0, 1)
        self.connect_nodes(1, 0) ## ELEMENTS: investigate why we need this connection
        self.connect_nodes(1, 2)
        self.sync_all()

    def run_test(self):
        self.nodes[0].generate(105)
        # Make sure test starts with no initial issuance.
        assert_equal(len(self.nodes[0].listissuances()), 0)

        # Unblinded issuance of asset
        issued = self.nodes[0].issueasset(1, 1, False)
        balance = self.nodes[0].getwalletinfo()["balance"]
        assert_equal(balance[issued["asset"]], 1)
        assert_equal(balance[issued["token"]], 1)
        # Quick unblinded reissuance check, making 2*COIN total
        self.nodes[0].reissueasset(issued["asset"], 1)

        self.nodes[0].generate(1)
        self.sync_all()

        issued2 = self.nodes[0].issueasset(2, 1)
        test_asset = issued2["asset"]
        assert_equal(self.nodes[0].getwalletinfo()['balance'][test_asset], Decimal(2))
        node1balance = self.nodes[1].getwalletinfo()['balance']
        if test_asset in node1balance:
            assert_equal(node1balance[test_asset], Decimal(0))

        # Send bitcoin to node 1 and then from 1 to 2 to force node 1 to
        # spend confidential money.
        self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 4)
        self.nodes[0].generate(1)
        self.sync_all()
        self.nodes[1].sendtoaddress(self.nodes[2].getnewaddress(), 3, "", "", False, False, 1, "UNSET", False, "", False)
        self.sync_all()
        self.nodes[0].generate(1)
        self.sync_all()

        # Destroy assets
        pre_destroy_btc_balance = self.nodes[2].getwalletinfo()['balance']['bitcoin']
        self.nodes[2].destroyamount('bitcoin', 2) # Destroy 2 BTC
        self.nodes[2].generate(1)
        self.sync_all()
        assert_greater_than_or_equal(pre_destroy_btc_balance - Decimal('2'), self.nodes[2].getbalance()['bitcoin'])

        issuedamount = self.nodes[0].getwalletinfo()['balance'][issued["token"]]
        assert_equal(issuedamount, Decimal('1.0'))
        self.nodes[0].destroyamount(issued["token"], issuedamount) # Destroy all reissuance tokens of one type

        self.nodes[0].generate(1)
        self.sync_all()
        assert issued["token"] not in self.nodes[0].getwalletinfo()['balance']

        # Test various issuance and auditing paths

        issuancedata = self.nodes[0].issueasset(Decimal('0.00000002'), Decimal('0.00000001')) #2 of asset, 1 reissuance token
        self.nodes[1].generate(1)
        self.sync_all()
        assert_equal(self.nodes[0].getwalletinfo()["balance"][issuancedata["asset"]], Decimal('0.00000002'))
        assert_equal(self.nodes[0].getwalletinfo()["balance"][issuancedata["token"]], Decimal('0.00000001'))
        self.nodes[0].reissueasset(issuancedata["asset"], Decimal('0.00000001'))
        self.sync_all()
        assert_equal(self.nodes[0].getwalletinfo()["balance"][issuancedata["asset"]], Decimal('0.00000003'))
        # Can't reissue an issuance token (yet)
        try:
            self.nodes[0].reissueasset(issuancedata["token"], Decimal('0.00000001'))
            raise AssertionError("You shouldn't be able to reissue a token yet")
        except JSONRPCException:
            pass


        issuancedata = self.nodes[2].issueasset(Decimal('0.00000005'), 0) #5 of asset, 0 reissuance token
        # No reissuance tokens
        try:
            self.nodes[2].reissueasset(issuancedata["token"], 5)
            raise AssertionError("You shouldn't be able to reissue without a token")
        except JSONRPCException:
            pass

        issuancedata = self.nodes[2].issueasset(0, Decimal('0.00000006')) #0 of asset, 6 reissuance token

        # Node 2 will send node 1 a reissuance token, both will generate assets
        self.nodes[2].sendtoaddress(self.nodes[1].getnewaddress(), Decimal('0.00000001'), "", "", False, False, 1, "UNSET", False, issuancedata["token"])
        # node 1 needs to know about a (re)issuance to reissue itself
        self.nodes[1].importaddress(self.nodes[2].gettransaction(issuancedata["txid"])["details"][0]["address"])
        # also send some bitcoin
        self.nodes[2].generate(1)
        self.sync_all()

        assert_equal(self.nodes[2].getwalletinfo()["balance"][issuancedata["token"]], Decimal('0.00000005'))
        assert_equal(self.nodes[1].getwalletinfo()["balance"][issuancedata["token"]], Decimal('0.00000001'))
        redata1 = self.nodes[1].reissueasset(issuancedata["asset"], Decimal('0.05'))
        redata2 = self.nodes[2].reissueasset(issuancedata["asset"], Decimal('0.025'))

        self.sync_all()
        # Watch-only issuances won't show up in wallet until confirmed
        self.nodes[1].generate(1)
        self.sync_all()

        # Now have node 0 audit these issuances
        blindingkey1 = self.nodes[1].dumpissuanceblindingkey(redata1["txid"], redata1["vin"])
        blindingkey2 = self.nodes[2].dumpissuanceblindingkey(redata2["txid"], redata2["vin"])
        blindingkey3 = self.nodes[2].dumpissuanceblindingkey(issuancedata["txid"], issuancedata["vin"])

        # Need addr to get transactions in wallet. TODO: importissuances?
        txdet1 = self.nodes[1].gettransaction(redata1["txid"])["details"]
        txdet2 = self.nodes[2].gettransaction(redata2["txid"])["details"]
        txdet3 = self.nodes[2].gettransaction(issuancedata["txid"])["details"]

        # Receive addresses added last
        addr1 = txdet1[len(txdet1)-1]["address"]
        addr2 = txdet2[len(txdet2)-1]["address"]
        addr3 = txdet3[len(txdet3)-1]["address"]

        assert_equal(len(self.nodes[0].listissuances()), 5)
        self.nodes[0].importaddress(addr1)
        self.nodes[0].importaddress(addr2)
        self.nodes[0].importaddress(addr3)

        issuances = self.nodes[0].listissuances()
        assert_equal(len(issuances), 8)

        for issue in issuances:
            if issue['txid'] == redata1["txid"] and issue['vin'] == redata1["vin"]:
                assert_equal(issue['assetamount'], Decimal('-1'))
            if issue['txid'] == redata2["txid"] and issue['vin'] == redata2["vin"]:
                assert_equal(issue['assetamount'], Decimal('-1'))
            if issue['txid'] == issuancedata["txid"] and issue['vin'] == issuancedata["vin"]:
                assert_equal(issue['assetamount'], Decimal('-1'))
                assert_equal(issue['tokenamount'], Decimal('-1'))

        # Test that importing the issuance blinding keys then reveals the issuance amounts
        self.nodes[0].importissuanceblindingkey(redata1["txid"], redata1["vin"], blindingkey1)
        self.nodes[0].importissuanceblindingkey(redata2["txid"], redata2["vin"], blindingkey2)
        self.nodes[0].importissuanceblindingkey(issuancedata["txid"], issuancedata["vin"], blindingkey3)

        issuances = self.nodes[0].listissuances()

        for issue in issuances:
            if issue['txid'] == redata1["txid"] and issue['vin'] == redata1["vin"]:
                assert_equal(issue['assetamount'], Decimal('0.05'))
            if issue['txid'] == redata2["txid"] and issue['vin'] == redata2["vin"]:
                assert_equal(issue['assetamount'], Decimal('0.025'))
            if issue['txid'] == issuancedata["txid"] and issue['vin'] == issuancedata["vin"]:
                assert_equal(issue['assetamount'], Decimal('0'))
                assert_equal(issue['tokenamount'], Decimal('0.00000006'))

        # Check for value accounting when asset issuance is null but token not, ie unblinded
        issued = self.nodes[0].issueasset(0, 1, False)
        assert issued["asset"] not in self.nodes[0].getwalletinfo()["balance"]
        assert_equal(self.nodes[0].getwalletinfo()["balance"][issued["token"]], 1)


        print("Raw issuance tests")
        # Addresses to send to to check proper blinding
        blind_addr = self.nodes[0].getnewaddress()
        nonblind_addr = self.nodes[0].validateaddress(blind_addr)['unconfidential']

        # Fail making non-witness issuance sourcing a single unblinded output.
        # See: https://github.com/ElementsProject/elements/issues/473
        total_amount = self.nodes[0].getbalance()['bitcoin']
        self.nodes[0].sendtoaddress(nonblind_addr, total_amount, "", "", True)
        self.nodes[1].generate(1)
        raw_tx = self.nodes[0].createrawtransaction([], [{nonblind_addr: 1}])
        funded_tx = self.nodes[0].fundrawtransaction(raw_tx)['hex']
        issued_tx = self.nodes[2].rawissueasset(funded_tx, [{"asset_amount":1, "asset_address":nonblind_addr, "blind":False}])[0]["hex"]
        blind_tx = self.nodes[0].blindrawtransaction(issued_tx) # This is a no-op
        signed_tx = self.nodes[0].signrawtransactionwithwallet(blind_tx)
        assert_raises_rpc_error(-26, "", self.nodes[0].sendrawtransaction, signed_tx['hex'])

        # Make single blinded output to ensure we work around above issue
        total_amount = self.nodes[0].getbalance()['bitcoin']
        self.nodes[0].sendtoaddress(blind_addr, total_amount, "", "", True)
        self.nodes[1].generate(1)

        # Start with single issuance input, unblinded (makes 5 outputs for later larger issuances)
        process_raw_issuance(self.nodes[0], [{"asset_amount": 2, "asset_address": nonblind_addr, "blind": False}])
        process_raw_issuance(self.nodes[0], [{"asset_amount": 2, "asset_address": nonblind_addr, "blind": True}])
        process_raw_issuance(self.nodes[0], [{"token_amount": 5, "token_address": nonblind_addr, "blind": False}])
        process_raw_issuance(self.nodes[0], [{"asset_amount": 7, "asset_address": nonblind_addr, "token_amount":2, "token_address":nonblind_addr, "blind":False}])
        process_raw_issuance(self.nodes[0], [{"asset_amount": 7, "asset_address": nonblind_addr, "token_amount":2, "token_address":blind_addr, "blind":False}])
        process_raw_issuance(self.nodes[0], [{"asset_amount": 7, "asset_address": blind_addr, "token_amount":2, "token_address":nonblind_addr, "blind":False}])
        process_raw_issuance(self.nodes[0], [{"asset_amount": 7, "asset_address": blind_addr, "token_amount":2, "token_address":blind_addr, "blind":False}])
        # Now do multiple with some issuance outputs blind, some unblinded
        process_raw_issuance(self.nodes[0], [{"asset_amount": 7, "asset_address": nonblind_addr, "token_amount":2, "token_address":nonblind_addr, "blind":False}, {"asset_amount":2, "asset_address":nonblind_addr, "blind":False}])
        process_raw_issuance(self.nodes[0], [{"asset_amount": 7, "asset_address": blind_addr, "token_amount":2, "token_address":nonblind_addr, "blind":False}, {"asset_amount":2, "asset_address":nonblind_addr, "blind":False}])
        # Up to 5 issuances since we're making 5 outputs each time
        process_raw_issuance(self.nodes[0], [{"asset_amount": 7, "asset_address": nonblind_addr, "token_amount":2, "token_address":blind_addr, "blind":False}, {"asset_amount":2, "asset_address":nonblind_addr, "blind":False}])
        process_raw_issuance(self.nodes[0], [{"asset_amount": 1, "asset_address": nonblind_addr, "token_amount":2, "token_address":blind_addr, "blind":False}, {"asset_amount":3, "asset_address":nonblind_addr, "blind":False}, {"asset_amount":4, "asset_address":nonblind_addr, "token_amount":5, "token_address":blind_addr, "blind":False}, {"asset_amount":6, "asset_address":nonblind_addr, "token_amount":7, "token_address":blind_addr, "blind":False}, {"asset_amount":8, "asset_address":nonblind_addr, "token_amount":9, "token_address":blind_addr, "blind":False}])
        # Default "blind" value is true, omitting explicit argument for last
        process_raw_issuance(self.nodes[0], [{"asset_amount": 1, "asset_address": nonblind_addr, "token_amount":2, "token_address":blind_addr, "blind":True}, {"asset_amount":3, "asset_address":nonblind_addr, "blind":True}, {"asset_amount":4, "asset_address":nonblind_addr, "token_amount":5, "token_address":blind_addr, "blind":True}, {"asset_amount":6, "asset_address":nonblind_addr, "token_amount":7, "token_address":blind_addr, "blind":True}, {"asset_amount":8, "asset_address":nonblind_addr, "token_amount":9, "token_address":blind_addr}])


        # Make sure that fee is checked
        valid_addr = self.nodes[0].getnewaddress()
        raw_tx = self.nodes[0].createrawtransaction([], [])
        assert_raises_rpc_error(-8, "Transaction must have at least one output.",
                self.nodes[0].rawissueasset, raw_tx, [{"asset_amount": 1, "asset_address": valid_addr}])
        raw_tx = self.nodes[0].createrawtransaction([], [{valid_addr: Decimal("1")}])
        assert_raises_rpc_error(-8, "Last transaction output must be fee.",
                self.nodes[0].rawissueasset, raw_tx, [{"asset_amount": 1, "asset_address": valid_addr}])

        # Make sure that invalid addresses are rejected.
        valid_addr = self.nodes[0].getnewaddress()
        raw_tx = self.nodes[0].createrawtransaction([], [{valid_addr: Decimal("1")}])
        funded_tx = self.nodes[0].fundrawtransaction(raw_tx, {"feeRate": Decimal('0.00050000')})['hex']
        assert_raises_rpc_error(-8, "Invalid asset address provided: foobar",
                self.nodes[0].rawissueasset, funded_tx, [{"asset_amount": 1, "asset_address": "foobar"}])
        assert_raises_rpc_error(-8, "Invalid token address provided: foobar",
                self.nodes[0].rawissueasset, funded_tx, [{"token_amount": 1, "token_address": "foobar"}])
        # Also test for missing value.
        assert_raises_rpc_error(-8, "Invalid parameter, missing corresponding asset_address",
                self.nodes[0].rawissueasset, funded_tx, [{"asset_amount": 1, "token_address": valid_addr}])
        assert_raises_rpc_error(-8, "Invalid parameter, missing corresponding token_address",
                self.nodes[0].rawissueasset, funded_tx, [{"token_amount": 1, "asset_address": valid_addr}])

        # Make sure contract hash is being interpreted as expected, resulting in different asset ids
        raw_tx = self.nodes[0].createrawtransaction([], [{nonblind_addr:self.nodes[0].getbalance()['bitcoin']-1}])
        funded_tx = self.nodes[0].fundrawtransaction(raw_tx)['hex']
        id_set = set()

        # First issue an asset with no argument
        issued_tx = self.nodes[2].rawissueasset(funded_tx, [{"asset_amount":1, "asset_address":nonblind_addr}])[0]["hex"]
        decode_tx = self.nodes[0].decoderawtransaction(issued_tx)
        id_set.add(decode_tx["vin"][0]["issuance"]["asset"])
        calc_asset = self.nodes[0].calculateasset(decode_tx["vin"][0]["txid"], decode_tx["vin"][0]["vout"])
        assert_equal(calc_asset["final_asset_entropy"], decode_tx["vin"][0]["issuance"]["assetEntropy"])
        assert_equal(calc_asset["asset_tag"], decode_tx["vin"][0]["issuance"]["asset"])

        # Again with 00..00 argument, which match the no-argument case
        issued_tx = self.nodes[2].rawissueasset(funded_tx, [{"asset_amount":1, "asset_address":nonblind_addr, "contract_hash":"00"*32}])[0]["hex"]
        decode_tx = self.nodes[0].decoderawtransaction(issued_tx)
        id_set.add(decode_tx["vin"][0]["issuance"]["asset"])
        assert_equal(len(id_set), 1)
        calc_asset = self.nodes[0].calculateasset(decode_tx["vin"][0]["txid"], decode_tx["vin"][0]["vout"], "00"*32)
        assert_equal(calc_asset["final_asset_entropy"], decode_tx["vin"][0]["issuance"]["assetEntropy"])
        assert_equal(calc_asset["asset_tag"], decode_tx["vin"][0]["issuance"]["asset"])

        # Random contract string should again differ
        issued_tx = self.nodes[2].rawissueasset(funded_tx, [{"asset_amount":1, "asset_address":nonblind_addr, "contract_hash":"deadbeef"*8}])[0]["hex"]
        decode_tx = self.nodes[0].decoderawtransaction(issued_tx)
        id_set.add(decode_tx["vin"][0]["issuance"]["asset"])
        assert_equal(len(id_set), 2)
        calc_asset = self.nodes[0].calculateasset(decode_tx["vin"][0]["txid"], decode_tx["vin"][0]["vout"], "deadbeef"*8)
        assert_equal(calc_asset["final_asset_entropy"], decode_tx["vin"][0]["issuance"]["assetEntropy"])
        assert_equal(calc_asset["asset_tag"], decode_tx["vin"][0]["issuance"]["asset"])
        issued_tx = self.nodes[2].rawissueasset(funded_tx, [{"asset_amount":1, "asset_address":nonblind_addr, "contract_hash":"deadbeee"*8}])[0]["hex"]
        decode_tx = self.nodes[0].decoderawtransaction(issued_tx)
        id_set.add(decode_tx["vin"][0]["issuance"]["asset"])
        assert_equal(len(id_set), 3)
        calc_asset = self.nodes[0].calculateasset(decode_tx["vin"][0]["txid"], decode_tx["vin"][0]["vout"], "deadbeee"*8)
        assert_equal(calc_asset["final_asset_entropy"], decode_tx["vin"][0]["issuance"]["assetEntropy"])
        assert_equal(calc_asset["asset_tag"], decode_tx["vin"][0]["issuance"]["asset"])

        # Finally, append an issuance on top of an already-"issued" raw tx
        # Same contract, different utxo being spent results in new asset type
        # We also create a reissuance token to test reissuance with contract hash
        issued_tx = self.nodes[2].rawissueasset(issued_tx, [{"asset_amount":1, "asset_address":nonblind_addr, "token_address":nonblind_addr, "contract":"deadbeee"*8}])[0]["hex"]
        decode_tx = self.nodes[0].decoderawtransaction(issued_tx)
        id_set.add(decode_tx["vin"][1]["issuance"]["asset"])
        assert_equal(len(id_set), 4)
        calc_asset = self.nodes[0].calculateasset(decode_tx["vin"][1]["txid"], decode_tx["vin"][1]["vout"], None, False)
        assert_equal(calc_asset["final_asset_entropy"], decode_tx["vin"][1]["issuance"]["assetEntropy"])
        assert_equal(calc_asset["asset_tag"], decode_tx["vin"][1]["issuance"]["asset"])
        assert_equal(calc_asset["reissuance_asset_tag"], decode_tx["vin"][1]["issuance"]["token"])
        # This issuance should not have changed
        id_set.add(decode_tx["vin"][0]["issuance"]["asset"])
        assert_equal(len(id_set), 4)

        print("Raw reissuance tests")
        issued_asset = self.nodes[0].issueasset(0, 1)
        self.nodes[0].generate(1)
        utxo_info = None
        # Find info about the token output using wallet
        for utxo in self.nodes[0].listunspent():
            if utxo["asset"] == issued_asset["token"]:
                utxo_info = utxo
                break
        assert utxo_info is not None

        issued_address = self.nodes[0].getnewaddress()
        # Create transaction spending the reissuance token
        raw_tx = self.nodes[0].createrawtransaction([], [{issued_address:Decimal('0.00000001'), "asset": issued_asset["token"]}], 0, False)
        funded_tx = self.nodes[0].fundrawtransaction(raw_tx)['hex']
        # Find the reissuance input
        reissuance_index = -1
        for i, tx_input in enumerate(self.nodes[0].decoderawtransaction(funded_tx)["vin"]):
            if tx_input["txid"] == utxo_info["txid"] and tx_input["vout"] == utxo_info["vout"]:
                reissuance_index = i
                break
        assert reissuance_index != -1
        reissued_tx = self.nodes[0].rawreissueasset(funded_tx, [{"asset_amount":3, "asset_address":self.nodes[0].getnewaddress(), "input_index":reissuance_index, "asset_blinder":utxo_info["assetblinder"], "entropy":issued_asset["entropy"]}])
        blind_tx = self.nodes[0].blindrawtransaction(reissued_tx["hex"])
        signed_tx = self.nodes[0].signrawtransactionwithwallet(blind_tx)
        tx_id = self.nodes[0].sendrawtransaction(signed_tx["hex"])
        self.nodes[0].generate(1)
        assert_equal(self.nodes[0].gettransaction(tx_id)["confirmations"], 1)

        # Now send reissuance token to blinded multisig, then reissue
        addrs = []
        for i in range(3):
            addrs.append(self.nodes[0].getaddressinfo(self.nodes[0].getnewaddress())["pubkey"])


        multisig_addr = self.nodes[0].addmultisigaddress(2,addrs)
        blinded_addr = self.nodes[0].getnewaddress()
        blinding_pubkey = self.nodes[0].validateaddress(blinded_addr)["confidential_key"]
        blinding_privkey = self.nodes[0].dumpblindingkey(blinded_addr)
        blinded_multisig = self.nodes[0].createblindedaddress(multisig_addr["address"], blinding_pubkey)
        # Import blinding key to be able to decrypt values sent to it
        self.nodes[0].importblindingkey(blinded_multisig, blinding_privkey)
        # Sending to this address must achieve blinding to reissue from this address
        self.nodes[0].sendtoaddress(blinded_multisig, self.nodes[0].getbalance()[issued_asset["token"]], "", "", False, False, 1, "UNSET", False, issued_asset["token"], False)
        self.nodes[0].generate(1)

        # Get that multisig output
        utxo_info = None
        # Find info about the token output using wallet
        for utxo in self.nodes[0].listunspent():
            if utxo["asset"] == issued_asset["token"]:
                utxo_info = utxo
                assert_equal(blinded_multisig, self.nodes[0].getaddressinfo(utxo_info["address"])["confidential"])
                break
        assert utxo_info is not None
        assert utxo_info["amountblinder"] != "0000000000000000000000000000000000000000000000000000000000000000"

        # Now make transaction spending that input
        raw_tx = self.nodes[0].createrawtransaction([], [{issued_address:1, "asset": issued_asset["token"]}], 0, False)
        funded_tx = self.nodes[0].fundrawtransaction(raw_tx)["hex"]
        # Find the reissuance input
        reissuance_index = -1
        for i, tx_input in enumerate(self.nodes[0].decoderawtransaction(funded_tx)["vin"]):
            if tx_input["txid"] == utxo_info["txid"] and tx_input["vout"] == utxo_info["vout"]:
                reissuance_index = i
                break
        assert reissuance_index != -1
        reissued_tx = self.nodes[0].rawreissueasset(funded_tx, [{"asset_amount":3, "asset_address":self.nodes[0].getnewaddress(), "input_index":reissuance_index, "asset_blinder":utxo_info["assetblinder"], "entropy":issued_asset["entropy"]}])

        blind_tx = self.nodes[0].blindrawtransaction(reissued_tx["hex"])
        signed_tx = self.nodes[0].signrawtransactionwithwallet(blind_tx)
        tx_id = self.nodes[0].sendrawtransaction(signed_tx["hex"])
        self.nodes[0].generate(1)
        assert_equal(self.nodes[0].gettransaction(tx_id)["confirmations"], 1)

        # Now make transaction spending a token that had non-null contract_hash
        contract_hash = "deadbeee"*8
        raw_tx = self.nodes[0].createrawtransaction([], [{self.nodes[0].getnewaddress():1}])
        funded_tx = self.nodes[0].fundrawtransaction(raw_tx)["hex"]
        issued_tx = self.nodes[0].rawissueasset(funded_tx, [{"token_amount":1, "token_address":self.nodes[0].getnewaddress(), "contract_hash":contract_hash}])[0]
        blinded_tx = self.nodes[0].blindrawtransaction(issued_tx["hex"])
        signed_tx = self.nodes[0].signrawtransactionwithwallet(blinded_tx)
        tx_id = self.nodes[0].sendrawtransaction(signed_tx["hex"])
        self.nodes[0].generate(1)
        assert_equal(self.nodes[0].gettransaction(tx_id)["confirmations"], 1)

        utxo_info = None
        # Find info about the token output using wallet
        for utxo in self.nodes[0].listunspent():
            if utxo["asset"] == issued_tx["token"]:
                utxo_info = utxo
                break
        assert utxo_info is not None

        # Now spend the token, and create reissuance
        raw_tx = self.nodes[0].createrawtransaction([], [{issued_address:1, "asset": issued_tx["token"]}], 0, False)
        funded_tx = self.nodes[0].fundrawtransaction(raw_tx)["hex"]
        # Find the reissuance input
        reissuance_index = -1
        for i, tx_input in enumerate(self.nodes[0].decoderawtransaction(funded_tx)["vin"]):
            if tx_input["txid"] == utxo_info["txid"] and tx_input["vout"] == utxo_info["vout"]:
                reissuance_index = i
                break
        assert reissuance_index != -1
        reissued_tx = self.nodes[0].rawreissueasset(funded_tx, [{"asset_amount":3, "asset_address":self.nodes[0].getnewaddress(), "input_index":reissuance_index, "asset_blinder":utxo_info["assetblinder"], "entropy":issued_tx["entropy"]}])

        blind_tx = self.nodes[0].blindrawtransaction(reissued_tx["hex"], False)
        signed_tx = self.nodes[0].signrawtransactionwithwallet(blind_tx)
        tx_id = self.nodes[0].sendrawtransaction(signed_tx["hex"])
        self.nodes[0].generate(1)
        assert_equal(self.nodes[0].gettransaction(tx_id)["confirmations"], 1)

if __name__ == '__main__':
    IssuanceTest ().main ()
