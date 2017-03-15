#!/usr/bin/env python3
# Copyright (c) 2016 The Bitcoin Core developers
# Distributed under the MIT/X11 software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

# Test the confidential transaction feature of the wallet.
# Does the following:
#   a) send coins to a unconfidential address
#   b) send coins to a confidential address
#   c) send coins to a unconfidential and confidential address
#      using the raw transaction interface
#   d) calls listreceivedbyaddress
#   e) checks the auditor functionality with importblindingkey
#       and listreceivedbyaddress
#   f) checks the behavior of blindrawtransaction in an edge case

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *

class CTTest (BitcoinTestFramework):

    def setup_chain(self):
        print("Initializing test directory "+self.options.tmpdir)
        initialize_chain_clean(self.options.tmpdir, 3)

    def setup_network(self, split=False):
        self.nodes = start_nodes(3, self.options.tmpdir)
        connect_nodes_bi(self.nodes,0,1)
        connect_nodes_bi(self.nodes,1,2)
        connect_nodes_bi(self.nodes,0,2)
        self.is_network_split=False
        self.sync_all()

    def run_test(self):
        print("Mining blocks...")
        self.nodes[0].generate(101)
        self.sync_all()
        #Running balances
        node0 = self.nodes[0].getbalance()["bitcoin"]
        node1 = 0
        node2 = 0

        self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), node0, "", "", True)
        self.nodes[0].generate(101)
        self.sync_all()
        assert_equal(self.nodes[0].getbalance()["bitcoin"], node0)
        assert_equal(self.nodes[1].getbalance("", 1, False, "bitcoin"), node1)
        assert_equal(self.nodes[2].getbalance("", 1, False, "bitcoin"), node2)

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
        assert_equal(self.nodes[1].getbalance("", 1, False, "bitcoin"), node1)
        assert_equal(self.nodes[2].getbalance()["bitcoin"], node2)

        # Send 5 BTC from 0 to a new address of 2 with the sendtoaddress call
        address = self.nodes[2].getnewaddress()
        unconfidential_address2 = self.nodes[2].validateaddress(address)["unconfidential"]
        value1 = 5
        confidential_tx_id = self.nodes[0].sendtoaddress(address, value1)
        self.nodes[0].generate(101)
        self.sync_all()

        node0 = node0 - value1
        node2 = node2 + value1

        assert_equal(self.nodes[0].getbalance()["bitcoin"], node0)
        assert_equal(self.nodes[1].getbalance("", 1, False, "bitcoin"), node1)
        assert_equal(self.nodes[2].getbalance()["bitcoin"], node2)

        # Send 7 BTC from 0 to the unconfidential address of 2 and 11 BTC to the
        # confidential address using the raw transaction interface
        change_address = self.nodes[0].getnewaddress()
        value2 = 7
        value3 = 11
        value23 = value2 + value3
        unspent = self.nodes[0].listunspent(1, 9999999, [], "bitcoin")
        unspent = [i for i in unspent if i['amount'] > value23]
        assert_equal(len(unspent), 1)
        fee = Decimal(0.0001)
        tx = self.nodes[0].createrawtransaction([{"txid": unspent[0]["txid"],
                                                  "vout": unspent[0]["vout"],
                                                  "nValue": unspent[0]["amount"]}],
                                                {unconfidential_address: value2, address: value3,
                                                change_address: unspent[0]["amount"] - value2 - value3 - fee})
        tx = self.nodes[0].blindrawtransaction(tx)
        tx_signed = self.nodes[0].signrawtransaction(tx)
        raw_tx_id = self.nodes[0].sendrawtransaction(tx_signed['hex'])
        self.nodes[0].generate(101)
        self.sync_all()

        node0 -= (value2 + value3)
        node2 += value2 + value3

        assert_equal(self.nodes[0].getbalance()["bitcoin"], node0)
        assert_equal(self.nodes[1].getbalance("", 1, False, "bitcoin"), node1)
        assert_equal(self.nodes[2].getbalance()["bitcoin"], node2)

        # Check 2's listreceivedbyaddress
        received_by_address = self.nodes[2].listreceivedbyaddress()
        validate_by_address = [(unconfidential_address2, value1 + value3), (unconfidential_address, value0 + value2)]
        assert_equal(sorted([(ele['address'], ele['amount']) for ele in received_by_address], key=lambda t: t[0]), 
                sorted(validate_by_address, key = lambda t: t[0]))

        # Give an auditor (node 1) a blinding key to allow her to look at
        # transaction values
        self.nodes[1].importaddress(address)
        received_by_address = self.nodes[1].listreceivedbyaddress(1, False, True)
        #Node sees nothing unless it understands the values
        assert_equal(len(received_by_address), 0)
        assert_equal(len(self.nodes[1].listunspent(1, 9999999, [], "bitcoin")), 0)

        # Import the blinding key
        blindingkey = self.nodes[2].dumpblindingkey(address)
        self.nodes[1].importblindingkey(address, blindingkey)
        # Check the auditor's gettransaction and listreceivedbyaddress
        # Needs rescan to update wallet txns
        assert_equal(self.nodes[1].gettransaction(confidential_tx_id, True)['amount']["bitcoin"], value1)
        assert_equal(self.nodes[1].gettransaction(raw_tx_id, True)['amount']["bitcoin"], value3)
        list_unspent = self.nodes[1].listunspent(1, 9999999, [], "bitcoin")
        assert_equal(list_unspent[0]['amount']+list_unspent[1]['amount'], value1+value3)
        received_by_address = self.nodes[1].listreceivedbyaddress(1, False, True)
        assert_equal(len(received_by_address), 1)
        assert_equal((received_by_address[0]['address'], received_by_address[0]['amount']),
                     (unconfidential_address2, value1 + value3))

        # Spending a single confidential output and sending it to a
        # unconfidential output is not possible with CT. Test the
        # correct behavior of blindrawtransaction.
        unspent = self.nodes[0].listunspent(1, 9999999, [], "bitcoin")
        unspent = [i for i in unspent if i['amount'] > value23]
        assert_equal(len(unspent), 1)
        tx = self.nodes[0].createrawtransaction([{"txid": unspent[0]["txid"],
                                                  "vout": unspent[0]["vout"],
                                                  "nValue": unspent[0]["amount"]}],
                                                  {unconfidential_address: unspent[0]["amount"] - fee});

        # Test that blindrawtransaction returns an exception
        try:
            tx = self.nodes[0].blindrawtransaction(tx)
            raise AssertionError("blindrawtransaction RPC should fail, but it doesn't")
        except JSONRPCException:
            pass

        # Create same transaction but with a change/dummy output.
        # It should pass the blinding step.
        value4 = 17
        change_address = self.nodes[0].getrawchangeaddress()
        tx = self.nodes[0].createrawtransaction([{"txid": unspent[0]["txid"],
                                                  "vout": unspent[0]["vout"],
                                                  "nValue": unspent[0]["amount"]}],
                                                  {unconfidential_address: value4,
                                                   change_address: unspent[0]["amount"] - value4 - fee});
        tx = self.nodes[0].blindrawtransaction(tx)

        tx_signed = self.nodes[0].signrawtransaction(tx)
        txid = self.nodes[0].sendrawtransaction(tx_signed['hex'])
        self.nodes[0].generate(101)
        self.sync_all()

        node0 -= value4
        node2 += value4
        assert_equal(self.nodes[0].getbalance()["bitcoin"], node0)
        assert_equal(self.nodes[1].getbalance("", 1, False, "bitcoin"), node1)
        assert_equal(self.nodes[2].getbalance()["bitcoin"], node2)
        
        # Testing wallet's ability to deblind its own outputs
        addr = self.nodes[0].getnewaddress()
        addr2 = self.nodes[0].getnewaddress()
        # We add two to-blind outputs, fundraw adds an already-blinded change output
        # If we only add one, the newly blinded will be 0-blinded because input = -output
        raw = self.nodes[0].createrawtransaction([], {addr:Decimal('1.1'), addr2:1})
        funded = self.nodes[0].fundrawtransaction(raw)
        blinded = self.nodes[0].blindrawtransaction(funded["hex"])
        # blind again to make sure we know output blinders
        blinded2 = self.nodes[0].blindrawtransaction(blinded)

        # Check createblindedaddress functionality
        blinded_addr = self.nodes[0].getnewaddress()
        validated_addr = self.nodes[0].validateaddress(blinded_addr)
        blinding_key = self.nodes[0].dumpblindingkey(blinded_addr)
        assert_equal(blinded_addr, self.nodes[1].createblindedaddress(validated_addr["unconfidential"], blinding_key))

        # If a blinding key is over-ridden by a newly imported one, funds may be unaccounted for
        new_addr = self.nodes[0].getnewaddress()
        new_validated = self.nodes[0].validateaddress(new_addr)
        self.nodes[2].sendtoaddress(new_addr, 1)
        diff_blind = self.nodes[1].createblindedaddress(new_validated["unconfidential"], blinding_key)
        self.sync_all()
        assert_equal(len(self.nodes[0].listunspent(0, 0, [new_validated["unconfidential"]])), 1)
        self.nodes[0].importblindingkey(diff_blind, blinding_key)
        # CT values for this wallet transaction  have been cached via importblindingkey
        # therefore result will be same even though we change blinding keys
        assert_equal(len(self.nodes[0].listunspent(0, 0, [new_validated["unconfidential"]])), 1)

        #### Confidential Assets Tests ####

        # Generate an asset, check wallet (This is is skeleton issuance API)
        testAssetHex = self.nodes[0].generateasset(2)
        self.nodes[0].addassetlabel(testAssetHex, "testasset")
        asset_list = self.nodes[0].dumpassetlabels()
        assert_equal(self.nodes[0].getwalletinfo("testasset")['balance'], Decimal(2))
        assert_equal(self.nodes[0].getwalletinfo(asset_list["testasset"])['balance'], Decimal(2))

        self.nodes[1].addassetlabel(asset_list["testasset"], "testasset2")
        assert_equal(self.nodes[1].getwalletinfo("testasset2")['balance'], Decimal(0))

        # Assets balance checking, note that accounts are completely ignored because
        # balance queries with accounts are horrifically broken upstream
        assert_equal(self.nodes[0].getbalance("*", 0, False, "bitcoin"), self.nodes[0].getbalance("accountsareignored", 0, False, "bitcoin"))
        assert_equal(self.nodes[0].getwalletinfo()['balance']['bitcoin'], self.nodes[0].getbalance("accountsareignored", 0, False, "bitcoin"))

        # Now test wallet interaction with unlabeled funds
        wallet_list = self.nodes[0].getinfo()['balance'] # returns list of known non-zero assets in wallet, labels if they exist, hex otherwise
        otherasset = ""
        for label in wallet_list:
            if label != "bitcoin" and label != "testasset":
                otherasset = label
        assert(otherasset != "")

        # Now send to another wallet's CT address, check received balance
        self.nodes[0].addassetlabel(otherasset, "OTHER")
        self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), wallet_list[otherasset], "", "", False, "OTHER")
        self.nodes[0].generate(1)

        assert_equal(self.nodes[2].getinfo()['balance'][otherasset], wallet_list[otherasset])

        # Send some bitcoin and other assets over as well to fund wallet
        addr = self.nodes[2].getnewaddress()
        self.nodes[0].sendtoaddress(addr, 5)
        self.nodes[0].sendmany("", {addr:1, self.nodes[2].getnewaddress():13}, 0, "", [], {addr:"testasset"})

        self.sync_all()

        # Should have exactly 1 in change(trusted, though not confirmed) after sending one off
        assert_equal(self.nodes[0].getbalance("doesntmatter", 0, False, "testasset"), 1)
        self.nodes[2].addassetlabel(asset_list["testasset"], "testasset")
        assert_equal(self.nodes[2].getunconfirmedbalance("testasset"), Decimal(1))

        b_utxos = self.nodes[2].listunspent(0, 0, [], "bitcoin")
        t_utxos = self.nodes[2].listunspent(0, 0, [], "testasset")

        assert_equal(len(self.nodes[2].listunspent(0, 0, [])), len(b_utxos)+len(t_utxos))

        # Now craft a blinded transaction via raw api
        rawaddrs = []
        for i in range(2):
            rawaddrs.append(self.nodes[1].getnewaddress())

        raw_assets = self.nodes[2].createrawtransaction([{"txid":b_utxos[0]['txid'], "vout":b_utxos[0]['vout'], "nValue":b_utxos[0]['amount']}, {"txid":b_utxos[1]['txid'], "vout":b_utxos[1]['vout'], "nValue":b_utxos[1]['amount'], "asset":b_utxos[1]['asset']}, {"txid":t_utxos[0]['txid'], "vout":t_utxos[0]['vout'], "nValue":t_utxos[0]['amount'], "asset":t_utxos[0]['asset']}], {rawaddrs[1]:Decimal(t_utxos[0]['amount']), rawaddrs[0]:Decimal(b_utxos[0]['amount']+b_utxos[1]['amount']-Decimal("0.01"))}, 0, {rawaddrs[0]:b_utxos[0]['asset'], rawaddrs[1]:t_utxos[0]['asset']})

        # Sign unblinded, then blinded
        signed_assets = self.nodes[2].signrawtransaction(raw_assets)
        blind_assets = self.nodes[2].blindrawtransaction(raw_assets)
        signed_assets = self.nodes[2].signrawtransaction(blind_assets)

        # And finally send
        self.nodes[2].sendrawtransaction(signed_assets['hex'])

if __name__ == '__main__':
    CTTest ().main ()
