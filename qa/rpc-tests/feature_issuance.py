#!/usr/bin/env python3
# Copyright (c) 2016 The Bitcoin Core developers
# Distributed under the MIT/X11 software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *

" Tests issued assets functionality including (re)issuance, and de-issuance "

class IssuanceTest (BitcoinTestFramework):

    def __init__(self):
        super().__init__()
        self.num_nodes = 3
        self.setup_clean_chain = True

    def setup_network(self, split=False):
        self.nodes = start_nodes(self.num_nodes, self.options.tmpdir)
        connect_nodes_bi(self.nodes,0,1)
        connect_nodes_bi(self.nodes,1,2)
        self.is_network_split=False
        self.sync_all()

    def run_test(self):

        # Unblinded issuance of asset
        issued = self.nodes[0].issueasset(1, 1, False)
        assert_equal(self.nodes[0].getwalletinfo()["balance"][issued["asset"]], 1)
        assert_equal(self.nodes[0].getwalletinfo()["balance"][issued["token"]], 1)
        # Quick unblinded reissuance check, making 2*COIN total
        self.nodes[0].reissueasset(issued["asset"], 1)

        self.nodes[0].generate(1)
        self.sync_all()

        issued2 = self.nodes[0].issueasset(2, 1)
        test_asset = issued2["asset"]
        assert_equal(self.nodes[0].getwalletinfo(test_asset)['balance'], Decimal(2))

        assert_equal(self.nodes[1].getwalletinfo(test_asset)['balance'], Decimal(0))

        # Send some bitcoin to other nodes
        self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 3)
        self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 3)
        self.nodes[0].generate(1)
        self.sync_all()

        # Destroy assets
        pre_destroy_btc_balance = self.nodes[2].getwalletinfo()['balance']['bitcoin']
        self.nodes[2].destroyamount('bitcoin', 2) # Destroy 2 BTC
        self.nodes[2].generate(1)
        self.sync_all()

        issuedamount = self.nodes[0].getwalletinfo()['balance'][issued["token"]]
        assert_equal(issuedamount, Decimal('1.0'))
        self.nodes[0].destroyamount(issued["token"], issuedamount) # Destroy all reissuance tokens of one type

        self.nodes[0].generate(1)
        self.sync_all()
        assert(issued["token"] not in self.nodes[0].getinfo()['balance'])

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
        self.nodes[2].sendtoaddress(self.nodes[1].getnewaddress(), Decimal('0.00000001'), "", "", False, issuancedata["token"])
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

        assert_equal(len(self.nodes[0].listissuances()), 6);
        self.nodes[0].importaddress(addr1)
        self.nodes[0].importaddress(addr2)
        self.nodes[0].importaddress(addr3)

        issuances = self.nodes[0].listissuances()
        assert_equal(len(issuances), 9)

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
        assert(issued["asset"] not in self.nodes[0].getwalletinfo()["balance"])
        assert_equal(self.nodes[0].getwalletinfo()["balance"][issued["token"]], 1)


if __name__ == '__main__':
    IssuanceTest ().main ()
