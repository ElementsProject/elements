#!/usr/bin/env python3
# Copyright (c) 2016 The Bitcoin Core developers
# Distributed under the MIT/X11 software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *

class AssetStatsTest (BitcoinTestFramework):

    def __init__(self):
        super().__init__()
        self.num_nodes = 3
        self.setup_clean_chain = True

    def setup_network(self, split=False):
        self.nodes = start_nodes(self.num_nodes, self.options.tmpdir)
        connect_nodes_bi(self.nodes,0,1)
        connect_nodes_bi(self.nodes,1,2)
        connect_nodes_bi(self.nodes,0,2)
        self.is_network_split=False
        self.sync_all()

    def run_test(self):
        print("Mining blocks...")
        self.nodes[0].generate(10)

        #issue new asset with re-issuance token
        asset1 = self.nodes[0].issueasset(Decimal('1000.0'),Decimal('1.0'))
        self.nodes[0].generate(10)
        self.sync_all()

        #check UTXO report on different node
        stats1 = self.nodes[1].getutxoassetinfo()
        iter = 0
        for assetstats in stats1:
            if asset1["asset"] == assetstats["asset"]:
                assert_equal(assetstats["amountspendable"], Decimal('1000.0'))
                assert_equal(assetstats["amountfrozen"], Decimal('0.0'))
                iter += 1
            if asset1["token"] == assetstats["asset"]:
                assert_equal(assetstats["amountspendable"], Decimal('1.0'))
                assert_equal(assetstats["amountfrozen"], Decimal('0.0'))
                iter += 1
        assert(iter == 2)

        #transact in the issued asset
        addr1 = self.nodes[1].getnewaddress()
        addr2 = self.nodes[2].getnewaddress()
        self.nodes[0].sendtoaddress(addr1,Decimal('20.0')," "," ",False,asset1["asset"],True)
        self.nodes[0].generate(10)
        self.sync_all()
        self.nodes[0].sendtoaddress(addr2,Decimal('30.0')," "," ",False,asset1["asset"],True)
        self.nodes[0].generate(10)
        self.sync_all()

        #check that the total amounts are the same
        stats2 = self.nodes[1].getutxoassetinfo()
        iter = 0
        for assetstats in stats2:
            if asset1["asset"] == assetstats["asset"]:
                assert_equal(assetstats["amountspendable"], Decimal('1000.0'))
                assert_equal(assetstats["amountfrozen"], Decimal('0.0'))
                iter +=1
            if asset1["token"] == assetstats["asset"]:
                assert_equal(assetstats["amountspendable"], Decimal('1.0'))
                assert_equal(assetstats["amountfrozen"], Decimal('0.0'))
                iter +=1
        assert(iter == 2)

        #reissue some asset
        ritx = self.nodes[0].reissueasset(asset1["asset"],Decimal('50.0'))
        self.nodes[0].generate(10)
        self.sync_all()

        #check asset report amounts
        stats2 = self.nodes[1].getutxoassetinfo()
        iter = 0
        for assetstats in stats2:
            if asset1["asset"] == assetstats["asset"]:
                assert_equal(assetstats["amountspendable"], Decimal('1050.0'))
                assert_equal(assetstats["amountfrozen"], Decimal('0.0'))
                iter +=1
            if asset1["token"] == assetstats["asset"]:
                assert_equal(assetstats["amountspendable"], Decimal('1.0'))
                assert_equal(assetstats["amountfrozen"], Decimal('0.0'))
                iter +=1
        assert(iter == 2)

        #destroy some asset
        self.nodes[0].destroyamount(asset1["asset"],Decimal('50.0'))
        self.nodes[0].generate(10)
        self.sync_all()

        #check asset report amounts
        stats3 = self.nodes[2].getutxoassetinfo()
        iter = 0
        for assetstats in stats3:
            if asset1["asset"] == assetstats["asset"]:
                assert_equal(assetstats["amountspendable"], Decimal('1000.0'))
                assert_equal(assetstats["amountfrozen"], Decimal('0.0'))
                iter +=1
            if asset1["token"] == assetstats["asset"]:
                assert_equal(assetstats["amountspendable"], Decimal('1.0'))
                assert_equal(assetstats["amountfrozen"], Decimal('0.0'))
                iter +=1
        assert(iter == 2)

        #issue a new asset
        asset2 = self.nodes[0].issueasset(Decimal('800.0'),Decimal('1.0'))
        self.nodes[0].generate(10)
        self.sync_all()        

        newadd = self.nodes[0].getnewaddress()
        txidnew = self.nodes[0].sendtoaddress(newadd,Decimal('750.0')," "," ",False,asset2["asset"],True)
        self.nodes[0].generate(10)
        self.sync_all()

        #send some asset to a frozen output

        #find vout
        vout = 0
        found = False
        isstx = self.nodes[0].getrawtransaction(txidnew,True)
        for output in isstx["vout"]:
            if output["asset"] == asset2["asset"] and output["value"] == Decimal('750.0'):
                vout = output["n"]
                found = True
        assert(found)

        #create raw tx
        addr4 = self.nodes[2].getnewaddress()
        addrfrz = "2dZRkPX3hrPtuBrmMkbGtxTxsuYYgAaFrXZ"
        rawtx = self.nodes[0].createrawtransaction([{"txid":txidnew,"vout":vout}],{addrfrz:Decimal('0.0001'),addr4:Decimal('749.9998'),"fee":Decimal("0.0001")},0,{addrfrz:asset2["asset"],addr4:asset2["asset"],"fee":asset2["asset"]})
        sigtx = self.nodes[0].signrawtransaction(rawtx)

        sendtx = self.nodes[0].sendrawtransaction(sigtx["hex"])

        self.nodes[0].generate(10)
        self.sync_all()

        #check asset report amounts
        stats4 = self.nodes[2].getutxoassetinfo()

        iter = 0
        for assetstats in stats4:
            if asset2["asset"] == assetstats["asset"]:
                assert_equal(assetstats["amountspendable"], Decimal('50.0001'))
                assert_equal(assetstats["amountfrozen"], Decimal('749.9999'))
                iter +=1
            if asset2["token"] == assetstats["asset"]:
                assert_equal(assetstats["amountspendable"], Decimal('1.0'))
                assert_equal(assetstats["amountfrozen"], Decimal('0.0'))
                iter +=1
        assert(iter == 2)

        #send some asset to a burn (OP_RETURN) output

        #first send 10 of asset2 to to a new output
        newadd = self.nodes[0].getnewaddress()
        txidnew = self.nodes[0].sendtoaddress(newadd,Decimal('10.0')," "," ",False,asset2["asset"],True)
        self.nodes[0].generate(10)
        self.sync_all()

        #find the vout
        vout = 0
        found = False
        isstx = self.nodes[0].getrawtransaction(txidnew,True)
        for output in isstx["vout"]:
            if output["asset"] == asset2["asset"] and output["value"] == Decimal('10.0'):
                vout = output["n"]
                found = True
        assert(found)

        #then send this output to a burn OP_RETURN
        rawtx = self.nodes[0].createrawburn(txidnew,str(vout),asset2["asset"],Decimal('10.0'))
        sigtx = self.nodes[0].signrawtransaction(rawtx["hex"])
        sendtx = self.nodes[0].sendrawtransaction(sigtx["hex"])

        self.nodes[0].generate(10)
        self.sync_all()    

        #check asset report amounts
        stats5 = self.nodes[2].getutxoassetinfo()

        iter = 0
        for assetstats in stats5:
            if asset2["asset"] == assetstats["asset"]:
                assert_equal(assetstats["amountspendable"], Decimal('40.0001'))
                assert_equal(assetstats["amountfrozen"], Decimal('749.9999'))
                iter +=1
            if asset2["token"] == assetstats["asset"]:
                assert_equal(assetstats["amountspendable"], Decimal('1.0'))
                assert_equal(assetstats["amountfrozen"], Decimal('0.0'))
                iter +=1
        assert(iter == 2)

if __name__ == '__main__':
    AssetStatsTest ().main ()
