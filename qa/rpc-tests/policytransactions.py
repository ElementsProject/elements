#!/usr/bin/env python3
# Copyright (c) 2014-2016 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *

class PolicyTransactionTest (BitcoinTestFramework):

    def __init__(self):
        super().__init__()
        self.setup_clean_chain = True
        self.num_nodes = 3
        self.extra_args = [['-txindex'] for i in range(3)]
        self.extra_args[0].append("-freezelist=1")
        self.extra_args[0].append("-burnlist=1")
        self.extra_args[1].append("-freezelist=1")
        self.extra_args[1].append("-burnlist=1")
        self.extra_args[2].append("-freezelist=1")
        self.extra_args[2].append("-burnlist=1")
        self.extra_args[0].append("-policycoins=50000000000000")
        self.extra_args[0].append("-issuancecoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac")
        self.extra_args[0].append("-freezelistcoinsdestination=76a91474168445da07d331faabd943422653dbe19321cd88ac")
        self.extra_args[0].append("-burnlistcoinsdestination=76a9142166a4cd304b86db7dfbbc7309131fb0c4b645cd88ac")
        self.extra_args[1].append("-policycoins=50000000000000")
        self.extra_args[1].append("-issuancecoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac")
        self.extra_args[1].append("-freezelistcoinsdestination=76a91474168445da07d331faabd943422653dbe19321cd88ac")
        self.extra_args[1].append("-burnlistcoinsdestination=76a9142166a4cd304b86db7dfbbc7309131fb0c4b645cd88ac")
        self.extra_args[2].append("-policycoins=50000000000000")
        self.extra_args[2].append("-issuancecoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac")
        self.extra_args[2].append("-freezelistcoinsdestination=76a91474168445da07d331faabd943422653dbe19321cd88ac")
        self.extra_args[2].append("-burnlistcoinsdestination=76a9142166a4cd304b86db7dfbbc7309131fb0c4b645cd88ac")

    def setup_network(self, split=False):
        self.nodes = start_nodes(3, self.options.tmpdir, self.extra_args[:3])
        connect_nodes_bi(self.nodes,0,1)
        connect_nodes_bi(self.nodes,1,2)
        connect_nodes_bi(self.nodes,0,2)
        self.is_network_split=False
        self.sync_all()

    def run_test (self):

        # import the policy keys into node 0
        self.nodes[0].importprivkey("cS29UJMQrpnee7UaUHo6NqJVpGr35TEqUDkKXStTnxSZCGUWavgE")
        self.nodes[0].importprivkey("cND4nfH6g2SopoLk5isQ8qGqqZ5LmbK6YwJ1QnyoyMVBTs8bVNNd")
        self.nodes[0].importprivkey("cTnxkovLhGbp7VRhMhGThYt8WDwviXgaVAD8DjaVa5G5DApwC6tF")


        self.nodes[0].generate(101)
        self.sync_all()

        #find txouts for the freezelistasset and burnlistasset
        pascript = "76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac"
        flscript = "76a91474168445da07d331faabd943422653dbe19321cd88ac"
        blscript = "76a9142166a4cd304b86db7dfbbc7309131fb0c4b645cd88ac"
        genhash = self.nodes[0].getblockhash(0)
        genblock = self.nodes[0].getblock(genhash)

        for txid in genblock["tx"]:
            rawtx = self.nodes[0].getrawtransaction(txid,True)
            if "assetlabel" in rawtx["vout"][0]:
                if rawtx["vout"][0]["assetlabel"] == "FREEZELIST":
                    flasset = rawtx["vout"][0]["asset"]
                    fltxid = txid
                    flvalue = rawtx["vout"][0]["value"]
                if rawtx["vout"][0]["assetlabel"] == "BURNLIST":
                    blasset = rawtx["vout"][0]["asset"]
                    bltxid = txid
                    blvalue = rawtx["vout"][0]["value"]
                if rawtx["vout"][0]["assetlabel"] == "ISSUANCE":
                    paasset = rawtx["vout"][0]["asset"]
                    patxid = txid
                    pavalue = rawtx["vout"][0]["value"]

        #issue some non-policy asset
        assaddr = self.nodes[0].getnewaddress()
        tokaddr = self.nodes[0].getnewaddress()
        cngaddr = self.nodes[0].getnewaddress()
        rawissue = self.nodes[0].createrawissuance(assaddr,1000.0,tokaddr,1.0,cngaddr,pavalue,'1',patxid,str(0))
        signissue = self.nodes[0].signrawtransaction(rawissue["rawtx"])
        sendissue = self.nodes[0].sendrawtransaction(signissue["hex"])

        self.nodes[0].generate(1)
        self.sync_all()

        #Send some coins to the second node
        fundaddr = self.nodes[1].getnewaddress()
        inputs = []
        vin = {}
        vin["txid"] = patxid
        vin["vout"] = 1
        inputs.append(vin)
        outp = {}
        outp[fundaddr] = 4999.999
        outp["fee"] = 0.001
        assets =  {}
        assets[fundaddr] = paasset;
        assets["fee"] = paasset;
        fundtx = self.nodes[0].createrawtransaction(inputs,outp,0,assets)
        fundtx_signed = self.nodes[0].signrawtransaction(fundtx)
        assert(fundtx_signed["complete"])
        fundtx_send = self.nodes[0].sendrawtransaction(fundtx_signed["hex"])

        self.nodes[0].generate(101)
        self.sync_all()

        #generate a public key for the policy wallet
        policyaddress = self.nodes[0].getnewaddress()
        validatepaddress = self.nodes[0].validateaddress(policyaddress)
        policypubkey = validatepaddress['pubkey']

        #get an address for the freezelist
        frzaddress1 = self.nodes[1].getnewaddress()

        #send some coins to that address
        rtxid = self.nodes[0].sendtoaddress(frzaddress1,100,"","",False,rawissue["asset"])

        self.nodes[0].generate(1)
        self.sync_all()

        #get the vout
        rawtx = self.nodes[1].getrawtransaction(rtxid,True)
        for vout in rawtx["vout"]:
            if vout["value"] == 100.0:
                rvout = vout["n"]


        assert_equal(self.nodes[0].queryfreezelist(frzaddress1), False)

        #generate the tx to freeze the user address
        inputs = []
        vin = {}
        vin["txid"] = fltxid
        vin["vout"] = 0
        inputs.append(vin)
        outputs = []
        outp = {}
        outp["pubkey"] = policypubkey
        outp["value"] = flvalue
        outp["address"] = frzaddress1
        outputs.append(outp)
        frztx = self.nodes[0].createrawpolicytx(inputs,outputs,0,flasset)
        frztx_signed = self.nodes[0].signrawtransaction(frztx)
        assert(frztx_signed["complete"])
        frztx_send = self.nodes[0].sendrawtransaction(frztx_signed["hex"])

        self.nodes[0].generate(1)
        self.sync_all()

        #check that the freezelist has been updated
        assert_equal(self.nodes[0].queryfreezelist(frzaddress1), True)

        #try and spend from the frozen output
        newaddr = self.nodes[1].getnewaddress()
        inputs = []
        vin = {}
        vin["txid"] = rtxid
        vin["vout"] = rvout
        inputs.append(vin)
        outp = {}
        outp[newaddr] = 99.999
        outp["fee"] = 0.001
        assmap = {}
        assmap[newaddr] = rawissue["asset"]
        assmap["fee"] = rawissue["asset"]
        newtx = self.nodes[1].createrawtransaction(inputs,outp,0,assmap)
        newtx_signed = self.nodes[1].signrawtransaction(newtx)
        assert(newtx_signed["complete"])
        try:
            newtx_send = self.nodes[1].sendrawtransaction(newtx_signed["hex"])
        except JSONRPCException as e:
            assert("freezelist-address-input" in e.error['message'])

        self.nodes[0].generate(1)
        self.sync_all()

        #remnove the address from the freezelist by spending the policy tx
        frzaddress2 = self.nodes[1].getnewaddress()
        #generate the tx to freeze the user address
        inputs = []
        vin = {}
        vin["txid"] = frztx_send
        vin["vout"] = 0
        inputs.append(vin)
        outputs = []
        outp = {}
        outp["pubkey"] = policypubkey
        outp["value"] = flvalue
        outp["address"] = frzaddress2
        outputs.append(outp)
        frztx = self.nodes[0].createrawpolicytx(inputs,outputs,0,flasset)
        frztx_signed = self.nodes[0].signrawtransaction(frztx)
        assert(frztx_signed["complete"])
        frztx_send = self.nodes[0].sendrawtransaction(frztx_signed["hex"])

        self.nodes[0].generate(1)
        self.sync_all()

        #check that the freezelist has been updated
        assert_equal(self.nodes[0].queryfreezelist(frzaddress1), False)

        #try and spend from the un-frozen output
        newtx_send = self.nodes[1].sendrawtransaction(newtx_signed["hex"])

        self.sync_all()

        mempool = self.nodes[0].getrawmempool()

        assert(newtx_send in mempool)

        self.nodes[0].generate(1)
        self.sync_all()

        #check the operation of the burnlist
        burnaddress1 = self.nodes[1].getnewaddress()

        assert_equal(self.nodes[0].queryburnlist(burnaddress1), False)

        #generate the tx to freeze the user address
        inputs = []
        vin = {}
        vin["txid"] = bltxid
        vin["vout"] = 0
        inputs.append(vin)
        outputs = []
        outp = {}
        outp["pubkey"] = policypubkey
        outp["value"] = blvalue
        outp["address"] = burnaddress1
        outputs.append(outp)
        brntx = self.nodes[0].createrawpolicytx(inputs,outputs,0,blasset)
        brntx_signed = self.nodes[0].signrawtransaction(brntx)
        assert(brntx_signed["complete"])
        brntx_send = self.nodes[0].sendrawtransaction(brntx_signed["hex"])

        self.nodes[0].generate(1)
        self.sync_all()

        #check that the freezelist has been updated
        assert_equal(self.nodes[0].queryburnlist(burnaddress1), True)

        #remnove the address from the freezelist by spending the policy tx
        burnaddress2 = self.nodes[1].getnewaddress()
        #generate the tx to freeze the user address
        inputs = []
        vin = {}
        vin["txid"] = brntx_send
        vin["vout"] = 0
        inputs.append(vin)
        outputs = []
        outp = {}
        outp["pubkey"] = policypubkey
        outp["value"] = blvalue
        outp["address"] = burnaddress2
        outputs.append(outp)
        brntx = self.nodes[0].createrawpolicytx(inputs,outputs,0,blasset)
        brntx_signed = self.nodes[0].signrawtransaction(brntx)
        assert(brntx_signed["complete"])
        brntx_send = self.nodes[0].sendrawtransaction(brntx_signed["hex"])

        self.nodes[0].generate(1)
        self.sync_all()

        #check that the freezelist has been updated
        assert_equal(self.nodes[0].queryburnlist(burnaddress1), False)

        return

if __name__ == '__main__':
    PolicyTransactionTest().main()
