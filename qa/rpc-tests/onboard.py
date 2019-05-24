#!/usr/bin/env python3
# Copyright (c) 2014-2016 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *
import filecmp
import time

class OnboardTest (BitcoinTestFramework):

    def __init__(self):
        super().__init__()
        self.setup_clean_chain = True
        self.num_nodes = 3
        self.extra_args = [['-txindex'] for i in range(3)]
        self.extra_args[0].append("-keypool=100")
        self.extra_args[0].append("-freezelist=1")
        self.extra_args[0].append("-burnlist=1")
        self.extra_args[0].append("-pkhwhitelist=1")
        self.extra_args[0].append("-rescan=1")
        self.extra_args[0].append("-initialfreecoins=2100000000000000")
        self.extra_args[0].append("-policycoins=50000000000000")
        self.extra_args[0].append("-initialfreecoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac")
        self.extra_args[0].append("-issuancecoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac")
        self.extra_args[0].append("-freezelistcoinsdestination=76a91474168445da07d331faabd943422653dbe19321cd88ac")
        self.extra_args[0].append("-burnlistcoinsdestination=76a9142166a4cd304b86db7dfbbc7309131fb0c4b645cd88ac")
        self.extra_args[0].append("-whitelistcoinsdestination=76a914427bf8530a3962ed77fd3c07d17fd466cb31c2fd88ac")
        self.extra_args[1].append("-rescan=1")
        self.extra_args[1].append("-pkhwhitelist-scan=1")
        self.extra_args[1].append("-keypool=100")
        self.extra_args[1].append("-initialfreecoins=2100000000000000")
        self.extra_args[1].append("-policycoins=50000000000000")
        self.extra_args[1].append("-initialfreecoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac")
        self.extra_args[1].append("-issuancecoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac")
        self.extra_args[1].append("-freezelistcoinsdestination=76a91474168445da07d331faabd943422653dbe19321cd88ac")
        self.extra_args[1].append("-burnlistcoinsdestination=76a9142166a4cd304b86db7dfbbc7309131fb0c4b645cd88ac")
        self.extra_args[1].append("-whitelistcoinsdestination=76a914427bf8530a3962ed77fd3c07d17fd466cb31c2fd88ac")
        self.extra_args[2].append("-rescan=1")
        self.extra_args[2].append("-pkhwhitelist-scan=1")
        self.extra_args[2].append("-keypool=100")
        self.extra_args[2].append("-initialfreecoins=2100000000000000")
        self.extra_args[2].append("-policycoins=50000000000000")
        self.extra_args[2].append("-initialfreecoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac")
        self.extra_args[2].append("-issuancecoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac")
        self.extra_args[2].append("-freezelistcoinsdestination=76a91474168445da07d331faabd943422653dbe19321cd88ac")
        self.extra_args[2].append("-burnlistcoinsdestination=76a9142166a4cd304b86db7dfbbc7309131fb0c4b645cd88ac")
        self.extra_args[2].append("-whitelistcoinsdestination=76a914427bf8530a3962ed77fd3c07d17fd466cb31c2fd88ac")

    def setup_network(self, split=False):
        self.nodes = start_nodes(3, self.options.tmpdir, self.extra_args[:3])
        connect_nodes_bi(self.nodes,0,1)
        connect_nodes_bi(self.nodes,1,2)
        connect_nodes_bi(self.nodes,0,2)
        self.is_network_split=False
        self.sync_all()

    def linecount(self, file):
        nlines=0
        with open(file) as f:
            for nlines, l in enumerate(f):
                pass
        return nlines

    def run_test (self):
        keypool=1

        # import the policy keys into node 0
        self.nodes[0].importprivkey("cS29UJMQrpnee7UaUHo6NqJVpGr35TEqUDkKXStTnxSZCGUWavgE")
        self.nodes[0].importprivkey("cND4nfH6g2SopoLk5isQ8qGqqZ5LmbK6YwJ1QnyoyMVBTs8bVNNd")
        self.nodes[0].importprivkey("cTnxkovLhGbp7VRhMhGThYt8WDwviXgaVAD8DjaVa5G5DApwC6tF")
        self.nodes[0].importprivkey("cNCQhCnpnzyeYh48NszsTJC2G4HPoFMZguUnUgBpJ5X9Vf2KaPYx")

        self.nodes[0].generate(101)
        self.sync_all()

        #find txouts for the freezelistasset and burnlistasset
        pascript = "76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac"
        flscript = "76a91474168445da07d331faabd943422653dbe19321cd88ac"
        blscript = "76a9142166a4cd304b86db7dfbbc7309131fb0c4b645cd88ac"
        wlscript = "76a914427bf8530a3962ed77fd3c07d17fd466cb31c2fd88ac"
        genhash = self.nodes[0].getblockhash(0)
        genblock = self.nodes[0].getblock(genhash)

        for txid in genblock["tx"]:
            rawtx = self.nodes[0].getrawtransaction(txid,True)
            if rawtx["vout"][0]["scriptPubKey"]["hex"] == flscript:
                flasset = rawtx["vout"][0]["asset"]
                fltxid = txid
                flvalue = rawtx["vout"][0]["value"]
            if rawtx["vout"][0]["scriptPubKey"]["hex"] == blscript:
                blasset = rawtx["vout"][0]["asset"]
                bltxid = txid
                blvalue = rawtx["vout"][0]["value"]
            if rawtx["vout"][0]["scriptPubKey"]["hex"] == pascript:
                paasset = rawtx["vout"][0]["asset"]
                patxid = txid
                pavalue = rawtx["vout"][0]["value"]
            if rawtx["vout"][0]["scriptPubKey"]["hex"] == wlscript:
                wlasset = rawtx["vout"][0]["asset"]
                wltxid = txid
                wlvalue = rawtx["vout"][0]["value"]

        #Whitelist node 0 addresses
        self.nodes[0].dumpderivedkeys("keys.main")
        self.nodes[0].readwhitelist("keys.main")
        os.remove("keys.main")

        #Register a KYC public key
        policyaddr=self.nodes[0].getnewaddress()
        assert(self.nodes[0].querywhitelist(policyaddr))
        policypubkey=self.nodes[0].validateaddress(policyaddr)["pubkey"]
        kycaddr=self.nodes[0].getnewaddress()
        kycpubkey=self.nodes[0].validateaddress(kycaddr)["pubkey"]

        inputs=[]
        vin = {}
        vin["txid"]= wltxid
        vin["vout"]= 0
        inputs.append(vin)
        outputs = []
        outp = {}
        outp["pubkey"]=policypubkey
        outp["value"]=wlvalue
        outp["userkey"]=kycpubkey
        outputs.append(outp)
        wltx=self.nodes[0].createrawpolicytx(inputs, outputs, 0, wlasset)
        wltx_signed=self.nodes[0].signrawtransaction(wltx)
        assert(wltx_signed["complete"])
        wltx_send = self.nodes[0].sendrawtransaction(wltx_signed["hex"])

        self.nodes[0].generate(101)
        self.sync_all()

        #Onboard node1
        kycfile="kycfile.dat"
        userOnboardPubKey=self.nodes[1].dumpkycfile(kycfile)

        self.nodes[0].generate(101)
        self.sync_all()

        balance_1=self.nodes[0].getwalletinfo()["balance"]["WHITELIST"]
        self.nodes[0].onboarduser(kycfile)

        os.remove(kycfile)

        self.nodes[0].generate(101)
        self.sync_all()
        balance_2=self.nodes[0].getwalletinfo()["balance"]["WHITELIST"]
        #Make sure the onboard transaction fee was zero
        assert((balance_1-balance_2) == 0)

        node1addr=self.nodes[1].getnewaddress()
        iswl=self.nodes[0].querywhitelist(node1addr)
        assert(iswl)

        keypool=100
        nwhitelisted=keypool

        #Send some tokens to node 1
        ntosend=10000.234
        self.nodes[0].sendtoaddress(node1addr, ntosend)
        self.nodes[0].sendtoaddress(node1addr, ntosend, "", "", False, paasset)

        self.nodes[0].generate(101)
        self.sync_all()

        bal1=self.nodes[1].getwalletinfo()["balance"]["ISSUANCE"]

        assert_equal(float(bal1),float(ntosend))

        #Restart the nodes. The whitelist will be restored. TODO
        wl1file="wl1.dat"
        self.nodes[1].dumpwhitelist(wl1file)

        # time.sleep(1)
        # try:
        #     stop_node(self.nodes[1],1)
        #  except ConnectionResetError as e:
        #     pass
        # except ConnectionRefusedError as e:
        #     pass
        # self.nodes[1] = start_node(1, self.options.tmpdir, self.extra_args[:3])
        # wl1file_2="wl1_2.dat"
        # self.nodes[1].dumpwhitelist(wl1file_2)
        # assert(filecmp.cmp(wlfile, wlfile_2))
 
        #Node 1 registers additional addresses to whitelist
        nadd=100
        self.nodes[1].sendaddtowhitelisttx(nadd,"CBT")
        time.sleep(5)
        self.nodes[0].generate(101)
        self.sync_all()
        nwhitelisted+=nadd
        wl1file_2="wl1_2.dat"
        self.nodes[1].dumpwhitelist(wl1file_2)
        nlines1=self.linecount(wl1file)
        nlines2=self.linecount(wl1file_2)
        assert_equal(nlines2-nlines1, nadd)


        self.nodes[1].sendaddtowhitelisttx(nadd,"CBT")
        self.nodes[1].sendaddtowhitelisttx(nadd,"CBT")
        self.nodes[1].sendaddtowhitelisttx(nadd,"CBT")
        time.sleep(5)
        self.nodes[0].generate(101)
        self.sync_all()
        nwhitelisted+=(3*nadd)
        wl1file_3="wl1_3.dat"
        self.nodes[1].dumpwhitelist(wl1file_3)
        nlines3=self.linecount(wl1file_3)
        assert_equal(nlines3-nlines2, 3*nadd)


        #Blacklist node 1
        wltx_decoded=self.nodes[1].decoderawtransaction(wltx)
        wltx_send
        wlvouts=wltx_decoded["vout"]

        wlvout = list(filter(lambda x: x["scriptPubKey"]["type"] == "multisig", wlvouts))[0]
        wlvoutn=wlvout["n"]
        blvalue=wlvout["value"]

        inputs=[]
        vin = {}
        vin["txid"]= wltx_send
        vin["vout"]= wlvoutn
        inputs.append(vin)
        outputs = []
        outp = {}
        outp["pubkey"]=policypubkey
        outp["value"]=blvalue
        outputs.append(outp)
        bltx=self.nodes[0].createrawpolicytx(inputs, outputs, 0, wlasset)
        bltx_signed=self.nodes[0].signrawtransaction(bltx)
        assert(bltx_signed["complete"])
        bltx_send = self.nodes[0].sendrawtransaction(bltx_signed["hex"])

        self.nodes[0].generate(101)
        self.sync_all()

        wl1_bl_file="wl1_bl.dat"
        self.nodes[1].dumpwhitelist(wl1_bl_file)

        #The whitelist should now be empty
        nlines=self.linecount(wl1file_3)
        nlines_bl=self.linecount(wl1_bl_file)

        assert_equal(nlines-nlines_bl,nwhitelisted)

        os.remove(wl1file)
        os.remove(wl1file_2)
        os.remove(wl1file_3)
        os.remove(wl1_bl_file)
        return

if __name__ == '__main__':
 OnboardTest().main()
