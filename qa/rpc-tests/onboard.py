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
        self.extra_args[0].append("-policycoins=50000000000000")
        self.extra_args[0].append("-initialfreecoins=50000000000000")
        self.extra_args[0].append("-initialfreecoinsdestination=76a914b87ed64e2613422571747f5d968fff29a466e24e88ac")
        self.extra_args[0].append("-issuancecoinsdestination=76a914df4439eb1a54b3a91d71979a0bb5b3f5971ff44c88ac")
        self.extra_args[0].append("-freezelistcoinsdestination=76a91474168445da07d331faabd943422653dbe19321cd88ac")
        self.extra_args[0].append("-burnlistcoinsdestination=76a9142166a4cd304b86db7dfbbc7309131fb0c4b645cd88ac")
        self.extra_args[0].append("-whitelistcoinsdestination=76a914427bf8530a3962ed77fd3c07d17fd466cb31c2fd88ac")
        self.extra_args[1].append("-rescan=1")
        self.extra_args[1].append("-pkhwhitelist-scan=1")
        self.extra_args[1].append("-keypool=100")
        self.extra_args[1].append("-policycoins=50000000000000")
        self.extra_args[1].append("-initialfreecoins=50000000000000")
        self.extra_args[1].append("-initialfreecoinsdestination=76a914b87ed64e2613422571747f5d968fff29a466e24e88ac")
        self.extra_args[1].append("-issuancecoinsdestination=76a914df4439eb1a54b3a91d71979a0bb5b3f5971ff44c88ac")
        self.extra_args[1].append("-freezelistcoinsdestination=76a91474168445da07d331faabd943422653dbe19321cd88ac")
        self.extra_args[1].append("-burnlistcoinsdestination=76a9142166a4cd304b86db7dfbbc7309131fb0c4b645cd88ac")
        self.extra_args[1].append("-whitelistcoinsdestination=76a914427bf8530a3962ed77fd3c07d17fd466cb31c2fd88ac")
        self.extra_args[2].append("-rescan=1")
        self.extra_args[2].append("-pkhwhitelist-scan=1")
        self.extra_args[2].append("-keypool=100")
        self.extra_args[2].append("-policycoins=50000000000000")
        self.extra_args[2].append("-initialfreecoins=50000000000000")
        self.extra_args[2].append("-initialfreecoinsdestination=76a914b87ed64e2613422571747f5d968fff29a466e24e88ac")
        self.extra_args[2].append("-issuancecoinsdestination=76a914df4439eb1a54b3a91d71979a0bb5b3f5971ff44c88ac")
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
        #Initial free coins
        self.nodes[0].importprivkey("cQRC9YB11Li3QHqyxMPff3uznfRggMUYdixctbyNdWdnNWr3koZy")
        #Issuance
        self.nodes[0].importprivkey("cSdWz4JStWKgVMQrdQ8TCqzmhAt7jprCPxvrZMpzy4s6WcBuW9NW")

        self.nodes[0].generate(101)
        self.sync_all()

        # issue some new asset (that is not the policy asset)
        issue = self.nodes[0].issueasset('100.0','0', False)
        self.nodes[0].generate(101)
        self.sync_all()

        #find txouts for the freezelistasset and burnlistasset
        issuescript = "76a914b87ed64e2613422571747f5d968fff29a466e24e88ac"
        pascript = "76a914b87ed64e2613422571747f5d968fff29a466e24e88ac"
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
            if "assetlabel" in rawtx["vout"][0]:
                if rawtx["vout"][0]["assetlabel"] == "WHITELIST":
                    wlasset = rawtx["vout"][0]["asset"]
                    wltxid = txid
                    wlvalue = rawtx["vout"][0]["value"]

        #Whitelist node 0 addresses
        self.nodes[0].dumpderivedkeys("keys.main")
        self.nodes[0].readwhitelist("keys.main")
        os.remove("keys.main")

        #No kycpubkeys available
        kycfile="kycfile.dat"
        try:
            userOnboardPubKey=self.nodes[1].dumpkycfile(kycfile)
        except JSONRPCException as e:
            assert("No unassigned KYC public keys available" in e.error['message'])

        #Register a KYC public key
        self.nodes[0].topupkycpubkeys(100)
        self.nodes[0].generate(101)
        self.sync_all()

        #Onboard node1
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
        ntosend=10.234
        self.nodes[0].sendtoaddress(node1addr, ntosend, "", "", False, "CBT")

        self.nodes[0].generate(101)
        self.sync_all()

        print(self.nodes[0].getwalletinfo())
        print(self.nodes[1].getwalletinfo())
        bal1=self.nodes[1].getwalletinfo()["balance"]["CBT"]

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


        #Get kyc pubkey for node1 from node1 and node0
        addr1=self.nodes[1].getnewaddress()
        kycpub1=self.nodes[0].getkycpubkey(addr1)
        assert_equal(kycpub1, self.nodes[1].getkycpubkey(addr1))

        #Blacklist node1 wallet
        self.nodes[0].blacklistkycpubkey(kycpub1)

        self.nodes[0].generate(101)
        self.sync_all()

        wl1_bl_file="wl1_bl.dat"
        self.nodes[1].dumpwhitelist(wl1_bl_file)

        #The whitelist should now be empty
        nlines=self.linecount(wl1file_3)
        nlines_bl=self.linecount(wl1_bl_file)

        assert_equal(nlines-nlines_bl,nwhitelisted)

        #Re-whitelist node1 wallet
        kycpubkeyarr=[kycpub1]
        self.nodes[0].whitelistkycpubkeys(kycpubkeyarr)

        self.nodes[0].generate(101)
        self.sync_all()

        wl1file_rwl="wl1_rwl.dat"
        self.nodes[1].dumpwhitelist(wl1file_rwl)
        nlines_rwl=self.linecount(wl1file_rwl)
        assert_equal(nlines_rwl, nlines)

        maxpercall=100
        #Whitelist more kycpubkeys
        while len(kycpubkeyarr) < maxpercall:
            kycpubkeyarr.append(kycpub1)

        self.nodes[0].whitelistkycpubkeys(kycpubkeyarr)
        self.nodes[0].generate(101)
        self.sync_all()

        #Test limit of nkeys per call
        kycpubkeyarr.append(kycpub1)

        try:
            self.nodes[0].whitelistkycpubkeys(kycpubkeyarr)
        except JSONRPCException as e:
            assert("too many keys in input array" in e.error['message'])

        os.remove(wl1file)
        os.remove(wl1file_2)
        os.remove(wl1file_3)
        os.remove(wl1_bl_file)
        return

if __name__ == '__main__':
 OnboardTest().main()

#  LocalWords:  ac
