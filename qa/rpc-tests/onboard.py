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
        self.extra_args[0].append("-regtest=0")
        self.extra_args[0].append("-initialfreecoinsdestination=76a914b87ed64e2613422571747f5d968fff29a466e24e88ac")
        self.extra_args[0].append("-issuancecoinsdestination=76a914df4439eb1a54b3a91d71979a0bb5b3f5971ff44c88ac")
        self.extra_args[0].append("-freezelistcoinsdestination=76a91474168445da07d331faabd943422653dbe19321cd88ac")
        self.extra_args[0].append("-burnlistcoinsdestination=76a9142166a4cd304b86db7dfbbc7309131fb0c4b645cd88ac")
        self.extra_args[0].append("-whitelistcoinsdestination=76a914427bf8530a3962ed77fd3c07d17fd466cb31c2fd88ac")
        self.extra_args[1].append("-rescan=1")
        self.extra_args[1].append("-regtest=0")
        self.extra_args[1].append("-pkhwhitelist-scan=1")
        self.extra_args[1].append("-keypool=100")
        self.extra_args[1].append("-freezelist=1")
        self.extra_args[1].append("-burnlistist=1")
        self.extra_args[1].append("-initialfreecoins=2100000000000000")
        self.extra_args[1].append("-policycoins=50000000000000")
        self.extra_args[1].append("-initialfreecoinsdestination=76a914b87ed64e2613422571747f5d968fff29a466e24e88ac")
        self.extra_args[1].append("-issuancecoinsdestination=76a914df4439eb1a54b3a91d71979a0bb5b3f5971ff44c88ac")
        self.extra_args[1].append("-freezelistcoinsdestination=76a91474168445da07d331faabd943422653dbe19321cd88ac")
        self.extra_args[1].append("-burnlistcoinsdestination=76a9142166a4cd304b86db7dfbbc7309131fb0c4b645cd88ac")
        self.extra_args[1].append("-whitelistcoinsdestination=76a914427bf8530a3962ed77fd3c07d17fd466cb31c2fd88ac")
        self.extra_args[2].append("-keypool=100")
        self.extra_args[2].append("-freezelist=1")
        self.extra_args[2].append("-burnlist=1")
        self.extra_args[2].append("-pkhwhitelist=1")
        self.extra_args[2].append("-rescan=1")
        self.extra_args[2].append("-initialfreecoins=2100000000000000")
        self.extra_args[2].append("-policycoins=50000000000000")
        self.extra_args[2].append("-regtest=0")
        self.extra_args[2].append("-initialfreecoinsdestination=76a914b87ed64e2613422571747f5d968fff29a466e24e88ac")
        self.extra_args[2].append("-issuancecoinsdestination=76a914df4439eb1a54b3a91d71979a0bb5b3f5971ff44c88ac")
        self.extra_args[2].append("-freezelistcoinsdestination=76a91474168445da07d331faabd943422653dbe19321cd88ac")
        self.extra_args[2].append("-burnlistcoinsdestination=76a9142166a4cd304b86db7dfbbc7309131fb0c4b645cd88ac")
        self.extra_args[2].append("-whitelistcoinsdestination=76a914427bf8530a3962ed77fd3c07d17fd466cb31c2fd88ac")
        self.files=[]
        self.nodes=[]

    def setup_network(self, split=False):
        #Start a node, get the wallet file, stop the node and use the wallet file as the whitelisting wallet
        #Start nodes
        self.nodes = start_nodes(3, self.options.tmpdir, self.extra_args[:3])
        #Set up wallet path and dump the wallet
        wlwalletname="wlwallet.dat"
        wlwalletpath=os.path.join(self.options.tmpdir,wlwalletname)
        time.sleep(5)
        self.nodes[0].backupwallet(wlwalletpath)
        
        #Stop the nodes
        stop_nodes(self.nodes)
        time.sleep(5)

        #Copy the wallet file to the node 0 and 2 data dirs
        #Give nodes 0 and 2 the same wallet (whitelist wallet)
        node0path=os.path.join(self.options.tmpdir, "node"+str(0))
        node1path=os.path.join(self.options.tmpdir, "node"+str(1))
        node2path=os.path.join(self.options.tmpdir, "node"+str(2))

        dest0=os.path.join(node0path, "ocean_test")
        dest0=os.path.join(dest0, wlwalletname)
        dest2=os.path.join(node2path, "ocean_test")
        dest2=os.path.join(dest2, wlwalletname)

        shutil.copyfile(wlwalletpath,dest0)
        shutil.copyfile(wlwalletpath,dest2)
        
        time.sleep(5)

        #Start the nodes again with a different wallet path argument
        self.extra_args[0].append("-wallet="+wlwalletname)
        self.extra_args[2].append("-wallet="+wlwalletname)
        self.nodes = start_nodes(3, self.options.tmpdir, self.extra_args[:3])

        time.sleep(5)

        #Node0 and node2 wallets should be the same
        addr0=self.nodes[0].getnewaddress()
        addr2=self.nodes[2].getnewaddress()

        assert(addr0 == addr2)

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

    def initfile(self, filename):
        self.files.append(filename)
        self.removefileifexists(filename)
        return filename

    def removefileifexists(self, filename):
        if(os.path.isfile(filename)):
            os.remove(filename)

    def cleanup_files(self):
        for file in self.files:
            self.removefileifexists(file)

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
        time.sleep(5)


        #Onboard node0
        kycfile0=self.initfile("kycfile0.dat")
        userOnboardPubKey=self.nodes[0].dumpkycfile(kycfile0)
        self.nodes[0].onboarduser(kycfile0)
        self.nodes[0].generate(101)
        self.sync_all()

        #Onboard node1
        kycfile=self.initfile("kycfile.dat")
        userOnboardPubKey=self.nodes[1].dumpkycfile(kycfile)

        self.nodes[0].generate(101)
        self.sync_all()
        time.sleep(5)

        balance_1=self.nodes[0].getwalletinfo()["balance"]["WHITELIST"]
        time.sleep(1)
        self.nodes[0].onboarduser(kycfile)

        self.nodes[0].generate(101)
        self.sync_all()
        balance_2=self.nodes[0].getwalletinfo()["balance"]["WHITELIST"]
        #Make sure the onboard transaction fee was zero
        assert((balance_1-balance_2) == 0)

        node1addr=self.nodes[1].getnewaddress()

        try:
            iswl=self.nodes[0].querywhitelist(node1addr)
        except JSONRPCException as e:
            print(e.error['message'])
            assert(False)
        assert(iswl)


        keypool=100
        nwhitelisted=keypool

        #Send some tokens to node 1
        ntosend=10.234
        self.nodes[0].sendtoaddress(node1addr, ntosend, "", "", False, "CBT")

        self.nodes[0].generate(101)
        self.sync_all()

        bal1=self.nodes[1].getwalletinfo()["balance"]["CBT"]


        assert_equal(float(bal1),float(ntosend))

        #Restart the nodes. The whitelist will be restored. TODO
        wl1file=self.initfile("wl1.dat")
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
        saveres=self.nodes[1].sendaddtowhitelisttx(nadd,"CBT")
        time.sleep(5)
        self.nodes[0].generate(101)
        self.sync_all()
        nwhitelisted+=nadd
        wl1file_2=self.initfile("wl1_2.dat")
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
        wl1file_3=self.initfile("wl1_3.dat")
        self.nodes[1].dumpwhitelist(wl1file_3)
        nlines3=self.linecount(wl1file_3)
        assert_equal(nlines3-nlines2, 3*nadd)

        clientAddress1=self.nodes[1].validateaddress(self.nodes[1].getnewaddress())
        clientAddress2=self.nodes[1].validateaddress(self.nodes[1].getnewaddress())
        clientAddress3=self.nodes[1].validateaddress(self.nodes[1].getnewaddress())
        clientAddress4=self.nodes[1].validateaddress(self.nodes[1].getnewaddress())

        #Creating a p2sh address for whitelisting
        multiAddress2=self.nodes[1].createmultisig(2,[clientAddress2['pubkey'],clientAddress3['pubkey'],clientAddress4['pubkey']])

        #Testing Multisig whitelisting registeraddress transaction
        multitx = self.nodes[1].sendaddmultitowhitelisttx(multiAddress2['address'],[clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey'],clientAddress4['derivedpubkey']],2,"CBT")

        time.sleep(5)
        self.nodes[0].generate(101)
        self.sync_all()
        nwhitelisted+=1
        time.sleep(1)
        wl1file_4=self.initfile("wl1_4.dat")
        self.nodes[1].dumpwhitelist(wl1file_4)
        nlines4=self.linecount(wl1file_4)
        assert_equal(nlines3+1, nlines4)

        try:
            iswl=self.nodes[1].querywhitelist(multiAddress2['address'])
        except JSONRPCException as e:
            print(e.error['message'])
            assert(False)
        assert(iswl)

        result = self.nodes[1].importmulti([{
            "scriptPubKey": {
                "address": multiAddress2['address']
            },
            "timestamp": "now",
            "redeemscript": multiAddress2['redeemScript'],
            "keys": [ self.nodes[1].dumpprivkey(clientAddress2['unconfidential']), self.nodes[1].dumpprivkey(clientAddress3['unconfidential']), self.nodes[1].dumpprivkey(clientAddress4['unconfidential'])]
        }])

        vaddr = self.nodes[1].validateaddress(multiAddress2['address'])

        assert(vaddr['ismine'])

        issue = self.nodes[0].issueasset('100.0','0')
        self.nodes[1].generate(1)
        self.sync_all()

        txhead = self.nodes[0].sendtoaddress(multiAddress2['address'], 11,"","",False,issue["asset"])
        self.nodes[0].generate(101)
        self.sync_all()
        try:
            rawtxm = self.nodes[2].getrawtransaction(txhead, 1)
            rawtxm2 = self.nodes[0].getrawtransaction(txhead, 1)
        except JSONRPCException as e:
            print(e)
            assert(False)

        assert_equal(self.nodes[0].getbalance("", 0, False, issue["asset"]), 100-11)
        assert_equal(self.nodes[1].getbalance("", 0, False, issue["asset"]), 11)

        multiAddress1=self.nodes[1].createmultisig(2,[clientAddress1['pubkey'],clientAddress2['pubkey'],clientAddress3['pubkey']])

        wl1file=self.initfile("wl1.dat")
        self.nodes[1].dumpwhitelist(wl1file)

        kycpubkey=self.nodes[0].getkycpubkey(self.nodes[1].getnewaddress())

        #Adding the created p2sh to the whitelist via addmultitowhitelist rpc
        self.nodes[1].addmultitowhitelist(multiAddress1['address'],[clientAddress1['derivedpubkey'],clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey']],2,kycpubkey)
        nwhitelisted+=1
        wl1file_2=self.initfile("wl1_2.dat")
        self.nodes[1].dumpwhitelist(wl1file_2)
        nlines1=self.linecount(wl1file)
        nlines2=self.linecount(wl1file_2)
        assert_equal(nlines1+1,nlines2)

        try:
            iswl=self.nodes[1].querywhitelist(multiAddress1['address'])
        except JSONRPCException as e:
            print(e.error['message'])
            assert(False)
        assert(iswl)

        if(clientAddress1['pubkey'] == clientAddress1['derivedpubkey']):
            raise AssertionError("Pubkey and derived pubkey are the same for a new address. Either tweaking failed or the contract is not valid/existing.")
        try:
            multiAddress2=self.nodes[1].createmultisig(2,["asdasdasdasdasdas",clientAddress2['pubkey'],clientAddress4['pubkey']])
            self.nodes[1].addmultitowhitelist(multiAddress2['address'],[clientAddress1['derivedpubkey'],clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey']],2,kycpubkey)
        except JSONRPCException as e:
            assert("Invalid public key: asdasdasdasdasdas" in e.error['message'])
        else:
            raise AssertionError("P2SH multisig with an invalid first pubkey has been validated and accepted to the whitelist.")

        try:
            self.nodes[1].addmultitowhitelist("XKyFz4ezBfJPyeCuQNmDGZhF77m9PF1Jv2",[clientAddress1['derivedpubkey'],clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey']],2,kycpubkey)
        except JSONRPCException as e:
            assert("invalid Bitcoin address: XKyFz4ezBfJPyeCuQNmDGZhF77m9PF1Jv2" in e.error['message'])
        else:
            raise AssertionError("P2SH multisig with an invalid address has been validated and accepted to the whitelist.")

        try:
            multiAddress2=self.nodes[1].createmultisig(2,[clientAddress1['pubkey'],clientAddress2['pubkey'],clientAddress4['pubkey']])
            self.nodes[1].addmultitowhitelist(multiAddress2['address'],[clientAddress1['derivedpubkey'],clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey']],2,kycpubkey)
        except JSONRPCException as e:
            assert("add_multisig_whitelist: address does not derive from public keys when tweaked with contract hash" in e.error['message'])
        else:
            raise AssertionError("P2SH multisig with a different third pubkey has been validated and accepted to the whitelist.")

        try:
            multiAddress2=self.nodes[1].createmultisig(2,[clientAddress1['pubkey'],clientAddress2['pubkey'],clientAddress3['derivedpubkey']])
            self.nodes[1].addmultitowhitelist(multiAddress2['address'],[clientAddress1['derivedpubkey'],clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey']],2,kycpubkey)
        except JSONRPCException as e:
            assert("add_multisig_whitelist: address does not derive from public keys when tweaked with contract hash" in e.error['message'])
        else:
            raise AssertionError("P2SH multisig with an untweaked third pubkey has been validated and accepted to the whitelist.")

        try:
            multiAddress2=self.nodes[1].createmultisig(2,[clientAddress1['pubkey'],clientAddress2['pubkey'],clientAddress3['pubkey'],clientAddress4['pubkey']])
            self.nodes[1].addmultitowhitelist(multiAddress2['address'],[clientAddress1['derivedpubkey'],clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey']],2,kycpubkey)
        except JSONRPCException as e:
            assert("add_multisig_whitelist: address does not derive from public keys when tweaked with contract hash" in e.error['message'])
        else:
            raise AssertionError("P2SH multisig with more pubkeys in redeem script than rpc has been validated and accepted to the whitelist.")

        try:
            multiAddress2=self.nodes[1].createmultisig(4,[clientAddress1['pubkey'],clientAddress2['pubkey'],clientAddress4['pubkey']])
            self.nodes[1].addmultitowhitelist(multiAddress2['address'],[clientAddress1['derivedpubkey'],clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey']],2,kycpubkey)
        except JSONRPCException as e:
            assert("not enough keys supplied (got 3 keys, but need at least 4 to redeem)" in e.error['message'])
        else:
            raise AssertionError("P2SH multisig with n > m has been validated and accepted to the whitelist.")

        try:
            multiAddress2=self.nodes[1].createmultisig(0,[clientAddress1['pubkey'],clientAddress2['pubkey'],clientAddress3['pubkey']])
            self.nodes[1].addmultitowhitelist(multiAddress2['address'],[clientAddress1['derivedpubkey'],clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey']],2,kycpubkey)
        except JSONRPCException as e:
            assert("a multisignature address must require at least one key to redeem" in e.error['message'])
        else:
            raise AssertionError("P2SH multisig with n=0 has been validated and accepted to the whitelist.")


        wl1_file=self.initfile("wl1.dat")
        self.nodes[1].dumpwhitelist(wl1_file)

        #Get kyc pubkey for node1 from node1 and node0
        addr1=self.nodes[1].getnewaddress()
        kycpub1=self.nodes[0].getkycpubkey(addr1)
        assert_equal(kycpub1, self.nodes[1].getkycpubkey(addr1))

        #Blacklist node1 wallet
        self.nodes[0].blacklistkycpubkey(kycpub1)

        self.nodes[0].generate(101)
        self.sync_all()

        wl1_bl_file=self.initfile("wl1_bl.dat")
        self.nodes[1].dumpwhitelist(wl1_bl_file)

        #The whitelist should now be empty
        nlines=self.linecount(wl1_file)
        nlines_bl=self.linecount(wl1_bl_file)

        assert_equal(nlines-nlines_bl,nwhitelisted)

        #Re-whitelist node1 wallet
        kycpubkeyarr=[kycpub1]
        self.nodes[0].whitelistkycpubkeys(kycpubkeyarr)

        self.nodes[0].generate(101)
        self.sync_all()

        wl1file_rwl=self.initfile("wl1_rwl.dat")
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


        #assert whitelist file are the same for the two nodes
        wl0file=self.initfile(self.options.tmpdir+"wl0.dat")
        self.nodes[0].dumpwhitelist(wl0file)

        wl2file=self.initfile(self.options.tmpdir+"wl2.dat")
        self.nodes[2].dumpwhitelist(wl2file)

        assert(filecmp.cmp(wl0file, wl2file))

        with open(wl0file, 'r') as fin0, open(wl2file, 'r') as fin2:
            lines0=fin0.readlines()
            lines2=fin2.readlines()

            set0=set(lines0)
            set2=set(lines2)

            len0=len(set0)
            len2=len(set2)


            assert(len0 == len2)

            diff0=set0.difference(set2)
            diff2=set2.difference(set0)

            lendiff0 = len(diff0)
            lendiff2 = len(diff2)

            assert(lendiff0 == 0)
            assert(lendiff2 == 0)
                

        self.cleanup_files()
        return

if __name__ == '__main__':
 OnboardTest().main()

#  LocalWords:  ac
