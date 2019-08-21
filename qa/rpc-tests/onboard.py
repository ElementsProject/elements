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
        self.extra_args[0].append("-pkhwhitelist-encrypt=0")
        self.extra_args[0].append("-rescan=1")
        self.extra_args[0].append("-reindex-chainstate=1")
        self.extra_args[0].append("-initialfreecoins=2100000000000000")
        self.extra_args[0].append("-policycoins=50000000000000")
        self.extra_args[0].append("-regtest=0")
        self.extra_args[0].append("-initialfreecoinsdestination=76a914b87ed64e2613422571747f5d968fff29a466e24e88ac")
        self.extra_args[0].append("-issuancecoinsdestination=76a914df4439eb1a54b3a91d71979a0bb5b3f5971ff44c88ac")
        self.extra_args[0].append("-freezelistcoinsdestination=76a91474168445da07d331faabd943422653dbe19321cd88ac")
        self.extra_args[0].append("-burnlistcoinsdestination=76a9142166a4cd304b86db7dfbbc7309131fb0c4b645cd88ac")
        self.extra_args[0].append("-whitelistcoinsdestination=76a914427bf8530a3962ed77fd3c07d17fd466cb31c2fd88ac")
        self.extra_args[1].append("-rescan=1")
        self.extra_args[1].append("-reindex-chainstate=1")
        self.extra_args[1].append("-regtest=0")
        self.extra_args[1].append("-pkhwhitelist=1")
        self.extra_args[1].append("-pkhwhitelist-encrypt=0")
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
        self.extra_args[2].append("-pkhwhitelist-encrypt=0")
        self.extra_args[2].append("-rescan=1")
        self.extra_args[2].append("-reindex-chainstate=1")
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
        #Start nodes
        self.nodes = start_nodes(3, self.options.tmpdir, self.extra_args[:3])
        time.sleep(5)
        connect_nodes_bi(self.nodes,0,1)
        connect_nodes_bi(self.nodes,1,2)
        connect_nodes_bi(self.nodes,0,2)
        self.is_network_split=split
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
        keypool=100
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


        #Initial WHITELIST token balance
        wb0_0=float(self.nodes[0].getbalance("", 1, False, "WHITELIST"))
        coin=float(1e8)
        assert_equal(wb0_0*coin,float(50000000000000))
                    
        #No kycpubkeys available
        kycfile=self.initfile(os.path.join(self.options.tmpdir,"kycfile.dat"))
        try:
            userOnboardPubKey=self.nodes[1].dumpkycfile(kycfile)
        except JSONRPCException as e:
            assert("No unassigned KYC public keys available" in e.error['message'])

        #Register a KYC public key
        self.nodes[0].topupkycpubkeys(1)
        self.nodes[0].generate(101)
        self.sync_all()
        time.sleep(5)

        wb0_1=float(self.nodes[0].getbalance("", 1, False, "WHITELIST"))
        assert_equal(wb0_1*coin,float(50000000000000-1))
        
        #Dump empty whitelist
        wl1file_empty=self.initfile(os.path.join(self.options.tmpdir,"wl1_empty.dat"))
        self.nodes[1].dumpwhitelist(wl1file_empty)

        #Onboard node0
        kycfile0=self.initfile(os.path.join(self.options.tmpdir,"kycfile0.dat"))
        userOnboardPubKey=self.nodes[0].dumpkycfile(kycfile0)
        self.nodes[0].onboarduser(kycfile0)
        self.nodes[0].generate(101)
        self.sync_all()
        
        wl1file=self.initfile(os.path.join(self.options.tmpdir,"wl1.dat"))
        self.nodes[1].dumpwhitelist(wl1file)
        nlines=self.linecount(wl1file)
        nlines_empty=self.linecount(wl1file_empty)
        assert_equal(nlines-nlines_empty,keypool)


        #Onboard node1
        userOnboardPubKey=self.nodes[1].dumpkycfile(kycfile)
        kycfile_plain=self.initfile(os.path.join(self.options.tmpdir,"kycfile_plain.dat"))
        self.nodes[0].readkycfile(kycfile, kycfile_plain)        

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

        self.nodes[1].dumpwhitelist(wl1file)
        nlines=self.linecount(wl1file)
        assert_equal(nlines-nlines_empty,2*keypool)
        
        node1addr=self.nodes[1].getnewaddress()

        try:
            iswl=self.nodes[0].querywhitelist(node1addr)
        except JSONRPCException as e:
            print(e.error['message'])
            assert(False)
        assert(iswl)

        
        #Send some tokens to node 1
        ntosend=10.234
        self.nodes[0].sendtoaddress(node1addr, ntosend, "", "", False, "CBT")
        self.nodes[0].generate(101)
        self.sync_all()


        bal1=self.nodes[1].getwalletinfo()["balance"]["CBT"]

        assert_equal(float(bal1),float(ntosend))

        #Restart one of the nodes. The whitelist will be restored.
        wl1file_rs1=self.initfile(os.path.join(self.options.tmpdir,"wl1_rs1.dat"))
        self.nodes[1].dumpwhitelist(wl1file_rs1)
        time.sleep(5)
        ntries=10
        success=True
        for ntry in range(ntries):
            try:
                stop_node(self.nodes[1],1)
            except ConnectionResetError as e:
                success=False
            except ConnectionRefusedError as e:
                success=False
            time.sleep(5)
            if success is True:
                break
        for ntry in range(ntries):
            try:
                success=True
                self.nodes[1] = start_node(1, self.options.tmpdir, self.extra_args[1])
            except Exception as e:
                success=False
                assert(e.args[0] == str('bitcoind exited with status -6 during initialization'))
                stop_node(self.nodes[1],1)
                time.sleep(5)
            if success is True:
                break
        time.sleep(5)
        connect_nodes_bi(self.nodes,0,1)
        connect_nodes_bi(self.nodes,1,2)
        time.sleep(5)
        wl1file_rs2=self.initfile(os.path.join(self.options.tmpdir,"wl1_rs2.dat"))
        self.nodes[1].dumpwhitelist(wl1file_rs2)
        assert(filecmp.cmp(wl1file_rs1, wl1file_rs2))

        self.nodes[1].dumpwhitelist(wl1file)
                
        #Node 1 registers additional addresses to whitelist
        nadd=100
        try:
            saveres=self.nodes[1].sendaddtowhitelisttx(nadd,"CBT")
        except JSONRPCException as e:            
            assert("Not implemented for unencrypted whitelist" in e.error['message'])


        clientAddress1=self.nodes[1].validateaddress(self.nodes[1].getnewaddress())
        clientAddress2=self.nodes[1].validateaddress(self.nodes[1].getnewaddress())
        clientAddress3=self.nodes[1].validateaddress(self.nodes[1].getnewaddress())
        clientAddress4=self.nodes[1].validateaddress(self.nodes[1].getnewaddress())

        #Creating a p2sh address for whitelisting
        multiAddress2=self.nodes[1].createmultisig(2,[clientAddress2['pubkey'],clientAddress3['pubkey'],clientAddress4['pubkey']])

                
        #Testing Multisig whitelisting registeraddress transaction
        try:
            multitx = self.nodes[1].sendaddmultitowhitelisttx(multiAddress2['address'],[clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey'],clientAddress4['derivedpubkey']],2,"CBT")
        except JSONRPCException as e:
            assert("Not implemented for unencrypted whitelist" in e.error['message'])

            
        time.sleep(5)
        self.nodes[0].generate(101)
        self.sync_all()
        time.sleep(1)
        wl1file_2=self.initfile(os.path.join(self.options.tmpdir,"wl1_2.dat"))
        self.nodes[1].dumpwhitelist(wl1file_2)
        nlines2=self.linecount(wl1file_2)
        assert_equal(nlines, nlines2)

        try:
            iswl=self.nodes[0].querywhitelist(multiAddress2['address'])
        except JSONRPCException as e:
            print(e.error['message'])
            assert(False)
        assert(iswl == False)

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

        multiAddress1=self.nodes[1].createmultisig(2,[clientAddress1['pubkey'],clientAddress2['pubkey'],clientAddress3['pubkey']])

        self.nodes[1].dumpwhitelist(wl1file)

        try:
            self.nodes[0].getkycpubkey(self.nodes[1].getnewaddress())
        except JSONRPCException as e:
            assert("Not implemented for unencrypted whitelist" in e.error['message'])

        #Adding the created p2sh to the whitelist via addmultitowhitelist rpc
        try:
            self.nodes[1].addmultitowhitelist(multiAddress1['address'],[clientAddress1['derivedpubkey'],clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey']],2,"")
        except JSONRPCException as e:
            assert("kycaddress argument not implemented for unencrypted whitelist" in e.error['message'])

            
        #Manual whitelisting - not via blockchain - manually added to all nodes.
        self.nodes[0].addmultitowhitelist(multiAddress1['address'],[clientAddress1['derivedpubkey'],clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey']],2)
        self.nodes[1].addmultitowhitelist(multiAddress1['address'],[clientAddress1['derivedpubkey'],clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey']],2)
        self.nodes[2].addmultitowhitelist(multiAddress1['address'],[clientAddress1['derivedpubkey'],clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey']],2)

        
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

        
#        self.nodes[0].removefromwhitelist(multiAddress1['address'])
#        self.nodes[1].removefromwhitelist(multiAddress1['address'])
#        self.nodes[2].removefromwhitelist(multiAddress1['address'])

#        wl1file_3=self.initfile(os.path.join(self.options.tmpdir,"wl1_3.dat"))
#        self.nodes[1].dumpwhitelist(wl1file_3)
#        nlines3=self.linecount(wl1file_3)
#        assert_equal(nlines1,nlines3)
                
#        try:
#            iswl=self.nodes[1].querywhitelist(multiAddress1['address'])
#        except JSONRPCException as e:
#            print(e.error['message'])
#            assert(False)
#        assert(iswl == False)

        if(clientAddress1['pubkey'] == clientAddress1['derivedpubkey']):
            raise AssertionError("Pubkey and derived pubkey are the same for a new address. Either tweaking failed or the contract is not valid/existing.")
        try:
            multiAddress2=self.nodes[1].createmultisig(2,["asdasdasdasdasdas",clientAddress2['pubkey'],clientAddress4['pubkey']])
            self.nodes[1].addmultitowhitelist(multiAddress2['address'],[clientAddress1['derivedpubkey'],clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey']],2)
        except JSONRPCException as e:
            assert("Invalid public key: asdasdasdasdasdas" in e.error['message'])
        else:
            raise AssertionError("P2SH multisig with an invalid first pubkey has been validated and accepted to the whitelist.")

        try:
            self.nodes[1].addmultitowhitelist("XKyFz4ezBfJPyeCuQNmDGZhF77m9PF1Jv2",[clientAddress1['derivedpubkey'],clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey']],2)
        except JSONRPCException as e:
            assert("invalid Bitcoin address: XKyFz4ezBfJPyeCuQNmDGZhF77m9PF1Jv2" in e.error['message'])
        else:
            raise AssertionError("P2SH multisig with an invalid address has been validated and accepted to the whitelist.")

        try:
            multiAddress2=self.nodes[1].createmultisig(2,[clientAddress1['pubkey'],clientAddress2['pubkey'],clientAddress4['pubkey']])
            self.nodes[1].addmultitowhitelist(multiAddress2['address'],[clientAddress1['derivedpubkey'],clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey']],2)
        except JSONRPCException as e:
            assert("add_multisig_whitelist: address does not derive from public keys when tweaked with contract hash" in e.error['message'])
        else:
            raise AssertionError("P2SH multisig with a different third pubkey has been validated and accepted to the whitelist.")

        try:
            multiAddress2=self.nodes[1].createmultisig(2,[clientAddress1['pubkey'],clientAddress2['pubkey'],clientAddress3['derivedpubkey']])
            self.nodes[1].addmultitowhitelist(multiAddress2['address'],[clientAddress1['derivedpubkey'],clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey']],2)
        except JSONRPCException as e:
            assert("add_multisig_whitelist: address does not derive from public keys when tweaked with contract hash" in e.error['message'])
        else:
            raise AssertionError("P2SH multisig with an untweaked third pubkey has been validated and accepted to the whitelist.")

        try:
            multiAddress2=self.nodes[1].createmultisig(2,[clientAddress1['pubkey'],clientAddress2['pubkey'],clientAddress3['pubkey'],clientAddress4['pubkey']])
            self.nodes[1].addmultitowhitelist(multiAddress2['address'],[clientAddress1['derivedpubkey'],clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey']],2)
        except JSONRPCException as e:
            assert("add_multisig_whitelist: address does not derive from public keys when tweaked with contract hash" in e.error['message'])
        else:
            raise AssertionError("P2SH multisig with more pubkeys in redeem script than rpc has been validated and accepted to the whitelist.")

        try:
            multiAddress2=self.nodes[1].createmultisig(4,[clientAddress1['pubkey'],clientAddress2['pubkey'],clientAddress4['pubkey']])
            self.nodes[1].addmultitowhitelist(multiAddress2['address'],[clientAddress1['derivedpubkey'],clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey']],2)
        except JSONRPCException as e:
            assert("not enough keys supplied (got 3 keys, but need at least 4 to redeem)" in e.error['message'])
        else:
            raise AssertionError("P2SH multisig with n > m has been validated and accepted to the whitelist.")

        try:
            multiAddress2=self.nodes[1].createmultisig(0,[clientAddress1['pubkey'],clientAddress2['pubkey'],clientAddress3['pubkey']])
            self.nodes[1].addmultitowhitelist(multiAddress2['address'],[clientAddress1['derivedpubkey'],clientAddress2['derivedpubkey'],clientAddress3['derivedpubkey']],2)
        except JSONRPCException as e:
            assert("a multisignature address must require at least one key to redeem" in e.error['message'])
        else:
            raise AssertionError("P2SH multisig with n=0 has been validated and accepted to the whitelist.")

        # issue some new asset (that is not the policy asset)
        issue = self.nodes[0].issueasset('100.0','0')
        self.nodes[1].generate(1)

        nonPolicyAddress1=self.nodes[1].validateaddress(self.nodes[1].getnewaddress())
        nonPolicyAddress2=self.nodes[1].validateaddress(self.nodes[1].getnewaddress())
        nonPolicyAddress3=self.nodes[1].validateaddress(self.nodes[1].getnewaddress())

        multiAddr = self.nodes[1].createmultisig(2,[nonPolicyAddress1['pubkey'],nonPolicyAddress2['pubkey'],nonPolicyAddress3['pubkey']])

        result = self.nodes[1].importmulti([{
            "scriptPubKey": {
                "address": multiAddr['address']
            },
            "timestamp": "now",
            "redeemscript": multiAddr['redeemScript'],
            "keys": [ self.nodes[1].dumpprivkey(nonPolicyAddress1['unconfidential']), self.nodes[1].dumpprivkey(nonPolicyAddress2['unconfidential']), self.nodes[1].dumpprivkey(nonPolicyAddress3['unconfidential'])]
        }])

        # Send 12 issued asset from 0 to 1 using sendtoaddress. Will fail to create mempool transaction because recipient addresses not whitelisted.
        txidm = self.nodes[0].sendtoaddress(multiAddr['address'], 12,"","",False,issue["asset"])
        self.nodes[1].generate(101)
        self.sync_all()

        try:
            rawtxm = self.nodes[1].getrawtransaction(txidm, 1)
        except JSONRPCException as e:
            assert("No such mempool or blockchain transaction. Use gettransaction for wallet transactions." in e.error['message'])
            #Abandon the transaction to allow the output to be respent
            self.nodes[0].abandontransaction(txidm)
        else:
            raise AssertionError("Output accepted to non-whitelisted address.")

        self.blacklist_test(kycfile, keypool)

        wb0_2=float(self.nodes[0].getbalance("", 1, False, "WHITELIST"))
        #Test that the onboard transaction does not spend and whitelist asset
        assert_equal(wb0_1, wb0_2)

        
        self.cleanup_files()
        return
    
    def blacklist_test(self, kycfile, keypool, toprint=""):
        print(toprint)
        #Blacklist node1 wallet
        wl1file_4=self.initfile(os.path.join(self.options.tmpdir,"wl1_4.dat"))
        self.nodes[1].dumpwhitelist(wl1file_4)
        nlines4=self.linecount(wl1file_4)

        self.nodes[0].blacklistuser(kycfile)
        self.nodes[0].generate(101)
        self.sync_all()

        wl1_bl_file=self.initfile(os.path.join(self.options.tmpdir,"wl1_bl.dat"))
        self.nodes[1].dumpwhitelist(wl1_bl_file)
        wl0_bl_file=self.initfile(os.path.join(self.options.tmpdir,"wl0_bl.dat"))
        self.nodes[1].dumpwhitelist(wl0_bl_file)

        #The whitelist should now be empty
        nlines_4=self.linecount(wl1file_4)
        nlines_bl=self.linecount(wl1_bl_file)
        nlines_0_bl=self.linecount(wl0_bl_file)

        assert_equal(nlines_4-nlines_0_bl,keypool)

        #Re-whitelist node1 wallet
        self.nodes[0].onboarduser(kycfile)

        self.nodes[0].generate(101)
        self.sync_all()

        wl1file_rwl=self.initfile(os.path.join(self.options.tmpdir,"wl1_rwl.dat"))
        self.nodes[1].dumpwhitelist(wl1file_rwl)
        nlines_rwl=self.linecount(wl1file_rwl)
        assert_equal(nlines_rwl, nlines_4)

        #assert whitelist file are the same for the two nodes
        wl0file=self.initfile(os.path.join(self.options.tmpdir,"wl0.dat"))
        self.nodes[0].dumpwhitelist(os.path.join(self.options.tmpdir,wl0file))

        wl2file=self.initfile(os.path.join(self.options.tmpdir,"wl2.dat"))
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


    
if __name__ == '__main__':
 OnboardTest().main()

#  LocalWords:  ac
