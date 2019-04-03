#!/usr/bin/env python3
# Copyright (c) 2014-2016 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *

class WhitelistingTest (BitcoinTestFramework):

    def __init__(self):
        super().__init__()
        self.setup_clean_chain = True
        self.num_nodes = 4
        self.extra_args = [['-usehd={:d}'.format(i%2==0), '-keypool=100'] for i in range(self.num_nodes)]
#Node 1 is a whitelist node. 
        self.extra_args[0].append("-pkhwhitelist=1")
        self.extra_args[1].append("-pkhwhitelist=1")

#Add keys from 'from_node' to the whitelist on 'whitelist_node'
    def add_keys_to_whitelist(self,from_node, whitelist_node):
        keys=from_node.getderivedkeys()
        addresses=keys['address']
        bpubkeys=keys['bpubkey']
        for i in range(len(addresses)):
            whitelist_node.addtowhitelist(addresses[i], bpubkeys[i])


#Add keys from 'from_node' to the whitelist on 'whitelist_node' by dumping to a file and then reading it
    def add_keys_to_whitelist_from_dumpfile(self,from_node, whitelist_node, filename):
        dumpfile_name=self.options.tmpdir + filename
        from_node.dumpderivedkeys(dumpfile_name)
        whitelist_node.readwhitelist(dumpfile_name)
     
    def setup_network(self, split=False):
        self.nodes = start_nodes(self.num_nodes, self.options.tmpdir, self.extra_args[:self.num_nodes])
        #Block signing node -- whitelist node -- client node
        connect_nodes_bi(self.nodes,0,1)
        connect_nodes_bi(self.nodes,1,2)
        connect_nodes_bi(self.nodes,1,3)
        connect_nodes_bi(self.nodes,2,3)
        self.is_network_split=False
        self.sync_all()

    def clear_whitelists(self):
        for node in self.nodes:
            node.clearwhitelist()

    #Count number of lines in file, removing commented and blank lines 
    def num_keys_in_file(self, fname):
        num_keys=0
        for line in open(fname):
            li=line.strip()
            #The tweaked public addresses start with 2d
            if li.startswith('2d'):
                num_keys=num_keys+1
        return num_keys

    def run_test (self):
        self.clear_whitelists()
        self.add_keys_to_whitelist(self.nodes[0], self.nodes[0])
        fname = self.options.tmpdir + 'node0whitelist'
        self.nodes[0].dumpwhitelist(fname)
        num_keys=self.num_keys_in_file(fname)
        assert_equal(num_keys,100)
        self.add_keys_to_whitelist(self.nodes[1], self.nodes[1])
        fname = self.options.tmpdir + 'node1whitelist'
        self.nodes[1].dumpwhitelist(fname)
        num_keys=self.num_keys_in_file(fname)
        assert_equal(num_keys,100)
        #dumo derived keys to file and validate 
        fname = self.options.tmpdir + 'node1derived'
        self.nodes[1].dumpderivedkeys(fname)
        self.nodes[1].validatederivedkeys(fname)
        #add in invalid key/addesss pair to the file and validate again 
        a_key='11caPoYB9NbtcG6cMAk5j3dPF2eFaD483'
        a_key_address_invalid='03c8847ab88a1a207ea74356a53f858535ebd3f3f5499f7da1ec5dad00d2adbcbe'
        with open(fname, 'a') as myfile:
            myfile.write(a_key + " " + a_key_address_invalid)
        #expect a invalid key id error
        try:
            self.nodes[1].validatederivedkeys(fname)
        except JSONRPCException as e:
            assert("Invalid key id" in e.error['message'])
          
        # Check that there's 100 UTXOs on each of the nodes
        assert_equal(len(self.nodes[0].listunspent()), 100)
        assert_equal(len(self.nodes[1].listunspent()), 100)
        assert_equal(len(self.nodes[2].listunspent()), 100)

        print("Before mining blocks - balance = 21000000")
        walletinfo = self.nodes[0].getwalletinfo()
        assert_equal(walletinfo['balance']["CBT"], 21000000)

        print("Mining blocks...")
        self.nodes[1].generate(101)
        self.sync_all()

        print("Check balances")
        for i in range(len(self.nodes)):
            assert_equal(self.nodes[i].getbalance("", 0, False, "CBT"), 21000000)

        #Set all OP_TRUE genesis outputs to the signing node
        print("Set all the OP_TRUE genesis outputs to a single node.")
        self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), 21000000, "", "", True)
        self.nodes[0].generate(101)
        self.sync_all()

        print("Check balance - now node0 should have 21000000, others should have 0.")
        #Check signing node.
        assert_equal(self.nodes[0].getbalance("", 0, False, "CBT"), 21000000)
        #Check the rest of the nodes.
        for i in range(len(self.nodes)):
            if(i==0):
                continue
            assert_equal(self.nodes[i].getbalance("", 0, False, "CBT"), 0)
       
        # issue some new asset (that is not the policy asset)
        issue = self.nodes[0].issueasset('100.0','0')
        self.nodes[1].generate(1)

        # Send 21 issued asset from 0 to 2 using sendtoaddress. Will fail to create mempool transaction because recipient addresses not whitelisted.
        print(self.nodes[0].getwalletinfo())
        print("Sending 21 issued asset from 0 to 2 using sendtoaddress.")
        txid1 = self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 11,"","",False,issue["asset"])
        txout1v0 = self.nodes[0].gettxout(txid1, 0)
        self.nodes[1].generate(101)
        self.sync_all()
        try:
            rawtx1 = self.nodes[1].getrawtransaction(txid1, 1)
            print("Raw trans:")
            print(rawtx1)
        except JSONRPCException as e:
            assert("No such mempool transaction" in e.error['message'])
            #Abandon the transaction to allow the output to be respent
            self.nodes[0].abandontransaction(txid1)
        else:
            raise AssertionError("Output accepted to non-whitelisted address.")


        txid2 = self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 10,"","",False,issue["asset"])
        txout2v0 = self.nodes[0].gettxout(txid2, 0)
        self.nodes[1].generate(101)
        self.sync_all()
        try:
            rawtx2 = self.nodes[1].getrawtransaction(txid2, 1)
        except JSONRPCException as e:
            assert("No such mempool transaction" in e.error['message'])
            #Abandon the transaction to allow the output to be respent
            self.nodes[0].abandontransaction(txid2)
        else:
            raise AssertionError("Output accepted to non-whitelisted address.")

        #query whitelist
        node2_test_address = self.nodes[2].getnewaddress()
        
        assert_equal(self.nodes[0].querywhitelist(node2_test_address), False)
        #add node2 to whitelist
        self.add_keys_to_whitelist(self.nodes[2], self.nodes[0])
        self.add_keys_to_whitelist(self.nodes[2], self.nodes[1])
        #query whitelist
        node2_test_address = self.nodes[2].getnewaddress()
        print(node2_test_address)
        assert_equal(self.nodes[0].querywhitelist(node2_test_address), True)
        #remove an address from the whitelist
        self.nodes[0].removefromwhitelist(node2_test_address)
        #address no longer in whitelist
        assert_equal(self.nodes[0].querywhitelist(node2_test_address), False)
        #next available address still in whitelist
        assert_equal(self.nodes[0].querywhitelist(self.nodes[2].getnewaddress()), True)
        
        # Send 21 BTC from 0 to 2 using sendtoaddress
        print("Sending 21 issued asset from 0 to 2 using sendtoaddress")
        print(self.nodes[0].getwalletinfo())
        txid1 = self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 11,"","",False,issue["asset"])
        txout1v0 = self.nodes[0].gettxout(txid1, 0)
        rawtx1 = self.nodes[0].getrawtransaction(txid1, 1)
        #amountcommit1 = rawtx1["vout"][0]["amountcommitment"]
        assert_equal(txout1v0['confirmations'], 0)
        assert(not txout1v0['coinbase'])
        #assert_equal(amountcommit1, txout1v0['amountcommitment'])


        txid2 = self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 10,"","",False,issue["asset"])
        txout2v0 = self.nodes[0].gettxout(txid2, 0)
        rawtx2 = self.nodes[0].getrawtransaction(txid2, 1)
        #amountcommit2 = rawtx2["vout"][0]["amountcommitment"]
        assert_equal(txout2v0['confirmations'], 0)
        assert(not txout2v0['coinbase'])
        #assert_equal(amountcommit2, txout2v0['amountcommitment'])

        walletinfo = self.nodes[0].getwalletinfo(issue["asset"])
        assert_equal(walletinfo['immature_balance'], 0)

        # Have node1 mine 101 blocks
        self.nodes[0].generate(101)
        self.sync_all()

        assert_equal(self.nodes[0].getbalance("", 0, False, issue["asset"]), 100-21)
        assert_equal(self.nodes[2].getbalance("", 0, False, issue["asset"]), 21)


        #check that dumpwhitelist dumps the correct number of keys
        fname = self.options.tmpdir + 'node0whitelist'
        self.nodes[0].dumpwhitelist(fname)
        num_keys=self.num_keys_in_file(fname)
        #expected N_keys is 199 because one key was removed using removekey
        assert_equal(num_keys, 199)

        #clear whitelists and check number of keys in wl = 0 and that we cannot send to previously whitelisted address 
        self.clear_whitelists()
        self.nodes[0].dumpwhitelist(fname)
        num_keys=num_keys=self.num_keys_in_file(fname)
        assert_equal(num_keys, 0)
        print(self.nodes[0].getwalletinfo("CBT"))
        print("Sending 21 BTC from 0 to 2 using sendtoaddress.")
        txid1 = self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 11,"","",False,issue["asset"])
        txout1v0 = self.nodes[0].gettxout(txid1, 0)
        try:
            rawtx1 = self.nodes[0].getrawtransaction(txid1, 1)
            print(rawtx1)
        except JSONRPCException as e:
            assert("No such mempool transaction" in e.error['message'])
            #Abandon the transaction to allow the output to be respent
            self.nodes[0].abandontransaction(txid1)
        else:
            raise AssertionError("Output accepted to non-whitelisted address.")

        txid2 = self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 10,"","",False,issue["asset"])
        txout2v0 = self.nodes[0].gettxout(txid2, 0)
        try:
            rawtx2 = self.nodes[0].getrawtransaction(txid2, 1)
        except JSONRPCException as e:
            assert("No such mempool transaction" in e.error['message'])
            #Abandon the transaction to allow the output to be respent
            self.nodes[0].abandontransaction(txid2)
        else:
            raise AssertionError("Output accepted to non-whitelisted address.")

        #add node2 to whitelist from file dump and try sending coins again
#        self.add_keys_to_whitelist_from_dumpfile(self.nodes[2], self.nodes[0], 'keys20')
#        self.add_keys_to_whitelist_from_dumpfile(self.nodes[2], self.nodes[1], 'keys21')
        self.add_keys_to_whitelist(self.nodes[0], self.nodes[0])
        self.add_keys_to_whitelist(self.nodes[1], self.nodes[1])
        self.add_keys_to_whitelist(self.nodes[2], self.nodes[0])
        self.add_keys_to_whitelist(self.nodes[2], self.nodes[1])

        # Send 21 BTC from 0 to 2 using sendtoaddress
        print("Sending 21 BTC from 0 to 2 using sendtoaddress")
        print(self.nodes[0].getwalletinfo("CBT"))
        txid1 = self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 11,"","",False,issue["asset"])
        txout1v0 = self.nodes[0].gettxout(txid1, 0)
        rawtx1 = self.nodes[0].getrawtransaction(txid1, 1)
        #amountcommit1 = rawtx1["vout"][0]["amountcommitment"]
        assert_equal(txout1v0['confirmations'], 0)
        assert(not txout1v0['coinbase'])
        #assert_equal(amountcommit1, txout1v0['amountcommitment'])


        txid2 = self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 10,"","",False,issue["asset"])
        txout2v0 = self.nodes[0].gettxout(txid2, 0)
        rawtx2 = self.nodes[0].getrawtransaction(txid2, 1)
        #amountcommit2 = rawtx2["vout"][0]["amountcommitment"]
        assert_equal(txout2v0['confirmations'], 0)
        assert(not txout2v0['coinbase'])
        #assert_equal(amountcommit2, txout2v0['amountcommitment'])

        walletinfo = self.nodes[0].getwalletinfo("CBT")
        assert_equal(walletinfo['immature_balance'], 0)

        # Have node1 mine 101 blocks
        self.nodes[0].generate(101)
        self.sync_all()

        assert_equal(self.nodes[0].getbalance("", 0, False, issue["asset"]), 100-42)
        assert_equal(self.nodes[2].getbalance("", 0, False, issue["asset"]), 42)

        print("End.")

if __name__ == '__main__':
    WhitelistingTest().main()
