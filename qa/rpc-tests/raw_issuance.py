#!/usr/bin/env python3
# Copyright (c) 2018-19 CommerceBlock developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *

class RawIssuance (BitcoinTestFramework):

    def __init__(self):
        super().__init__()
        self.setup_clean_chain = True
        self.num_nodes = 4
        self.extra_args = [['-issuanceblock'] for i in range(4)]
        self.extra_args[0].append("-txindex")
        self.extra_args[0].append("-policycoins=50000000000000")
        self.extra_args[0].append("-issuancecoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac")
        self.extra_args[1].append("-txindex")
        self.extra_args[1].append("-policycoins=50000000000000")
        self.extra_args[1].append("-issuancecoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac")
        self.extra_args[2].append("-txindex")
        self.extra_args[2].append("-policycoins=50000000000000")
        self.extra_args[2].append("-issuancecoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac")

    def setup_network(self, split=False):
        self.nodes = start_nodes(3, self.options.tmpdir, self.extra_args[:3])
        connect_nodes_bi(self.nodes,0,1)
        connect_nodes_bi(self.nodes,1,2)
        connect_nodes_bi(self.nodes,0,2)
        self.is_network_split=False
        self.sync_all()

    def run_test (self):

        # Check that there's 100 UTXOs on each of the nodes
        assert_equal(len(self.nodes[0].listunspent()), 100)
        assert_equal(len(self.nodes[1].listunspent()), 100)
        assert_equal(len(self.nodes[2].listunspent()), 100)

        self.nodes[2].importprivkey("cTnxkovLhGbp7VRhMhGThYt8WDwviXgaVAD8DjaVa5G5DApwC6tF")

        walletinfo = self.nodes[2].getbalance()
        assert_equal(walletinfo["CBT"], 21000000)
        assert_equal(walletinfo["ISSUANCE"], 500000)

        print("Mining blocks...")
        self.nodes[1].generate(101)
        self.sync_all()

        asscript = "76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac";

        assert_equal(self.nodes[0].getbalance("", 0, False, "CBT"), 21000000)
        assert_equal(self.nodes[1].getbalance("", 0, False, "CBT"), 21000000)
        assert_equal(self.nodes[2].getbalance("", 0, False, "CBT"), 21000000)

        #Set all OP_TRUE genesis outputs to single node
        self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), 21000000, "", "", True)
        self.nodes[0].generate(6)
        self.sync_all()

        assert_equal(self.nodes[0].getbalance("", 0, False, "CBT"), 21000000)
        assert_equal(self.nodes[1].getbalance("", 0, False, "CBT"), 0)
        assert_equal(self.nodes[2].getbalance("", 0, False, "CBT"), 0)

        #test creatation of raw multisig issuance transactions
        #get a new address and public and private key for each node
        address_node1 = self.nodes[0].getnewaddress()
        val_addr_node1 = self.nodes[0].validateaddress(address_node1)
        privkey_node1 = self.nodes[0].dumpprivkey(address_node1)

        address_node2 =self.nodes[1].getnewaddress()
        val_addr_node2 = self.nodes[1].validateaddress(address_node2)
        privkey_node2 =self.nodes[1].dumpprivkey(address_node2)

        address_node3 =self.nodes[2].getnewaddress()
        val_addr_node3 = self.nodes[2].validateaddress(address_node3)
        privkey_node3 =self.nodes[2].dumpprivkey(address_node3)

        #create 2 of 3 multisig P2SH script and address
        multisig = self.nodes[0].createmultisig(2,[val_addr_node1["pubkey"],val_addr_node2["pubkey"],val_addr_node3["pubkey"]])
        #send some policyasset to the P2SH address
        pa_txid = self.nodes[2].sendtoaddress(multisig["address"],1,"","",False,"ISSUANCE")
        self.nodes[1].generate(1)
        self.sync_all()

        #get the vout and scriptPubKey of the multisig output
        vout = 0
        pa_tx = self.nodes[1].getrawtransaction(pa_txid,1)

        for val in pa_tx["vout"]:
            for i,j in val.items():
                if i == "n": vout_t = j
            for i,j in val.items():
                if i == "scriptPubKey":
                    for i2,j2 in j.items():
                        if i2 == "hex": script_t = j2
                    for i2,j2 in j.items():
                        if(i2 == "type" and j2 == "scripthash"):
                            script_pk = script_t
                            vout = vout_t

        #get address to send tokens and re-issuance tokens
        asset_addr = self.nodes[1].getnewaddress()
        token_addr = self.nodes[2].getnewaddress()

        #create an unsigned raw issuance transaction
        issuance_tx = self.nodes[1].createrawissuance(asset_addr,10.0,token_addr,1.0,multisig["address"],1.0000,'1',pa_txid,str(vout))


        #node1 partially sign transaction
        partial_signed = self.nodes[0].signrawtransaction(issuance_tx["rawtx"],[{"txid":pa_txid,"vout":vout,"scriptPubKey":script_pk,"redeemScript":multisig["redeemScript"]}],[privkey_node1])
        assert(not partial_signed["complete"])

        #node1 partially sign transaction
        signed_tx = self.nodes[1].signrawtransaction(partial_signed["hex"],[{"txid":pa_txid,"vout":vout,"scriptPubKey":script_pk,"redeemScript":multisig["redeemScript"]}],[privkey_node2])

        assert(signed_tx["complete"])
        self.nodes[1].generate(1)
        self.sync_all()

        #submit signed transaction to network
        submit = self.nodes[1].sendrawtransaction(signed_tx["hex"])

        #confirm transaction accepted by mempool
        mempool_tx = self.nodes[1].getrawmempool()
        assert_equal(mempool_tx[0],submit)
        self.nodes[1].generate(1)
        self.sync_all()

        #confirm asset can be spent by node2 wallet
        asset_addr2 = self.nodes[2].getnewaddress()
        asset_tx = self.nodes[1].sendtoaddress(asset_addr2,5,' ',' ',False,issuance_tx["asset"],True)
        mempool1 = self.nodes[1].getrawmempool()
        assert_equal(mempool1[0],asset_tx)
        self.nodes[1].generate(1)
        self.sync_all()

        #create raw issuance transaction with an issued asset as input
        vout = 0
        outvalue = 0.0
        ia_tx = self.nodes[2].getrawtransaction(asset_tx,1)

        for val in ia_tx["vout"]:
            for i,j in val.items():
                if i == "n": vout_t = j
                if i == "value": outvalue = j
            for i,j in val.items():
                if i == "scriptPubKey":
                    for i2,j2 in j.items():
                        if(i2 == "addresses" and j2[0] == asset_addr2):
                            vout = vout_t

        dum_addr1 = self.nodes[1].getnewaddress()
        dum_addr2 = self.nodes[1].getnewaddress()

        #create an unsigned raw issuance transaction
        issuance_tx2 = self.nodes[2].createrawissuance(dum_addr1,20.0,dum_addr2,2.0,asset_addr2,outvalue,'1',asset_tx,str(vout))

        #node2 sign transaction
        tx_signed = self.nodes[2].signrawtransaction(issuance_tx2["rawtx"])
        assert(tx_signed["complete"])

        #submit signed transaction to network
        try:
            submit2 = self.nodes[2].sendrawtransaction(tx_signed["hex"])
        except JSONRPCException as exp:
            assert("fblockissuancetx-non-issuance-asset" in exp.error['message']) # blocked issuance
        else:
            assert(False)

        self.nodes[2].generate(1)
        self.sync_all()

        #create a raw reissuance transaction using the reissuance token of issuance_tx
        #reissue 4.5 new tokens
        reissuaed_asset_addr = self.nodes[2].getnewaddress()
        new_token_address = self.nodes[2].getnewaddress()
        reissuance_tx = self.nodes[2].createrawreissuance(reissuaed_asset_addr,4.5,new_token_address,1.0,submit,'1',issuance_tx["entropy"])

        #check asset and token derivations
        assert_equal(reissuance_tx["asset"],issuance_tx["asset"])
        assert_equal(reissuance_tx["token"],issuance_tx["token"])

        #sign, check and submit tx
        signed_reissuance = self.nodes[2].signrawtransaction(reissuance_tx["hex"])
        assert(signed_reissuance["complete"])
        submit3 = self.nodes[2].sendrawtransaction(signed_reissuance["hex"])

        #confirm transaction accepted by mempool
        mempool_tx = self.nodes[2].getrawmempool()
        assert_equal(mempool_tx[0],submit3)
        self.nodes[2].generate(1)
        self.sync_all()

        # Now test a raw issuance with whitelisting enabled
        issuance_addr = self.nodes[1].getnewaddress()
        pa_txid = self.nodes[2].sendtoaddress(issuance_addr,1,"","",False,"ISSUANCE")
        self.nodes[2].generate(1)
        self.sync_all()
        # get the vout output
        vout = self.nodes[1].listunspent(1, 9999999, [], True, "ISSUANCE")[0]['vout']

        # stop and apply whitelisting
        self.stop_node(1)
        self.extra_args[1].append("-pkhwhitelist=1")
        self.nodes[1] = start_node(1, self.options.tmpdir, self.extra_args[1])
        connect_nodes_bi(self.nodes, 0, 1)
        connect_nodes_bi(self.nodes, 2, 1)
        self.sync_all()

        # get address to send tokens and re-issuance tokens
        whitelist_addr = self.nodes[1].getnewaddress()
        val_whitelist_addr = self.nodes[1].validateaddress(whitelist_addr)
        token_addr = self.nodes[2].getnewaddress()

        # create an unsigned raw issuance transaction
        issuance_tx = self.nodes[1].createrawissuance(whitelist_addr,10.0,token_addr,1.0,issuance_addr,1.0000,'1',pa_txid,str(vout))
        signed_tx = self.nodes[1].signrawtransaction(issuance_tx['rawtx'])
        try:
            self.nodes[1].sendrawtransaction(signed_tx['hex'])
        except JSONRPCException as e:
            assert("fblockissuancetx-non-whitelisted-address" in e.error['message'])

        self.nodes[1].addtowhitelist(whitelist_addr, val_whitelist_addr['derivedpubkey'])
        assert_equal(self.nodes[1].querywhitelist(whitelist_addr), True)
        self.nodes[1].generate(1)
        self.sync_all()

        txid = self.nodes[1].sendrawtransaction(signed_tx['hex'])
        assert(txid in self.nodes[1].getrawmempool())
        self.nodes[1].generate(1)
        self.sync_all()

        return

if __name__ == '__main__':
    RawIssuance().main()
