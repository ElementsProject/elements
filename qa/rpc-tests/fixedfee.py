#!/usr/bin/env python3
# Copyright (c) 2019 CommerceBlock developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *

class FixedFee (BitcoinTestFramework):

    def __init__(self):
        super().__init__()
        self.setup_clean_chain = True
        self.num_nodes = 4
        self.extra_args = [['-issuanceblock'] for i in range(4)]
        self.extra_args[0].append("-txindex")
        self.extra_args[0].append("-contractintx=1")
        self.extra_args[0].append("-fixedtxfee=100000")
        self.extra_args[0].append("-policycoins=50000000000000")
        self.extra_args[0].append("-issuancecoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac")
        self.extra_args[1].append("-txindex")
        self.extra_args[1].append("-contractintx=1")
        self.extra_args[1].append("-fixedtxfee=100000")
        self.extra_args[1].append("-policycoins=50000000000000")
        self.extra_args[1].append("-issuancecoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac")
        self.extra_args[2].append("-txindex")
        self.extra_args[2].append("-contractintx=1")
        self.extra_args[2].append("-fixedtxfee=100000")
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

        genhash = self.nodes[2].getblockhash(0)
        genblock = self.nodes[2].getblock(genhash)

        for txid in genblock["tx"]:
            rawtx = self.nodes[2].getrawtransaction(txid,True)
            if "assetlabel" in rawtx["vout"][0]:
                if rawtx["vout"][0]["assetlabel"] == "ISSUANCE":
                    asasset = rawtx["vout"][0]["asset"]
                    astxid = txid
                    asvalue = rawtx["vout"][0]["value"]

        assert_equal(self.nodes[0].getbalance("", 0, False, "CBT"), 21000000)
        assert_equal(self.nodes[1].getbalance("", 0, False, "CBT"), 21000000)
        assert_equal(self.nodes[2].getbalance("", 0, False, "CBT"), 21000000)

        #Set all OP_TRUE genesis outputs to single node
        txid1 = self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), 21000000, "", "", True)
        self.nodes[0].generate(101)
        self.sync_all()

        assert_equal(self.nodes[0].getbalance("", 0, False, "CBT"), 21000000)
        assert_equal(self.nodes[1].getbalance("", 0, False, "CBT"), 0)
        assert_equal(self.nodes[2].getbalance("", 0, False, "CBT"), 0)

        rawtx1 = self.nodes[0].getrawtransaction(txid1,True)
        for out in rawtx1["vout"]:
            if out["scriptPubKey"]["type"] == "fee": tfee = out["value"]

        assert_equal(int(tfee*100000000),100000)

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
        pa_txid = self.nodes[2].sendtoaddress(multisig["address"],1,"","",False,asasset)
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
        self.nodes[1].generate(2)
        self.sync_all()

        #submit signed transaction to network
        submit = self.nodes[1].sendrawtransaction(signed_tx["hex"])

        #confirm transaction accepted by mempool 
        mempool_tx = self.nodes[1].getrawmempool()
        assert_equal(mempool_tx[0],submit)
        self.nodes[1].generate(10)
        self.sync_all()

        #confirm asset can be spent by node2 wallet
        asset_addr2 = self.nodes[2].getnewaddress()
        asset_tx = self.nodes[1].sendtoaddress(asset_addr2,5,' ',' ',False,issuance_tx["asset"],True)
        asset_txd = self.nodes[1].getrawtransaction(asset_tx,True)
        mempool1 = self.nodes[1].getrawmempool()
        assert_equal(mempool1[0],asset_tx)
        self.nodes[1].generate(2)
        self.sync_all()

        #check fee is fixed value
        for out in asset_txd["vout"]:
            if out["scriptPubKey"]["type"] == "fee": tfee = out["value"]
        assert_equal(int(tfee*100000000),100000)

        #create raw transaction with incorrect fee
        fee = 0.0001
        new_addr = self.nodes[0].getnewaddress()
        unspent = self.nodes[2].listunspent()

        outputs = {}
        outputs[new_addr] = 5-fee
        outputs["fee"] = fee

        asset_ids = {}
        asset_ids[new_addr] = issuance_tx["asset"]
        asset_ids["fee"] = issuance_tx["asset"]

        for us in unspent:
            if us["txid"] == asset_tx: us_vout = us["vout"]
        raw_tx = self.nodes[2].createrawtransaction([{"txid":asset_tx,"vout":us_vout}],outputs,0,asset_ids)
        signed_tx = self.nodes[2].signrawtransaction(raw_tx)

        #submit signed transaction to network
        try:
            txid2 = self.nodes[2].sendrawtransaction(signed_tx["hex"])
        except JSONRPCException as exp:
            assert_equal(exp.error['code'], -26) # blocked tx incorrect fee
        else:
            assert(False)

        #use excessive fee
        fee = 0.01
        outputs[new_addr] = 5-fee
        outputs["fee"] = fee

        raw_tx = self.nodes[2].createrawtransaction([{"txid":asset_tx,"vout":us_vout}],outputs,0,asset_ids)
        signed_tx = self.nodes[2].signrawtransaction(raw_tx)

        #submit signed transaction to network
        try:
            txid2 = self.nodes[2].sendrawtransaction(signed_tx["hex"])
        except JSONRPCException as exp:
            assert_equal(exp.error['code'], -26) # blocked tx incorrect fee
        else:
            assert(False)        

        #use correct fee
        fee = 0.001
        outputs[new_addr] = 5-fee
        outputs["fee"] = fee

        raw_tx = self.nodes[2].createrawtransaction([{"txid":asset_tx,"vout":us_vout}],outputs,0,asset_ids)
        signed_tx = self.nodes[2].signrawtransaction(raw_tx)

        #submit signed transaction to network
        try:
            txid2 = self.nodes[2].sendrawtransaction(signed_tx["hex"])
        except JSONRPCException as exp:
            assert(False)

        self.nodes[2].generate(10)
        self.sync_all()

        #send some CBT to node 2
        new_add = self.nodes[2].getnewaddress()
        txid = self.nodes[0].sendtoaddress(new_addr,11)
        self.nodes[2].generate(10)
        self.sync_all()
        rawtx = self.nodes[2].getrawtransaction(txid,True)
        for out in rawtx["vout"]:
            if out["value"] == 11.0:
                asset = out["asset"]
                us_vout = out["n"]

        #create a transaction with split outputs
        new_add1 = self.nodes[0].getnewaddress()
        new_add2 = self.nodes[0].getnewaddress()
        inputs = []
        inputs.append({"txid":txid,"vout":us_vout})
        inputs.append({"txid":txid2,"vout":0})

        outputs = {}
        outputs[new_add1] = 2.499
        outputs[new_add1] = 2.499
        outputs[new_add2] = 5.5
        outputs[new_add2] = 5.5
        outputs["fee"] = 0.001

        asset_ids = {}
        asset_ids[new_add1] = issuance_tx["asset"]
        asset_ids["fee"] = issuance_tx["asset"]
        asset_ids[new_add2] = asset

        raw_tx = self.nodes[2].createrawtransaction(inputs,outputs,0,asset_ids)

        #createrawtransaction will not allow you to create a transaction sending more than one output to the same address
        #so add the doubled outputs manually by splitting up the hex
        doubled_outputs_tx = raw_tx[0:176] + '05' + raw_tx[178:316] + raw_tx[178:316] + raw_tx[316:454] + raw_tx[316:454] + raw_tx[454:]

        signed_tx = self.nodes[2].signrawtransaction(doubled_outputs_tx)

        #submit signed transaction to network
        try:
            txid3 = self.nodes[2].sendrawtransaction(signed_tx["hex"])
        except JSONRPCException as exp:
            assert_equal(exp.error['code'], -26) # blocked tx spam-split outputs
        else:
            assert(False)

        self.nodes[2].generate(10)
        self.sync_all()

        return

if __name__ == '__main__':
    FixedFee().main()
