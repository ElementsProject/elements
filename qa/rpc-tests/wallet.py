#!/usr/bin/env python3
# Copyright (c) 2014-2016 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *

class WalletTest (BitcoinTestFramework):

    def check_fee_amount(self, curr_balance, balance_with_fee, fee_per_byte, tx_size):
        """Return curr_balance after asserting the fee was in range"""
        fee = balance_with_fee - curr_balance
        assert_fee_amount(fee, tx_size, fee_per_byte * 1000)
        return curr_balance

    def __init__(self):
        super().__init__()
        self.setup_clean_chain = True
        self.num_nodes = 4
        self.extra_args = [['-usehd={:d}'.format(i%2==0)] for i in range(4)]
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

        self.nodes[2].importprivkey("cTnxkovLhGbp7VRhMhGThYt8WDwviXgaVAD8DjaVa5G5DApwC6tF")

        # Check that there's 100 UTXOs on each of the nodes
        assert_equal(len(self.nodes[0].listunspent()), 100)
        assert_equal(len(self.nodes[1].listunspent()), 100)
        assert_equal(len(self.nodes[2].listunspent()), 200)

        

        walletinfo = self.nodes[2].getbalance()
        assert_equal(walletinfo["CBT"], 21000000)
        assert_equal(walletinfo["ISSUANCE"], 500000)

        print("Mining blocks...")
        self.nodes[2].generate(101)
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
        self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), 21000000, "", "", True)
        self.nodes[0].generate(101)
        self.sync_all()

        assert_equal(self.nodes[0].getbalance("", 0, False, "CBT"), 21000000)
        assert_equal(self.nodes[1].getbalance("", 0, False, "CBT"), 0)
        assert_equal(self.nodes[2].getbalance("", 0, False, "CBT"), 0)

        #self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 1000000)
        #self.nodes[0].generate(1)
        #self.sync_all()

        #self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 100000)
        #self.nodes[0].generate(101)
        #self.sync_all()

        #assert_equal(self.nodes[0].getbalance(), 21000000-1100000)
        #assert_equal(self.nodes[1].getbalance(), 1000000)
        #assert_equal(self.nodes[2].getbalance(), 100000)

        # Send 21 BTC from 0 to 2 using sendtoaddress call.
        txid1 = self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 11)
        txout1v0 = self.nodes[0].gettxout(txid1, 0)
        rawtx1 = self.nodes[0].getrawtransaction(txid1, 1)
        #amountcommit1 = rawtx1["vout"][0]["amountcommitment"]
        assert_equal(txout1v0['confirmations'], 0)
        assert(not txout1v0['coinbase'])
        #assert_equal(amountcommit1, txout1v0['amountcommitment'])


        txid2 = self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 10)
        txout2v0 = self.nodes[0].gettxout(txid2, 0)
        rawtx2 = self.nodes[0].getrawtransaction(txid2, 1)
        #amountcommit2 = rawtx2["vout"][0]["amountcommitment"]
        assert_equal(txout2v0['confirmations'], 0)
        assert(not txout2v0['coinbase'])
        #assert_equal(amountcommit2, txout2v0['amountcommitment'])

        walletinfo = self.nodes[0].getwalletinfo("CBT")
        assert_equal(walletinfo['immature_balance'], 0)

        # Have node0 mine a block, thus it will collect its own fee. Confirm previous transactions.
        self.nodes[0].generate(1)
        self.sync_all()

        # Exercise locking of unspent outputs
        unspent_0 = self.nodes[2].listunspent(1, 9999999, [], True, "CBT")[0]
        unspent_0 = {"txid": unspent_0["txid"], "vout": unspent_0["vout"]}
        self.nodes[2].lockunspent(False, [unspent_0])
        assert_raises_message(JSONRPCException, "Insufficient funds", self.nodes[2].sendtoaddress, self.nodes[2].getnewaddress(), 20)
        assert_equal([unspent_0], self.nodes[2].listlockunspent())
        self.nodes[2].lockunspent(True, [unspent_0])
        assert_equal(len(self.nodes[2].listlockunspent()), 0)

        # Have node1 generate 100 blocks (so node0 can recover the fee)
        self.nodes[1].generate(100)
        self.sync_all()

        # node0 should end up with 100 btc in block rewards plus fees, but
        # minus the 21 plus fees sent to node2
        assert_equal(self.nodes[0].getbalance("", 0, False, "CBT"), 21000000-21)
        assert_equal(self.nodes[2].getbalance("", 0, False, "CBT"), 21)

        # Node0 should have three spendable outputs since 0-value coinbase outputs will be OP_RETURN.
        # Create a couple of transactions to send them to node2, submit them through
        # node1, and make sure both node0 and node2 pick them up properly:
        node0utxos = self.nodes[0].listunspent(1, 9999999, [], True, "CBT")
        assert_equal(len(node0utxos), 3)

        # create both transactions
        txns_to_send = []
        for utxo in node0utxos:
            if utxo["amount"] <= 3: # arbitrary value of 3?
                continue
            inputs = []
            outputs = {}
            inputs.append({ "txid" : utxo["txid"], "vout" : utxo["vout"], "nValue":utxo["amount"]})
            outputs = {self.nodes[2].getnewaddress("from1"): utxo["amount"] - Decimal('1'),
                        "fee": Decimal('1')}
            raw_tx = self.nodes[0].createrawtransaction(inputs, outputs)
            raw_tx = self.nodes[0].blindrawtransaction(raw_tx)
            txns_to_send.append(self.nodes[0].signrawtransaction(raw_tx))

        # Have node 1 (miner) send the transaction
        txid = self.nodes[1].sendrawtransaction(txns_to_send[0]["hex"], True)

        # Have node1 mine a block to confirm transaction:
        self.nodes[1].generate(1)
        self.sync_all()

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
        token_addr = self.nodes[1].getnewaddress()

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
        asset_addr2 = self.nodes[0].getnewaddress()
        asset_tx = self.nodes[1].sendtoaddress(asset_addr2,5,' ',' ',False,issuance_tx["asset"],True)
        mempool1 = self.nodes[1].getrawmempool()
        assert_equal(mempool1[0],asset_tx)

        return #TODO fix the rest
        txoutv0 = self.nodes[0].gettxout(txid, 0)
        assert_equal(txoutv0['confirmations'], 1)
        assert(not txoutv0['coinbase'])

        assert_equal(self.nodes[0].getbalance(), 0)
        assert_equal(self.nodes[2].getbalance(), 94)
        assert_equal(self.nodes[2].getbalance("from1"), 94-21)

        # Send 10 BTC normal
        address = self.nodes[0].getnewaddress("test")
        fee_per_byte = Decimal('0.001') / 1000
        self.nodes[2].settxfee(fee_per_byte * 1000)
        txid = self.nodes[2].sendtoaddress(address, 10, "", "", False)
        self.nodes[2].generate(1)
        self.sync_all()
        node_2_bal = self.check_fee_amount(self.nodes[2].getbalance(), Decimal('84'), fee_per_byte, count_bytes(self.nodes[2].getrawtransaction(txid)))
        assert_equal(self.nodes[0].getbalance(), Decimal('10'))

        # Send 10 BTC with subtract fee from amount
        txid = self.nodes[2].sendtoaddress(address, 10, "", "", True)
        self.nodes[2].generate(1)
        self.sync_all()
        node_2_bal -= Decimal('10')
        assert_equal(self.nodes[2].getbalance(), node_2_bal)
        node_0_bal = self.check_fee_amount(self.nodes[0].getbalance(), Decimal('20'), fee_per_byte, count_bytes(self.nodes[2].getrawtransaction(txid)))

        # Sendmany 10 BTC
        txid = self.nodes[2].sendmany('from1', {address: 10}, 0, "", [], {'fee': 'CBT'})
        self.nodes[2].generate(1)
        self.sync_all()
        node_0_bal += Decimal('10')
        node_2_bal = self.check_fee_amount(self.nodes[2].getbalance(), node_2_bal - Decimal('10'), fee_per_byte, count_bytes(self.nodes[2].getrawtransaction(txid)))
        assert_equal(self.nodes[0].getbalance(), node_0_bal)

        # Sendmany 10 BTC with subtract fee from amount
        txid = self.nodes[2].sendmany('from1', {address: 10}, 0, "", [address], {'fee': 'CBT'})
        self.nodes[2].generate(1)
        self.sync_all()
        node_2_bal -= Decimal('10')
        assert_equal(self.nodes[2].getbalance(), node_2_bal)
        node_0_bal = self.check_fee_amount(self.nodes[0].getbalance(), node_0_bal + Decimal('10'), fee_per_byte, count_bytes(self.nodes[2].getrawtransaction(txid)))

        # Test ResendWalletTransactions:
        # Create a couple of transactions, then start up a fourth
        # node (nodes[3]) and ask nodes[0] to rebroadcast.
        # EXPECT: nodes[3] should have those transactions in its mempool.
        txid1 = self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 1)
        txid2 = self.nodes[1].sendtoaddress(self.nodes[0].getnewaddress(), 1)
        sync_mempools(self.nodes)

        self.nodes.append(start_node(3, self.options.tmpdir, self.extra_args[3]))
        connect_nodes_bi(self.nodes, 0, 3)
        sync_blocks(self.nodes)

        relayed = self.nodes[0].resendwallettransactions()
        assert_equal(set(relayed), {txid1, txid2})
        sync_mempools(self.nodes)

        assert(txid1 in self.nodes[3].getrawmempool())

        # Exercise balance rpcs
        assert_equal(self.nodes[0].getwalletinfo()["unconfirmed_balance"], 1)
        assert_equal(self.nodes[0].getunconfirmedbalance(), 1)

        #check if we can list zero value tx as available coins
        #1. create rawtx
        #2. hex-changed one output to 0.0
        #3. sign and send
        #4. check if recipient (node0) can list the zero value tx
        usp = self.nodes[1].listunspent()
        inputs = [{"txid":usp[0]['txid'], "vout":usp[0]['vout']}]
        outputs = {self.nodes[1].getnewaddress(): 49.998, self.nodes[0].getnewaddress(): 11.11}

        rawTx = self.nodes[1].createrawtransaction(inputs, outputs).replace("c0833842", "00000000") #replace 11.11 with 0.0 (int32)
        decRawTx = self.nodes[1].decoderawtransaction(rawTx)
        signedRawTx = self.nodes[1].signrawtransaction(rawTx)
        decRawTx = self.nodes[1].decoderawtransaction(signedRawTx['hex'])
        zeroValueTxid= decRawTx['txid']
        sendResp = self.nodes[1].sendrawtransaction(signedRawTx['hex'])

        self.sync_all()
        self.nodes[1].generate(1) #mine a block
        self.sync_all()

        unspentTxs = self.nodes[0].listunspent() #zero value tx must be in listunspents output
        found = False
        for uTx in unspentTxs:
            if uTx['txid'] == zeroValueTxid:
                found = True
                assert_equal(uTx['amount'], Decimal('0'))
        assert(found)

        #do some -walletbroadcast tests
        stop_nodes(self.nodes)
        self.nodes = start_nodes(3, self.options.tmpdir, [["-walletbroadcast=0"],["-walletbroadcast=0"],["-walletbroadcast=0"]])
        connect_nodes_bi(self.nodes,0,1)
        connect_nodes_bi(self.nodes,1,2)
        connect_nodes_bi(self.nodes,0,2)
        self.sync_all()

        txIdNotBroadcasted  = self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 2)
        txObjNotBroadcasted = self.nodes[0].gettransaction(txIdNotBroadcasted)
        self.nodes[1].generate(1) #mine a block, tx should not be in there
        self.sync_all()
        assert_equal(self.nodes[2].getbalance(), node_2_bal) #should not be changed because tx was not broadcasted

        #now broadcast from another node, mine a block, sync, and check the balance
        self.nodes[1].sendrawtransaction(txObjNotBroadcasted['hex'])
        self.nodes[1].generate(1)
        self.sync_all()
        node_2_bal += 2
        txObjNotBroadcasted = self.nodes[0].gettransaction(txIdNotBroadcasted)
        assert_equal(self.nodes[2].getbalance(), node_2_bal)

        #create another tx
        txIdNotBroadcasted  = self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 2)

        #restart the nodes with -walletbroadcast=1
        stop_nodes(self.nodes)
        self.nodes = start_nodes(3, self.options.tmpdir)
        connect_nodes_bi(self.nodes,0,1)
        connect_nodes_bi(self.nodes,1,2)
        connect_nodes_bi(self.nodes,0,2)
        sync_blocks(self.nodes)

        self.nodes[0].generate(1)
        sync_blocks(self.nodes)
        node_2_bal += 2

        #tx should be added to balance because after restarting the nodes tx should be broadcastet
        assert_equal(self.nodes[2].getbalance(), node_2_bal)

        #send a tx with value in a string (PR#6380 +)
        txId  = self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), "2")
        txObj = self.nodes[0].gettransaction(txId)
        assert_equal(txObj['amount'], Decimal('-2'))

        txId  = self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), "0.0001")
        txObj = self.nodes[0].gettransaction(txId)
        assert_equal(txObj['amount'], Decimal('-0.0001'))

        #check if JSON parser can handle scientific notation in strings
        txId  = self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), "1e-4")
        txObj = self.nodes[0].gettransaction(txId)
        assert_equal(txObj['amount'], Decimal('-0.0001'))

        try:
            txId  = self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), "1f-4")
        except JSONRPCException as e:
            assert("Invalid amount" in e.error['message'])
        else:
            raise AssertionError("Must not parse invalid amounts")


        try:
            self.nodes[0].generate("2")
            raise AssertionError("Must not accept strings as numeric")
        except JSONRPCException as e:
            assert("not an integer" in e.error['message'])

        # Import address and private key to check correct behavior of spendable unspents
        # 1. Send some coins to generate new UTXO
        address_to_import = self.nodes[2].getnewaddress()
        txid = self.nodes[0].sendtoaddress(address_to_import, 1)
        self.nodes[0].generate(1)
        self.sync_all()

        # 2. Import address from node2 to node1
        self.nodes[1].importaddress(address_to_import)

        # 3. Validate that the imported address is watch-only on node1
        assert(self.nodes[1].validateaddress(address_to_import)["iswatchonly"])

        # 4. Check that the unspents after import are not spendable
        assert_array_result(self.nodes[1].listunspent(),
                           {"address": address_to_import},
                           {"spendable": False})

        # 5. Import private key of the previously imported address on node1
        priv_key = self.nodes[2].dumpprivkey(address_to_import)
        self.nodes[1].importprivkey(priv_key)

        # 6. Check that the unspents are now spendable on node1
        assert_array_result(self.nodes[1].listunspent(),
                           {"address": address_to_import},
                           {"spendable": True})

        # Mine a block from node0 to an address from node1
        cbAddr = self.nodes[1].getnewaddress()
        blkHash = self.nodes[0].generatetoaddress(1, cbAddr)[0]
        cbTxId = self.nodes[0].getblock(blkHash)['tx'][0]
        self.sync_all()

        # Check that the txid and balance is found by node1
        self.nodes[1].gettransaction(cbTxId)

        # check if wallet or blockchain maintenance changes the balance
        self.sync_all()
        blocks = self.nodes[0].generate(2)
        self.sync_all()
        balance_nodes = [self.nodes[i].getbalance() for i in range(3)]
        block_count = self.nodes[0].getblockcount()

        # Check modes:
        #   - True: unicode escaped as \u....
        #   - False: unicode directly as UTF-8
        for mode in [True, False]:
            self.nodes[0].ensure_ascii = mode
            # unicode check: Basic Multilingual Plane, Supplementary Plane respectively
            for s in [u'рыба', u'𝅘𝅥𝅯']:
                addr = self.nodes[0].getaccountaddress(s)
                label = self.nodes[0].getaccount(addr)
                assert_equal(label, s)
                assert(s in self.nodes[0].listaccounts().keys())
        self.nodes[0].ensure_ascii = True # restore to default

        # maintenance tests
        maintenance = [
            '-rescan',
            '-reindex',
            '-zapwallettxes=1',
            '-zapwallettxes=2',
            # disabled until issue is fixed: https://github.com/bitcoin/bitcoin/issues/7463
            # '-salvagewallet',
        ]
        chainlimit = 6
        for m in maintenance:
            print("check " + m)
            stop_nodes(self.nodes)
            # set lower ancestor limit for later
            self.nodes = start_nodes(3, self.options.tmpdir, [[m, "-limitancestorcount="+str(chainlimit)]] * 3)
            while m == '-reindex' and [block_count] * 3 != [self.nodes[i].getblockcount() for i in range(3)]:
                # reindex will leave rpc warm up "early"; Wait for it to finish
                time.sleep(0.1)
            assert_equal(balance_nodes, [self.nodes[i].getbalance() for i in range(3)])

        # Exercise listsinceblock with the last two blocks
        coinbase_tx_1 = self.nodes[0].listsinceblock(blocks[0])
        assert_equal(coinbase_tx_1["lastblock"], blocks[1])
        assert_equal(len(coinbase_tx_1["transactions"]), 1)
        assert_equal(coinbase_tx_1["transactions"][0]["blockhash"], blocks[1])
        assert_equal(len(self.nodes[0].listsinceblock(blocks[1])["transactions"]), 0)

        # ==Check that wallet prefers to use coins that don't exceed mempool limits =====

        # Get all non-zero utxos together
        chain_addrs = [self.nodes[0].getnewaddress(), self.nodes[0].getnewaddress()]
        singletxid = self.nodes[0].sendtoaddress(chain_addrs[0], self.nodes[0].getbalance(), "", "", True)
        self.nodes[0].generate(1)
        node0_balance = self.nodes[0].getbalance()
        # Split into two chains
        rawtx = self.nodes[0].createrawtransaction([{"txid":singletxid, "vout":0}], {chain_addrs[0]:node0_balance/2-Decimal('0.01'), chain_addrs[1]:node0_balance/2-Decimal('0.01')})
        signedtx = self.nodes[0].signrawtransaction(rawtx)
        singletxid = self.nodes[0].sendrawtransaction(signedtx["hex"])
        self.nodes[0].generate(1)

        # Make a long chain of unconfirmed payments without hitting mempool limit
        # Each tx we make leaves only one output of change on a chain 1 longer
        # Since the amount to send is always much less than the outputs, we only ever need one output
        # So we should be able to generate exactly chainlimit txs for each original output
        sending_addr = self.nodes[1].getnewaddress()
        txid_list = []
        for i in range(chainlimit*2):
            txid_list.append(self.nodes[0].sendtoaddress(sending_addr, Decimal('0.0001')))
        assert_equal(self.nodes[0].getmempoolinfo()['size'], chainlimit*2)
        assert_equal(len(txid_list), chainlimit*2)

        # Without walletrejectlongchains, we will still generate a txid
        # The tx will be stored in the wallet but not accepted to the mempool
        extra_txid = self.nodes[0].sendtoaddress(sending_addr, Decimal('0.0001'))
        assert(extra_txid not in self.nodes[0].getrawmempool())
        assert(extra_txid in [tx["txid"] for tx in self.nodes[0].listtransactions()])
        self.nodes[0].abandontransaction(extra_txid)
        total_txs = len(self.nodes[0].listtransactions("*",99999))

        # Try with walletrejectlongchains
        # Double chain limit but require combining inputs, so we pass SelectCoinsMinConf
        stop_node(self.nodes[0],0)
        self.nodes[0] = start_node(0, self.options.tmpdir, ["-walletrejectlongchains", "-limitancestorcount="+str(2*chainlimit)])

        # wait for loadmempool
        timeout = 10
        while (timeout > 0 and len(self.nodes[0].getrawmempool()) < chainlimit*2):
            time.sleep(0.5)
            timeout -= 0.5
        assert_equal(len(self.nodes[0].getrawmempool()), chainlimit*2)

        node0_balance = self.nodes[0].getbalance()
        # With walletrejectlongchains we will not create the tx and store it in our wallet.
        assert_raises_message(JSONRPCException, "mempool chain", self.nodes[0].sendtoaddress, sending_addr, node0_balance - Decimal('0.01'))

        # Verify nothing new in wallet
        assert_equal(total_txs, len(self.nodes[0].listtransactions("*",99999)))

if __name__ == '__main__':
    WalletTest().main()
