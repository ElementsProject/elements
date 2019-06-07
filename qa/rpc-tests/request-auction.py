#!/usr/bin/env python3
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *

# Test for request auction of the covalence system
class RequestAuctionTest(BitcoinTestFramework):
    def __init__(self):
        super().__init__()
        self.setup_clean_chain = True
        self.num_nodes = 4
        self.extra_args = [["-txindex=1 -initialfreecoins=50000000000000", "-policycoins=50000000000000",
        "-permissioncoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac",
        "-initialfreecoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac"] for i in range(4)]
        self.extra_args[0].append("-requestlist=1")

    def setup_network(self, split=False):
        self.nodes = start_nodes(self.num_nodes, self.options.tmpdir,
                                 self.extra_args[:self.num_nodes])
        connect_nodes_bi(self.nodes, 0, 1)
        connect_nodes_bi(self.nodes, 0, 2)
        connect_nodes_bi(self.nodes, 0, 3)
        self.is_network_split = False
        self.sync_all()

    def test_badheight(self, node_id, request_txid, height, price):
        # test create raw bid transaction
        addr = self.nodes[node_id].getnewaddress()
        pubkey = self.nodes[node_id].validateaddress(addr)["pubkey"]
        pubkeyFee = self.nodes[node_id].validateaddress(self.nodes[node_id].getnewaddress())["pubkey"]
        unspent = self.nodes[node_id].listunspent(1, 9999999, [], True, self.asset_hash)[0]
        inputs = [{"txid": unspent["txid"], "vout": unspent["vout"], "asset": self.asset_hash}]
        fee = Decimal('0.0001')
        outputs = {"endBlockHeight": height - 5, "requestTxid": request_txid, "feePubkey": pubkeyFee,
            "pubkey": pubkey, "fee": fee, "value": price + 1,
            "change": unspent["amount"] - price - 1 - fee, "changeAddress": addr}

        tx = self.nodes[node_id].createrawbidtx(inputs, outputs)
        signedtx = self.nodes[node_id].signrawtransaction(tx)
        return self.nodes[node_id].sendrawtransaction(signedtx['hex'])

    def test_badprice(self, node_id, request_txid, height, price):
        # test create raw bid transaction
        addr = self.nodes[node_id].getnewaddress()
        pubkey = self.nodes[node_id].validateaddress(addr)["pubkey"]
        pubkeyFee = self.nodes[node_id].validateaddress(self.nodes[node_id].getnewaddress())["pubkey"]
        unspent = self.nodes[node_id].listunspent(1, 9999999, [], True, self.asset_hash)[0]
        inputs = [{"txid": unspent["txid"], "vout": unspent["vout"], "asset": self.asset_hash}]
        fee = Decimal('0.0001')
        outputs = {"endBlockHeight": height, "requestTxid": request_txid, "feePubkey": pubkeyFee,
            "pubkey": pubkey, "fee": fee, "value": price - 1,
            "change": unspent["amount"] - price + 1 - fee, "changeAddress": addr}

        tx = self.nodes[node_id].createrawbidtx(inputs, outputs)
        signedtx = self.nodes[node_id].signrawtransaction(tx)
        return self.nodes[node_id].sendrawtransaction(signedtx['hex'])

    def test_bid(self, node_id, request_txid, height, price):
        # test create raw bid transaction
        addr = self.nodes[node_id].getnewaddress()
        pubkey = self.nodes[node_id].validateaddress(addr)["pubkey"]
        pubkeyFee = self.nodes[node_id].validateaddress(self.nodes[node_id].getnewaddress())["pubkey"]
        unspent = self.nodes[node_id].listunspent(1, 9999999, [], True, self.asset_hash)[0]
        inputs = [{"txid": unspent["txid"], "vout": unspent["vout"], "asset": self.asset_hash}]
        fee = Decimal('0.0001')
        outputs = {"endBlockHeight": height, "requestTxid": request_txid, "feePubkey": pubkeyFee,
            "pubkey": pubkey, "fee": fee, "value": price,
            "change": unspent["amount"] - price - fee, "changeAddress": addr}

        tx = self.nodes[node_id].createrawbidtx(inputs, outputs)
        signedtx = self.nodes[node_id].signrawtransaction(tx)
        return self.nodes[node_id].sendrawtransaction(signedtx['hex'])

    def run_test(self):
        self.nodes[0].importprivkey("cTnxkovLhGbp7VRhMhGThYt8WDwviXgaVAD8DjaVa5G5DApwC6tF")
        self.nodes[0].generate(101)
        self.sync_all()

        asset = self.nodes[0].issueasset(500, 0)
        self.asset_hash = asset['asset']
        self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 100, "", "", False, self.asset_hash)
        self.nodes[0].sendtoaddress(self.nodes[2].getnewaddress(), 100, "", "", False, self.asset_hash)
        self.nodes[0].sendtoaddress(self.nodes[3].getnewaddress(), 100, "", "", False, self.asset_hash)
        self.nodes[0].generate(1) # 102
        self.sync_all()

        # create request
        end_height = 130
        addr = self.nodes[0].getnewaddress()
        pubkey = self.nodes[0].validateaddress(addr)["pubkey"]
        unspent = self.nodes[0].listunspent(1, 9999999, [], True, "PERMISSION")
        genesis = "867da0e138b1014173844ee0e4d557ff8a2463b14fcaeab18f6a63aa7c7e1d05"
        inputs = {"txid": unspent[0]["txid"], "vout": unspent[0]["vout"]}
        outputs = {"decayConst": 100, "endBlockHeight": end_height, "fee": 3, "genesisBlockHash": genesis,
        "startBlockHeight": 115, "tickets": 2, "startPrice": 20, "value": unspent[0]["amount"], "pubkey": pubkey}

        tx = self.nodes[0].createrawrequesttx(inputs, outputs)
        signedtx = self.nodes[0].signrawtransaction(tx)
        request_txid = self.nodes[0].sendrawtransaction(signedtx["hex"])

        self.nodes[0].generate(1) # 103
        self.sync_all()
        request = self.nodes[0].getrequests(genesis)[0]
        assert_equal(103, request['confirmedBlockHeight'])
        assert_equal(20.0, float(request['auctionPrice']))

        bad_txid = self.test_badheight(1, request_txid, end_height, request['auctionPrice'])
        self.sync_all()
        self.nodes[0].generate(1) # 104
        self.sync_all()
        request = self.nodes[0].getrequestbids(request_txid)
        assert_equal(19.90049751, float(request['auctionPrice']))
        assert_equal([], request['bids'])
        assert_equal(self.nodes[1].getrequestbids(request_txid), request)

        bad_txid = self.test_badprice(1, request_txid, end_height, request['auctionPrice'])
        self.sync_all()
        self.nodes[0].generate(1) # 105
        self.sync_all()
        request = self.nodes[0].getrequestbids(request_txid)
        assert_equal(19.48051948, float(request['auctionPrice']))
        assert_equal([], request['bids'])
        assert_equal(self.nodes[2].getrequestbids(request_txid), request)

        bid1_txid = self.test_bid(1, request_txid, end_height, request['auctionPrice'])
        self.sync_all()
        self.nodes[0].generate(1) # 106
        self.sync_all()
        request = self.nodes[1].getrequestbids(request_txid)
        assert_equal(18.73536299, float(request['auctionPrice']))
        assert_equal(1, len(request['bids']))
        assert_equal(bid1_txid, request['bids'][0]['txid'])
        assert_equal(self.nodes[3].getrequestbids(request_txid), request)

        bid2_txid = self.test_bid(2, request_txid, end_height, request['auctionPrice'])
        self.sync_all()
        self.nodes[0].generate(1) # 107
        self.sync_all()
        request = self.nodes[0].getrequestbids(request_txid)
        assert_equal(17.73049645, float(request['auctionPrice']))
        assert_equal(2, len(request['bids']))
        assert(request['bids'][0] != request['bids'][1])
        assert(request['bids'][0]['txid'] == bid1_txid)
        assert(request['bids'][1]['txid'] == bid2_txid)
        assert_equal(self.nodes[1].getrequestbids(request_txid), request)

        bid3_txid = self.test_bid(3, request_txid, end_height, request['auctionPrice'])
        self.sync_all()
        self.nodes[0].generate(1) # 108
        self.sync_all()
        request = self.nodes[0].getrequestbids(request_txid)
        assert_equal(16.55172413, float(request['auctionPrice']))
        assert_equal(2, len(request['bids']))
        assert(request['bids'][0] != request['bids'][1])
        assert(request['bids'][0]['txid'] == bid1_txid)
        assert(request['bids'][1]['txid'] == bid2_txid)
        assert_equal(self.nodes[2].getrequestbids(request_txid), request)

        self.nodes[0].generate(10) # 118
        self.sync_all()
        request = self.nodes[0].getrequestbids(request_txid)

        #test stopping and restarting to make sure list is reloaded
        self.stop_node(0)
        self.nodes[0] = start_node(0, self.options.tmpdir, self.extra_args[0])
        request_restart = self.nodes[0].getrequestbids(request_txid)
        assert_equal(request, request_restart)
        assert(request_restart['bids'][0] != request_restart['bids'][1])
        assert(request_restart['bids'][0]['txid'] == bid1_txid)
        assert(request_restart['bids'][1]['txid'] == bid2_txid)
        connect_nodes_bi(self.nodes, 0, 1)
        connect_nodes_bi(self.nodes, 0, 2)
        connect_nodes_bi(self.nodes, 0, 3)
        self.sync_all()

        self.nodes[0].generate(20) # 138
        self.sync_all()

        try:
            self.nodes[0].getrequestbids(request_txid)
        except JSONRPCException as exp:
            assert_equal(exp.error["message"], "No such request transaction")
        else:
            assert(False)
        try:
            self.nodes[3].getrequestbids(request_txid)
        except JSONRPCException as exp:
            assert_equal(exp.error["message"], "No such request transaction")
        else:
            assert(False)

        return

if __name__ == '__main__':
    RequestAuctionTest().main()
