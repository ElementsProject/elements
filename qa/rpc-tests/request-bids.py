#!/usr/bin/env python3
# Copyright (c) 2019 CommerceBlock developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *

# Test for request bids of the covalence system
class RequestbidsTest(BitcoinTestFramework):
  def __init__(self):
    super().__init__()
    self.setup_clean_chain = True
    self.num_nodes = 2
    self.extra_args = [["-txindex=1 -initialfreecoins=50000000000000", "-policycoins=50000000000000",
    "-permissioncoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac",
    "-initialfreecoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac"] for i in range(2)]
    self.extra_args[1].append("-requestlist=1")

  def setup_network(self, split=False):
    self.nodes = start_nodes(self.num_nodes, self.options.tmpdir,
                             self.extra_args[:self.num_nodes])
    connect_nodes_bi(self.nodes, 0, 1)
    self.is_network_split = False
    self.sync_all()

  def run_test(self):
    self.nodes[0].importprivkey("cTnxkovLhGbp7VRhMhGThYt8WDwviXgaVAD8DjaVa5G5DApwC6tF")
    self.nodes[0].generate(101)
    self.sync_all()

    asset = self.nodes[0].issueasset(500, 0)
    asset_hash = asset['asset']
    self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 50, "", "", False, asset_hash)
    self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 50, "", "", False, asset_hash)
    self.nodes[0].generate(1)
    self.sync_all()
    assert_equal(100, self.nodes[1].getbalance()[asset_hash])

    # create request
    addr = self.nodes[0].getnewaddress()
    pubkey = self.nodes[0].validateaddress(addr)["pubkey"]
    unspent = self.nodes[0].listunspent(1, 9999999, [], True, "PERMISSION")
    genesis = "867da0e138b1014173844ee0e4d557ff8a2463b14fcaeab18f6a63aa7c7e1d05"
    inputs = {"txid": unspent[0]["txid"], "vout": unspent[0]["vout"]}
    outputs = {"decayConst": 10, "endBlockHeight": 110, "fee": 1, "genesisBlockHash": genesis,
    "startBlockHeight": 105, "tickets": 10, "startPrice": 5, "value": unspent[0]["amount"], "pubkey": pubkey}

    tx = self.nodes[0].createrawrequesttx(inputs, outputs)
    signedtx = self.nodes[0].signrawtransaction(tx)
    requestTxid = self.nodes[0].sendrawtransaction(signedtx["hex"])
    self.nodes[0].generate(1)
    self.sync_all()

    request_bids = self.nodes[1].getrequestbids(requestTxid)
    assert(request_bids != {})
    assert_equal(request_bids, self.nodes[0].getrequestbids(requestTxid))
    assert_equal(genesis, request_bids['genesisBlock'])
    assert_equal([], request_bids['bids'])

    # test create raw bid transaction
    addr = self.nodes[1].getnewaddress()
    pubkey = self.nodes[1].validateaddress(addr)["pubkey"]
    pubkeyFee = self.nodes[1].validateaddress(self.nodes[1].getnewaddress())["pubkey"]
    unspent = self.nodes[1].listunspent(1, 9999999, [], True, asset_hash)
    inputs = [{"txid": unspent[0]["txid"], "vout": unspent[0]["vout"], "asset": asset_hash},
            {"txid": unspent[1]["txid"], "vout": unspent[1]["vout"], "asset": asset_hash}]
    fee = Decimal('0.0001')
    outputs = {"endBlockHeight": 110, "requestTxid": requestTxid, "feePubkey": pubkeyFee,
        "pubkey": pubkey, "fee": fee, "value": 75 - fee,
        "change": 25, "changeAddress": addr}

    tx = self.nodes[1].createrawbidtx(inputs, outputs)
    signedtx = self.nodes[1].signrawtransaction(tx)
    txid = self.nodes[1].sendrawtransaction(signedtx['hex'])

    self.sync_all()
    self.nodes[0].generate(1)
    self.sync_all()
    assert_equal(25, self.nodes[1].getbalance()[asset_hash])

    request_bids = self.nodes[1].getrequestbids(requestTxid)
    assert(request_bids != {})
    assert_equal(request_bids, self.nodes[0].getrequestbids(requestTxid))
    assert_equal(txid, request_bids['bids'][0]['txid'])
    assert_equal(pubkeyFee, request_bids['bids'][0]['feePubKey'])
    assert_equal(genesis, request_bids['genesisBlock'])


    fulltr = self.nodes[1].getrawtransaction(txid, True)
    foundBid = False
    for tout in fulltr['vout']:
        if "bid" in tout:
            rawbid = tout["bid"]
            if (rawbid['txid'] == request_bids['bids'][0]['txid']):
                assert_equal(request_bids['bids'][0]['feePubKey'], rawbid['feePubKey'])
                foundBid = True
                break
    assert(foundBid)

    #test stopping and restarting to make sure list is reloaded
    self.stop_node(1)
    self.nodes[1] = start_node(1, self.options.tmpdir, self.extra_args[1])
    assert_equal(request_bids, self.nodes[1].getrequestbids(requestTxid))
    connect_nodes_bi(self.nodes, 0, 1)
    self.sync_all()

    # try send spend transaction
    inputPrev = {"txid": txid, "vout": 0, "sequence": 4294967294}
    addr = self.nodes[1].getnewaddress()
    txSpend = self.nodes[1].createrawtransaction([inputPrev], {addr: unspent[0]["amount"]}, self.nodes[1].getblockcount(), {addr: asset_hash})
    signedTxSpend = self.nodes[1].signrawtransaction(txSpend)
    assert_equal(signedTxSpend["errors"][0]["error"], "Locktime requirement not satisfied")

    # make bid inactive and spend again
    self.nodes[0].generate(10)
    self.sync_all()

    # need to add another input to pay for fees
    unspent = self.nodes[1].listunspent()
    inputFee = {"txid": unspent[0]["txid"], "vout": unspent[0]["vout"]}
    addrChange = self.nodes[1].getnewaddress()
    txSpend = self.nodes[1].createrawtransaction([inputPrev, inputFee],
        {addr: 75 - fee, addrChange: 25 - fee, "fee": fee},
        self.nodes[1].getblockcount(),
        {addr: asset_hash, addrChange: asset_hash, "fee": asset_hash})
    signedTxSpend = self.nodes[1].signrawtransaction(txSpend)
    txidSpend = self.nodes[1].sendrawtransaction(signedTxSpend["hex"])

    self.sync_all()
    self.nodes[0].generate(1)
    self.sync_all()
    assert_equal(Decimal('99.99980000'), self.nodes[1].getbalance()[asset_hash])

    try:
        request_bids = self.nodes[1].getrequestbids(requestTxid)
    except JSONRPCException as exp:
        assert_equal(exp.error["message"], "No such request transaction")
    else:
        assert(False)
    try:
        request_bids = self.nodes[0].getrequestbids(requestTxid)
    except JSONRPCException as exp:
        assert_equal(exp.error["message"], "No such request transaction")
    else:
        assert(False)

    #test stopping and restarting to make sure list is reloaded
    self.stop_node(1)
    self.nodes[1] = start_node(1, self.options.tmpdir, self.extra_args[1])
    try:
        request_bids = self.nodes[1].getrequestbids(requestTxid)
    except JSONRPCException as exp:
        assert_equal(exp.error["message"], "No such request transaction")
    else:
        assert(False)

    return

if __name__ == '__main__':
  RequestbidsTest().main()
