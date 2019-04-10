#!/usr/bin/env python3
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *

# Test for the guardnode system
# TODO: add more tests as work on this progresses
class GuardnodeTest(BitcoinTestFramework):
  def __init__(self):
    super().__init__()
    self.setup_clean_chain = True
    self.num_nodes = 2
    self.extra_args = [["-txindex=1 -initialfreecoins=50000000000000",
    "-permissioncoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac",
    "-initialfreecoinsdestination=76a914bc835aff853179fa88f2900f9003bb674e17ed4288ac"] for i in range(2)]

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

    # send PERMISSION asset to node 1
    self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 1000, "", "", False, "PERMISSION")
    self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 1000, "", "", False, "PERMISSION")
    self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 1000, "", "", False, "CBT")
    self.nodes[0].generate(1)
    self.sync_all()
    assert(self.nodes[1].getbalance()["PERMISSION"] == 2000)

    # test create request with incorrect asset
    addr = self.nodes[1].getnewaddress()
    priv = self.nodes[1].dumpprivkey(addr)
    pubkey = self.nodes[1].validateaddress(addr)["pubkey"]
    unspent = self.nodes[1].listunspent(1, 9999999, [], True, "CBT")
    genesis = "867da0e138b1014173844ee0e4d557ff8a2463b14fcaeab18f6a63aa7c7e1d05"
    genesis2 = "967da0e138b1014173844ee0e4d557ff8a2463b14fcaeab18f6a63aa7c7e1d05"
    inputs = {"txid": unspent[0]["txid"], "vout": unspent[0]["vout"], "asset": unspent[0]["asset"]}
    outputs = {"decayConst": 10, "endBlockHeight": 20000, "fee": 1, "genesisBlockHash": genesis,
    "startBlockHeight": 10000, "tickets": 10, "value": unspent[0]["amount"], "pubkey": pubkey}

    # catch errror - missing pubkey from outputs
    try:
        tx = self.nodes[1].createrawrequesttx(inputs, outputs)
        signedtx = self.nodes[1].signrawtransaction(tx)
        self.nodes[1].sendrawtransaction(signedtx["hex"])
    except JSONRPCException as e:
        assert("bad-txns-in-ne-out" in e.error['message'])

    # create new raw request transaction with missing details
    unspent = self.nodes[1].listunspent(1, 9999999, [], True, "PERMISSION")
    inputs = {"txid": unspent[0]["txid"], "vout": unspent[0]["vout"], "asset": unspent[0]["asset"]}
    inputs2 = {"txid": unspent[1]["txid"], "vout": unspent[1]["vout"], "asset": unspent[1]["asset"]}
    outputs = {"decayConst": 10, "endBlockHeight": 20000, "fee": 1, "genesisBlockHash": genesis,
    "startBlockHeight": 10000, "tickets": 10, "value": unspent[0]["amount"]}

    # catch errror - missing pubkey from outputs
    try:
        tx = self.nodes[1].createrawrequesttx(inputs, outputs)
    except Exception as e:
        assert(e)

    # re create transaction again and add pubkey
    outputs = {"decayConst": 10, "endBlockHeight": 105, "fee": 1, "genesisBlockHash": genesis,
    "startBlockHeight": 100, "tickets": 10, "value": unspent[0]["amount"], "pubkey": pubkey}
    outputs2 = {"decayConst": 5, "endBlockHeight": 120, "fee": 3, "genesisBlockHash": genesis2,
    "startBlockHeight": 105, "tickets": 5, "value": unspent[1]["amount"], "pubkey": pubkey}

    # send transaction
    tx = self.nodes[1].createrawrequesttx(inputs, outputs)
    signedtx = self.nodes[1].signrawtransaction(tx)
    txid = self.nodes[1].sendrawtransaction(signedtx["hex"])

    tx2 = self.nodes[1].createrawrequesttx(inputs2, outputs2)
    signedtx2 = self.nodes[1].signrawtransaction(tx2)
    txid2 = self.nodes[1]. sendrawtransaction(signedtx2["hex"])
    self.sync_all()
    self.nodes[0].generate(1)
    self.sync_all()
    assert(txid in self.nodes[0].getblock(self.nodes[0].getblockhash(self.nodes[0].getblockcount()))["tx"])

    # test get request method with/without genesis hash parameter
    requests = self.nodes[0].getrequests()
    assert_equal(2, len(requests))
    for req in requests:
        if txid == req['txid']:
            assert_equal(req['endBlockHeight'], 105)
            assert_equal(req['genesisBlock'], genesis)
            assert_equal(req['numTickets'], 10)
            assert_equal(req['decayConst'], 10)
            assert_equal(req['feePercentage'], 1)
            assert_equal(req['startBlockHeight'], 100)
        elif txid2 == req['txid']:
            assert(True)
        else:
            assert(False)
    requests = self.nodes[0].getrequests(genesis)
    assert_equal(1, len(requests))
    for req in requests:
        if txid == req['txid']:
            assert_equal(req['endBlockHeight'], 105)
            assert_equal(req['genesisBlock'], genesis)
            assert_equal(req['numTickets'], 10)
            assert_equal(req['decayConst'], 10)
            assert_equal(req['feePercentage'], 1)
            assert_equal(req['startBlockHeight'], 100)
        else:
            assert(False)
    requests = self.nodes[0].getrequests(genesis2)
    assert_equal(1, len(requests))
    for req in requests:
        if txid2 == req['txid']:
            assert_equal(req['endBlockHeight'], 120)
            assert_equal(req['genesisBlock'], genesis2)
            assert_equal(req['numTickets'], 5)
            assert_equal(req['decayConst'], 5)
            assert_equal(req['feePercentage'], 3)
            assert_equal(req['startBlockHeight'], 105)
        else:
            assert(False)
    requests = self.nodes[0].getrequests("123450e138b1014173844ee0e4d557ff8a2463b14fcaeab18f6a63aa7c7e1d05")
    assert_equal(requests, [])

    # try send spend transaction
    inputs = {"txid": txid, "vout": 0, "sequence": 4294967294}
    fee = Decimal('0.0001')
    addr = self.nodes[1].getnewaddress()
    outputs = {addr: unspent[0]["amount"] - fee, "fee": fee}
    txSpend = self.nodes[1].createrawtransaction([inputs], outputs, self.nodes[1].getblockcount())
    signedTxSpend = self.nodes[1].signrawtransaction(txSpend)
    assert_equal(signedTxSpend["errors"][0]["error"], "Locktime requirement not satisfied")

    # make request 1 inactive
    self.nodes[0].generate(10)
    requests = self.nodes[0].getrequests()
    assert_equal(1, len(requests))
    for req in requests:
        if txid2 == req['txid']:
            assert_equal(req['endBlockHeight'], 120)
            assert_equal(req['genesisBlock'], genesis2)
            assert_equal(req['numTickets'], 5)
            assert_equal(req['decayConst'], 5)
            assert_equal(req['feePercentage'], 3)
            assert_equal(req['startBlockHeight'], 105)
        else:
            assert(False)
    requests = self.nodes[0].getrequests(genesis2)
    assert_equal(1, len(requests))
    for req in requests:
        if txid2 == req['txid']:
            assert_equal(req['endBlockHeight'], 120)
            assert_equal(req['genesisBlock'], genesis2)
            assert_equal(req['numTickets'], 5)
            assert_equal(req['decayConst'], 5)
            assert_equal(req['feePercentage'], 3)
            assert_equal(req['startBlockHeight'], 105)
        else:
            assert(False)

    # make request 2 inactive
    self.nodes[0].generate(10)
    assert_equal([], self.nodes[0].getrequests())

    # # generate more blocks and try again
    # # CLTV signing not supported in bitcoin
    # txraw = self.nodes[1].getrawtransaction(txid, 1)
    # txSpend2 = self.nodes[1].createrawtransaction([inputs], outputs, self.nodes[1].getblockcount())
    # signedTxSpend2 = self.nodes[1].signrawtransaction(txSpend2,
    #     [{
    #         "txid": txid,
    #         "vout": 0,
    #         "scriptPubKey": txraw["vout"][0]["scriptPubKey"]["hex"],
    #         "amount": unspent[0]["amount"]
    #     }],
    #     [priv])
    # print(signedTxSpend2)
    # print(self.nodes[1].decoderawtransaction(signedTxSpend2["hex"]))
    # assert_equal(signedTxSpend2["errors"][0]["error"], "")

    return

if __name__ == '__main__':
  GuardnodeTest().main()
