#!/usr/bin/env python3
# Copyright (c) 2020 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

#
# Test OP_CHECKEXCHANGE
#

from test_framework.test_framework import BitcoinTestFramework
from test_framework.messages import COIN, COutPoint, CTransaction, CTxIn, CTxOut, FromHex, sha256, ToHex, CTxOutAsset, CTxOutValue
from test_framework.script import CScript, OP_HASH160, OP_CHECKSIG, OP_0, hash160, OP_EQUAL, OP_DUP, OP_EQUALVERIFY, OP_1, OP_2, OP_CHECKMULTISIG, OP_TRUE, OP_DROP, OP_RETURN, OP_CHECKEXCHANGE, OP_VERIFY
from test_framework.util import assert_equal, assert_raises_rpc_error, bytes_to_hex_str, connect_nodes, hex_str_to_bytes, sync_blocks, try_rpc

class CheckExchangeTests(BitcoinTestFramework):
    """
    """

    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 2
        [["-initialfreecoins=2100000000000000", "-anyonecanspendaremine=1", "-con_connect_genesis_outputs=1", "-con_blocksubsidy=0"]]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def setup_network(self, split=False):
        self.setup_nodes()
        connect_nodes(self.nodes[0], 1)
        self.sync_all()

    def run_test(self):
        self.nodes[0].generate(101)
        feetxid = self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 10)
        feetxblk = self.nodes[0].generate(1)[0]
        self.sync_all()

        # Issue two assets
        issuance1 = self.nodes[0].issueasset(100, 1, False)
        asset1hex = issuance1["asset"]
        asset1raw = bytearray.fromhex(asset1hex)
        asset1raw.reverse()
        asset1commitment = b"\x01" + asset1raw
        asset1 = CTxOutAsset(asset1commitment)

        issuance2 = self.nodes[0].issueasset(100, 1, False)
        asset2hex = issuance2["asset"]
        asset2raw = bytearray.fromhex(asset2hex)
        asset2raw.reverse()
        asset2commitment = b"\x01" + asset2raw
        asset2 = CTxOutAsset(asset2commitment)

        # Set up a giveaway-asset1 faucet
        # - constraint: may take a maximum of 1 sat worth, and must return remainder to faucet (i.e. same address)
        faucet = CScript([asset1raw, OP_1, OP_1, OP_0, OP_CHECKEXCHANGE])

        # Also set up auto-exchange 1 asset1 for 2 asset2, where the payments go back to the faucet
        # - constraint: must pay 1 sat worth of asset 1, and must take no more than 2 sat worth of asset 2
        exchange = CScript([asset2raw, OP_2, OP_1, asset1raw, OP_1, faucet, OP_1, OP_CHECKEXCHANGE])

        tx = CTransaction()
        tx.vout.append(CTxOut(int(1.00 * COIN), faucet, asset1))
        tx.vout.append(CTxOut(int(2.00 * COIN), exchange, asset2))
        txhex = ToHex(tx)
        funded = self.nodes[nodeid].fundrawtransaction(txhex)['hex']
        blinded = self.nodes[nodeid].blindrawtransaction(funded)
        signed = self.nodes[nodeid].signrawtransactionwithwallet(blinded)['hex']
        tx = FromHex(CTransaction(), signed)
        counter=0
        faucetpos=-1
        exchangepos=-1
        for i in tx.vout:
            if i.scriptPubKey == faucet:
                faucetpos=counter
            if i.scriptPubKey == exchange:
                exchangepos=counter
            counter += 1

        assert faucetpos > -1
        assert exchangepos > -1
        faucettxidstr = self.nodes[0].sendrawtransaction(signed)

        tx.calc_sha256()
        faucettxid = tx.sha256
        faucetoutpoint = COutPoint(faucettxid, faucetpos)
        exchangeoutpoint = COutPoint(faucettxid, exchangepos)

        self.nodes[0].generate(1)
        self.sync_all()

        node1balance_pre = self.nodes[1].getbalance()
        node1balance_pre_asset1 = node1balance_pre[asset1hex] if asset1hex in node1balance_pre else 0

        # Set up script to take 1 asset1 from faucet
        addr = self.nodes[1].getnewaddress()
        spk = bytearray.fromhex(self.nodes[1].getaddressinfo(addr)['scriptPubKey'])

        tx = self.prefund(1)
        tx.vin.append(CTxIn(faucetoutpoint))
        node1asset1vout = len(tx.vout)
        tx.vout.append(CTxOut(int(1), spk, asset1))
        tx.vout.append(CTxOut(int(1.00 * COIN - 1), faucet, asset1))
        txhex = ToHex(tx)
        signed = self.nodes[1].signrawtransactionwithwallet(txhex)['hex']
        self.nodes[1].sendrawtransaction(signed)
        tx = FromHex(CTransaction(), signed)
        tx.calc_sha256()
        node1asset1txid = tx.sha256
        node1asset1outpoint = COutPoint(node1asset1txid, node1asset1vout)

        self.sync_all()
        self.nodes[0].generate(1)

        node1balance_post = self.nodes[1].getbalance()
        node1balance_post_str = "%.8f" % (node1balance_post[asset1hex])
        assert node1balance_post_str == "0.00000001"

        # now use the exchange to get 2 asset2's for our 1 asset1

        # Set up script to buy 2 asset2 using 1 asset1 from exchange
        addr = self.nodes[1].getnewaddress()
        spk = bytearray.fromhex(self.nodes[1].getaddressinfo(addr)['scriptPubKey'])

        # fundrawtransaction doesn't like weird inputs it can't solve for, so we prep a "fee" tx
        tx = self.prefund(1)

        # IN
        # first input is our very own 1-asset1 that we got above
        tx.vin.append(CTxIn(node1asset1outpoint))           # [A] 1 in, 1 out 
        # second is the exchange
        tx.vin.append(CTxIn(exchangeoutpoint))              # [B] 2*COIN in, 2*COIN out
        # OUT
        tx.vout.append(CTxOut(int(2), spk, asset2))
        tx.vout.append(CTxOut(int(1), faucet, asset1))
        tx.vout.append(CTxOut(int(2.00 * COIN - 2), exchange, asset2))
        txhex = ToHex(tx)
        signed = self.nodes[1].signrawtransactionwithwallet(txhex)['hex']
        self.nodes[1].sendrawtransaction(signed)

        self.sync_all()
        self.nodes[0].generate(1)

        node1balance_post2 = self.nodes[1].getbalance()
        assert asset1hex not in node1balance_post2
        node1balance_post2_str = "%.8f" % (node1balance_post2[asset2hex])
        assert node1balance_post2_str == "0.00000002"

    def prefund(self, nodeid):
        # fundrawtransaction doesn't like weird inputs it can't solve for, so we prep a "fee" tx
        tx = CTransaction()
        tx.vout.append(CTxOut(int(50000), spk))
        feetx = self.nodes[nodeid].fundrawtransaction(ToHex(tx), {"feeRate": "0.0001"})
        tx = FromHex(CTransaction(), feetx['hex'])
        # bump changepos to get back those 50k above, since we will be removing that output
        tx.vout[feetx['changepos']].nValue = CTxOutValue(tx.vout[feetx['changepos']].nValue.getAmount() + 50000)
        # clean out all outputs except the changepos and fee output
        newvout = [tx.vout[feetx['changepos']]]
        for i in tx.vout:
            if i.scriptPubKey == b'':
                newvout = newvout + [i]
        tx.vout = newvout
        return tx

if __name__ == '__main__':
    CheckExchangeTests().main()
