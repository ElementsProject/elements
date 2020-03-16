#!/usr/bin/env python3
# Copyright (c) 2018 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test the wallet balance RPC methods."""
from decimal import Decimal

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    assert_raises_rpc_error,
    BITCOIN_ASSET,
)

RANDOM_COINBASE_ADDRESS = 'XSUuFy4upmMmBo75Gpw3RPXsKJp81FpVVi'

def create_transactions(node, address, amt, fees):
    # Create and sign raw transactions from node to address for amt.
    # Creates a transaction for each fee and returns an array
    # of the raw transactions.
    utxos = node.listunspent(0)

    # Create transactions
    inputs = []
    ins_total = 0
    for utxo in utxos:
        assert utxo['asset'] == BITCOIN_ASSET
        inputs.append({"txid": utxo["txid"], "vout": utxo["vout"]})
        ins_total += utxo['amount']
        if ins_total + max(fees) > amt:
            break
    # make sure there was enough utxos
    assert ins_total >= amt + max(fees)

    txs = []
    for fee in fees:
        outputs = {address: amt}
        # prevent 0 change output
        if ins_total > amt + fee:
            outputs[node.getrawchangeaddress()] = ins_total - amt - fee
        if fee > 0:
            outputs["fee"] = fee
        raw_tx = node.createrawtransaction(inputs, outputs, 0, True)
        raw_tx = node.signrawtransactionwithwallet(raw_tx)
        txs.append(raw_tx)

    return txs

class WalletTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 2
        self.setup_clean_chain = True

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):
        # Check that nodes don't own any UTXOs
        assert_equal(len(self.nodes[0].listunspent()), 0)
        assert_equal(len(self.nodes[1].listunspent()), 0)

        self.log.info("Mining one block for each node")

        self.nodes[0].generate(1)
        self.sync_all()
        self.nodes[1].generate(1)
        self.nodes[1].generatetoaddress(100, RANDOM_COINBASE_ADDRESS)
        self.sync_all()

        assert_equal(self.nodes[0].getbalance()['bitcoin'], 50)
        assert_equal(self.nodes[1].getbalance()['bitcoin'], 50)

        self.log.info("Test getbalance with different arguments")
        assert_equal(self.nodes[0].getbalance("*")['bitcoin'], 50)
        assert_equal(self.nodes[0].getbalance("*", 1)['bitcoin'], 50)
        assert_equal(self.nodes[0].getbalance("*", 1, True)['bitcoin'], 50)
        assert_equal(self.nodes[0].getbalance(minconf=1)['bitcoin'], 50)

        # Send 40 BTC from 0 to 1 and 60 BTC from 1 to 0.
        txs = create_transactions(self.nodes[0], self.nodes[1].getnewaddress(), 40, [Decimal('0.01')])
        self.nodes[0].sendrawtransaction(txs[0]['hex'])
        self.nodes[1].sendrawtransaction(txs[0]['hex'])  # sending on both nodes is faster than waiting for propagation

        self.sync_all()
        txs = create_transactions(self.nodes[1], self.nodes[0].getnewaddress(), 60, [Decimal('0.01'), Decimal('0.02')])
        self.nodes[1].sendrawtransaction(txs[0]['hex'])
        self.nodes[0].sendrawtransaction(txs[0]['hex'])  # sending on both nodes is faster than waiting for propagation
        self.sync_all()

        # First argument of getbalance must be set to "*"
        assert_raises_rpc_error(-32, "dummy first argument must be excluded or set to \"*\"", self.nodes[1].getbalance, "")

        self.log.info("Test getbalance and getunconfirmedbalance with unconfirmed inputs")

        # getbalance without any arguments includes unconfirmed transactions, but not untrusted transactions
        assert_equal(self.nodes[0].getbalance()['bitcoin'], Decimal('9.99'))  # change from node 0's send
        assert_equal(self.nodes[1].getbalance()['bitcoin'], Decimal('29.99'))  # change from node 1's send
        # Same with minconf=0
        assert_equal(self.nodes[0].getbalance(minconf=0)['bitcoin'], Decimal('9.99'))
        assert_equal(self.nodes[1].getbalance(minconf=0)['bitcoin'], Decimal('29.99'))
        # getbalance with a minconf incorrectly excludes coins that have been spent more recently than the minconf blocks ago
        # TODO: fix getbalance tracking of coin spentness depth
        assert_equal(self.nodes[0].getbalance(minconf=1)['bitcoin'], Decimal('0'))
        assert_equal(self.nodes[1].getbalance(minconf=1)['bitcoin'], Decimal('0'))
        # getunconfirmedbalance
        assert_equal(self.nodes[0].getunconfirmedbalance()['bitcoin'], Decimal('60'))  # output of node 1's spend
        assert_equal(self.nodes[1].getunconfirmedbalance()['bitcoin'], Decimal('0'))  # Doesn't include output of node 0's send since it was spent

        # Node 1 bumps the transaction fee and resends
        self.nodes[1].sendrawtransaction(txs[1]['hex'])
        self.sync_all()

        self.log.info("Test getbalance and getunconfirmedbalance with conflicted unconfirmed inputs")

        assert_equal(self.nodes[0].getwalletinfo()["unconfirmed_balance"]['bitcoin'], Decimal('60'))  # output of node 1's send
        assert_equal(self.nodes[0].getunconfirmedbalance()['bitcoin'], Decimal('60'))
        assert_equal(self.nodes[1].getwalletinfo()["unconfirmed_balance"]['bitcoin'], Decimal('0'))  # Doesn't include output of node 0's send since it was spent
        assert_equal(self.nodes[1].getunconfirmedbalance()['bitcoin'], Decimal('0'))

        self.nodes[1].generatetoaddress(1, RANDOM_COINBASE_ADDRESS)
        self.sync_all()

        # balances are correct after the transactions are confirmed
        assert_equal(self.nodes[0].getbalance()['bitcoin'], Decimal('69.99'))  # node 1's send plus change from node 0's send
        assert_equal(self.nodes[1].getbalance()['bitcoin'], Decimal('29.98'))  # change from node 0's send

        # Send total balance away from node 1
        txs = create_transactions(self.nodes[1], self.nodes[0].getnewaddress(), Decimal('29.97'), [Decimal('0.01')])
        self.nodes[1].sendrawtransaction(txs[0]['hex'])
        self.nodes[1].generatetoaddress(2, RANDOM_COINBASE_ADDRESS)
        self.sync_all()

        # getbalance with a minconf incorrectly excludes coins that have been spent more recently than the minconf blocks ago
        # TODO: fix getbalance tracking of coin spentness depth
        # getbalance with minconf=3 should still show the old balance
        assert_equal(self.nodes[1].getbalance(minconf=3)['bitcoin'], Decimal('0'))

        # getbalance with minconf=2 will show the new balance.
        assert_equal(self.nodes[1].getbalance(minconf=2)['bitcoin'], Decimal('0'))

        # Balances of assets
        for blind in [True, False]:
            self.log.info("Testing {} issued asset balances".format("blinded" if blind else "unblinded"))
            asset = self.nodes[0].issueasset(100, 0, blind)["asset"]

            # Balances with unconfirmed issuance.
            # They are indicated as confirmed because they are sent by the RPC and thus "trusted".
            walletinfo = self.nodes[0].getwalletinfo()
            assert_equal(walletinfo["balance"].get(asset, 0), Decimal('100'))
            assert_equal(walletinfo["unconfirmed_balance"].get(asset, 0), Decimal('0'))

            # Balances with confirmed issuance.
            self.nodes[0].generatetoaddress(1, RANDOM_COINBASE_ADDRESS)
            walletinfo = self.nodes[0].getwalletinfo()
            assert_equal(walletinfo["balance"].get(asset, 0), Decimal('100'))
            assert_equal(walletinfo["unconfirmed_balance"].get(asset, 0), Decimal('0'))

            # Sending coins to other wallet.
            self.nodes[0].sendtoaddress(address=self.nodes[1].getnewaddress(), amount="50", assetlabel=asset)
            self.sync_all()

            # Balances with unconfirmed receive
            walletinfo = self.nodes[1].getwalletinfo()
            assert_equal(walletinfo["balance"].get(asset, 0), Decimal('0'))
            assert_equal(walletinfo["unconfirmed_balance"].get(asset, 0), Decimal('50'))

            # Balances with confirmed receive
            self.nodes[1].generatetoaddress(1, RANDOM_COINBASE_ADDRESS)
            walletinfo = self.nodes[1].getwalletinfo()
            assert_equal(walletinfo["balance"].get(asset, 0), Decimal('50'))
            assert_equal(walletinfo["unconfirmed_balance"].get(asset, 0), Decimal('0'))

if __name__ == '__main__':
    WalletTest().main()
