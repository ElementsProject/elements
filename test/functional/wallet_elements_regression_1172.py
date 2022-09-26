#!/usr/bin/env python3
# Copyright (c) 2017-2020 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test blinding logic when change is dropped and we have only one other blinded input

Constructs a transaction with a sufficiently small change output that it
gets dropped, in which there is only one other blinded input. In the case
that we have no blinded inputs, we would need to add an OP_RETURN output
to the transaction, neccessitating special logic.

Check that this special logic still results in a correct transaction that
sends the money to the desired recipient (and that the recipient is able
to receive/spend the money).
"""

from decimal import Decimal

from test_framework.blocktools import COINBASE_MATURITY
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    satoshi_round,
)

class WalletCtTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 3
        self.extra_args = [[
            "-blindedaddresses=1",
            "-initialfreecoins=2100000000000000",
            "-con_blocksubsidy=0",
            "-con_connect_genesis_outputs=1",
            "-txindex=1",
        ]] * self.num_nodes
        self.extra_args[0].append("-anyonecanspendaremine=1") # first node gets the coins

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def test_send(self, amt, from_idx, to_idx, confidential):
        # Try to send those coins to yet another wallet, sending a large enough amount
        # that the change output is dropped.
        address = self.nodes[to_idx].getnewaddress()
        if not confidential:
            address = self.nodes[to_idx].getaddressinfo(address)['unconfidential']
        txid = self.nodes[from_idx].sendtoaddress(address, amt)
        self.log.info(f"Sent {amt} LBTC to node {to_idx} in {txid}")
        self.nodes[from_idx].generate(2)
        self.sync_all()

        for i in range(self.num_nodes):
            self.log.info(f"Finished with node {i} balance: {self.nodes[i].getbalance()}")
        assert_equal(self.nodes[from_idx].getbalance(), { "bitcoin": Decimal(0) })
        assert_equal(self.nodes[to_idx].getbalance(), { "bitcoin": amt })

    def run_test(self):
        # Mine 101 blocks to get the initial coins out of IBD
        self.nodes[0].generate(COINBASE_MATURITY + 1)
        self.nodes[0].syncwithvalidationinterfacequeue()
        self.sync_all()

        for i in range(self.num_nodes):
            self.log.info(f"Starting with node {i} balance: {self.nodes[i].getbalance()}")

        # Send 1 coin to a new wallet
        txid = self.nodes[0].sendtoaddress(self.nodes[1].getnewaddress(), 1)
        self.log.info(f"Sent one coin to node 1 in {txid}")
        self.nodes[0].generate(2)
        self.sync_all()

        # Try to send those coins to yet another wallet, sending a large enough amount
        # that the change output is dropped.
        amt = satoshi_round(Decimal(0.9995))
        self.test_send(amt, 1, 2, True)

        # Repeat, sending to a non-confidential output
        amt = satoshi_round(Decimal(amt - Decimal(0.00035)))
        self.test_send(amt, 2, 1, False)

        # Again, sending from non-confidential to non-confidential
        amt = satoshi_round(Decimal(amt - Decimal(0.00033)))
        self.test_send(amt, 1, 2, False)

        # Finally sending from non-confidential to confidential
        amt = satoshi_round(Decimal(amt - Decimal(0.0005)))
        self.test_send(amt, 2, 1, True)

        # Then send the coins again to make sure they're spendable
        amt = satoshi_round(Decimal(amt - Decimal(0.0005)))
        self.test_send(amt, 1, 2, True)

        addresses = [ self.nodes[1].getnewaddress() for i in range(15) ] \
            + [ self.nodes[2].getnewaddress() for i in range(15) ]
        txid = self.nodes[2].sendmany(amounts={address: satoshi_round(Decimal(0.00025)) for address in addresses})
        self.log.info(f"Sent many small UTXOs to nodes 1 and 2 in {txid}")
        self.nodes[2].generate(2)
        self.sync_all()

        self.log.info(f"Issuing some assets from node 1")
        # Try issuing assets
        amt = satoshi_round(Decimal(1))
        res1 = self.nodes[1].issueasset(amt, amt, True)
        res2 = self.nodes[1].issueasset(amt, amt, False)

        assets = [ res1["asset"], res1["token"], res2["asset"], res2["token"] ]
        addresses = [ self.nodes[2].getnewaddress() for i in range(len(assets)) ]
        txid = self.nodes[1].sendmany(
            amounts={address: amt for address in addresses},
            output_assets={addresses[i]: assets[i] for i in range(len(assets))},
        )
        self.log.info(f"Sent them to node 2 in {txid}")
        self.nodes[1].generate(2)
        self.sync_all()
        # Send them back
        addresses = [ self.nodes[1].getnewaddress() for i in range(len(assets)) ]
        txid = self.nodes[2].sendmany(
            amounts={address: amt for address in addresses},
            output_assets={addresses[i]: assets[i] for i in range(len(assets))},
        )
        self.log.info(f"Sent them back to node 1 in {txid}")

if __name__ == '__main__':
    WalletCtTest().main()

