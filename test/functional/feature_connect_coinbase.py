#!/usr/bin/env python3
# Copyright (c) 2014-2018 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test connecting genesis coinbase"""

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal, assert_raises_rpc_error

class ConnectGenesisTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 2
        self.setup_clean_chain = True
        # First node doesn't connect coinbase output to db, second does
        self.extra_args = [["-con_connect_coinbase=0", "-initialfreecoins=5000000000"], ["-con_connect_coinbase=1", "-initialfreecoins=5000000000"]]

    def run_test(self):
        # Same genesis block
        assert_equal(self.nodes[0].getblockhash(0), self.nodes[1].getblockhash(0))

        # Different UTXO set
        node0_info = self.nodes[0].gettxoutsetinfo()
        node1_info = self.nodes[1].gettxoutsetinfo()
        print(node0_info)
        print(node1_info)
        assert_equal(node0_info["txouts"], 0)
        assert_equal(node0_info["transactions"], 0)
        assert_equal(node0_info["total_amount"], 0)
        assert_equal(node1_info["txouts"], 1)
        assert_equal(node1_info["transactions"], 1)
        assert_equal(node1_info["total_amount"], 50)

        coinbase_tx = self.nodes[0].getblock(self.nodes[0].getblockhash(0))["tx"][0]
        issuance_tx = self.nodes[0].getblock(self.nodes[0].getblockhash(0))["tx"][1]

        # Test rpc getraw functionality

        # Coinbase transaction is provably unspendable (OP_RETURN), so even AddCoin won't add it
        assert_raises_rpc_error(-5, "No such mempool transaction. Use -txindex to enable blockchain transaction queries. Use gettransaction for wallet transactions.", self.nodes[0].getrawtransaction, coinbase_tx)
        assert_raises_rpc_error(-5, "No such mempool transaction. Use -txindex to enable blockchain transaction queries. Use gettransaction for wallet transactions.", self.nodes[1].getrawtransaction, coinbase_tx)

        # Issuance transaction is an OP_TRUE, so will be available to second node
        assert_raises_rpc_error(-5, "No such mempool transaction. Use -txindex to enable blockchain transaction queries. Use gettransaction for wallet transactions.", self.nodes[0].getrawtransaction, issuance_tx)
        self.nodes[1].getrawtransaction(issuance_tx)

if __name__ == '__main__':
    ConnectGenesisTest().main()
