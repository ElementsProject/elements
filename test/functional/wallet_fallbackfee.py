#!/usr/bin/env python3
# Copyright (c) 2017-2018 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test wallet replace-by-fee capabilities in conjunction with the fallbackfee."""
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_raises_rpc_error
from test_framework.util import rpc_port ## ELEMENTS

class WalletRBFTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 2
        self.setup_clean_chain = True

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):
        self.nodes[0].generate(101)

        # sending a transaction without fee estimations must be possible by default on regtest
        self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), 1)

        # test sending a tx with disabled fallback fee (must fail)
        self.restart_node(0, extra_args=["-fallbackfee=0"])
        assert_raises_rpc_error(-6, "Fee estimation failed", lambda: self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), 1))
        assert_raises_rpc_error(-4, "Fee estimation failed", lambda: self.nodes[0].fundrawtransaction(self.nodes[0].createrawtransaction([], [{self.nodes[0].getnewaddress(): 1}])))
        assert_raises_rpc_error(-6, "Fee estimation failed", lambda: self.nodes[0].sendmany("", {self.nodes[0].getnewaddress(): 1}))

        ## ELEMENTS: test claimpegin with fallback fee set to zero
        # getpeginaddress does not work with descriptor wallets yet
        if not self.options.descriptors:
            extra_args = [
                '-fallbackfee=0',
                '-mainchainrpchost=127.0.0.1',
                '-mainchainrpcport=%s' % rpc_port(0),
                '-parentgenesisblockhash=%s' % self.nodes[0].getblockhash(0),
                '-con_parent_chain_signblockscript=51',
                '-parentscriptprefix=75',
            ]
            self.restart_node(0)
            self.restart_node(1, extra_args)

            addrs = self.nodes[1].getpeginaddress()
            txid = self.nodes[0].sendtoaddress(addrs["mainchain_address"], 5)
            raw = self.nodes[0].getrawtransaction(txid)
            self.nodes[0].generate(12)
            proof = self.nodes[0].gettxoutproof([txid])
            assert_raises_rpc_error(-6, "Fee estimation failed", lambda: self.nodes[1].claimpegin(raw, proof))

            # Try again with fallbackfee below the min relay fee. It should just work
            # (will let the relay fee override the fallbackfee)
            extra_args[0] = '-fallbackfee=0.00000001'
            self.restart_node(1, extra_args)
            self.nodes[1].claimpegin(raw, proof)

if __name__ == '__main__':
    WalletRBFTest().main()
