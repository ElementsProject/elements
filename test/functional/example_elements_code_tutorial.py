#!/usr/bin/env python3
# Copyright (c) 2017-2020 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Tests reissuance functionality from the elements code tutorial
See: https://elementsproject.org/elements-code-tutorial/reissuing-assets

TODO: add functionality from contrib/assets_tutorial/assets_tutorial.py into here
"""
from test_framework.blocktools import COINBASE_MATURITY
from test_framework.test_framework import BitcoinTestFramework

class WalletTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 2
        self.extra_args = [[
            "-blindedaddresses=1",
            "-initialfreecoins=2100000000000000",
            "-con_blocksubsidy=0",
            "-con_connect_genesis_outputs=1",
            "-txindex=1",
        ]] * self.num_nodes
        self.extra_args[0].append("-anyonecanspendaremine=1")

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()
        self.skip_if_no_bdb()

    def run_test(self):
        self.generate(self.nodes[0], COINBASE_MATURITY + 1)
        self.sync_all()

        assert self.nodes[0].dumpassetlabels() == {'bitcoin': 'b2e15d0d7a0c94e4e2ce0fe6e8691b9e451377f6e46e8045a86f7c4b5d4f0f23'}

        issuance = self.nodes[0].issueasset(100, 1)
        asset = issuance['asset']
        #token = issuance['token']
        issuance_txid = issuance['txid']
        issuance_vin = issuance['vin']

        assert len(self.nodes[0].listissuances()) == 2  # asset & reisuance token

        self.nodes[0].generatetoaddress(1, self.nodes[0].getnewaddress(), invalid_call=False)  # confirm the tx

        issuance_addr = self.nodes[0].gettransaction(issuance_txid)['details'][0]['address']
        self.nodes[1].importaddress(issuance_addr)

        issuance_key = self.nodes[0].dumpissuanceblindingkey(issuance_txid, issuance_vin)
        self.nodes[1].importissuanceblindingkey(issuance_txid, issuance_vin, issuance_key)
        issuances = self.nodes[1].listissuances()
        assert (issuances[0]['tokenamount'] == 1 and issuances[0]['assetamount'] == 100) \
            or (issuances[1]['tokenamount'] == 1 and issuances[1]['assetamount'] == 100)

        self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), 1)
        self.generate(self.nodes[0], 10)

        reissuance_tx = self.nodes[0].reissueasset(asset, 99)
        reissuance_txid = reissuance_tx['txid']
        issuances = self.nodes[0].listissuances(asset)
        assert len(issuances) == 2
        assert issuances[0]['isreissuance'] or issuances[1]['isreissuance']

        self.generate(self.nodes[0], 1)

        expected_amt = {
            'bitcoin': 0,
            '8f1560e209f6bcac318569a935a0b2513c54f326ee4820ccd5b8c1b1b4632373': 0,
            '4fa41f2929d4bf6975a55967d9da5b650b6b9bfddeae4d7b54b04394be328f7f': 99
        }
        assert self.nodes[0].gettransaction(reissuance_txid)['amount'] == expected_amt

if __name__ == '__main__':
    WalletTest().main()
