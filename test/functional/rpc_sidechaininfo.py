#!/usr/bin/env python3
# Copyright (c) 2026 The Elements developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test the getsidechaininfo fee-asset contract."""

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import BITCOIN_ASSET, assert_equal, assert_is_hash_string


OVERRIDE_FEE_ASSET = "11" * 32


class SidechainInfoTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 2
        self.setup_clean_chain = True
        self.extra_args = [[], [f"-feeasset={OVERRIDE_FEE_ASSET}"]]

    def setup_network(self):
        self.setup_nodes()

    def run_test(self):
        default_info = self.nodes[0].getsidechaininfo()
        override_info = self.nodes[1].getsidechaininfo()

        for info in [default_info, override_info]:
            assert_is_hash_string(info["pegged_asset"])
            assert_is_hash_string(info["fee_asset"])
            assert_equal(info["pegged_asset"], BITCOIN_ASSET)

        assert_equal(default_info["fee_asset"], default_info["pegged_asset"])
        assert_equal(override_info["fee_asset"], OVERRIDE_FEE_ASSET)
        assert_equal(override_info["pegged_asset"], default_info["pegged_asset"])


if __name__ == "__main__":
    SidechainInfoTest().main()
