#!/usr/bin/env python3
# Copyright (c) 2026 The Elements developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test the getsidechaininfo fee-asset contract."""

from copy import deepcopy
from decimal import Decimal

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import BITCOIN_ASSET, assert_equal


DEFAULT_INFO = {
    "fedpegscript": "51",
    "current_fedpeg_programs": ["a91472c44f957fc011d97e3406667dca5b1c930c402687"],
    "current_fedpegscripts": ["51"],
    "pegged_asset": BITCOIN_ASSET,
    "fee_asset": BITCOIN_ASSET,
    "genesis_subsidy": Decimal("50.00000000"),
    "subsidy_asset": BITCOIN_ASSET,
    "subsidy_halving_interval": 150,
    "min_peg_diff": "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
    "parent_blockhash": "0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206",
    "parent_chain_has_pow": True,
    "enforce_pak": False,
    "pegin_confirmation_depth": 8,
}
OVERRIDE_FEE_ASSET = "11" * 32
BLOCKSUBSIDY_INFO = {
    "genesis_subsidy": 0,
    "subsidy_asset": "aa" * 32,
    "subsidy_halving_interval": 10,
}


class SidechainInfoTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 3
        self.setup_clean_chain = True
        self.extra_args = [
            # node 0: default
            [],
            # node 1: override feeasset
            [f"-feeasset={OVERRIDE_FEE_ASSET}"],
            # node 2: override blocksubsidy params
            [
                f"-con_blocksubsidy={BLOCKSUBSIDY_INFO['genesis_subsidy']}",
                f"-con_nsubsidyhalvinginterval={BLOCKSUBSIDY_INFO['subsidy_halving_interval']}",
                f"-subsidyasset={BLOCKSUBSIDY_INFO['subsidy_asset']}",
            ]
        ]

    def setup_network(self):
        self.setup_nodes()

    def run_test(self):
        assert_equal(self.nodes[0].getsidechaininfo(), DEFAULT_INFO)

        info = deepcopy(DEFAULT_INFO)
        info.update({"fee_asset": OVERRIDE_FEE_ASSET})
        assert_equal(self.nodes[1].getsidechaininfo(), info)

        info = deepcopy(DEFAULT_INFO)
        info.update(BLOCKSUBSIDY_INFO)
        assert_equal(self.nodes[2].getsidechaininfo(), info)


if __name__ == "__main__":
    SidechainInfoTest(__file__).main()
