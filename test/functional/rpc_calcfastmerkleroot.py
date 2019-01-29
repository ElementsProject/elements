#!/usr/bin/env python3

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal, calcfastmerkleroot
from test_framework import util

class CalcFastMerkleRoot(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 1

    def run_test(self):
        util.node_fastmerkle = self.nodes[0]

        test_leaves = ["b66b041650db0f297b53f8d93c0e8706925bf3323f8c59c14a6fac37bfdcd06f", "99cb2fa68b2294ae133550a9f765fc755d71baa7b24389fed67d1ef3e5cb0255", "257e1b2fa49dd15724c67bac4df7911d44f6689860aa9f65a881ae0a2f40a303", "b67b0b9f093fa83d5e44b707ab962502b7ac58630e556951136196e65483bb80"]
        test_roots = ["0000000000000000000000000000000000000000000000000000000000000000", "b66b041650db0f297b53f8d93c0e8706925bf3323f8c59c14a6fac37bfdcd06f", "f752938da0cb71c051aabdd5a86658e8d0b7ac00e1c2074202d8d2a79d8a6cf6", "245d364a28e9ad20d522c4a25ffc6a7369ab182f884e1c7dcd01aa3d32896bd3", "317d6498574b6ca75ee0368ec3faec75e096e245bdd5f36e8726fa693f775dfc"]

        leaves = []
        for i in range(4):
            root = calcfastmerkleroot(leaves)
            assert_equal(root, test_roots[i])
            leaves.append(test_leaves[i])

if __name__ == '__main__':
    CalcFastMerkleRoot().main()
