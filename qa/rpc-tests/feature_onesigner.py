#!/usr/bin/env python3

from feature_blocksign import BlockSignTest

if __name__ == '__main__':
    BlockSignTest(num_nodes=1, required_signers=1).main()
