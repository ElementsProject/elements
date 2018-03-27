#!/usr/bin/env python3
# Copyright (c) 2018-2018 The Elements Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    bitcoind_processes,
    start_nodes,
    start_node,
    stop_nodes,
)

import os
import tempfile
import time

class EmergencyModeTest(BitcoinTestFramework):

    def __init__(self):
        super().__init__()
        self.setup_clean_chain = True
        self.num_nodes = 1
        # Both -testemergencymode and -ignoreemergencymode shouldn't do anything
        self.extra_args = [['-debug', '-testemergencymode', '-ignoreemergencymode']]

    def setup_network(self):
        self.nodes = start_nodes(self.num_nodes, self.options.tmpdir, self.extra_args)

    def run_test(self):

        print("Ensure that node is not already in emergency mode.")
        emergency_file_path = self.options.tmpdir + "/node0/elementsregtest/ERROR_elementsregtest_HAS_SUFFERED_A_CRITICAL_FAILURE_AND_MAY_BE_UNSAFE_CORRECT_ERROR_BEFORE_REMOVING_THIS_FILE"
        assert(not os.path.isfile(emergency_file_path))
        
        self.nodes[0].generate(1) # Just to double-check the node works
        stop_nodes(self.nodes)

        self.extra_args = [['-debug', '-testemergencymode']]
        log_stderr = tempfile.SpooledTemporaryFile(max_size=2**16)
        try:
            self.nodes[0] = start_node(0, self.options.tmpdir, self.extra_args[0], stderr=log_stderr)
            raise Exception("Node shouldn't start correctly with -testemergencymode")
        except Exception as e:
            return_code = bitcoind_processes[0].wait()
            assert(return_code == 1)
            assert(str(e) == "bitcoind exited with status 1 during initialization")
            assert(os.path.isfile(emergency_file_path))
            log_stderr.seek(0)
            stderr_out = log_stderr.read().decode('utf-8')
            assert(stderr_out == 'Error: Using -testemergencymode\n'
                   'Error: Error: A fatal internal error occurred, see debug.log for details\n')
            log_stderr.close()

        os.remove(emergency_file_path)
        # Once the file is removed it starts normally again
        self.extra_args = [['-debug']]
        self.nodes = start_nodes(self.num_nodes, self.options.tmpdir, self.extra_args)
        
        print("Success!")

if __name__ == '__main__':
    EmergencyModeTest().main()
