#!/usr/bin/env python3
# Copyright (c) 2020-2021 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test error messages for 'getaddressinfo' and 'validateaddress' RPC commands."""

from test_framework.test_framework import BitcoinTestFramework

from test_framework.util import (
    assert_equal,
    assert_raises_rpc_error,
)

BECH32_VALID = 'ert1qtmp74ayg7p24uslctssvjm06q5phz4yr7gdkdv'
BECH32_VALID_CAPITALS = 'ERT1QTMP74AYG7P24USLCTSSVJM06Q5PHZ4YR7GDKDV'
BECH32_VALID_MULTISIG = 'ert1qmzm84udpuz6axdstxlpwafca7g7nh5w2yu8c7vqhe0rhjkcrfcfqwymvhe'

BECH32_INVALID_BECH32 = 'ert1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqugsf3u'
BECH32_INVALID_BECH32M = 'ert1qw508d6qejxtdg4y5r3zarvary0c5xw7kfqwaud'
BECH32_INVALID_VERSION = 'ert130xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq4q68pj'
BECH32_INVALID_SIZE = 'ert1s0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v8n0nx0muaewav25pltc58'
BECH32_INVALID_V0_SIZE = 'ert1qw508d6qejxtdg4y5r3zarvary0c5xw7kqq2287l0'
BECH32_INVALID_PREFIX = 'bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7k7grplx'
BECH32_TOO_LONG = 'ert1q049edschfnwystcqnsvyfpj23mpsg3jcedq9xv049edschfnwystcqnsvyfpj23mpsg3jcedq9xv049edschfnwystcqnsvyfpj23m'
BECH32_ONE_ERROR = 'ert1qtmp7aayg7p24uslctssvjm06q5phz4yr7gdkdv'
BECH32_ONE_ERROR_CAPITALS = 'ERT1QTMP7AAYG7P24USLCTSSVJM06Q5PHZ4YR7GDKDV'
BECH32_TWO_ERRORS = 'ert1qtmp74syg7p24uslctsavjm06q5phz4yr7gdkdv'
BECH32_NO_SEPARATOR = 'ertq049ldschfnwystcqnsvyfpj23mpsg3jcedq9xv'
BECH32_INVALID_CHAR = 'ert1q04oldschfnwystcqnsvyfpj23mpsg3jcedq9xv'
BECH32_MULTISIG_TWO_ERRORS = 'ert1qmzm84udpua6axdstxlpwafca7g7na5w2yu8c7vqhe0rhjkcrfcfqwymvhe'
BECH32_WRONG_VERSION = 'ert1ptmp74ayg7p24uslctssvjm06q5phz4yr7gdkdv'

BASE58_VALID = '2dcjQH4DQC3pMcSQkMkSQyPPEr7rZ6Ga4GR'
BASE58_INVALID_PREFIX = '17VZNX1SN5NtKa8UQFxwQbFeFc3iqRYhem'
BASE58_INVALID_CHECKSUM = 'mipcBbFg9gMiCh81Kj8tqqdgoZub1ZJJfn'
BASE58_INVALID_LENGTH = '2dcjQH4DQC3pMcSQkMkSQyPPEr7rZ6Ga4GR7rZ6Ga4GR'

INVALID_ADDRESS = 'asfah14i8fajz0123f'
INVALID_ADDRESS_2 = '1q049ldschfnwystcqnsvyfpj23mpsg3jcedq9xv'

# ELEMENTS
BLECH32_VALID = 'el1qq0umk3pez693jrrlxz9ndlkuwne93gdu9g83mhhzuyf46e3mdzfpva0w48gqgzgrklncnm0k5zeyw8my2ypfsmxh4xcjh2rse'
BLECH32_INVALID_BLECH32 = 'el1pq0umk3pez693jrrlxz9ndlkuwne93gdu9g83mhhzuyf46e3mdzfpva0w48gqgzgrklncnm0k5zeyw8my2ypfsxguu9nrdg2pc'
BLECH32_INVALID_BLECH32M = 'el1qq0umk3pez693jrrlxz9ndlkuwne93gdu9g83mhhzuyf46e3mdzfpva0w48gqgzgrklncnm0k5zeyw8my2ypfsnnmzrstzt7de'
BLECH32_INVALID_VERSION = 'ert130xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq4q68pj'
BLECH32_INVALID_SIZE = 'el1pq0umk3pez693jrrlxz9ndlkuwne93gdu9g83mhhzuyf46e3mdzfpva0w48gqgzgrklncnm0k5zeyw8my2ypfsqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqpe9jfn0gypaj'
BLECH32_INVALID_V0_SIZE = 'ert1qw508d6qejxtdg4y5r3zarvary0c5xw7kqq2287l0'
BLECH32_INVALID_PREFIX = 'lq1qq0umk3pez693jrrlxz9ndlkuwne93gdu9g83mhhzuyf46e3mdzfpva0w48gqgzgrklncnm0k5zeyw8my2ypfscmm3q74jvv3r'


class InvalidAddressErrorMessageTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 1

    def check_valid(self, addr):
        info = self.nodes[0].validateaddress(addr)
        assert info['isvalid']
        assert 'error' not in info
        assert 'error_locations' not in info

    def check_invalid(self, addr, error_str, error_locations=None):
        res = self.nodes[0].validateaddress(addr)
        assert not res['isvalid']
        assert_equal(res['error'], error_str)
        if error_locations:
            assert_equal(res['error_locations'], error_locations)
        else:
            assert_equal(res['error_locations'], [])

    def test_validateaddress(self):
        # Invalid Bech32
        self.check_invalid(BECH32_INVALID_SIZE, 'Invalid Bech32 address data size')
        self.check_invalid(BECH32_INVALID_PREFIX, 'Invalid prefix for Bech32 address')
        self.check_invalid(BECH32_INVALID_BECH32, 'Version 1+ witness address must use Bech32m checksum')
        self.check_invalid(BECH32_INVALID_BECH32M, 'Version 0 witness address must use Bech32 checksum')
        self.check_invalid(BECH32_INVALID_VERSION, 'Invalid Bech32 address witness version')
        self.check_invalid(BECH32_INVALID_V0_SIZE, 'Invalid Bech32 v0 address data size')
        self.check_invalid(BECH32_TOO_LONG, 'Bech32 string too long', list(range(90, 107)))
        self.check_invalid(BECH32_ONE_ERROR, 'Invalid Bech32 checksum', [9])
        self.check_invalid(BECH32_TWO_ERRORS, 'Invalid Bech32 checksum', [10, 23])
        self.check_invalid(BECH32_ONE_ERROR_CAPITALS, 'Invalid Bech32 checksum', [9])
        self.check_invalid(BECH32_NO_SEPARATOR, 'Missing separator')
        self.check_invalid(BECH32_INVALID_CHAR, 'Invalid Base 32 character', [7])
        self.check_invalid(BECH32_MULTISIG_TWO_ERRORS, 'Invalid Bech32 checksum', [14, 33])
        self.check_invalid(BECH32_WRONG_VERSION, 'Invalid Bech32 checksum', [4])

        # Valid Bech32
        self.check_valid(BECH32_VALID)
        self.check_valid(BECH32_VALID_CAPITALS)
        self.check_valid(BECH32_VALID_MULTISIG)

        # Invalid Base58
        self.check_invalid(BASE58_INVALID_PREFIX, 'Invalid prefix for Base58-encoded address')
        self.check_invalid(BASE58_INVALID_CHECKSUM, 'Invalid checksum or length of Base58 address')
        self.check_invalid(BASE58_INVALID_LENGTH, 'Invalid checksum or length of Base58 address')

        # Valid Base58
        self.check_valid(BASE58_VALID)

        # Invalid address format
        self.check_invalid(INVALID_ADDRESS, 'Not a valid Bech32 or Base58 encoding')
        self.check_invalid(INVALID_ADDRESS_2, 'Not a valid Bech32 or Base58 encoding')

        # ELEMENTS
        info = self.nodes[0].validateaddress(BLECH32_INVALID_SIZE)
        assert not info['isvalid']
        assert_equal(info['error'], 'Invalid Blech32 address data size')

        info = self.nodes[0].validateaddress(BLECH32_INVALID_PREFIX)
        assert not info['isvalid']
        assert_equal(info['error'], 'Invalid prefix for Blech32 address')

        info = self.nodes[0].validateaddress(BLECH32_INVALID_BLECH32)
        assert not info['isvalid']
        assert_equal(info['error'], 'Version 1+ witness address must use Blech32m checksum')

        info = self.nodes[0].validateaddress(BLECH32_INVALID_BLECH32M)
        assert not info['isvalid']
        assert_equal(info['error'], 'Version 0 witness address must use Blech32 checksum')

        info = self.nodes[0].validateaddress(BLECH32_VALID)
        assert info['isvalid']
        assert 'error' not in info

    def test_getaddressinfo(self):
        node = self.nodes[0]

        assert_raises_rpc_error(-5, "Invalid Bech32 address data size", node.getaddressinfo, BECH32_INVALID_SIZE)

        # assert_raises_rpc_error(-5, "Not a valid Bech32 or Base58 encoding", node.getaddressinfo, BECH32_INVALID_PREFIX) # ELEMENTS: FIXME

        assert_raises_rpc_error(-5, "Invalid prefix for Base58-encoded address", node.getaddressinfo, BASE58_INVALID_PREFIX)

        # assert_raises_rpc_error(-5, "Invalid HRP or Base58 character in address", node.getaddressinfo, INVALID_ADDRESS) # ELEMENTS: FIXME
        # assert_raises_rpc_error(-5, "Not a valid Bech32 or Base58 encoding", node.getaddressinfo, INVALID_ADDRESS) # ELEMENTS: FIXME

        # ELEMENTS
        assert_raises_rpc_error(-5, "Invalid Blech32 address data size", node.getaddressinfo, BLECH32_INVALID_SIZE)

        assert_raises_rpc_error(-5, "Invalid prefix for Blech32 address", node.getaddressinfo, BLECH32_INVALID_PREFIX)

    def run_test(self):
        self.test_validateaddress()

        if self.is_wallet_compiled():
            self.init_wallet(node=0)
            self.test_getaddressinfo()


if __name__ == '__main__':
    InvalidAddressErrorMessageTest().main()