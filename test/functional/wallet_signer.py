#!/usr/bin/env python3
# Copyright (c) 2017-2021 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test external signer.

Verify that a bitcoind node can use an external signer command
See also rpc_signer.py for tests without wallet context.
"""
import os
import platform

from test_framework.test_framework import BitcoinTestFramework, SkipTest
from test_framework.util import (
    assert_equal,
    assert_raises_rpc_error,
)


class WalletSignerTest(BitcoinTestFramework):
    def add_options(self, parser):
        self.add_wallet_options(parser, legacy=False)

    def mock_signer_path(self):
        path = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'mocks', 'signer.py')
        if platform.system() == "Windows":
            return "py " + path
        else:
            return path

    def mock_invalid_signer_path(self):
        path = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'mocks', 'invalid_signer.py')
        if platform.system() == "Windows":
            return "py " + path
        else:
            return path

    def mock_multi_signers_path(self):
        path = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'mocks', 'multi_signers.py')
        if platform.system() == "Windows":
            return "py " + path
        else:
            return path

    def set_test_params(self):
        self.num_nodes = 2
        # The experimental syscall sandbox feature (-sandbox) is not compatible with -signer (which
        # invokes execve).
        self.disable_syscall_sandbox = True

        self.extra_args = [
            [],
            [f"-signer={self.mock_signer_path()}", '-keypool=10'],
        ]

    def skip_test_if_missing_module(self):
        self.skip_if_no_external_signer()
        self.skip_if_no_wallet()
        raise SkipTest("ELEMENTS: see `git blame` on this line of code for more info")

    def set_mock_result(self, node, res):
        with open(os.path.join(node.cwd, "mock_result"), "w", encoding="utf8") as f:
            f.write(res)

    def clear_mock_result(self, node):
        os.remove(os.path.join(node.cwd, "mock_result"))

    def run_test(self):
        self.test_valid_signer()
        self.restart_node(1, [f"-signer={self.mock_invalid_signer_path()}", "-keypool=10"])
        self.test_invalid_signer()
        self.restart_node(1, [f"-signer={self.mock_multi_signers_path()}", "-keypool=10"])
        self.test_multiple_signers()

    def test_valid_signer(self):
        self.log.debug(f"-signer={self.mock_signer_path()}")

        # Create new wallets for an external signer.
        # disable_private_keys and descriptors must be true:
        assert_raises_rpc_error(-4, "Private keys must be disabled when using an external signer", self.nodes[1].createwallet, wallet_name='not_hww', disable_private_keys=False, descriptors=True, external_signer=True)
        if self.is_bdb_compiled():
            assert_raises_rpc_error(-4, "Descriptor support must be enabled when using an external signer", self.nodes[1].createwallet, wallet_name='not_hww', disable_private_keys=True, descriptors=False, external_signer=True)
        else:
            assert_raises_rpc_error(-4, "Compiled without bdb support (required for legacy wallets)", self.nodes[1].createwallet, wallet_name='not_hww', disable_private_keys=True, descriptors=False, external_signer=True)

        self.nodes[1].createwallet(wallet_name='hww', disable_private_keys=True, descriptors=True, external_signer=True)
        hww = self.nodes[1].get_wallet_rpc('hww')
        assert_equal(hww.getwalletinfo()["external_signer"], True)

        # Flag can't be set afterwards (could be added later for non-blank descriptor based watch-only wallets)
        self.nodes[1].createwallet(wallet_name='not_hww', disable_private_keys=True, descriptors=True, external_signer=False)
        not_hww = self.nodes[1].get_wallet_rpc('not_hww')
        assert_equal(not_hww.getwalletinfo()["external_signer"], False)
        assert_raises_rpc_error(-8, "Wallet flag is immutable: external_signer", not_hww.setwalletflag, "external_signer", True)

        # assert_raises_rpc_error(-4, "Multiple signers found, please specify which to use", wallet_name='not_hww', disable_private_keys=True, descriptors=True, external_signer=True)

        # TODO: Handle error thrown by script
        # self.set_mock_result(self.nodes[1], "2")
        # assert_raises_rpc_error(-1, 'Unable to parse JSON',
        #     self.nodes[1].createwallet, wallet_name='not_hww2', disable_private_keys=True, descriptors=True, external_signer=False
        # )
        # self.clear_mock_result(self.nodes[1])

        assert_equal(hww.getwalletinfo()["keypoolsize"], 40)

        address1 = hww.getnewaddress(address_type="bech32")
        assert_equal(address1, "ert1qm90ugl4d48jv8n6e5t9ln6t9zlpm5th6ljqheg")
        address_info = hww.getaddressinfo(address1)
        assert_equal(address_info['solvable'], True)
        assert_equal(address_info['ismine'], True)
        assert_equal(address_info['hdkeypath'], "m/84'/1'/0'/0/0")

        address2 = hww.getnewaddress(address_type="p2sh-segwit")
        assert_equal(address2, "XLnRBrfcjE3fPgwXLof1VaXReFDPSfNAxj")
        address_info = hww.getaddressinfo(address2)
        assert_equal(address_info['solvable'], True)
        assert_equal(address_info['ismine'], True)
        assert_equal(address_info['hdkeypath'], "m/49'/1'/0'/0/0")

        address3 = hww.getnewaddress(address_type="legacy")
        assert_equal(address3, "2duF7kC8JfjZM5mYbDZ6z8scVZcrH8XEB7Y")
        address_info = hww.getaddressinfo(address3)
        assert_equal(address_info['solvable'], True)
        assert_equal(address_info['ismine'], True)
        assert_equal(address_info['hdkeypath'], "m/44'/1'/0'/0/0")

        address4 = hww.getnewaddress(address_type="bech32m")
        assert_equal(address4, "bcrt1phw4cgpt6cd30kz9k4wkpwm872cdvhss29jga2xpmftelhqll62ms4e9sqj")
        address_info = hww.getaddressinfo(address4)
        assert_equal(address_info['solvable'], True)
        assert_equal(address_info['ismine'], True)
        assert_equal(address_info['hdkeypath'], "m/86'/1'/0'/0/0")

        self.log.info('Test walletdisplayaddress')
        result = hww.walletdisplayaddress(address1)
        assert_equal(result, {"address": address1})

        # Handle error thrown by script
        self.set_mock_result(self.nodes[1], "2")
        assert_raises_rpc_error(-1, 'RunCommandParseJSON error',
            hww.walletdisplayaddress, address1
        )
        self.clear_mock_result(self.nodes[1])

        self.log.info('Prepare mock PSBT')
        self.nodes[0].sendtoaddress(address4, 1)
        self.generate(self.nodes[0], 1)

        # Load private key into wallet to generate a signed PSBT for the mock
        self.nodes[1].createwallet(wallet_name="mock", disable_private_keys=False, blank=True, descriptors=True)
        mock_wallet = self.nodes[1].get_wallet_rpc("mock")
        assert mock_wallet.getwalletinfo()['private_keys_enabled']

        result = mock_wallet.importdescriptors([{
            "desc": "tr([00000001/86'/1'/0']tprv8ZgxMBicQKsPd7Uf69XL1XwhmjHopUGep8GuEiJDZmbQz6o58LninorQAfcKZWARbtRtfnLcJ5MQ2AtHcQJCCRUcMRvmDUjyEmNUWwx8UbK/0/*)#0jtt2jc9",
            "timestamp": 0,
            "range": [0,1],
            "internal": False,
            "active": True
        },
        {
            "desc": "tr([00000001/86'/1'/0']tprv8ZgxMBicQKsPd7Uf69XL1XwhmjHopUGep8GuEiJDZmbQz6o58LninorQAfcKZWARbtRtfnLcJ5MQ2AtHcQJCCRUcMRvmDUjyEmNUWwx8UbK/1/*)#7xw2h8ga",
            "timestamp": 0,
            "range": [0, 0],
            "internal": True,
            "active": True
        }])
        assert_equal(result[0], {'success': True})
        assert_equal(result[1], {'success': True})
        assert_equal(mock_wallet.getwalletinfo()["txcount"], 1)
        dest = self.nodes[0].getnewaddress(address_type='bech32')
        mock_psbt = mock_wallet.walletcreatefundedpsbt([], {dest:0.5}, 0, {}, True)['psbt']
        mock_psbt_signed = mock_wallet.walletprocesspsbt(psbt=mock_psbt, sign=True, sighashtype="ALL", bip32derivs=True)
        mock_psbt_final = mock_wallet.finalizepsbt(mock_psbt_signed["psbt"])
        mock_tx = mock_psbt_final["hex"]
        assert(mock_wallet.testmempoolaccept([mock_tx])[0]["allowed"])

        # # Create a new wallet and populate with specific public keys, in order
        # # to work with the mock signed PSBT.
        # self.nodes[1].createwallet(wallet_name="hww4", disable_private_keys=True, descriptors=True, external_signer=True)
        # hww4 = self.nodes[1].get_wallet_rpc("hww4")
        #
        # descriptors = [{
        #     "desc": "wpkh([00000001/84'/1'/0']tpubD6NzVbkrYhZ4WaWSyoBvQwbpLkojyoTZPRsgXELWz3Popb3qkjcJyJUGLnL4qHHoQvao8ESaAstxYSnhyswJ76uZPStJRJCTKvosUCJZL5B/0/*)#x30uthjs",
        #     "timestamp": "now",
        #     "range": [0, 1],
        #     "internal": False,
        #     "watchonly": True,
        #     "active": True
        # },
        # {
        #     "desc": "wpkh([00000001/84'/1'/0']tpubD6NzVbkrYhZ4WaWSyoBvQwbpLkojyoTZPRsgXELWz3Popb3qkjcJyJUGLnL4qHHoQvao8ESaAstxYSnhyswJ76uZPStJRJCTKvosUCJZL5B/1/*)#h92akzzg",
        #     "timestamp": "now",
        #     "range": [0, 0],
        #     "internal": True,
        #     "watchonly": True,
        #     "active": True
        # }]

        # result = hww4.importdescriptors(descriptors)
        # assert_equal(result[0], {'success': True})
        # assert_equal(result[1], {'success': True})
        assert_equal(hww.getwalletinfo()["txcount"], 1)

        assert(hww.testmempoolaccept([mock_tx])[0]["allowed"])

        with open(os.path.join(self.nodes[1].cwd, "mock_psbt"), "w", encoding="utf8") as f:
            f.write(mock_psbt_signed["psbt"])

        self.log.info('Test send using hww1')

        res = hww.send(outputs={dest:0.5},options={"add_to_wallet": False})
        assert(res["complete"])
        assert_equal(res["hex"], mock_tx)

        self.log.info('Test sendall using hww1')

        res = hww.sendall(recipients=[{dest:0.5}, hww.getrawchangeaddress()],options={"add_to_wallet": False})
        assert(res["complete"])
        assert_equal(res["hex"], mock_tx)

        # # Handle error thrown by script
        # self.set_mock_result(self.nodes[4], "2")
        # assert_raises_rpc_error(-1, 'Unable to parse JSON',
        #     hww4.signerprocesspsbt, psbt_orig, "00000001"
        # )
        # self.clear_mock_result(self.nodes[4])

    def test_invalid_signer(self):
        self.log.debug(f"-signer={self.mock_invalid_signer_path()}")
        self.log.info('Test invalid external signer')
        assert_raises_rpc_error(-1, "Invalid descriptor", self.nodes[1].createwallet, wallet_name='hww_invalid', disable_private_keys=True, descriptors=True, external_signer=True)

    def test_multiple_signers(self):
        self.log.debug(f"-signer={self.mock_multi_signers_path()}")
        self.log.info('Test multiple external signers')

        assert_raises_rpc_error(-1, "GetExternalSigner: More than one external signer found", self.nodes[1].createwallet, wallet_name='multi_hww', disable_private_keys=True, descriptors=True, external_signer=True)

if __name__ == '__main__':
    WalletSignerTest().main()
