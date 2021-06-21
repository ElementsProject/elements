#!/usr/bin/env python3
# Copyright (c) 2014-2016 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

#
# Test use of assetdir to locally label assets.
# Test listissuances returns a list of all issuances or specific issuances based on asset hex or asset label.
#

from test_framework.blind import calculate_reissuance_token
from test_framework.blind import calculate_asset
from test_framework.messages import uint256_from_str
from test_framework.blind import generate_asset_entropy
from test_framework.messages import COutPoint
from test_framework.key import ECKey, ECPubKey
from test_framework.messages import CAsset, COIN, CTransaction, FromHex
from test_framework.test_framework import BitcoinTestFramework, SkipTest
from test_framework.blind import blind_transaction
from test_framework import util

import sys

class BlindTest(BitcoinTestFramework):
    """
    Check whether a blinded transaction created from testframework is accepted in mempool.
    This works on secp bindings which only work on linux.
    Build with
    ~/secp256k1-zkp$ ./configure --enable-experimental \
                             --enable-module-generator \
                             --enable-module-rangeproof \
                             --enable-module-surjectionproof \
                             --enable-module-ecdh \
                             --enable-module-recovery
    and provide the location of the so file in LD_LIBRARY_PATH variable

    If secp256k1_zkp is built at home, that would be
    export LD_LIBRARY_PATH=$HOME/secp256k1-zkp/.libs/
    """

    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 1
        self.extra_args = [["-initialfreecoins=2100000000000000", "-anyonecanspendaremine=1", "-blindedaddresses=1"]]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def setup_network(self, split=False):
        self.setup_nodes()

    def run_test(self):
        self.log.info("Check for linux")
        if not sys.platform.startswith('linux'):
            raise SkipTest("This test can only be run on linux.")

        self.nodes[0].generate(101)
        self.wait_until(lambda: self.nodes[0].getblockcount() == 101, timeout=5)
        self.nodes[0].generate(101)

        util.node_fastmerkle = self.nodes[0]
        addr = self.nodes[0].getnewaddress()

        # unconf_addr = self.nodes[0].getaddressinfo(addr)['unconfidential']

        raw_tx = self.nodes[0].createrawtransaction([], [{addr: 1.2}])
        fund_tx = self.nodes[0].fundrawtransaction(raw_tx)["hex"]
        fund_tx = self.nodes[0].rawissueasset(fund_tx, [{"asset_amount":1, "asset_address": addr, "blind": False}])
        fund_tx = fund_tx[0]["hex"]

        spent = self.nodes[0].listunspent()[0]

        tx = FromHex(CTransaction(), fund_tx)

        output_pk = ECPubKey()
        output_pk.set(tx.vout[0].nNonce.vchCommitment)
        assert(output_pk.is_valid)

        key = ECKey()
        key.generate()
        output_pk2 = key.get_pubkey()

        key = ECKey()
        key.generate()
        output_pk3 = key.get_pubkey()

        in_v_blind = bytes.fromhex(spent['amountblinder'])
        in_a_blind = bytes.fromhex(spent["assetblinder"])
        in_amount = int(spent['amount']*COIN)
        in_asset = CAsset(bytes.fromhex(spent["asset"])[::-1])

        # Must have 1 input now.
        (res, v_blind, a_blind) = blind_transaction(tx, input_value_blinding_factors=[in_v_blind], \
            input_asset_blinding_factors = [in_a_blind], \
            input_assets = [in_asset], \
            input_amounts = [in_amount], \
            output_pubkeys =  [output_pk, output_pk2, output_pk3], \
            issuance_blinding_priv_keys = [key],
            # token_blinding_priv_keys = [key],
            )

        # Check that the transcation is accepted in mempool and can be mined
        signed_raw_tx = self.nodes[0].signrawtransactionwithwallet(tx.serialize().hex())
        # print(signed_raw_tx)
        assert(res == 4), ("blinding failed %d", res)
        self.nodes[0].sendrawtransaction(signed_raw_tx['hex'])
        tx = FromHex(CTransaction(), signed_raw_tx['hex'])
        tx.rehash()
        self.nodes[0].generate(1)
        last_blk = self.nodes[0].getblock(self.nodes[0].getbestblockhash())
        assert(tx.hash in last_blk['tx'])


        # Random test for asset issuance and internal code
        prevout_str = "8903ee739b52859877fbfedc58194c2d59d0f5a4ea3c2774dc3cba3031cec757"
        prevout_ind = 0
        prevout = COutPoint(uint256_from_str(bytes.fromhex(prevout_str)[::-1]), prevout_ind)
        contracthash = bytes(32)
        entropy = generate_asset_entropy(prevout, contracthash)
        exp_entropy_hex = "b9789de8589dc1b664e4f2bda4d04af9d4d2180394a8c47b1f889acfb5e0acc4"
        assert entropy[::-1].hex() == exp_entropy_hex
        asset = calculate_asset(entropy)
        exp_asset_hex = "bdab916e8cda17781bcdb84505452e44d0ab2f080e9e5dd7765ffd5ce0c07cd9"
        assert asset.id[::-1].hex() == exp_asset_hex
        exp_token_hex = "f144868169dfc7afc024c4d8f55607ac8dfe925e67688650a9cdc54c3cfa5b1c"
        token = calculate_reissuance_token(entropy, True)
        assert token.id[::-1].hex() == exp_token_hex

if __name__ == '__main__':
    BlindTest().main()

