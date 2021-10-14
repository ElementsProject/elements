#!/usr/bin/env python3
# Copyright (c) 2019 The Elements Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

"""
Test the post-dynafed elements-only SIGHASH_RANGEPROOF sighash flag.
"""

import struct
from test_framework.test_framework import BitcoinTestFramework
from test_framework.address import base58_to_byte
from test_framework.script import (
    hash160,
    LegacySignatureHash,
    SegwitV0SignatureHash,
    SIGHASH_ALL,
    SIGHASH_RANGEPROOF,
    CScript,
    CScriptOp,
    OP_CHECKSIG,
    OP_DUP,
    OP_EQUALVERIFY,
    OP_HASH160,
)
from test_framework.key import ECKey

from test_framework.messages import (
    CBlock,
    tx_from_hex,
    from_hex,
)

from test_framework import util
from test_framework.util import (
    assert_equal,
    hex_str_to_bytes,
    assert_raises_rpc_error,
)

from test_framework.blocktools import add_witness_commitment

def get_p2pkh_script(pubkeyhash):
    """Get the script associated with a P2PKH."""
    return CScript([CScriptOp(OP_DUP), CScriptOp(OP_HASH160), pubkeyhash, CScriptOp(OP_EQUALVERIFY), CScriptOp(OP_CHECKSIG)])

class SighashRangeproofTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 3
        # We want to test activation of dynafed
        self.extra_args = [[
            "-con_dyna_deploy_start=1000",
            "-con_dyna_deploy_signal=1",
            "-blindedaddresses=1",
            "-initialfreecoins=2100000000000000",
            "-con_blocksubsidy=0",
            "-con_connect_genesis_outputs=1",
            "-txindex=1",
        ]] * self.num_nodes
        self.extra_args[0].append("-anyonecanspendaremine=1") # first node gets the coins

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def prepare_tx_signed_with_sighash(self, address_type, sighash_rangeproof_aware, attach_issuance):
        # Create a tx that is signed with a specific version of the sighash
        # method.
        # If `sighash_rangeproof_aware` is
        # true, the sighash will contain the rangeproofs if SIGHASH_RANGEPROOF is set
        # false, the sighash will NOT contain the rangeproofs if SIGHASH_RANGEPROOF is set

        addr = self.nodes[1].getnewaddress("", address_type)
        assert len(self.nodes[1].getaddressinfo(addr)["confidential_key"]) > 0
        self.nodes[0].sendtoaddress(addr, 1.0)
        self.nodes[0].generate(1)
        self.sync_all()
        utxo = self.nodes[1].listunspent(1, 1, [addr])[0]
        utxo_tx = tx_from_hex(self.nodes[1].getrawtransaction(utxo["txid"]))
        utxo_spk = CScript(hex_str_to_bytes(utxo["scriptPubKey"]))
        utxo_value = utxo_tx.vout[utxo["vout"]].nValue

        assert len(utxo["amountblinder"]) > 0
        sink_addr = self.nodes[2].getnewaddress()
        unsigned_hex = self.nodes[1].createrawtransaction(
            [{"txid": utxo["txid"], "vout": utxo["vout"]}],
            [{sink_addr: 0.9}, {"fee": 0.1}]
        )
        if attach_issuance:
            # Attach a blinded issuance
            unsigned_hex = self.nodes[1].rawissueasset(
                unsigned_hex,
                [{
                    "asset_amount": 100,
                    "asset_address": self.nodes[1].getnewaddress(),
                    "token_amount": 100,
                    "token_address": self.nodes[1].getnewaddress(),
                    "blind": True, # FIXME: if blind=False, `blindrawtranaction` fails. Should fix this in a future PR
                }]
            )[0]["hex"]
        blinded_hex = self.nodes[1].blindrawtransaction(unsigned_hex)
        blinded_tx = tx_from_hex(blinded_hex)
        signed_hex = self.nodes[1].signrawtransactionwithwallet(blinded_hex)["hex"]
        signed_tx = tx_from_hex(signed_hex)

        # Make sure that the tx the node produced is always valid.
        test_accept = self.nodes[0].testmempoolaccept([signed_hex])[0]
        assert test_accept["allowed"], "not accepted: {}".format(test_accept["reject-reason"])

        # Prepare the keypair we need to re-sign the tx.
        wif = self.nodes[1].dumpprivkey(addr)
        (b, v) = base58_to_byte(wif)
        privkey = ECKey()
        privkey.set(b[0:32], len(b) == 33)
        pubkey = privkey.get_pubkey()

        # Now we need to replace the signature with an equivalent one with the new sighash set,
        # which we do using the Python logic to detect any forking changes in the sighash format.
        hashtype = SIGHASH_ALL | SIGHASH_RANGEPROOF
        if address_type == "legacy":
            if sighash_rangeproof_aware:
                (sighash, _) = LegacySignatureHash(utxo_spk, blinded_tx, 0, hashtype)
            else:
                (sighash, _) = LegacySignatureHash(utxo_spk, blinded_tx, 0, hashtype, enable_sighash_rangeproof=False)
            signature = privkey.sign_ecdsa(sighash) + chr(hashtype).encode('latin-1')
            assert len(signature) <= 0xfc
            assert len(pubkey.get_bytes()) <= 0xfc
            signed_tx.vin[0].scriptSig = CScript(
                struct.pack("<B", len(signature)) + signature
                + struct.pack("<B", len(pubkey.get_bytes())) + pubkey.get_bytes()
            )
        elif address_type == "bech32" or address_type == "p2sh-segwit":
            assert signed_tx.wit.vtxinwit[0].scriptWitness.stack[1] == pubkey.get_bytes()
            pubkeyhash = hash160(pubkey.get_bytes())
            script = get_p2pkh_script(pubkeyhash)
            if sighash_rangeproof_aware:
                sighash = SegwitV0SignatureHash(script, blinded_tx, 0, hashtype, utxo_value)
            else:
                sighash = SegwitV0SignatureHash(script, blinded_tx, 0, hashtype, utxo_value, enable_sighash_rangeproof=False)
            signature = privkey.sign_ecdsa(sighash) + chr(hashtype).encode('latin-1')
            signed_tx.wit.vtxinwit[0].scriptWitness.stack[0] = signature
        else:
            assert False

        # Make sure that the tx we manually signed is valid
        signed_hex = signed_tx.serialize_with_witness().hex()
        test_accept = self.nodes[0].testmempoolaccept([signed_hex])[0]
        if sighash_rangeproof_aware:
            assert test_accept["allowed"], "not accepted: {}".format(test_accept["reject-reason"])
        else:
            assert not test_accept["allowed"], "tx was accepted"

        if sighash_rangeproof_aware:
            signed_hex = self.nodes[1].signrawtransactionwithwallet(blinded_hex, [], "ALL|RANGEPROOF")["hex"]
            signed_tx = tx_from_hex(signed_hex)

            # Make sure that the tx that the node signed is valid
            test_accept = self.nodes[0].testmempoolaccept([signed_hex])[0]
            assert test_accept["allowed"], "not accepted: {}".format(test_accept["reject-reason"])

            # Try re-signing with node 0, which should have no effect since the transaction was already complete
            signed_hex = self.nodes[0].signrawtransactionwithwallet(signed_hex)["hex"]
            test_accept = self.nodes[0].testmempoolaccept([signed_hex])[0]
            assert test_accept["allowed"], "not accepted: {}".format(test_accept["reject-reason"])

            # Try signing using the PSBT interface
            psbt_hex = self.nodes[0].converttopsbt(unsigned_hex)
            signed_psbt = self.nodes[1].walletprocesspsbt(psbt_hex, True, "ALL|RANGEPROOF")
            extracted_tx = self.nodes[0].finalizepsbt(signed_psbt["psbt"])
            assert extracted_tx["complete"]
            test_accept = self.nodes[0].testmempoolaccept([extracted_tx["hex"]])[0]
            assert test_accept["allowed"], "not accepted: {}".format(test_accept["reject-reason"])
        else:
            signed_tx.rehash()

        return signed_tx

    def assert_tx_standard(self, tx, assert_standard=True):
        # Test the standardness of the tx by submitting it to the mempool.

        test_accept = self.nodes[0].testmempoolaccept([tx.serialize(with_witness=True).hex()])[0]
        if assert_standard:
            assert test_accept["allowed"], "tx was not accepted: {}".format(test_accept["reject-reason"])
        else:
            assert not test_accept["allowed"], "tx was accepted"

    def assert_tx_valid(self, tx, assert_valid=True):
        # Test the validity of the transaction by manually mining a block that contains the tx.

        block = from_hex(CBlock(), self.nodes[2].getnewblockhex())
        assert len(block.vtx) > 0
        block.vtx.append(tx)
        block.hashMerkleRoot = block.calc_merkle_root()
        add_witness_commitment(block)
        block.solve()
        block_hex = block.serialize(with_witness=True).hex()

        # First test the testproposed block RPC.
        if assert_valid:
            self.nodes[0].testproposedblock(block_hex)
        else:
            assert_raises_rpc_error(-25, "block-validation-failed", self.nodes[0].testproposedblock, block_hex)

        # Then try submit the block and check if it was accepted or not.
        pre = self.nodes[0].getblockcount()
        self.nodes[0].submitblock(block_hex)
        post = self.nodes[0].getblockcount()

        if assert_valid:
            # assert block was accepted
            assert pre < post
        else:
            # assert block was not accepted
            assert pre == post

    def run_test(self):
        util.node_fastmerkle = self.nodes[0]
        ADDRESS_TYPES = ["legacy", "bech32", "p2sh-segwit"]

        # Different test scenarios.
        # - before activation, using the flag is non-standard
        # - before activation, using the flag but a non-flag-aware signature is legal
        # - after activation, using the flag but a non-flag-aware signature is illegal
        # - after activation, using the flag is standard (and thus also legal)

        # Mine come coins for node 0.
        self.nodes[0].generate(200)
        self.sync_all()

        # Ensure that if we use the SIGHASH_RANGEPROOF flag before it's activated,
        # - the tx is not accepted in the mempool and
        # - the tx is accepted if manually mined in a block
        for address_type in ADDRESS_TYPES:
            self.log.info("Pre-activation for {} address".format(address_type))
            tx = self.prepare_tx_signed_with_sighash(address_type, False, False)
            self.assert_tx_standard(tx, False)
            self.assert_tx_valid(tx, True)

            self.log.info("Pre-activation for {} address (with issuance)".format(address_type))
            tx = self.prepare_tx_signed_with_sighash(address_type, False, True)
            self.assert_tx_standard(tx, False)
            self.assert_tx_valid(tx, True)

        # Activate dynafed (nb of blocks taken from dynafed activation test)
        # Generate acress several calls to `generatetoaddress` to ensure no individual call times out
        self.nodes[0].generate(503)
        self.nodes[0].generate(503)
        self.nodes[0].generate(1 + 144 + 144)
        assert_equal(self.nodes[0].getblockchaininfo()["softforks"]["dynafed"]["bip9"]["status"], "active")

        self.sync_all()

        # Test that the use of SIGHASH_RANGEPROOF is legal and standard
        # after activation.
        for address_type in ADDRESS_TYPES:
            self.log.info("Post-activation for {} address".format(address_type))
            tx = self.prepare_tx_signed_with_sighash(address_type, True, False)
            self.assert_tx_standard(tx, True)
            self.assert_tx_valid(tx, True)

            self.log.info("Post-activation for {} address (with issuance)".format(address_type))
            tx = self.prepare_tx_signed_with_sighash(address_type, True, True)
            self.assert_tx_standard(tx, True)
            self.assert_tx_valid(tx, True)

        # Ensure that if we then use the old sighash algorithm that doesn't hash
        # the rangeproofs, the signature is no longer valid.
        for address_type in ADDRESS_TYPES:
            self.log.info("Post-activation invalid sighash for {} address".format(address_type))
            tx = self.prepare_tx_signed_with_sighash(address_type, False, False)
            self.assert_tx_standard(tx, False)
            self.assert_tx_valid(tx, False)

            self.log.info("Post-activation invalid sighash for {} address (with issuance)".format(address_type))
            tx = self.prepare_tx_signed_with_sighash(address_type, False, True)
            self.assert_tx_standard(tx, False)
            self.assert_tx_valid(tx, False)

if __name__ == '__main__':
    SighashRangeproofTest().main()

