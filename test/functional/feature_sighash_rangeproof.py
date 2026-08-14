#!/usr/bin/env python3
# Copyright (c) 2019 The Elements Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

"""
Test the post-dynafed elements-only SIGHASH_RANGEPROOF sighash flag.

Also tests that the per-input ECDSA sighash midstate cache (SigHashCache= in
src/script/interpreter.cpp) treats the SIGHASH_RANGEPROOF (0x40) bit as part
of its key.
"""

import struct
from decimal import Decimal
from test_framework import util
from test_framework.address import (
    base58_to_byte,
    script_to_p2sh,
    script_to_p2wsh,
)
from test_framework.blocktools import add_witness_commitment
from test_framework.key import ECKey
from test_framework.messages import (
    COIN,
    CBlock,
    CTxInWitness,
    hash256,
    sha256,
    from_hex,
    tx_from_hex,
)
from test_framework.script import (
    OP_CHECKSIG,
    OP_DUP,
    OP_EQUAL,
    OP_EQUALVERIFY,
    OP_HASH160,
    SIGHASH_ALL,
    SIGHASH_RANGEPROOF,
    OP_0,
    OP_2,
    OP_CHECKMULTISIG,
    CScript,
    CScriptOp,
    LegacySignatureHash,
    LegacySignatureMsg,
    SegwitV0SignatureHash,
    SegwitV0SignatureMsg,
    hash160,
)
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    assert_raises_rpc_error,
)


def get_p2pkh_script(pubkeyhash):
    """Get the script associated with a P2PKH."""
    return CScript([CScriptOp(OP_DUP), CScriptOp(OP_HASH160), pubkeyhash, CScriptOp(OP_EQUALVERIFY), CScriptOp(OP_CHECKSIG)])

class SighashRangeproofTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 3
        # We want to test activation of dynafed
        self.extra_args = [[
            "-evbparams=dynafed:1000:::",
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
        self.generate(self.nodes[0], 1)
        self.sync_all()
        utxo = self.nodes[1].listunspent(1, 1, [addr])[0]
        utxo_tx = tx_from_hex(self.nodes[1].getrawtransaction(utxo["txid"]))
        utxo_spk = CScript(bytes.fromhex(utxo["scriptPubKey"]))
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
        (b, _v) = base58_to_byte(wif)
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
        elif address_type == "blech32" or address_type == "p2sh-segwit":
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
            if not attach_issuance: # FIXME: We need to skip the issuance since the example assumes it was a blinded issuance, thus the reissuance token is incorrect.
                psbt_hex = self.nodes[0].converttopsbt(unsigned_hex)
                signed_psbt = self.nodes[1].walletprocesspsbt(psbt_hex, True, "ALL|RANGEPROOF")
                extracted_tx = self.nodes[0].finalizepsbt(signed_psbt["psbt"])
                assert extracted_tx["complete"]
                test_accept = self.nodes[0].testmempoolaccept([extracted_tx["hex"]])[0]
                assert test_accept["allowed"], "not accepted: {}".format(test_accept["reject-reason"])
        else:
            signed_tx.rehash()

        return signed_tx

    def assert_default_sign_commits_rangeproof(self, address_type, expect_rangeproof):
        # Sign a blinded tx using the wallet default sighash (no explicit sighash
        # argument) and assert whether the resulting pre-Taproot signatures
        # commit to the SIGHASH_RANGEPROOF (0x40) bit.
        addr = self.nodes[1].getnewaddress("", address_type)
        assert len(self.nodes[1].getaddressinfo(addr)["confidential_key"]) > 0
        self.nodes[0].sendtoaddress(addr, 1.0)
        self.generate(self.nodes[0], 1)
        self.sync_all()
        utxo = self.nodes[1].listunspent(1, 1, [addr])[0]

        sink_addr = self.nodes[2].getnewaddress()
        unsigned_hex = self.nodes[1].createrawtransaction(
            [{"txid": utxo["txid"], "vout": utxo["vout"]}],
            [{sink_addr: 0.9}, {"fee": 0.1}]
        )
        blinded_hex = self.nodes[1].blindrawtransaction(unsigned_hex)
        # Deliberately omit the sighash argument to exercise the wallet default.
        signed = self.nodes[1].signrawtransactionwithwallet(blinded_hex)
        assert signed["complete"], f"default-signed tx incomplete: {signed}"
        signed_tx = tx_from_hex(signed["hex"])

        # The tx must be accepted (standard + valid) with the default sighash.
        test_accept = self.nodes[0].testmempoolaccept([signed["hex"]])[0]
        assert test_accept["allowed"], "default-signed tx not accepted: {}".format(test_accept["reject-reason"])

        # Extract the sighash byte from the signature and check the 0x40 bit.
        if address_type == "legacy":
            # scriptSig: <sig> <pubkey>; the signature is the first push.
            script_sig = signed_tx.vin[0].scriptSig
            # The first byte is the push length of the signature.
            sig_len = script_sig[0]
            sig = script_sig[1:1 + sig_len]
        else:
            # segwit v0 (native or p2sh-wrapped): signature is first witness item.
            sig = signed_tx.wit.vtxinwit[0].scriptWitness.stack[0]
        sighash_byte = sig[-1]
        has_rangeproof = bool(sighash_byte & SIGHASH_RANGEPROOF)
        assert_equal(has_rangeproof, expect_rangeproof)

    def prepare_mixed_sighash_multisig_tx(self, address_type, use_polluted_midstate):
        # Spend of a 2-of-2 CHECKMULTISIG output where the two signatures
        # are made over the same scriptCode with sighash bytes that differ only in
        # the SIGHASH_RANGEPROOF bit: the first uses ALL|RANGEPROOF and the second ALL.
        # Both checks happen while evaluating a single input, so they share a `SigHashCache`.
        #
        # If `use_polluted_midstate` is
        #  false, each signiture is made over its own (correct) sighash.
        #  true,  the second signature is made over the hash a node whose cache
        #        ignores the SIGHASH_RANGEPROOF bit would compute: the 0x41 preimage with the
        #        sighash type replaced by 0x01.

        key_a = ECKey()
        key_a.generate()
        key_b = ECKey()
        key_b.generate()
        pubkey_a = key_a.get_pubkey().get_bytes()
        pubkey_b = key_b.get_pubkey().get_bytes()

        # scriptCode is the same for both CHECKSIG evaluations
        script = CScript([OP_2, pubkey_a, pubkey_b, OP_2, CScriptOp(OP_CHECKMULTISIG)])
        if address_type == "p2wsh":
            address = script_to_p2wsh(script)
            script_pubkey = CScript([OP_0, sha256(script)])
        elif address_type == "p2sh":
            address = script_to_p2sh(script)
            script_pubkey = CScript([CScriptOp(OP_HASH160), hash160(script), CScriptOp(OP_EQUAL)])
        else:
            assert False

        # Fund the multisig
        funding_txid = self.nodes[0].sendtoaddress(address, 1.0)
        self.generate(self.nodes[0], 1)
        self.sync_all()
        funding_tx = tx_from_hex(self.nodes[0].getrawtransaction(funding_txid))
        vout = None
        for i, out in enumerate(funding_tx.vout):
            if out.scriptPubKey == bytes(script_pubkey):
                vout = i
                break
        assert vout is not None, "could not find the multisig output"
        utxo_value = funding_tx.vout[vout].nValue
        amount = Decimal(utxo_value.getAmount()) / COIN

        # Spend it to two blinded outputs, so the transaction has rangeproofs.
        unsigned_hex = self.nodes[0].createrawtransaction(
            [{"txid": funding_txid, "vout": vout}],
            [
                {self.nodes[2].getnewaddress(): amount / 4},
                {self.nodes[2].getnewaddress(): amount / 2},
                {"fee": amount - amount / 4 - amount / 2},
            ]
        )
        zero_blinder = "00" * 32
        asset = self.nodes[0].getsidechaininfo()["pegged_asset"]
        blinded_hex = self.nodes[0].rawblindrawtransaction(
            unsigned_hex, [zero_blinder], [amount], [asset], [zero_blinder]
        )
        tx = tx_from_hex(blinded_hex)
        assert any(len(wit.vchRangeproof) > 0 for wit in tx.wit.vtxoutwit), "the outputs were not blinded"

        hashtype_rp = SIGHASH_ALL | SIGHASH_RANGEPROOF
        hashtype_plain = SIGHASH_ALL

        # Build the preimages
        if address_type == "p2wsh":
            msg_rp = SegwitV0SignatureMsg(script, tx, 0, hashtype_rp, utxo_value)
            msg_plain = SegwitV0SignatureMsg(script, tx, 0, hashtype_plain, utxo_value)
        else:
            (msg_rp, err) = LegacySignatureMsg(script, tx, 0, hashtype_rp)
            assert err is None, err
            (msg_plain, err) = LegacySignatureMsg(script, tx, 0, hashtype_plain)
            assert err is None, err

        # CHECKMULTISIG signature_b is checked first and populates the cache entry; signature_a is the check that reads it back. The polluted
        # signature must therefore be signature_a: a 0x40-blind cache serves it signature_b's
        # midstate, computed without the rangeproof commitment, and then appends 0x41.
        polluted_msg = msg_plain[:-4] + hashtype_rp.to_bytes(4, "little")
        assert polluted_msg != msg_rp, "the 0x40 bit did not change the preimage"

        signature_a = key_a.sign_ecdsa(
            hash256(polluted_msg if use_polluted_midstate else msg_rp)
        ) + bytes([hashtype_rp])
        signature_b = key_b.sign_ecdsa(hash256(msg_plain)) + bytes([hashtype_plain])

        # CHECKMULTISIG checks signature_a against pubkey_a first, so signature_a
        # populates the cache entry and signature_b is the check that reads it back.
        if address_type == "p2wsh":
            if len(tx.wit.vtxinwit) != len(tx.vin):
                tx.wit.vtxinwit = [CTxInWitness() for _ in tx.vin]
            tx.wit.vtxinwit[0].scriptWitness.stack = [b'', signature_a, signature_b, bytes(script)]
        else:
            tx.vin[0].scriptSig = CScript([OP_0, signature_a, signature_b, bytes(script)])
        tx.rehash()
        return tx


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
        ADDRESS_TYPES = ["legacy", "blech32", "p2sh-segwit"]

        # Different test scenarios.
        # - before activation, using the flag is non-standard
        # - before activation, using the flag but a non-flag-aware signature is legal
        # - after activation, using the flag but a non-flag-aware signature is illegal
        # - after activation, using the flag is standard (and thus also legal)

        # Mine come coins for node 0.
        self.generate(self.nodes[0], 200)
        self.sync_all()

        # Ensure that if we use the SIGHASH_RANGEPROOF flag before it's activated,
        # - the tx is not accepted in the mempool and
        # - the tx is accepted if manually mined in a block
        for address_type in ADDRESS_TYPES:
            self.log.info(f"Pre-activation for {address_type} address")
            tx = self.prepare_tx_signed_with_sighash(address_type, False, False)
            self.assert_tx_standard(tx, False)
            self.assert_tx_valid(tx, True)

            self.log.info(f"Pre-activation for {address_type} address (with issuance)")
            tx = self.prepare_tx_signed_with_sighash(address_type, False, True)
            self.assert_tx_standard(tx, False)
            self.assert_tx_valid(tx, True)

            # Pre-activation, the wallet default must NOT set SIGHASH_RANGEPROOF,
            # otherwise it would produce non-standard/invalid signatures.
            self.log.info(f"Pre-activation default sighash for {address_type} address")
            self.assert_default_sign_commits_rangeproof(address_type, expect_rangeproof=False)

        # Activate dynafed (nb of blocks taken from dynafed activation test)
        # Generate across several calls to `generatetoaddress` to ensure no individual call times out
        self.generate(self.nodes[0], 503)
        self.generate(self.nodes[0], 503)
        self.generate(self.nodes[0], 1 + 144 + 144)
        assert_equal(self.nodes[0].getdeploymentinfo()["deployments"]["dynafed"]["bip9"]["status"], "active")

        self.sync_all()

        # Test that the use of SIGHASH_RANGEPROOF is legal and standard
        # after activation.
        for address_type in ADDRESS_TYPES:
            self.log.info(f"Post-activation for {address_type} address")
            tx = self.prepare_tx_signed_with_sighash(address_type, True, False)
            self.assert_tx_standard(tx, True)
            self.assert_tx_valid(tx, True)

            self.log.info(f"Post-activation for {address_type} address (with issuance)")
            tx = self.prepare_tx_signed_with_sighash(address_type, True, True)
            self.assert_tx_standard(tx, True)
            self.assert_tx_valid(tx, True)

            # Post-activation, the wallet default must set SIGHASH_RANGEPROOF.
            self.log.info(f"Post-activation default sighash for {address_type} address")
            self.assert_default_sign_commits_rangeproof(address_type, expect_rangeproof=True)

        # Ensure that if we then use the old sighash algorithm that doesn't hash
        # the rangeproofs, the signature is no longer valid.
        for address_type in ADDRESS_TYPES:
            self.log.info(f"Post-activation invalid sighash for {address_type} address")
            tx = self.prepare_tx_signed_with_sighash(address_type, False, False)
            self.assert_tx_standard(tx, False)
            self.assert_tx_valid(tx, False)

            self.log.info(f"Post-activation invalid sighash for {address_type} address (with issuance)")
            tx = self.prepare_tx_signed_with_sighash(address_type, False, True)
            self.assert_tx_standard(tx, False)
            self.assert_tx_valid(tx, False)

        # Two ECDSA checks in one input, same scriptCode, sighash bytes differing
        # only in SIGHASH_RANGEPROOF. The sighash midstate cache must not
        # serve one check's midstate to the other.
        for multisig_type in ["p2wsh", "p2sh"]:
            self.log.info("Mixed SIGHASH_RANGEPROOF 2-of-2 for {}".format(multisig_type))
            tx = self.prepare_mixed_sighash_multisig_tx(multisig_type, False)
            self.assert_tx_standard(tx, True)
            self.assert_tx_valid(tx, True)

            self.log.info("Polluted sighash midstate for {}".format(multisig_type))
            tx = self.prepare_mixed_sighash_multisig_tx(multisig_type, True)
            self.assert_tx_standard(tx, False)
            self.assert_tx_valid(tx, False)

if __name__ == '__main__':
    SighashRangeproofTest().main()
