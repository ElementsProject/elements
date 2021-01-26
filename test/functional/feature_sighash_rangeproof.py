#!/usr/bin/env python3
# Copyright (c) 2019 The Elements Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

"""
Test the post-dynafed elements-only SIGHASH_RANGEPROOF sighash flag.
"""

import struct
from test_framework.test_framework import BitcoinTestFramework
from test_framework.script import (
    hash160,
    SignatureHash,
    SegwitVersion1SignatureHash,
    SIGHASH_ALL,
    SIGHASH_SINGLE,
    SIGHASH_NONE,
    SIGHASH_ANYONECANPAY,
    SIGHASH_RANGEPROOF,
    CScript,
    CScriptOp,
    FindAndDelete,
    OP_CODESEPARATOR,
    OP_CHECKSIG,
    OP_DUP,
    OP_EQUALVERIFY,
    OP_HASH160,
)
from test_framework.key import ECKey

from test_framework.messages import (
    CBlock,
    CTransaction,
    CTxOut,
    FromHex,
    WitToHex,
    hash256, uint256_from_str, ser_uint256, ser_string, ser_vector
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

def SignatureHash_legacy(script, txTo, inIdx, hashtype):
    """
    This method is identical to the regular `SignatureHash` method,
    but without support for SIGHASH_RANGEPROOF.
    So basically it's the old version of the method from before the
    new sighash flag was added.
    """
    HASH_ONE = b'\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'

    if inIdx >= len(txTo.vin):
        return (HASH_ONE, "inIdx %d out of range (%d)" % (inIdx, len(txTo.vin)))
    txtmp = CTransaction(txTo)

    for txin in txtmp.vin:
        txin.scriptSig = b''
    txtmp.vin[inIdx].scriptSig = FindAndDelete(script, CScript([OP_CODESEPARATOR]))

    if (hashtype & 0x1f) == SIGHASH_NONE:
        txtmp.vout = []

        for i in range(len(txtmp.vin)):
            if i != inIdx:
                txtmp.vin[i].nSequence = 0

    elif (hashtype & 0x1f) == SIGHASH_SINGLE:
        outIdx = inIdx
        if outIdx >= len(txtmp.vout):
            return (HASH_ONE, "outIdx %d out of range (%d)" % (outIdx, len(txtmp.vout)))

        tmp = txtmp.vout[outIdx]
        txtmp.vout = []
        for i in range(outIdx):
            txtmp.vout.append(CTxOut(-1))
        txtmp.vout.append(tmp)

        for i in range(len(txtmp.vin)):
            if i != inIdx:
                txtmp.vin[i].nSequence = 0

    if hashtype & SIGHASH_ANYONECANPAY:
        tmp = txtmp.vin[inIdx]
        txtmp.vin = []
        txtmp.vin.append(tmp)

    # sighash serialization is different from non-witness serialization
    # do manual sighash serialization:
    s = b""
    s += struct.pack("<i", txtmp.nVersion)
    s += ser_vector(txtmp.vin)
    s += ser_vector(txtmp.vout)
    s += struct.pack("<I", txtmp.nLockTime)

    # add sighash type
    s += struct.pack(b"<I", hashtype)

    hash = hash256(s)

    return (hash, None)

def SegwitVersion1SignatureHash_legacy(script, txTo, inIdx, hashtype, amount):
    """
    This method is identical to the regular `SegwitVersion1SignatureHash`
    method, but without support for SIGHASH_RANGEPROOF.
    So basically it's the old version of the method from before the
    new sighash flag was added.
    """

    hashPrevouts = 0
    hashSequence = 0
    hashIssuance = 0
    hashOutputs = 0

    if not (hashtype & SIGHASH_ANYONECANPAY):
        serialize_prevouts = bytes()
        for i in txTo.vin:
            serialize_prevouts += i.prevout.serialize()
        hashPrevouts = uint256_from_str(hash256(serialize_prevouts))

    if (not (hashtype & SIGHASH_ANYONECANPAY) and (hashtype & 0x1f) != SIGHASH_SINGLE and (hashtype & 0x1f) != SIGHASH_NONE):
        serialize_sequence = bytes()
        for i in txTo.vin:
            serialize_sequence += struct.pack("<I", i.nSequence)
        hashSequence = uint256_from_str(hash256(serialize_sequence))

    if not (hashtype & SIGHASH_ANYONECANPAY):
        serialize_issuance = bytes()
        # TODO actually serialize issuances
        for _ in txTo.vin:
            serialize_issuance += b'\x00'
        hashIssuance = uint256_from_str(hash256(serialize_issuance))

    if ((hashtype & 0x1f) != SIGHASH_SINGLE and (hashtype & 0x1f) != SIGHASH_NONE):
        serialize_outputs = bytes()
        for o in txTo.vout:
            serialize_outputs += o.serialize()
        hashOutputs = uint256_from_str(hash256(serialize_outputs))
    elif ((hashtype & 0x1f) == SIGHASH_SINGLE and inIdx < len(txTo.vout)):
        serialize_outputs = txTo.vout[inIdx].serialize()
        hashOutputs = uint256_from_str(hash256(serialize_outputs))

    ss = bytes()
    ss += struct.pack("<i", txTo.nVersion)
    ss += ser_uint256(hashPrevouts)
    ss += ser_uint256(hashSequence)
    ss += ser_uint256(hashIssuance)
    ss += txTo.vin[inIdx].prevout.serialize()
    ss += ser_string(script)
    ss += amount.serialize()
    ss += struct.pack("<I", txTo.vin[inIdx].nSequence)
    ss += ser_uint256(hashOutputs)
    ss += struct.pack("<i", txTo.nLockTime)
    ss += struct.pack("<I", hashtype)

    return hash256(ss)


class SighashRangeproofTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 3
        # We want to test activation of dynafed
        args = ["-con_dyna_deploy_start=1000", "-blindedaddresses=1", "-initialfreecoins=2100000000000000", "-con_blocksubsidy=0", "-con_connect_genesis_outputs=1", "-txindex=1"]
        self.extra_args = [args] * self.num_nodes
        self.extra_args[0].append("-anyonecanspendaremine=1") # first node gets the coins

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def prepare_tx_signed_with_sighash(self, address_type, sighash_rangeproof_aware):
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
        utxo_tx = FromHex(CTransaction(), self.nodes[1].getrawtransaction(utxo["txid"]))
        utxo_spk = CScript(hex_str_to_bytes(utxo["scriptPubKey"]))
        utxo_value = utxo_tx.vout[utxo["vout"]].nValue

        assert len(utxo["amountblinder"]) > 0
        sink_addr = self.nodes[2].getnewaddress()
        unsigned_hex = self.nodes[1].createrawtransaction(
            [{"txid": utxo["txid"], "vout": utxo["vout"]}],
            {sink_addr: 0.9, "fee": 0.1}
        )
        blinded_hex = self.nodes[1].blindrawtransaction(unsigned_hex)
        blinded_tx = FromHex(CTransaction(), blinded_hex)
        signed_hex = self.nodes[1].signrawtransactionwithwallet(blinded_hex)["hex"]
        signed_tx = FromHex(CTransaction(), signed_hex)

        # Make sure that the tx the node produced is always valid.
        test_accept = self.nodes[0].testmempoolaccept([signed_hex])[0]
        assert test_accept["allowed"], "not accepted: {}".format(test_accept["reject-reason"])

        # Prepare the keypair we need to re-sign the tx.
        wif = self.nodes[1].dumpprivkey(addr)
        privkey = ECKey()
        privkey.set_wif(wif)
        pubkey = privkey.get_pubkey()

        # Now we need to replace the signature with an equivalent one with the new sighash set.
        hashtype = SIGHASH_ALL | SIGHASH_RANGEPROOF
        if address_type == "legacy":
            if sighash_rangeproof_aware:
                (sighash, _) = SignatureHash(utxo_spk, blinded_tx, 0, hashtype)
            else:
                (sighash, _) = SignatureHash_legacy(utxo_spk, blinded_tx, 0, hashtype)
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
                sighash = SegwitVersion1SignatureHash(script, blinded_tx, 0, hashtype, utxo_value)
            else:
                sighash = SegwitVersion1SignatureHash_legacy(script, blinded_tx, 0, hashtype, utxo_value)
            signature = privkey.sign_ecdsa(sighash) + chr(hashtype).encode('latin-1')
            signed_tx.wit.vtxinwit[0].scriptWitness.stack[0] = signature
        else:
            assert False

        signed_tx.rehash()
        return signed_tx

    def assert_tx_standard(self, tx, assert_standard=True):
        # Test the standardness of the tx by submitting it to the mempool.

        test_accept = self.nodes[0].testmempoolaccept([WitToHex(tx)])[0]
        if assert_standard:
            assert test_accept["allowed"], "tx was not accepted: {}".format(test_accept["reject-reason"])
        else:
            assert not test_accept["allowed"], "tx was accepted"

    def assert_tx_valid(self, tx, assert_valid=True):
        # Test the validity of the transaction by manually mining a block that contains the tx.

        block = FromHex(CBlock(), self.nodes[2].getnewblockhex())
        assert len(block.vtx) > 0
        block.vtx.append(tx)
        block.hashMerkleRoot = block.calc_merkle_root()
        add_witness_commitment(block)
        block.solve()
        block_hex = WitToHex(block)

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
            tx = self.prepare_tx_signed_with_sighash(address_type, False)
            self.assert_tx_standard(tx, False)
            self.assert_tx_valid(tx, True)

        # Activate dynafed (nb of blocks taken from dynafed activation test)
        self.nodes[0].generate(1006 + 1 + 144 + 144)
        assert_equal(self.nodes[0].getblockchaininfo()["bip9_softforks"]["dynafed"]["status"], "active")
        self.sync_all()

        # Test that the use of SIGHASH_RANGEPROOF is legal and standard
        # after activation.
        for address_type in ADDRESS_TYPES:
            self.log.info("Post-activation for {} address".format(address_type))
            tx = self.prepare_tx_signed_with_sighash(address_type, True)
            self.assert_tx_standard(tx, True)
            self.assert_tx_valid(tx, True)

        # Ensure that if we then use the old sighash algorith that doesn't hash
        # the rangeproofs, the signature is no longer valid.
        for address_type in ADDRESS_TYPES:
            self.log.info("Post-activation invalid sighash for {} address".format(address_type))
            tx = self.prepare_tx_signed_with_sighash(address_type, False)
            self.assert_tx_standard(tx, False)
            self.assert_tx_valid(tx, False)

if __name__ == '__main__':
    SighashRangeproofTest().main()

