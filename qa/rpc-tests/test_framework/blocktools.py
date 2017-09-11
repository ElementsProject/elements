#!/usr/bin/env python3
# blocktools.py - utilities for manipulating blocks and transactions
# Copyright (c) 2015-2016 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

from .mininode import *
from .script import CScript, OP_TRUE, OP_CHECKSIG, OP_RETURN

# Create a block (with regtest difficulty)
def create_block(hashprev, coinbase, nTime=None, height=0):
    block = CBlock()
    if nTime is None:
        import time
        block.nTime = int(time.time()+600)
    else:
        block.nTime = nTime
    block.hashPrevBlock = hashprev
    block.vtx.append(coinbase)
    block.hashMerkleRoot = block.calc_merkle_root()
    block.nHeight = height
    block.proof.challenge = CScript([OP_TRUE])
    block.proof.solution = b''
    block.calc_sha256()
    return block

# From BIP141
WITNESS_COMMITMENT_HEADER = b"\xaa\x21\xa9\xed"

# According to BIP141, blocks with witness rules active must commit to the
# hash of all in-block transactions including witness.
def add_witness_commitment(block, nonce=0):
    # First calculate the merkle root of the block's
    # transactions, with witnesses.
    witness_nonce = nonce
    witness_root = block.calc_witness_merkle_root()
    witness_commitment = uint256_from_str(hash256(ser_uint256(witness_root)+ser_uint256(witness_nonce)))
    # witness_nonce should go to coinbase witness.
    block.vtx[0].wit.vtxinwit = [CTxInWitness()]
    block.vtx[0].wit.vtxinwit[0].scriptWitness.stack = [ser_uint256(witness_nonce)]

    # witness commitment is the last OP_RETURN output in coinbase
    output_data = WITNESS_COMMITMENT_HEADER + ser_uint256(witness_commitment)
    block.vtx[0].vout.append(CTxOut(CTxOutValue(0), CScript([OP_RETURN, output_data])))
    block.vtx[0].rehash()
    block.hashMerkleRoot = block.calc_merkle_root()
    block.rehash()

# Create a coinbase transaction, assuming no miner fees.
# If pubkey is passed in, the coinbase output will be a P2PK output;
# otherwise an anyone-can-spend output.
def create_coinbase(height, pubkey = None, amount = 0):
    coinbase = CTransaction()
    # coinbase transaction scriptsigs must be at least 2 bytes
    coinbase.vin.append(CTxIn(COutPoint(0, 0xffffffff),
        CScript([height, OP_TRUE]), 0xffffffff))
    coinbaseoutput = CTxOut()

    coinbaseoutput.nValue.setToAmount(amount)
    coinbaseoutput.nAsset.setToAsset(b'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa')

    if amount == 0:
        # zero utxo's must be made unspendable
        coinbaseoutput.scriptPubKey = CScript([OP_RETURN])
    elif pubkey != None:
        coinbaseoutput.scriptPubKey = CScript([pubkey, OP_CHECKSIG])
    else:
        coinbaseoutput.scriptPubKey = CScript([OP_TRUE])
    coinbase.vout = [ coinbaseoutput ]
    coinbase.calc_sha256()
    return coinbase

# Create a transaction.
# If the scriptPubKey is not specified, make it anyone-can-spend.
def create_transaction(prevtx, n, sig, value, scriptPubKey=CScript()):
    tx = CTransaction()
    assert(n < len(prevtx.vout))
    tx.vin.append(CTxIn(COutPoint(prevtx.sha256, n), sig, 0xffffffff))
    tx.vout.append(CTxOut(CTxOutValue(value), scriptPubKey))
    tx.calc_sha256()
    return tx

def get_legacy_sigopcount_block(block, fAccurate=True):
    count = 0
    for tx in block.vtx:
        count += get_legacy_sigopcount_tx(tx, fAccurate)
    return count

def get_legacy_sigopcount_tx(tx, fAccurate=True):
    count = 0
    for i in tx.vout:
        count += i.scriptPubKey.GetSigOpCount(fAccurate)
    for j in tx.vin:
        # scriptSig might be of type bytes, so convert to CScript for the moment
        count += CScript(j.scriptSig).GetSigOpCount(fAccurate)
    return count
