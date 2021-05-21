#!/usr/bin/env python3
# Copyright (c) 2015-2020 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""
Interface for low level bindings from secp256k1(zkp)
to deal with python data structures
"""
from .secp256k1_zkp_bind import (
    SECP256K1_GENERATOR_SIZE, SECP256K1_PEDERSEN_COMMITMENT_SIZE, _secp256k1, secp256k1_blind_context)
import ctypes

from .messages import (COIN, CTxOutAsset, CAsset, CT_BITS, CT_EXPONENT, CTxOutNonce, CTxOutValue, CTxOutWitness)
from .script import CScript
from .key import ECKey, ECPubKey

import os
import hashlib

"""
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

"""
Parse a serialized compressed bitcoin public key into secp key
"""
def parse_raw_pk(pk):
    assert(isinstance(pk, ECPubKey))
    assert(pk.valid)
    assert(pk.compressed)
    raw_pub = ctypes.create_string_buffer(64)
    key_bytes = pk.get_bytes()
    _secp256k1.secp256k1_ec_pubkey_parse(secp256k1_blind_context, raw_pub, key_bytes, 33)
    return raw_pub.raw

"""
Blind an asset.
asset: Either a CAsset or 32 bytes id
assetblind: 32 byte

Returns: confidential asset(CTxOutAsset)
and the other blinded generator 'h' in generator form
"""
def blind_asset(asset, assetblind):
    if type(asset) is CAsset:
        asset_id = asset.id
    elif type(asset) is bytes and len(asset) == 32:
        asset_id = asset
    else:
        raise TypeError
    assert(type(assetblind) is bytes and len(assetblind) == 32)

    gen = ctypes.create_string_buffer(SECP256K1_GENERATOR_SIZE)
    ret = _secp256k1.secp256k1_generator_generate_blinded(
        secp256k1_blind_context, gen, asset_id, assetblind)
    if ret != 1:
        raise RuntimeError('secp256k1_generator_generate_blinded failed')
    result_commitment = ctypes.create_string_buffer(33)
    ret = _secp256k1.secp256k1_generator_serialize(
        secp256k1_blind_context, result_commitment, gen)
    if ret != 1:
        raise RuntimeError('secp256k1_generator_serialize failed')

    confAsset = CTxOutAsset(vchCommitment=bytes(result_commitment))

    # Return a pair fo ConfAsset and the blinding generator `h`
    return (confAsset, bytes(gen))

"""
Create a value commitment
amount: amount as int in satoshis.
blind: 32 byte byte array
gen: The generator `h` for used for blinding

returns:
confValue: CTxOutValue for the value commitment
value_commit: Pedersen commit in the generator form
"""
def create_value_commitment(amount, blind, gen):
    assert(type(blind) is bytes and len(blind) == 32)
    assert(type(gen) is bytes and len(gen) == SECP256K1_GENERATOR_SIZE)
    assert(isinstance(amount, int) and amount >=0 and amount/COIN <= 21000000)

    value_commit = ctypes.create_string_buffer(SECP256K1_PEDERSEN_COMMITMENT_SIZE)
    ret = _secp256k1.secp256k1_pedersen_commit(
        secp256k1_blind_context, value_commit, blind, amount, gen)
    if ret != 1:
        raise RuntimeError('secp256k1_pedersen_commit failed')
    result_commitment = ctypes.create_string_buffer(33)
    ret = _secp256k1.secp256k1_pedersen_commitment_serialize(
        secp256k1_blind_context, result_commitment, value_commit)
    if ret != 1:
        raise RuntimeError('secp256k1_pedersen_commitment_serialize failed')

    confValue = CTxOutValue()
    confValue.vchCommitment = bytes(result_commitment)

    return (confValue, bytes(value_commit))

"""
Create a new rangeproof nonce to be used for rewinding.
This is a ECDH of other receiver pubkey and an ephemeral
key chosen by the wallet.
Inputs:
output_pubkey (ECPubkey): The receiver pubkey(called as output_pubkey in c++ code)

Returns:
a) the ECDH nonce(32 bytes):
b) The chosen ephemeral pubkey(CTxOutNonce).

The ephemeral Pk is set as the nNonce in the txOut
"""
def generate_output_rangeproof_nonce(output_pubkey):
    # Generate ephemeral key for ECDH nonce generation
    assert(isinstance(output_pubkey, ECPubKey))
    key = ECKey()
    key.generate()
    ephemeral_pk = key.get_pubkey()

    raw_key = parse_raw_pk(output_pubkey)
    # Generate nonce
    ecdh_res = ctypes.create_string_buffer(32)
    ret = _secp256k1.secp256k1_ecdh(secp256k1_blind_context, ecdh_res, raw_key, key.get_bytes(), None, None)
    if ret != 1:
        raise Exception("secp256k1_ecdh failed")
    nonce = hashlib.sha256(ecdh_res.raw).digest()

    ephemeral_pk = CTxOutNonce(vchCommitment=ephemeral_pk.get_bytes())
    return nonce, ephemeral_pk

"""
Create a rangeproof.
Inputs:
amount: (int) the amount in satoshis
in_value_blind: (32 bytes)  The blinds corresponding to value.
asset: (CAsset) The AssetId of the asset in this output
in_asset_blind: (32 bytes) The blind corresponding to the asset.
nonce: The rangeproof nonce to be used for encrypting the message inside the proof
scriptPubkey: The scriptpubkey in the output
value_commit: The commitment over which we are creating the rangeproof
gen: The generator `h` corresponding to the asset
ct_exponent: (int) For specifying exponent. default 0
ct_bits: (int) the number of bits over which we are doing rangeproof, default 52

Output:
Rangeproof: bytes
"""
def generate_rangeproof(amount, in_value_blind, asset, in_asset_blind, nonce, scriptPubKey, value_commit, gen, ct_exponent = CT_EXPONENT, ct_bits = CT_BITS):

    assert(isinstance(nonce, bytes) and len(nonce) == 32)
    assert(isinstance(amount, int) and amount >=0 and amount/COIN <= 21000000)
    assert(isinstance(scriptPubKey, CScript))
    assert(isinstance(value_commit, (bytes, bytearray)))
    if len(value_commit) != SECP256K1_PEDERSEN_COMMITMENT_SIZE:
        raise ValueError('len(value_commit) != SECP256K1_PEDERSEN_COMMITMENT_SIZE')
    assert(isinstance(asset, CAsset))
    assert(isinstance(gen, (bytes, bytearray)))
    if len(gen) != SECP256K1_GENERATOR_SIZE:
        raise ValueError('len(gen) != SECP256K1_GENERATOR_SIZE')
    assert(isinstance(in_value_blind, bytes) and len(in_value_blind) == 32)
    assert(isinstance(in_asset_blind, bytes) and len(in_asset_blind) == 32)

    # Prep range proof
    nRangeProofLen = ctypes.c_size_t(5134)
    rangeproof = ctypes.create_string_buffer(nRangeProofLen.value)

    # Compose sidechannel message to convey asset info (ID and asset blinds)
    assetsMessage = asset.serialize() + in_asset_blind
    assert(len(assetsMessage) == 64)

    # Sign rangeproof
    # If min_value is 0, scriptPubKey must be unspendable
    min_value = None
    if scriptPubKey.IsUnspendable():
        min_value = 0
    else:
        # Can probably something better for min_value?
        min_value = 1

    ret = _secp256k1.secp256k1_rangeproof_sign(secp256k1_blind_context,
        rangeproof, ctypes.byref(nRangeProofLen),
        min_value, value_commit, in_value_blind, nonce, ct_exponent, ct_bits,
        amount, assetsMessage, len(assetsMessage),
        None if len(scriptPubKey) == 0 else scriptPubKey, len(scriptPubKey), gen)

    if ret != 1:
        raise RuntimeError('secp256k1_rangeproof_sign failed')

    # Double check and try to rewind it
    blind_out = ctypes.create_string_buffer(32)
    value_out = ctypes.c_uint64(0)
    messsage_out = ctypes.create_string_buffer(4096)
    min_value = ctypes.c_uint64(0)
    max_value = ctypes.c_uint64(0)
    out_len = ctypes.c_size_t(0)
    ret = _secp256k1.secp256k1_rangeproof_rewind( secp256k1_blind_context,
        blind_out, ctypes.byref(value_out), messsage_out, out_len,
        nonce, ctypes.byref(max_value), ctypes.byref(min_value),
        value_commit, rangeproof, nRangeProofLen,
        None if len(scriptPubKey) == 0 else scriptPubKey, len(scriptPubKey), gen
        )
    if ret != 1:
        raise RuntimeError('secp256k1_rangeproof_rewind failed')

    return rangeproof.raw[:nRangeProofLen.value]

# Returns a surjection proof
"""
Create surjection proof
Inputs:
surjection_targets: (List[ CAsset]) The list of targets which is surjection target
target_asset_generators: (List[Generators]) The list of secp generators corresponding to the targets
target_asset_blinders: (List[32 byte]) The blinders corresponding to the assets
asset_blind: The blind corresponding to asset being blinded
output_asset_gen: The generator corresponding to the asset being blinded
asset: The asset being blinded

Output:
The surjection proof as bytes
"""
def generate_surjectionproof(surjection_targets, target_asset_generators, target_asset_blinders, asset, output_asset_gen, asset_blind):

    # Sanity checks
    assert(isinstance(surjection_targets, list))
    assert(isinstance(target_asset_generators, list))
    assert(isinstance(asset, CAsset))
    assert(len(asset_blind) == 32 and isinstance(asset_blind, bytes))
    assert(isinstance(output_asset_gen, bytes) and len(output_asset_gen) == SECP256K1_GENERATOR_SIZE)
    for target in surjection_targets:
        assert(len(target.id) == 32 and isinstance(target, CAsset))
    for gen in target_asset_generators:
        assert(len(gen) == SECP256K1_GENERATOR_SIZE and isinstance(gen, bytes))
    for blind in target_asset_blinders:
        assert(len(blind) == 32 and isinstance(blind, bytes))
    nInputsToSelect = min(3, len(target_asset_blinders))
    randseed = os.urandom(32)

    # Prepare the outputs
    input_index = ctypes.c_size_t()
    # Not possible to know the size of proof unlike in rangeproof
    # Therefore, need to call library function to allocate
    proof = ctypes.c_void_p()
    fixed_input_tags = [target.id for target in surjection_targets]
    fixed_input_tags_buf = b"".join(fixed_input_tags)
    assert(asset.id in fixed_input_tags)
    max_tries = 100
    # Find correlation between asset tag and listed input tags
    ret = _secp256k1.secp256k1_surjectionproof_allocate_initialized(
        secp256k1_blind_context,
        ctypes.byref(proof), ctypes.byref(input_index),
        fixed_input_tags_buf, len(surjection_targets),
        nInputsToSelect, asset.id, max_tries, randseed)

    if ret == 0:
        # This happens when assets is not contained in surjection targets.
        # Or malloc failures(should not happen)
        return None

    try:
        target_asset_gen_buf = b"".join(target_asset_generators)

        # Using the input chosen, build proof
        ret = _secp256k1.secp256k1_surjectionproof_generate(
            secp256k1_blind_context, proof,
            target_asset_gen_buf, len(target_asset_generators),
            output_asset_gen, input_index, target_asset_blinders[input_index.value], asset_blind)

        if ret != 1:
            raise RuntimeError('secp256k1_surjectionproof_generate failed')

        # Verify again, to check that this works
        ret = _secp256k1.secp256k1_surjectionproof_verify(
            secp256k1_blind_context, proof,
            target_asset_gen_buf, len(target_asset_generators), output_asset_gen)

        if ret != 1:
            raise RuntimeError('secp256k1_surjectionproof_verify failed')

        # Finally, serialize
        expected_output_len = _secp256k1.secp256k1_surjectionproof_serialized_size(
            secp256k1_blind_context, proof)
        output_len = ctypes.c_size_t(expected_output_len)
        serialized_proof = ctypes.create_string_buffer(output_len.value)
        _secp256k1.secp256k1_surjectionproof_serialize(
            secp256k1_blind_context, serialized_proof, ctypes.byref(output_len), proof)
        assert output_len.value == expected_output_len
    finally:
        # This is rewritten from python-elements-tx
        _secp256k1.secp256k1_surjectionproof_destroy(proof)

    return serialized_proof.raw

# TODO: implement issuances
"""
Blind Transcation: Ideally should be method on the transaction class,
but we don't prefer editting for now in order to keep changes required
to make blinding work in a separate file.

Note: Does not support issuances currently

Inputs:
tx: (CTransaction)  The transaction being blinded. All it's outputs must be unblinded
input_value_blinding_factors: (List[byte 32]) The value blinding factors
input_assets: (List[CAsset]) The input assets
input_asset_blinding_factors: (List[byte 32]) The asset blinding factors
input_amount: (List[int]) The amounts being blinded
output_pubkeys: The receiver pubkeys with which we do ECDH to get the nonce. In the
    workflow this is set in nNonce field of the Transaction, which is later replaced
    by a fresh ephemeral pk we choose. The nonce derived in used in rangeproofs for
    encyrption.
auxillary_generators: (List(secp_generators)) Additional generators for surjection proof
    anonymity set

output:
num_blinded: (int) The number of outputs blinded
output_value_blind_factors: (List[byte 32]) The List of output value blind factors
output_asset_blind_factors: (List[byte 32]) The list of output asset blind factors
"""
def blind_transaction(tx, input_value_blinding_factors, input_asset_blinding_factors, input_assets, input_amounts, output_pubkeys, auxiliary_generators = None):
    assert(len(tx.vout) >= len(output_pubkeys))
    assert(len(tx.vin) == len(input_value_blinding_factors) == len(input_asset_blinding_factors) == len(input_amounts) == len(input_assets))
    for i in range(len(tx.vin)):
        assert(isinstance(input_value_blinding_factors[i], bytes) and len(input_value_blinding_factors[i]) == 32)
        assert(isinstance(input_asset_blinding_factors[i], bytes) and len(input_asset_blinding_factors[i]) == 32)
        assert(isinstance(input_assets[i], CAsset))
        assert(isinstance(input_amounts[i], int))

    num_blind_attempts = 0
    num_blinded = 0

    max_targets = len(tx.vin)*3

    if auxiliary_generators:
        assert(len(auxiliary_generators) > len(tx.vin))
        max_targets += (len(auxiliary_generators) - len(tx.vin))

    target_asset_blinders = []
    total_targets = 0
    surjection_targets = [None for _ in range(max_targets)]
    target_asset_generators = [None for _ in range(max_targets)]

    output_value_blinding_factors = [None for _ in range(len(tx.vout))]
    output_asset_blinding_factors = [None for _ in range(len(tx.vout))]

    for i in range(len(tx.vin)):
        if input_assets[i].isNull():
            if auxiliary_generators:
                asset_generator = ctypes.create_string_buffer(SECP256K1_GENERATOR_SIZE)
                result = _secp256k1.secp256k1_generator_parse(
                    secp256k1_blind_context, asset_generator, auxiliary_generators[i])
                if result != 1:
                    raise Exception("Input auxillary generateors failed to parse")
            else:
                raise Exception("Input asset is empty, but no aux generators supplied")
        else:
            # Create a new asset generator
            asset_generator = ctypes.create_string_buffer(SECP256K1_GENERATOR_SIZE)
            ret = _secp256k1.secp256k1_generator_generate_blinded(
                secp256k1_blind_context, asset_generator,
                input_assets[i].id,
                input_asset_blinding_factors[i])
            if ret != 1:
                raise Exception('secp256k1_generator_generate_blinded Failed')

        target_asset_generators[total_targets] = asset_generator.raw
        surjection_targets[total_targets] = input_assets[i]
        target_asset_blinders.append(input_asset_blinding_factors[i])
        total_targets += 1

        # TODO: issuances

    if auxiliary_generators:
        # Add auxiallary gens to the blinding
        for i in range(len(tx.vin), len(auxiliary_generators)):
            gen = ctypes.create_string_buffer(SECP256K1_GENERATOR_SIZE)
            ret = _secp256k1.secp256k1_generator_parse(
                secp256k1_blind_context,
                gen, auxiliary_generators[i])
            if ret != 1:
                raise Exception("Auxillary generator not valid")
            target_asset_generators[total_targets] = gen.raw
            surjection_targets[total_targets] = b"\x00"*32
            target_asset_blinders.append(b"\x00"*32)
            total_targets += 1

    assert(total_targets == len(target_asset_blinders))

    # Remove all None elements
    del surjection_targets[total_targets:]
    del target_asset_generators[total_targets:]

    # Total blinded inputs that you own (that you are balancing against)
    num_known_input_blinds = 0
    # Number of outputs and issuances to blind
    num_to_blind = 0
    value_blinds = []
    asset_blinds = []
    blinded_amounts = []

    for i in range(len(tx.vin)):
        if input_amounts[i] < 0: # Don't need to check other conditions as they are already checked
            raise Exception("Amount negative")
        value_blinds.append(input_value_blinding_factors[i])
        asset_blinds.append(input_asset_blinding_factors[i])
        blinded_amounts.append(input_amounts[i])
        num_known_input_blinds += 1

        #TODO: issuances
        assert(tx.vin[i].assetIssuance.isNull())

    # Checks about the transaction outputs
    for n_out, pk in enumerate(output_pubkeys):
        if pk is not None:
            if (not tx.vout[n_out].nValue.isExplicit()) or (not tx.vout[n_out].nAsset.isExplicit()) or \
                (len(tx.wit.vtxoutwit) > n_out and tx.wit.vtxoutwit[n_out].is_null()) or \
                tx.vout[n_out].is_fee():
                    raise Exception("TxOuts must have explicit asset/values while blinding and proofs must be empty")
            num_to_blind += 1

    tx.wit.vtxoutwit = [CTxOutWitness() for _ in range(len(tx.vout))]

    for n_out in range(len(output_pubkeys)):
        if output_pubkeys[n_out].valid:
            out = tx.vout[n_out]
            num_blind_attempts += 1;
            conf_asset = out.nAsset
            conf_value = out.nValue
            amount = conf_value.getAmount()
            asset = conf_asset.getAsset()
            blinded_amounts.append(amount)

            value_blinds.append(os.urandom(32))
            asset_blinds.append(os.urandom(32))

            if num_blind_attempts == num_to_blind:
                if num_blind_attempts == 1 and num_known_input_blinds == 0:
                    return (num_blinded, output_value_blinding_factors, output_asset_blinding_factors)


                blinded_amounts_ptr = (ctypes.c_uint64 * len(blinded_amounts))(*blinded_amounts)
                asset_blind_ptrs = (ctypes.c_char_p* len(asset_blinds))()
                for i, blind in enumerate(asset_blinds):
                    asset_blind_ptrs[i] = blind

                last_blind = ctypes.create_string_buffer(value_blinds[-1], len(value_blinds[-1]))
                value_blind_ptrs = (ctypes.c_char_p*len(value_blinds))()
                for i, blind in enumerate(value_blinds[:-1]):
                    value_blind_ptrs[i] = blind
                value_blind_ptrs[-1] = ctypes.cast(last_blind, ctypes.c_char_p)

                assert(len(asset_blind_ptrs) == num_blind_attempts + num_known_input_blinds)
                assert(len(blinded_amounts) == len(asset_blind_ptrs))

                import hashlib
                _immutable_check_hash = hashlib.sha256(b''.join(b for b in value_blinds)).digest()

                # Compute the last factor in the last position of asset_blind_ptr
                ret = _secp256k1.secp256k1_pedersen_blind_generator_blind_sum(
                    secp256k1_blind_context,
                    blinded_amounts_ptr, asset_blind_ptrs, value_blind_ptrs,
                    num_blind_attempts + num_known_input_blinds, 0 + num_known_input_blinds)

                if ret != 1:

                    raise RuntimeError('secp256k1_pedersen_blind_generator_blind_sum returned failure')

                assert(_immutable_check_hash == hashlib.sha256(b''.join(b
                                                                        for b in value_blinds)).digest()),\
                    ("secp256k1_pedersen_blind_generator_blind_sum should not change "
                        "blinding factors other than the last one. Failing this assert "
                        "probably means that we supplied incorrect parameters to the function.")

                value_blinds[-1] = bytes(last_blind)

                if value_blinds[-1] == b"\x00"*32:
                    num_blinded += 1
                    return (num_blinded, output_value_blinding_factors, output_asset_blinding_factors)

            output_value_blinding_factors[n_out] = value_blinds[-1]
            output_asset_blinding_factors[n_out] = asset_blinds[-1]

            # Create confidential asset
            (conf_asset, gen) = blind_asset(asset, asset_blinds[-1])
            out.nAsset = conf_asset

            # Create confidential value
            (conf_value, value_commit) = create_value_commitment(amount, value_blinds[-1], gen)
            out.nValue = conf_value

            # Create the nonce to by doing ECDH (used for creating the range proof)
            (nonce, ephemeral_pk) = generate_output_rangeproof_nonce(output_pubkeys[n_out])
            out.nNonce = ephemeral_pk

            # TODO: support custom bits
            range_proof = generate_rangeproof(amount, value_blinds[-1], asset, asset_blinds[-1], nonce, CScript(out.scriptPubKey), value_commit, gen)

            surjection_proof = generate_surjectionproof(surjection_targets, target_asset_generators, target_asset_blinders, asset, gen, asset_blinds[-1])

            if not surjection_proof:
                continue

            tx.wit.vtxoutwit[n_out].vchRangeproof = range_proof
            tx.wit.vtxoutwit[n_out].vchSurjectionproof = surjection_proof

            num_blinded += 1
    return (num_blinded, output_value_blinding_factors, output_asset_blinding_factors)