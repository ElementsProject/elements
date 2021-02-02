# Copyright (C) 2019 The python-elementstx developers
# Copyright (C) 2018 The python-bitcointx developers
#
# This file is from python-elementstx.
#
# This file was originally under the GNU LESSER GENERAL PUBLIC LICENSE
# from python-bitcointx.(https://github.com/Simplexum/python-bitcointx/blob/master/LICENSE)
# and was later allowed by the permission of the authors to be relicensed
# for the elements project under the MIT LICENSE.
# Author: Dmitry Petukhov <dp@simplexum.com>
#
# Copyright (c) 2014-2018 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
#

# pylama:ignore=E501

import ctypes
from typing import List

from bitcointx.core.secp256k1 import (
    load_secp256k1_library,
    SECP256K1_CONTEXT_SIGN, SECP256K1_CONTEXT_VERIFY,
    secp256k1_create_and_init_context
)

_secp256k1 = load_secp256k1_library()


def _set_zkp_func_types() -> None:
    _secp256k1.secp256k1_rangeproof_info.restype = ctypes.c_int
    _secp256k1.secp256k1_rangeproof_info.argtypes = [
        ctypes.c_void_p,
        ctypes.POINTER(ctypes.c_int), ctypes.POINTER(ctypes.c_int),
        ctypes.POINTER(ctypes.c_uint64), ctypes.POINTER(ctypes.c_uint64),
        ctypes.c_char_p, ctypes.c_size_t
    ]
    _secp256k1.secp256k1_generator_parse.restype = ctypes.c_int
    _secp256k1.secp256k1_generator_parse.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p]
    _secp256k1.secp256k1_generator_generate.restype = ctypes.c_int
    _secp256k1.secp256k1_generator_generate.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p]
    _secp256k1.secp256k1_generator_generate_blinded.restype = ctypes.c_int
    _secp256k1.secp256k1_generator_generate_blinded.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p, ctypes.c_char_p]
    _secp256k1.secp256k1_generator_serialize.restype = ctypes.c_int
    _secp256k1.secp256k1_generator_serialize.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p]
    _secp256k1.secp256k1_pedersen_commit.restype = ctypes.c_int
    _secp256k1.secp256k1_pedersen_commit.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p, ctypes.c_uint64, ctypes.c_char_p]
    _secp256k1.secp256k1_pedersen_commitment_serialize.restype = ctypes.c_int
    _secp256k1.secp256k1_pedersen_commitment_serialize.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p]
    _secp256k1.secp256k1_pedersen_commitment_parse.restype = ctypes.c_int
    _secp256k1.secp256k1_pedersen_commitment_parse.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p]
    _secp256k1.secp256k1_pedersen_blind_generator_blind_sum.restype = ctypes.c_int
    _secp256k1.secp256k1_pedersen_blind_generator_blind_sum.argtypes = [
        ctypes.c_void_p,  # const secp256k1_context* ctx
        ctypes.POINTER(ctypes.c_uint64),  # const uint64_t *value
        ctypes.POINTER(ctypes.c_char_p),  # const unsigned char* const* generator_blind
        ctypes.POINTER(ctypes.c_char_p),  # unsigned char* const* blinding_factor
        ctypes.c_size_t,  # size_t n_total
        ctypes.c_size_t   # size_t n_inputs
    ]
    _secp256k1.secp256k1_rangeproof_sign.restype = ctypes.c_int
    _secp256k1.secp256k1_rangeproof_sign.argtypes = [
        ctypes.c_void_p,  # const secp256k1_context* ctx
        ctypes.c_char_p,  # unsigned char *proof
        ctypes.POINTER(ctypes.c_size_t),  # size_t *plen
        ctypes.c_uint64,   # uint64_t min_value,
        ctypes.c_char_p,  # const secp256k1_pedersen_commitment *commit,
        ctypes.c_char_p,  # const unsigned char *blind,
        ctypes.c_char_p,  # const unsigned char *nonce,
        ctypes.c_int,     # int exp,
        ctypes.c_int,     # int min_bits,
        ctypes.c_uint64,  # uint64_t value,
        ctypes.c_char_p,  # const unsigned char *message,
        ctypes.c_size_t,  # size_t msg_len,
        ctypes.c_char_p,  # const unsigned char *extra_commit,
        ctypes.c_size_t,  # size_t extra_commit_len,
        ctypes.c_char_p   # const secp256k1_generator* gen
    ]
    _secp256k1.secp256k1_rangeproof_rewind.restype = ctypes.c_int
    _secp256k1.secp256k1_rangeproof_rewind.argtypes = [
        ctypes.c_void_p,  # const secp256k1_context* ctx
        ctypes.c_char_p,  # unsigned char *blind_out
        ctypes.POINTER(ctypes.c_uint64),  # uint64_t *value_out
        ctypes.c_char_p,  # unsigned char *message_out,
        ctypes.POINTER(ctypes.c_size_t),  # size_t *outlen
        ctypes.c_char_p,  # const unsigned char *nonce
        ctypes.POINTER(ctypes.c_uint64),  # uint64_t *min_value
        ctypes.POINTER(ctypes.c_uint64),  # uint64_t *max_value
        ctypes.c_char_p,  # const secp256k1_pedersen_commitment *commit
        ctypes.c_char_p,  # const unsigned char *proof
        ctypes.c_size_t,  # size_t plen
        ctypes.c_char_p,  # const unsigned char *extra_commit
        ctypes.c_size_t,  # size_t extra_commit_len,
        ctypes.c_char_p   # const secp256k1_generator* gen
    ]
    _secp256k1.secp256k1_surjectionproof_allocate_initialized.restype = ctypes.c_int
    _secp256k1.secp256k1_surjectionproof_allocate_initialized.argtypes = [
        ctypes.c_void_p,  # const secp256k1_context* ctx
        ctypes.POINTER(ctypes.c_void_p),  # secp256k1_surjectionproof** proof_out_p
        ctypes.POINTER(ctypes.c_size_t),  # size_t *input_index
        #                   NOTE: use build_aligned_data_array()
        ctypes.c_char_p,  # const secp256k1_fixed_asset_tag* fixed_input_tags
        ctypes.c_size_t,  # const size_t n_input_tags
        ctypes.c_size_t,  # const size_t n_input_tags_to_use
        ctypes.c_char_p,  # const secp256k1_fixed_asset_tag* fixed_output_tag
        ctypes.c_size_t,  # const size_t n_max_iterations
        ctypes.c_char_p   # const unsigned char *random_seed32
    ]
    _secp256k1.secp256k1_surjectionproof_destroy.restype = None
    _secp256k1.secp256k1_surjectionproof_destroy.argtypes = [
        ctypes.c_void_p,  # const secp256k1_surjectionproof* proof
    ]

    _secp256k1.secp256k1_surjectionproof_generate.restype = ctypes.c_int
    _secp256k1.secp256k1_surjectionproof_generate.argtypes = [
        ctypes.c_void_p,  # const secp256k1_context* ctx
        ctypes.c_void_p,  # secp256k1_surjectionproof* proof
        #                   NOTE: use build_aligned_data_array()
        ctypes.c_char_p,  # const secp256k1_generator* ephemeral_input_tags
        ctypes.c_size_t,  # size_t n_ephemeral_input_tags
        ctypes.c_char_p,  # const secp256k1_generator* ephemeral_output_tag
        ctypes.c_size_t,  # size_t input_index
        ctypes.c_char_p,  # const unsigned char *input_blinding_key
        ctypes.c_char_p   # const unsigned char *output_blinding_key
    ]

    _secp256k1.secp256k1_surjectionproof_verify.restype = ctypes.c_int
    _secp256k1.secp256k1_surjectionproof_verify.argtypes = [
        ctypes.c_void_p,  # const secp256k1_context* ctx
        ctypes.c_void_p,  # const secp256k1_surjectionproof* proof
        #                   NOTE: use build_aligned_data_array()
        ctypes.c_char_p,  # const secp256k1_generator* ephemeral_input_tags
        ctypes.c_size_t,  # size_t n_ephemeral_input_tags
        ctypes.c_char_p   # const secp256k1_generator* ephemeral_output_tag
    ]
    _secp256k1.secp256k1_surjectionproof_serialized_size.restype = ctypes.c_int
    _secp256k1.secp256k1_surjectionproof_serialized_size.argtypes = [ctypes.c_void_p, ctypes.c_void_p]

    _secp256k1.secp256k1_ec_pubkey_serialize.restype = ctypes.c_int
    _secp256k1.secp256k1_ec_pubkey_serialize.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.POINTER(ctypes.c_size_t), ctypes.c_char_p, ctypes.c_uint]

    _secp256k1.secp256k1_surjectionproof_serialize.restype = ctypes.c_int
    _secp256k1.secp256k1_surjectionproof_serialize.argtypes = [
        ctypes.c_void_p,  # const secp256k1_context* ctx
        ctypes.c_char_p,  # unsigned char *output
        ctypes.POINTER(ctypes.c_size_t),  # size_t *outputlen
        ctypes.c_void_p   # const secp256k1_surjectionproof *proof
    ]


secp256k1_has_zkp = False
secp256k1_blind_context = None

if getattr(_secp256k1, 'secp256k1_rangeproof_info', None):
    secp256k1_has_zkp = True
    _set_zkp_func_types()

    secp256k1_blind_context = secp256k1_create_and_init_context(
        _secp256k1, SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY)

def build_aligned_data_array(data_list: List[bytes], expected_len: int) -> bytes:
    assert expected_len % 32 == 0, "we only deal with 32-byte aligned data"
    # It is much simpler to just build buffer by concatenating the data,
    # than create a ctypes array of N-byte arrays.
    # with fixed byte size, we do not need to bother about alignment.
    buf = b''.join(data_list)
    # but we must check that our expectation of the data size is correct
    assert len(buf) % expected_len == 0
    assert len(buf) // expected_len == len(data_list)

    return buf


SECP256K1_GENERATOR_SIZE = 64
SECP256K1_PEDERSEN_COMMITMENT_SIZE = 64

__all__ = (
    'secp256k1_has_zkp',
    'secp256k1_blind_context',
    'build_aligned_data_array',
    'SECP256K1_GENERATOR_SIZE',
    'SECP256K1_PEDERSEN_COMMITMENT_SIZE'
)
