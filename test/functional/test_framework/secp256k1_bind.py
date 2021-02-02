# Copyright (C) 2018 The python-bitcointx developers
#
# This file is from python-bitcointx.
#
# This file was originally under the GNU LESSER GENERAL PUBLIC LICENSE
# from python-bitcointx.(https://github.com/Simplexum/python-bitcointx/blob/master/LICENSE)
# and was later allowed by the permission of the authors to relicensed
# for the elements project under the MIT LICENSE.
# Author: Dmitry Petukhov <dp@simplexum.com>
#
# Copyright (c) 2014-2018 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
#

# pylama:ignore=E501,E221

# NOTE: for simplicity, when we need to pass an array of structs to secp256k1
# function, we will build an array of bytes out of elements, and then pass
# this array. we are dealing with 32 or 64-byte aligned data,
# so this should be safe. You can use build_aligned_data_array() for this.

# NOTE: special care should be taken with functions that may write to parts
# of their arguments, like secp256k1_pedersen_blind_generator_blind_sum,
# which will overwrite the element pointed to by blinding_factor.
# python's byte instance is supposed to be immutable, and for mutable byte
# buffers you should use ctypes.create_string_buffer().

import os
import ctypes
import ctypes.util
from types import FunctionType
from typing import Dict, Union, Any, Optional, cast

import bitcointx.util


PUBLIC_KEY_SIZE             = 65
COMPRESSED_PUBLIC_KEY_SIZE  = 33
SIGNATURE_SIZE              = 72
COMPACT_SIGNATURE_SIZE      = 65


class Libsecp256k1Exception(EnvironmentError):
    pass


SECP256K1_FLAGS_TYPE_CONTEXT = (1 << 0)
SECP256K1_FLAGS_BIT_CONTEXT_SIGN = (1 << 9)
SECP256K1_FLAGS_BIT_CONTEXT_VERIFY = (1 << 8)

SECP256K1_CONTEXT_SIGN = \
    (SECP256K1_FLAGS_TYPE_CONTEXT | SECP256K1_FLAGS_BIT_CONTEXT_SIGN)
SECP256K1_CONTEXT_VERIFY = \
    (SECP256K1_FLAGS_TYPE_CONTEXT | SECP256K1_FLAGS_BIT_CONTEXT_VERIFY)

SECP256K1_FLAGS_TYPE_COMPRESSION = (1 << 1)
SECP256K1_FLAGS_BIT_COMPRESSION = (1 << 8)

SECP256K1_EC_COMPRESSED = (SECP256K1_FLAGS_TYPE_COMPRESSION | SECP256K1_FLAGS_BIT_COMPRESSION)
SECP256K1_EC_UNCOMPRESSED = (SECP256K1_FLAGS_TYPE_COMPRESSION)


class Secp256k1LastErrorContextVar(bitcointx.util.ContextVarsCompat):
    last_error: Optional[Dict[str, Union[int, str]]]


_secp256k1_error_storage = Secp256k1LastErrorContextVar(last_error=None)

_ctypes_functype = getattr(ctypes, 'WINFUNCTYPE', getattr(ctypes, 'CFUNCTYPE'))


@_ctypes_functype(ctypes.c_void_p, ctypes.c_char_p, ctypes.c_void_p)
def _secp256k1_illegal_callback_fn(error_str, _data):  # type: ignore
    _secp256k1_error_storage.last_error = {'code': -2, 'type': 'illegal_argument', 'message': str(error_str)}


def secp256k1_get_last_error() -> Dict[str, Union[int, str]]:
    return cast(Dict[str, Union[int, str]],
                getattr(_secp256k1_error_storage, 'last_error', None))


def _check_ressecp256k1_void_p(val: int, _func: FunctionType,
                               _args: Any) -> ctypes.c_void_p:
    if val == 0:
        err = getattr(_secp256k1_error_storage, 'last_error', None)
        if err is None:
            raise Libsecp256k1Exception(
                -3, ('error handling callback function was not called, '
                     'error is not known'))
        raise Libsecp256k1Exception(err['code'], err['message'])
    return ctypes.c_void_p(val)


secp256k1_has_pubkey_recovery = False
secp256k1_has_privkey_negate = False
secp256k1_has_pubkey_negate = False
secp256k1_has_ecdh = False


def _add_function_definitions(_secp256k1: ctypes.CDLL) -> None:
    global secp256k1_has_pubkey_recovery
    global secp256k1_has_privkey_negate
    global secp256k1_has_pubkey_negate
    global secp256k1_has_ecdh

    if getattr(_secp256k1, 'secp256k1_ecdsa_sign_recoverable', None):
        secp256k1_has_pubkey_recovery = True
        _secp256k1.secp256k1_ecdsa_sign_recoverable.restype = ctypes.c_int
        _secp256k1.secp256k1_ecdsa_sign_recoverable.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p, ctypes.c_char_p, ctypes.c_void_p, ctypes.c_void_p]

        _secp256k1.secp256k1_ecdsa_recoverable_signature_serialize_compact.restype = ctypes.c_int
        _secp256k1.secp256k1_ecdsa_recoverable_signature_serialize_compact.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.POINTER(ctypes.c_int), ctypes.c_char_p]

        _secp256k1.secp256k1_ecdsa_recover.restype = ctypes.c_int
        _secp256k1.secp256k1_ecdsa_recover.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p, ctypes.c_char_p]

        _secp256k1.secp256k1_ecdsa_recoverable_signature_parse_compact.restype = ctypes.c_int
        _secp256k1.secp256k1_ecdsa_recoverable_signature_parse_compact.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p, ctypes.c_int]

    _secp256k1.secp256k1_context_create.restype = ctypes.c_void_p
    _secp256k1.secp256k1_context_create.errcheck = _check_ressecp256k1_void_p  # type: ignore
    _secp256k1.secp256k1_context_create.argtypes = [ctypes.c_uint]

    _secp256k1.secp256k1_context_randomize.restype = ctypes.c_int
    _secp256k1.secp256k1_context_randomize.argtypes = [ctypes.c_void_p, ctypes.c_char_p]

    _secp256k1.secp256k1_context_set_illegal_callback.restype = None
    _secp256k1.secp256k1_context_set_illegal_callback.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p]

    _secp256k1.secp256k1_ecdsa_sign.restype = ctypes.c_int
    _secp256k1.secp256k1_ecdsa_sign.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p, ctypes.c_char_p, ctypes.c_void_p, ctypes.c_void_p]

    _secp256k1.secp256k1_ecdsa_signature_serialize_der.restype = ctypes.c_int
    _secp256k1.secp256k1_ecdsa_signature_serialize_der.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.POINTER(ctypes.c_size_t), ctypes.c_char_p]

    _secp256k1.secp256k1_ec_pubkey_create.restype = ctypes.c_int
    _secp256k1.secp256k1_ec_pubkey_create.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p]

    _secp256k1.secp256k1_ec_seckey_verify.restype = ctypes.c_int
    _secp256k1.secp256k1_ec_seckey_verify.argtypes = [ctypes.c_void_p, ctypes.c_char_p]

    _secp256k1.secp256k1_ecdsa_signature_parse_der.restype = ctypes.c_int
    _secp256k1.secp256k1_ecdsa_signature_parse_der.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p, ctypes.c_size_t]

    _secp256k1.secp256k1_ecdsa_signature_normalize.restype = ctypes.c_int
    _secp256k1.secp256k1_ecdsa_signature_normalize.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p]

    _secp256k1.secp256k1_ecdsa_verify.restype = ctypes.c_int
    _secp256k1.secp256k1_ecdsa_verify.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p, ctypes.c_char_p]

    _secp256k1.secp256k1_ec_pubkey_parse.restype = ctypes.c_int
    _secp256k1.secp256k1_ec_pubkey_parse.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p, ctypes.c_size_t]

    _secp256k1.secp256k1_ec_pubkey_tweak_add.restype = ctypes.c_int
    _secp256k1.secp256k1_ec_pubkey_tweak_add.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p]

    _secp256k1.secp256k1_ec_privkey_tweak_add.restype = ctypes.c_int
    _secp256k1.secp256k1_ec_privkey_tweak_add.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p]

    if getattr(_secp256k1, 'secp256k1_ec_pubkey_negate', None):
        secp256k1_has_pubkey_negate = True
        _secp256k1.secp256k1_ec_pubkey_negate.restype = ctypes.c_int
        _secp256k1.secp256k1_ec_pubkey_negate.argtypes = [ctypes.c_void_p, ctypes.c_char_p]

    if getattr(_secp256k1, 'secp256k1_ec_privkey_negate', None):
        secp256k1_has_privkey_negate = True
        _secp256k1.secp256k1_ec_privkey_negate.restype = ctypes.c_int
        _secp256k1.secp256k1_ec_privkey_negate.argtypes = [ctypes.c_void_p, ctypes.c_char_p]

    _secp256k1.secp256k1_ec_pubkey_combine.restype = ctypes.c_int
    _secp256k1.secp256k1_ec_pubkey_combine.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.POINTER(ctypes.c_char_p), ctypes.c_int]

    if getattr(_secp256k1, 'secp256k1_ecdh', None):
        secp256k1_has_ecdh = True
        _secp256k1.secp256k1_ecdh.restype = ctypes.c_int
        _secp256k1.secp256k1_ecdh.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p, ctypes.c_void_p, ctypes.c_void_p]


class _secp256k1_context:
    """dummy type for typecheck purposes"""


def secp256k1_create_and_init_context(_secp256k1: ctypes.CDLL, flags: int
                                      ) -> _secp256k1_context:
    if flags not in (SECP256K1_CONTEXT_SIGN, SECP256K1_CONTEXT_VERIFY,
                     (SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY)):
        raise ValueError(
            'Value for flags is unexpected. '
            'Must be either SECP256K1_CONTEXT_SIGN, SECP256K1_CONTEXT_VERIFY, '
            'or a combination of these two')

    ctx = _secp256k1.secp256k1_context_create(flags)
    if ctx is None:
        raise RuntimeError('secp256k1_context_create() returned None')

    _secp256k1.secp256k1_context_set_illegal_callback(ctx, _secp256k1_illegal_callback_fn, 0)

    seed = os.urandom(32)
    # secp256k1 commit 6198375218b8132f016b701ef049fb295ca28c95 comment
    # says that "non-signing contexts may use randomization in the future"
    # so we always call randomize, but check for success only for
    # signing context, because older lib versions return 0 for non-signing ctx.
    res = _secp256k1.secp256k1_context_randomize(ctx, seed)
    if res != 1:
        assert res == 0
        if (flags & SECP256K1_CONTEXT_SIGN) == SECP256K1_CONTEXT_SIGN:
            raise RuntimeError("secp256k1 context randomization failed")
        elif flags != SECP256K1_CONTEXT_VERIFY:
            raise AssertionError('unexpected value for flags')

    return cast(_secp256k1_context, ctx)


def load_secp256k1_library(path: Optional[str] = None) -> ctypes.CDLL:
    """load libsecp256k1 via ctypes, add default function definitions
    to the library handle, and return this handle.

    Callers of this function must assume responsibility for correct usage
    of the underlying C library.
    ctypes is a low-level foreign function interface, and using the underlying
    library though it should be done with the same care as if you would be
    programming in C directly.

    Note that default function definitions are only those that relevant
    to the code that uses them in python code within this library.
    You probably should to add your own definitions for the functions that
    you want to call directly, even if they are defined here by default.
    Although removing the default function definition should be considered
    mild API breakage and should be communicated via release notes.
    """

    if path is None:
        path = ctypes.util.find_library('secp256k1')
        if path is None:
            raise ImportError('secp256k1 library not found')

    try:
        handle = ctypes.cdll.LoadLibrary(path)
    except Exception as e:
        raise ImportError('Cannot load secp256k1 library: {}'.format(e))

    _add_function_definitions(handle)

    return handle


# the handle is not exported purposefully: ctypes interface is low-level,
# you are basically calling the C functions directly.
# Anyone that uses it directly should know that they are doing.
_secp256k1 = load_secp256k1_library(bitcointx.util._secp256k1_library_path)

secp256k1_context_sign = secp256k1_create_and_init_context(_secp256k1, SECP256K1_CONTEXT_SIGN)
secp256k1_context_verify = secp256k1_create_and_init_context(_secp256k1, SECP256K1_CONTEXT_VERIFY)


__all__ = (
    'load_secp256k1_library',
    'secp256k1_context_sign',
    'secp256k1_context_verify',
    'SIGNATURE_SIZE',
    'COMPACT_SIGNATURE_SIZE',
    'PUBLIC_KEY_SIZE',
    'COMPRESSED_PUBLIC_KEY_SIZE',
    'SECP256K1_EC_COMPRESSED',
    'SECP256K1_EC_UNCOMPRESSED',
    'SECP256K1_CONTEXT_SIGN',
    'SECP256K1_CONTEXT_VERIFY',
    'secp256k1_has_pubkey_recovery',
)
