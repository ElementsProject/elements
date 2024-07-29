#!/usr/bin/env python3
# Copyright (c) 2016-2021 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Encode and decode Bitcoin addresses.

- base58 P2PKH and P2SH addresses.
- bech32 segwit v0 P2WPKH and P2WSH addresses.
- bech32m segwit v1 P2TR addresses."""

import enum
import unittest

from .script import (
    CScript,
    OP_0,
    OP_TRUE,
    hash160,
    hash256,
    sha256,
    taproot_construct,
)
from .segwit_addr import encode_segwit_address
from .util import assert_equal

ADDRESS_BCRT1_UNSPENDABLE = 'ert1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq458dk'
ADDRESS_BCRT1_UNSPENDABLE_DESCRIPTOR = 'addr(ert1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq458dk)#446fqfj4'
# Coins sent to this address can be spent with a witness stack of just OP_TRUE
ADDRESS_BCRT1_P2WSH_OP_TRUE = 'ert1qft5p2uhsdcdc3l2ua4ap5qqfg4pjaqlp250x7us7a8qqhrxrxfsqp24xws'


class AddressType(enum.Enum):
    bech32 = 'bech32'
    p2sh_segwit = 'p2sh-segwit'
    legacy = 'legacy'  # P2PKH


b58chars = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'


def create_deterministic_address_bcrt1_p2tr_op_true(hrp="ert"):
    """
    Generates a deterministic bech32m address (segwit v1 output) that
    can be spent with a witness stack of OP_TRUE and the control block
    with internal public key (script-path spending).

    Returns a tuple with the generated address and the internal key.
    """
    internal_key = (2).to_bytes(32, 'big') # ELEMENTS: the given internal key from upstream failed to verify
    scriptPubKey = taproot_construct(internal_key, [(None, CScript([OP_TRUE]))]).scriptPubKey
    address = encode_segwit_address(hrp, 1, scriptPubKey[2:])
    if hrp == "ert":
        assert_equal(address, 'ert1pxaxh5xm2p349fg5wqstrreat4atm00ktumm6q4vfu960ls09265sf37hcj')
    if hrp == "bcrt":
        assert_equal(address, 'bcrt1pxaxh5xm2p349fg5wqstrreat4atm00ktumm6q4vfu960ls09265sczkf3k')
    return (address, internal_key)


def byte_to_base58(b, version):
    result = ''
    b = bytes([version]) + b  # prepend version
    b += hash256(b)[:4]       # append checksum
    value = int.from_bytes(b, 'big')
    while value > 0:
        result = b58chars[value % 58] + result
        value //= 58
    while b[0] == 0:
        result = b58chars[0] + result
        b = b[1:]
    return result


def base58_to_byte(s):
    """Converts a base58-encoded string to its data and version.

    Throws if the base58 checksum is invalid."""
    if not s:
        return b''
    n = 0
    for c in s:
        n *= 58
        assert c in b58chars
        digit = b58chars.index(c)
        n += digit
    h = '%x' % n
    if len(h) % 2:
        h = '0' + h
    res = n.to_bytes((n.bit_length() + 7) // 8, 'big')
    pad = 0
    for c in s:
        if c == b58chars[0]:
            pad += 1
        else:
            break
    res = b'\x00' * pad + res

    if hash256(res[:-4])[:4] != res[-4:]:
        raise ValueError('Invalid Base58Check checksum')

    return res[1:-4], int(res[0])


def keyhash_to_p2pkh(hash, main=False, version=235):
    assert len(hash) == 20
    return byte_to_base58(hash, version)

def scripthash_to_p2sh(hash, main=False, prefix=75):
    assert len(hash) == 20
    version = prefix
    return byte_to_base58(hash, version)

def key_to_p2pkh(key, main=False, **kwargs):
    key = check_key(key)
    return keyhash_to_p2pkh(hash160(key), main, **kwargs)

def script_to_p2sh(script, main=False, prefix=75):
    script = check_script(script)
    return scripthash_to_p2sh(hash160(script), main, prefix)

def key_to_p2sh_p2wpkh(key, main=False, **kwargs):
    key = check_key(key)
    p2shscript = CScript([OP_0, hash160(key)])
    return script_to_p2sh(p2shscript, main, **kwargs)

def program_to_witness(version, program, main=False, hrp="ert"):
    if (type(program) is str):
        program = bytes.fromhex(program)
    assert 0 <= version <= 16
    assert 2 <= len(program) <= 40
    assert version > 0 or len(program) in [20, 32]
    return encode_segwit_address(hrp, version, program)

def script_to_p2wsh(script, main=False):
    script = check_script(script)
    return program_to_witness(0, sha256(script), main)

def key_to_p2wpkh(key, main=False, **kwargs):
    key = check_key(key)
    return program_to_witness(0, hash160(key), main, **kwargs)

def script_to_p2sh_p2wsh(script, main=False):
    script = check_script(script)
    p2shscript = CScript([OP_0, sha256(script)])
    return script_to_p2sh(p2shscript, main)

def check_key(key):
    if (type(key) is str):
        key = bytes.fromhex(key)  # Assuming this is hex string
    if (type(key) is bytes and (len(key) == 33 or len(key) == 65)):
        return key
    assert False

def check_script(script):
    if (type(script) is str):
        script = bytes.fromhex(script)  # Assuming this is hex string
    if (type(script) is bytes or type(script) is CScript):
        return script
    assert False


class TestFrameworkScript(unittest.TestCase):
    def test_base58encodedecode(self):
        def check_base58(data, version):
            self.assertEqual(base58_to_byte(byte_to_base58(data, version)), (data, version))

        check_base58(bytes.fromhex('1f8ea1702a7bd4941bca0941b852c4bbfedb2e05'), 111)
        check_base58(bytes.fromhex('3a0b05f4d7f66c3ba7009f453530296c845cc9cf'), 111)
        check_base58(bytes.fromhex('41c1eaf111802559bad61b60d62b1f897c63928a'), 111)
        check_base58(bytes.fromhex('0041c1eaf111802559bad61b60d62b1f897c63928a'), 111)
        check_base58(bytes.fromhex('000041c1eaf111802559bad61b60d62b1f897c63928a'), 111)
        check_base58(bytes.fromhex('00000041c1eaf111802559bad61b60d62b1f897c63928a'), 111)
        check_base58(bytes.fromhex('1f8ea1702a7bd4941bca0941b852c4bbfedb2e05'), 0)
        check_base58(bytes.fromhex('3a0b05f4d7f66c3ba7009f453530296c845cc9cf'), 0)
        check_base58(bytes.fromhex('41c1eaf111802559bad61b60d62b1f897c63928a'), 0)
        check_base58(bytes.fromhex('0041c1eaf111802559bad61b60d62b1f897c63928a'), 0)
        check_base58(bytes.fromhex('000041c1eaf111802559bad61b60d62b1f897c63928a'), 0)
        check_base58(bytes.fromhex('00000041c1eaf111802559bad61b60d62b1f897c63928a'), 0)
