#!/usr/bin/env python3
# Copyright (c) 2010 ArtForz -- public domain half-a-node
# Copyright (c) 2012 Jeff Garzik
# Copyright (c) 2010-2020 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Bitcoin test framework primitive and message structures

CBlock, CTransaction, CBlockHeader, CTxIn, CTxOut, etc....:
    data structures that should map to corresponding structures in
    bitcoin/primitives

msg_block, msg_tx, msg_headers, etc.:
    data structures that represent network messages

ser_*, deser_*: functions that handle serialization/deserialization.

Classes use __slots__ to ensure extraneous attributes aren't accidentally added
by tests, compromising their intended effect.
"""
from codecs import encode
import copy
import hashlib
from io import BytesIO
import math
import random
import socket
import struct
import time

from test_framework.siphash import siphash256
from test_framework.util import hex_str_to_bytes, calcfastmerkleroot, BITCOIN_ASSET_OUT, assert_equal

MIN_VERSION_SUPPORTED = 60001
MY_VERSION = 70016  # past wtxid relay
MY_SUBVERSION = b"/python-p2p-tester:0.0.3/"
MY_RELAY = 1 # from version 70001 onwards, fRelay should be appended to version messages (BIP37)

MAX_LOCATOR_SZ = 101
MAX_BLOCK_BASE_SIZE = 1000000
MAX_BLOOM_FILTER_SIZE = 36000
MAX_BLOOM_HASH_FUNCS = 50

COIN = 100000000  # 1 btc in satoshis
MAX_MONEY = 21000000 * COIN

BIP125_SEQUENCE_NUMBER = 0xfffffffd  # Sequence number that is BIP 125 opt-in and BIP 68-opt-out

MAX_PROTOCOL_MESSAGE_LENGTH = 4000000  # Maximum length of incoming protocol messages
MAX_HEADERS_RESULTS = 2000  # Number of headers sent in one getheaders result
MAX_INV_SIZE = 50000  # Maximum number of entries in an 'inv' protocol message

NODE_NETWORK = (1 << 0)
NODE_GETUTXO = (1 << 1)
NODE_BLOOM = (1 << 2)
NODE_WITNESS = (1 << 3)
NODE_COMPACT_FILTERS = (1 << 6)
NODE_NETWORK_LIMITED = (1 << 10)

MSG_TX = 1
MSG_BLOCK = 2
MSG_FILTERED_BLOCK = 3
MSG_CMPCT_BLOCK = 4
MSG_WTX = 5
MSG_WITNESS_FLAG = 1 << 30
MSG_TYPE_MASK = 0xffffffff >> 2
MSG_WITNESS_TX = MSG_TX | MSG_WITNESS_FLAG

FILTER_TYPE_BASIC = 0

WITNESS_SCALE_FACTOR = 4

# Serialization/deserialization tools
def sha256(s):
    return hashlib.new('sha256', s).digest()

def hash256(s):
    return sha256(sha256(s))

def ser_compact_size(l):
    r = b""
    if l < 253:
        r = struct.pack("B", l)
    elif l < 0x10000:
        r = struct.pack("<BH", 253, l)
    elif l < 0x100000000:
        r = struct.pack("<BI", 254, l)
    else:
        r = struct.pack("<BQ", 255, l)
    return r

def deser_compact_size(f):
    nit = struct.unpack("<B", f.read(1))[0]
    if nit == 253:
        nit = struct.unpack("<H", f.read(2))[0]
    elif nit == 254:
        nit = struct.unpack("<I", f.read(4))[0]
    elif nit == 255:
        nit = struct.unpack("<Q", f.read(8))[0]
    return nit

def deser_string(f):
    nit = deser_compact_size(f)
    return f.read(nit)

def ser_string(s):
    return ser_compact_size(len(s)) + s

def deser_uint256(f):
    r = 0
    for i in range(8):
        t = struct.unpack("<I", f.read(4))[0]
        r += t << (i * 32)
    return r


def ser_uint256(u):
    rs = b""
    for _ in range(8):
        rs += struct.pack("<I", u & 0xFFFFFFFF)
        u >>= 32
    return rs


def uint256_from_str(s):
    r = 0
    t = struct.unpack("<IIIIIIII", s[:32])
    for i in range(8):
        r += t[i] << (i * 32)
    return r


def uint256_from_compact(c):
    nbytes = (c >> 24) & 0xFF
    v = (c & 0xFFFFFF) << (8 * (nbytes - 3))
    return v


# deser_function_name: Allow for an alternate deserialization function on the
# entries in the vector.
def deser_vector(f, c, deser_function_name=None):
    nit = deser_compact_size(f)
    r = []
    for _ in range(nit):
        t = c()
        if deser_function_name:
            getattr(t, deser_function_name)(f)
        else:
            t.deserialize(f)
        r.append(t)
    return r


# ser_function_name: Allow for an alternate serialization function on the
# entries in the vector (we use this for serializing the vector of transactions
# for a witness block).
def ser_vector(l, ser_function_name=None):
    r = ser_compact_size(len(l))
    for i in l:
        if ser_function_name:
            r += getattr(i, ser_function_name)()
        else:
            r += i.serialize()
    return r


def deser_uint256_vector(f):
    nit = deser_compact_size(f)
    r = []
    for _ in range(nit):
        t = deser_uint256(f)
        r.append(t)
    return r


def ser_uint256_vector(l):
    r = ser_compact_size(len(l))
    for i in l:
        r += ser_uint256(i)
    return r


def deser_string_vector(f):
    nit = deser_compact_size(f)
    r = []
    for _ in range(nit):
        t = deser_string(f)
        r.append(t)
    return r


def ser_string_vector(l):
    r = ser_compact_size(len(l))
    for sv in l:
        r += ser_string(sv)
    return r


# Deserialize from a hex string representation (eg from RPC)
def FromHex(obj, hex_string):
    obj.deserialize(BytesIO(hex_str_to_bytes(hex_string)))
    return obj

# Convert a binary-serializable object to hex (eg for submission via RPC)
def ToHex(obj):
    return obj.serialize().hex()

# Convert a binary-serializable object to hex (eg for submission via RPC)
# This variant also serializes the witness.
def WitToHex(obj):
    return obj.serialize(with_witness=True).hex()

# Objects that map to bitcoind objects, which can be serialized/deserialized


class CAddress:
    __slots__ = ("net", "ip", "nServices", "port", "time")

    # see https://github.com/bitcoin/bips/blob/master/bip-0155.mediawiki
    NET_IPV4 = 1

    ADDRV2_NET_NAME = {
        NET_IPV4: "IPv4"
    }

    ADDRV2_ADDRESS_LENGTH = {
        NET_IPV4: 4
    }

    def __init__(self):
        self.time = 0
        self.nServices = 1
        self.net = self.NET_IPV4
        self.ip = "0.0.0.0"
        self.port = 0

    def deserialize(self, f, *, with_time=True):
        """Deserialize from addrv1 format (pre-BIP155)"""
        if with_time:
            # VERSION messages serialize CAddress objects without time
            self.time = struct.unpack("<I", f.read(4))[0]
        self.nServices = struct.unpack("<Q", f.read(8))[0]
        # We only support IPv4 which means skip 12 bytes and read the next 4 as IPv4 address.
        f.read(12)
        self.net = self.NET_IPV4
        self.ip = socket.inet_ntoa(f.read(4))
        self.port = struct.unpack(">H", f.read(2))[0]

    def serialize(self, *, with_time=True):
        """Serialize in addrv1 format (pre-BIP155)"""
        assert self.net == self.NET_IPV4
        r = b""
        if with_time:
            # VERSION messages serialize CAddress objects without time
            r += struct.pack("<I", self.time)
        r += struct.pack("<Q", self.nServices)
        r += b"\x00" * 10 + b"\xff" * 2
        r += socket.inet_aton(self.ip)
        r += struct.pack(">H", self.port)
        return r

    def deserialize_v2(self, f):
        """Deserialize from addrv2 format (BIP155)"""
        self.time = struct.unpack("<I", f.read(4))[0]

        self.nServices = deser_compact_size(f)

        self.net = struct.unpack("B", f.read(1))[0]
        assert self.net == self.NET_IPV4

        address_length = deser_compact_size(f)
        assert address_length == self.ADDRV2_ADDRESS_LENGTH[self.net]

        self.ip = socket.inet_ntoa(f.read(4))

        self.port = struct.unpack(">H", f.read(2))[0]

    def serialize_v2(self):
        """Serialize in addrv2 format (BIP155)"""
        assert self.net == self.NET_IPV4
        r = b""
        r += struct.pack("<I", self.time)
        r += ser_compact_size(self.nServices)
        r += struct.pack("B", self.net)
        r += ser_compact_size(self.ADDRV2_ADDRESS_LENGTH[self.net])
        r += socket.inet_aton(self.ip)
        r += struct.pack(">H", self.port)
        return r

    def __repr__(self):
        return ("CAddress(nServices=%i net=%s addr=%s port=%i)"
                % (self.nServices, self.ADDRV2_NET_NAME[self.net], self.ip, self.port))


class CInv:
    __slots__ = ("hash", "type")

    typemap = {
        0: "Error",
        MSG_TX: "TX",
        MSG_BLOCK: "Block",
        MSG_TX | MSG_WITNESS_FLAG: "WitnessTx",
        MSG_BLOCK | MSG_WITNESS_FLAG: "WitnessBlock",
        MSG_FILTERED_BLOCK: "filtered Block",
        MSG_CMPCT_BLOCK: "CompactBlock",
        MSG_WTX: "WTX",
    }

    def __init__(self, t=0, h=0):
        self.type = t
        self.hash = h

    def deserialize(self, f):
        self.type = struct.unpack("<I", f.read(4))[0]
        self.hash = deser_uint256(f)

    def serialize(self):
        r = b""
        r += struct.pack("<I", self.type)
        r += ser_uint256(self.hash)
        return r

    def __repr__(self):
        return "CInv(type=%s hash=%064x)" \
            % (self.typemap[self.type], self.hash)

    def __eq__(self, other):
        return isinstance(other, CInv) and self.hash == other.hash and self.type == other.type


class CBlockLocator:
    __slots__ = ("nVersion", "vHave")

    def __init__(self):
        self.nVersion = MY_VERSION
        self.vHave = []

    def deserialize(self, f):
        self.nVersion = struct.unpack("<i", f.read(4))[0]
        self.vHave = deser_uint256_vector(f)

    def serialize(self):
        r = b""
        r += struct.pack("<i", self.nVersion)
        r += ser_uint256_vector(self.vHave)
        return r

    def __repr__(self):
        return "CBlockLocator(nVersion=%i vHave=%s)" \
            % (self.nVersion, repr(self.vHave))


class COutPoint:
    __slots__ = ("hash", "n")

    def __init__(self, hash=0, n=0):
        self.hash = hash
        self.n = n

    def isNull(self):
        return self.hash == 0 and self.n == 4294967295

    def deserialize(self, f):
        self.hash = deser_uint256(f)
        self.n = struct.unpack("<I", f.read(4))[0]

    def serialize(self):
        r = b""
        r += ser_uint256(self.hash)
        r += struct.pack("<I", self.n)
        return r

    def __repr__(self):
        return "COutPoint(hash=%064x n=%i)" % (self.hash, self.n)

OUTPOINT_ISSUANCE_FLAG = (1 << 31)
OUTPOINT_PEGIN_FLAG = (1 << 30)
OUTPOINT_INDEX_MASK = 0x3fffffff

class CAssetIssuance():
    __slots__ = ("assetBlindingNonce", "assetEntropy", "nAmount", "nInflationKeys")

    def __init__(self):
        self.assetBlindingNonce = 0
        self.assetEntropy = 0
        self.nAmount = CTxOutValue()
        self.nInflationKeys = CTxOutValue()

    def isNull(self):
        return self.nAmount.isNull() and self.nInflationKeys.isNull()

    def deserialize(self, f):
        self.assetBlindingNonce = deser_uint256(f)
        self.assetEntropy = deser_uint256(f)
        self.nAmount = CTxOutValue()
        self.nAmount.deserialize(f)
        self.nInflationKeys = CTxOutValue()
        self.nInflationKeys.deserialize(f)

    def serialize(self):
        r = b""
        r += ser_uint256(self.assetBlindingNonce)
        r += ser_uint256(self.assetEntropy)
        r += self.nAmount.serialize()
        r += self.nInflationKeys.serialize()
        return r

    # serialization of asset issuance used in taproot sighash
    def taphash_asset_issuance_serialize(self):
        if self.isNull():
            return b'\x00'
        r = b''
        r += self.serialize()
        return r

    def __repr__(self):
        return "CAssetIssuance(assetBlindingNonce=%064x assetEntropy=%064x nAmount=%s nInflationKeys=%s)" % (self.assetBlindingNonce, self.assetEntropy, self.nAmount.vchCommitment, self.nInflationKeys.vchCommitment)

class CTxIn:
    __slots__ = ("nSequence", "prevout", "scriptSig", "m_is_pegin", "assetIssuance")

    def __init__(self, outpoint=None, scriptSig=b"", nSequence=0):
        if outpoint is None:
            self.prevout = COutPoint()
        else:
            self.prevout = outpoint
        self.scriptSig = scriptSig
        self.nSequence = nSequence
        self.m_is_pegin = False
        self.assetIssuance = CAssetIssuance()

    def deserialize(self, f):
        self.prevout = COutPoint()
        self.prevout.deserialize(f)

        has_asset_issuance = False
        # Do masking, extract presence of assetIssuance
        if not self.prevout.isNull(): # ignore coinbase for issuance/pegin
            if self.prevout.n & OUTPOINT_ISSUANCE_FLAG > 0:
                has_asset_issuance = True
            if self.prevout.n & OUTPOINT_PEGIN_FLAG > 0:
                self.m_is_pegin = True
            self.prevout.n = self.prevout.n & OUTPOINT_INDEX_MASK

        self.scriptSig = deser_string(f)
        self.nSequence = struct.unpack("<I", f.read(4))[0]

        if has_asset_issuance:
            self.assetIssuance = CAssetIssuance()
            self.assetIssuance.deserialize(f)

    def serialize(self):
        outpoint = COutPoint()
        outpoint.hash = self.prevout.hash
        outpoint.n = self.prevout.n
        # First apply peg-in and issuance logic to prevout.n, before serializing
        if self.prevout.n != 4294967295: # ignore coinbase for issuance/pegin
            if not self.assetIssuance.isNull():
                outpoint.n |= OUTPOINT_ISSUANCE_FLAG
            if self.m_is_pegin:
                outpoint.n |= OUTPOINT_PEGIN_FLAG

        r = b""
        r += outpoint.serialize()
        r += ser_string(self.scriptSig)
        r += struct.pack("<I", self.nSequence)
        if self.prevout.n != 4294967295 and outpoint.n & OUTPOINT_ISSUANCE_FLAG:
            r += self.assetIssuance.serialize()
        return r

    def __repr__(self):
        return "CTxIn(prevout=%s scriptSig=%s nSequence=%i m_is_pegin=%s assetIssuance=%s)" \
            % (repr(self.prevout), self.scriptSig.hex(),
               self.nSequence, self.m_is_pegin, self.assetIssuance)

class CTxOutAsset:
    __slots__ = ("vchCommitment")

    def __init__(self, vchCommitment=b"\x00"):
        self.vchCommitment = vchCommitment

    def setNull(self):
        self.vchCommitment = b'\x00'

    def deserialize(self, f):
        version = ord(f.read(1))
        if version == 0:
            self.vchCommitment = b'\x00'
        elif version == 1:
            self.vchCommitment = b'\x01' + f.read(32)
        elif version == 0xff:
            self.vchCommitment = b'\xff' + f.read(32)
        elif version == 10 or version == 11:
            self.vchCommitment = bytes([version]) + f.read(32)
        else:
            raise 'invalid CTxOutAsset in deserialize'

    def serialize(self):
        r = b""
        r += self.vchCommitment
        return r

    def setToAsset(self, val):
       if len(val) != 32:
           raise 'invalid asset hash (expected 32 bytes)'
       self.vchCommitment = b'\x01' + val

    def __repr__(self):
        return "CTxOutAsset(vchCommitment=%s)" % self.vchCommitment

class CTxOutValue:
    __slots__ = ("vchCommitment")

    def __init__(self, value=None):
        self.setNull()
        if value is not None:
            self.setToAmount(value)

    def setNull(self):
        self.vchCommitment = b'\x00'

    def isNull(self):
        return self.vchCommitment == b'\x00'

    def deserialize(self, f):
        version = ord(f.read(1))
        if version == 0:
            self.vchCommitment = b'\x00'
        elif version == 1:
            self.vchCommitment = b'\x01' + f.read(8)
        elif version == 0xff:
            self.vchCommitment = b'\xff' + f.read(8)
        elif version == 8 or version == 9:
            self.vchCommitment = bytes([version]) + f.read(32)
        else:
            raise Exception('invalid CTxOutValue in deserialize. version %d' % version)

    def serialize(self):
        r = b""
        if len(self.vchCommitment) < 1:
            raise ValueError('invalid commitment')
        r += self.vchCommitment
        return r

    def setToAmount(self, amount):
        if type(amount) == int:
            commit = [1]*9
            for i in range(8): #8 bytes
                commit[8-i] = ((amount >> (i*8)) & 0xff)
            self.vchCommitment = bytes(commit)
        else:
            if len(amount) != 8:
                raise 'invalid explicit amount (expected 8 bytes)'
            self.vchCommitment = b'\x01' + amount[::-1]

    def getAmount(self):
        if self.vchCommitment[0] != 1:
            raise ValueError('getAmount() called on non-explicit CTxOutValue')
        ret = 0
        for i in range(8): #8 bytes
            ret <<= 8
            ret |= self.vchCommitment[i+1]
        return ret

    def __repr__(self):
        return "CTxOutValue(vchCommitment=%s)" % self.vchCommitment

class CTxOutNonce:
    __slots__ = ("vchCommitment")

    def __init__(self, vchCommitment=b"\x00"):
        self.vchCommitment = vchCommitment

    def setNull(self):
        self.vchCommitment = b'\x00'

    def deserialize(self, f):
        version = ord(f.read(1))
        if version == 0:
            self.vchCommitment = b'\x00'
        elif version == 1:
            self.vchCommitment = b'\x01' + f.read(32)
        elif version == 0xff:
            self.vchCommitment = b'\xff' + f.read(32)
        elif version == 2 or version == 3:
            self.vchCommitment = bytes([version]) + f.read(32)
        else:
            raise ValueError('invalid CTxOutNonce in deserialize')

    def serialize(self):
        r = b""
        r += self.vchCommitment
        return r

    def __repr__(self):
        return "CTxOutNonce(vchCommitment=%s)" % self.vchCommitment


class CTxOut():
    __slots__ = ("nValue", "scriptPubKey", "nAsset", "nNonce")

    def __init__(self, nValue=CTxOutValue(), scriptPubKey=b'', nAsset=CTxOutAsset(BITCOIN_ASSET_OUT), nNonce=CTxOutNonce()):
        self.nAsset = nAsset
        if type(nValue) is int:
            self.nValue = CTxOutValue(nValue)
        else:
            self.nValue = nValue
        self.nNonce = nNonce
        self.scriptPubKey = scriptPubKey

    def setNull(self):
        self.nAsset.setNull()
        self.nValue.setNull()
        self.nNonce.setNull()
        self.scriptPubKey = b''

    def is_fee(self):
        return len(self.scriptPubKey) == 0

    def deserialize(self, f):
        self.nAsset = CTxOutAsset()
        self.nAsset.deserialize(f)
        self.nValue = CTxOutValue()
        self.nValue.deserialize(f)
        self.nNonce = CTxOutNonce()
        self.nNonce.deserialize(f)
        self.scriptPubKey = deser_string(f)

    def serialize(self):
        r = b""
        r += self.nAsset.serialize()
        r += self.nValue.serialize()
        r += self.nNonce.serialize()
        r += ser_string(self.scriptPubKey)
        return r

    def from_pegin_witness_data(self, peg_witness):
        self.nAsset = CTxOutAsset()
        self.nAsset.setToAsset(peg_witness.stack[1])
        self.nValue = CTxOutValue()
        self.nValue.setToAmount(peg_witness.stack[0])
        self.scriptPubKey = peg_witness.stack[3]

    def __repr__(self):
        return "CTxOut(nAsset=%s nValue=%s nNonce=%s scriptPubKey=%s)" \
            % (self.nAsset, self.nValue, self.nNonce, self.scriptPubKey.hex())


class CScriptWitness:
    __slots__ = ("stack",)

    def __init__(self):
        # stack is a vector of strings
        self.stack = []

    def __repr__(self):
        return "CScriptWitness(%s)" % \
               (",".join([x.hex() for x in self.stack]))

    def is_null(self):
        if self.stack:
            return False
        return True


class CTxInWitness:
    __slots__ = ("scriptWitness", "vchIssuanceAmountRangeproof",
                 "vchInflationKeysRangeproof", "peginWitness")

    def __init__(self):
        self.vchIssuanceAmountRangeproof = b''
        self.vchInflationKeysRangeproof = b''
        self.scriptWitness = CScriptWitness()
        self.peginWitness = CScriptWitness()

    def deserialize(self, f):
        self.vchIssuanceAmountRangeproof = deser_string(f)
        self.vchInflationKeysRangeproof = deser_string(f)
        self.scriptWitness.stack = deser_string_vector(f)
        self.peginWitness.stack = deser_string_vector(f)

    def serialize(self):
        r = b''
        r += ser_string(self.vchIssuanceAmountRangeproof)
        r += ser_string(self.vchInflationKeysRangeproof)
        r += ser_string_vector(self.scriptWitness.stack)
        r += ser_string_vector(self.peginWitness.stack)
        return r

    # Used in taproot sighash calculation
    def serialize_issuance_proofs(self):
        r = b''
        r += ser_string(self.vchIssuanceAmountRangeproof)
        r += ser_string(self.vchInflationKeysRangeproof)
        return r

    def calc_witness_hash(self):
        leaves = [
            encode(hash256(ser_string(self.vchIssuanceAmountRangeproof))[::-1], 'hex_codec').decode('ascii'),
            encode(hash256(ser_string(self.vchInflationKeysRangeproof))[::-1], 'hex_codec').decode('ascii'),
            encode(hash256(ser_string_vector(self.scriptWitness.stack))[::-1], 'hex_codec').decode('ascii'),
            encode(hash256(ser_string_vector(self.peginWitness.stack))[::-1], 'hex_codec').decode('ascii')
        ]
        return calcfastmerkleroot(leaves)

    def __repr__(self):
        return "CTxInWitness (%s, %s, %s %s)" % (self.vchIssuanceAmountRangeproof,
            self.vchInflationKeysRangeproof, self.scriptWitness, self.peginWitness)

    def is_null(self):
        return len(self.vchIssuanceAmountRangeproof) == 0 \
            and len(self.vchInflationKeysRangeproof) == 0 \
            and self.peginWitness.is_null() \
            and self.scriptWitness.is_null()


class CTxOutWitness:
    __slots__ = ("vchSurjectionproof", "vchRangeproof")

    def __init__(self):
        self.vchSurjectionproof = b''
        self.vchRangeproof = b''

    def deserialize(self, f):
        self.vchSurjectionproof = deser_string(f)
        self.vchRangeproof = deser_string(f)

    def serialize(self):
        r = b''
        r += ser_string(self.vchSurjectionproof)
        r += ser_string(self.vchRangeproof)
        return r

    def calc_witness_hash(self):
        leaves = [
            encode(hash256(ser_string(self.vchSurjectionproof))[::-1], 'hex_codec').decode('ascii'),
            encode(hash256(ser_string(self.vchRangeproof))[::-1], 'hex_codec').decode('ascii')
        ]
        return calcfastmerkleroot(leaves)

    def __repr__(self):
        return "CTxOutWitness (%s, %s)" % (self.vchSurjectionproof, self.vchRangeproof)

    def is_null(self):
        return len(self.vchSurjectionproof) == 0 \
            and len(self.vchRangeproof) == 0


class CTxWitness:
    __slots__ = ("vtxinwit", "vtxoutwit")

    def __init__(self):
        self.vtxinwit = []
        self.vtxoutwit = []

    def deserialize(self, f):
        for i in range(len(self.vtxinwit)):
            self.vtxinwit[i].deserialize(f)
        for i in range(len(self.vtxoutwit)):
            self.vtxoutwit[i].deserialize(f)

    def serialize(self):
        r = b""
        # This is different than the usual vector serialization --
        # we omit the length of the vector, which is required to be
        # the same length as the transaction's vin vector.
        for x in self.vtxinwit:
            r += x.serialize()
        for x in self.vtxoutwit:
            r += x.serialize()
        return r

    def __repr__(self):
        return "CTxWitness([%s], [%s])" % \
               (';'.join([repr(x) for x in self.vtxinwit]),
               ';'.join([repr(x) for x in self.vtxoutwit]))

    def is_null(self):
        for x in self.vtxinwit:
            if not x.is_null():
                return False
        for x in self.vtxoutwit:
            if not x.is_null():
                return False
        return True


class CTransaction:
    __slots__ = ("hash", "nLockTime", "nVersion", "sha256", "vin", "vout",
                 "wit")

    def __init__(self, tx=None):
        if tx is None:
            self.nVersion = 1
            self.vin = []
            self.vout = []
            self.wit = CTxWitness()
            self.nLockTime = 0
            self.sha256 = None
            self.hash = None
        else:
            self.nVersion = tx.nVersion
            self.vin = copy.deepcopy(tx.vin)
            self.vout = copy.deepcopy(tx.vout)
            self.nLockTime = tx.nLockTime
            self.sha256 = tx.sha256
            self.hash = tx.hash
            self.wit = copy.deepcopy(tx.wit)

    def deserialize(self, f):
        self.nVersion = struct.unpack("<i", f.read(4))[0]
        flags = struct.unpack("<B", f.read(1))[0]
        self.vin = deser_vector(f, CTxIn)
        self.vout = deser_vector(f, CTxOut)
        self.nLockTime = struct.unpack("<I", f.read(4))[0]
        if flags & 1 > 0:
            self.wit.vtxinwit = [CTxInWitness() for _ in range(len(self.vin))]
            self.wit.vtxoutwit = [CTxOutWitness() for _ in range(len(self.vout))]
            self.wit.deserialize(f)
        else:
            self.wit = CTxWitness()
        if flags > 1:
            raise TypeError('Extra witness flags:' + str(flags))
        self.sha256 = None
        self.hash = None

    # Only applicable for non-CT, non-segwit transactions
    def serialize_without_witness(self):
        r = b""
        r += struct.pack("<i", self.nVersion)
        r += struct.pack("B", 0)
        r += ser_vector(self.vin)
        r += ser_vector(self.vout)
        r += struct.pack("<I", self.nLockTime)
        return r

    # Only serialize with witness when explicitly called for
    def serialize_with_witness(self):
        flags = 0
        if not self.wit.is_null():
            flags |= 1
        r = b""
        r += struct.pack("<i", self.nVersion)
        r += struct.pack("<B", flags)
        r += ser_vector(self.vin)
        r += ser_vector(self.vout)
        r += struct.pack("<I", self.nLockTime)
        if flags & 1:
            if len(self.wit.vtxinwit) != len(self.vin):
                # vtxinwit must have the same length as vin
                self.wit.vtxinwit = self.wit.vtxinwit[:len(self.vin)]
                for _ in range(len(self.wit.vtxinwit), len(self.vin)):
                    self.wit.vtxinwit.append(CTxInWitness())
            if len(self.wit.vtxoutwit) != len(self.vout):
                # vtxoutwit must have the same length as vout
                self.wit.vtxoutwit = self.wit.vtxoutwit[:len(self.vout)]
                for i in range(len(self.wit.vtxoutwit), len(self.vout)):
                    self.wit.vtxoutwit.append(CTxOutWitness())
            r += self.wit.serialize()
        return r

    def serialize(self, with_witness=True):
        if with_witness:
            return self.serialize_with_witness()
        else:
            return self.serialize_without_witness()

    def rehash(self):
        self.sha256 = None
        self.calc_sha256()
        return self.hash

    # We will only cache the serialization without witness in
    # self.sha256 and self.hash -- those are expected to be the txid.
    def calc_sha256(self, with_witness=False):
        if with_witness:
            # Don't cache the result, just return it
            return uint256_from_str(hash256(self.serialize_with_witness()))

        if self.sha256 is None:
            self.sha256 = uint256_from_str(hash256(self.serialize_without_witness()))
        self.hash = encode(hash256(self.serialize_without_witness())[::-1], 'hex_codec').decode('ascii')

    def calc_witness_hash(self):
        leaves = []
        for i in range(len(self.vin)):
            if i >= len(self.wit.vtxinwit) or self.vin[i].prevout.isNull():
                wit = CTxInWitness()
            else:
                wit = self.wit.vtxinwit[i]
            leaves.append(wit.calc_witness_hash())
        inwitroot = calcfastmerkleroot(leaves)

        leaves = []
        for i in range(len(self.vout)):
            wit = self.wit.vtxoutwit[i] if i < len(self.wit.vtxoutwit) else CTxOutWitness()
            leaves.append(wit.calc_witness_hash())
        outwitroot = calcfastmerkleroot(leaves)

        # returns bitcoin hash print style string
        return calcfastmerkleroot([inwitroot, outwitroot])

    def is_valid(self):
        self.calc_sha256()
        for tout in self.vout:
            if tout.nValue < 0 or tout.nValue > 21000000 * COIN:
                return False
        return True

    # Calculate the virtual transaction size using witness and non-witness
    # serialization size (does NOT use sigops).
    def get_vsize(self):
        with_witness_size = len(self.serialize_with_witness())
        without_witness_size = len(self.serialize_without_witness())
        return math.ceil(((WITNESS_SCALE_FACTOR - 1) * without_witness_size + with_witness_size) / WITNESS_SCALE_FACTOR)

    def __repr__(self):
        return "CTransaction(nVersion=%i vin=%s vout=%s wit=%s nLockTime=%i)" \
            % (self.nVersion, repr(self.vin), repr(self.vout), repr(self.wit), self.nLockTime)


class CProof:
    __slots__ = ("challenge", "solution")

    # Default allows OP_TRUE blocks
    def __init__(self, challenge=bytearray.fromhex('51'), solution=b""):
        self.challenge = challenge
        self.solution = solution

    def set_null(self):
        self.challenge = b""
        self.solution = b""

    def deserialize(self, f):
        self.challenge = deser_string(f)
        self.solution = deser_string(f)

    def serialize(self):
        r = b""
        r += ser_string(self.challenge)
        r += ser_string(self.solution)
        return r

    def serialize_for_hash(self):
        r = b""
        r += ser_string(self.challenge)
        return r

    def __repr__(self):
        return "CProof(challenge=%s solution=%s)" \
            % (self.challenge, self.solution)

class DynaFedParamEntry:
    __slots__ = ("m_serialize_type", "m_signblockscript", "m_signblock_witness_limit", "m_fedpeg_program", "m_fedpegscript", "m_extension_space", "m_elided_root")

    # Constructor args will define serialization type:
    # null = 0
    # signblock-related fields = 1, required for m_current on non-epoch-starts
    # all fields = 2, required for epoch starts
    def __init__(self, m_signblockscript=b"", m_signblock_witness_limit=0, m_fedpeg_program=b"", m_fedpegscript=b"", m_extension_space=None, m_elided_root=0):
        if m_extension_space is None:
            m_extension_space = []
        self.m_signblockscript = m_signblockscript
        self.m_signblock_witness_limit = m_signblock_witness_limit
        self.m_fedpeg_program = m_fedpeg_program
        self.m_fedpegscript = m_fedpegscript
        self.m_extension_space = m_extension_space
        if self.is_null():
            self.m_serialize_type = 0
        elif m_fedpegscript==b"" and m_fedpeg_program==b"" and m_extension_space == []:
            self.m_serialize_type = 1
            # We also set the "extra root" in this case
            self.m_elided_root = m_elided_root
        else:
            self.m_serialize_type = 2

    def set_null(self):
        self.m_signblockscript = b""
        self.m_signblock_witness_limit = 0
        self.m_fedpeg_program = b""
        self.m_fedpegscript = b""
        self.m_extension_space = []
        self.m_serialize_type = 0
        self.m_elided_root = 0

    def is_null(self):
        return self.m_signblockscript == b"" and self.m_signblock_witness_limit == 0 and \
                self.m_fedpeg_program == b"" and self.m_fedpegscript == b"" and \
                self.m_extension_space == []

    def serialize(self):
        r = b""
        r += struct.pack("B", self.m_serialize_type)
        if self.m_serialize_type == 1:
            r += ser_string(self.m_signblockscript)
            r += struct.pack("<I", self.m_signblock_witness_limit)
            r += ser_uint256(self.m_elided_root)
        elif self.m_serialize_type == 2:
            r += ser_string(self.m_signblockscript)
            r += struct.pack("<I", self.m_signblock_witness_limit)
            r += ser_string(self.m_fedpeg_program)
            r += ser_string(self.m_fedpegscript)
            r += ser_string_vector(self.m_extension_space)
        elif self.m_serialize_type > 2:
            raise Exception("Invalid serialization type for DynaFedParamEntry")
        return r

    def deserialize(self, f):
        self.m_serialize_type = struct.unpack("B", f.read(1))[0]
        if self.m_serialize_type == 1:
            self.m_signblockscript = deser_string(f)
            self.m_signblock_witness_limit = struct.unpack("<I", f.read(4))[0]
            self.m_elided_root = deser_uint256(f)
        elif self.m_serialize_type == 2:
            self.m_signblockscript = deser_string(f)
            self.m_signblock_witness_limit = struct.unpack("<I", f.read(4))[0]
            self.m_fedpeg_program = deser_string(f)
            self.m_fedpegscript = deser_string(f)
            self.m_extension_space = deser_string_vector(f)

    def __repr__(self):
        return "DynaFedParamEntry(m_signblockscript=%s m_fedpegscript=%s m_extension_space=%s)" \
                % (self.m_signblockscript, self.m_fedpegscript, self.m_extension_space)

class DynaFedParams:
    __slots__ = ("m_current", "m_proposed")

    def __init__(self, m_current=DynaFedParamEntry(), m_proposed=DynaFedParamEntry()):
        self.m_current = m_current
        self.m_proposed = m_proposed

    def set_null(self):
        self.m_current.set_null()
        self.m_proposed.set_null()

    def is_null(self):
        return self.m_current.is_null() and self.m_proposed.is_null()

    def serialize(self):
        r = b""
        r += self.m_current.serialize()
        r += self.m_proposed.serialize()
        return r

    def deserialize(self, f):
        self.m_current.deserialize(f)
        self.m_proposed.deserialize(f)

    def __repr__(self):
        return "DynaFedParams(m_current=%s m_proposed=%s)" \
                % (self.m_current, self.m_proposed)


HEADER_HF_BIT = 1 << 31
HEADER_DYNAFED_HF_MASK = 0x7fffffff
class CBlockHeader:
    __slots__ = ("hash", "hashMerkleRoot", "hashPrevBlock", "nBits", "nNonce",
                 "nTime", "nVersion", "sha256", "block_height", "proof", "m_dynafed_params",
                 "m_signblock_witness")

    def __init__(self, header=None):
        if header is None:
            self.set_null()
        else:
            self.nVersion = header.nVersion
            self.hashPrevBlock = header.hashPrevBlock
            self.hashMerkleRoot = header.hashMerkleRoot
            self.nTime = header.nTime
            self.block_height = header.block_height
            self.proof = header.proof
            self.sha256 = header.sha256
            self.hash = header.hash
            self.m_dynafed_params = header.m_dynafed_params
            self.m_signblock_witness = header.m_signblock_witness
            self.calc_sha256()

    def set_null(self):
        self.nVersion = 1
        self.hashPrevBlock = 0
        self.hashMerkleRoot = 0
        self.nTime = 0
        self.block_height = 0
        self.proof = CProof()
        self.m_dynafed_params = DynaFedParams()
        self.m_signblock_witness = CScriptWitness()
        self.sha256 = None
        self.hash = None

    def deserialize(self, f):
        self.nVersion = struct.unpack("<i", f.read(4))[0]
        is_dyna = False

        if self.nVersion < 0:
            is_dyna = True
            self.nVersion = HEADER_DYNAFED_HF_MASK & self.nVersion

        self.hashPrevBlock = deser_uint256(f)
        self.hashMerkleRoot = deser_uint256(f)
        self.nTime = struct.unpack("<I", f.read(4))[0]
        self.block_height = struct.unpack("<I", f.read(4))[0]
        if is_dyna:
            self.m_dynafed_params.deserialize(f)
            self.m_signblock_witness.stack = deser_string_vector(f)
        else:
            self.proof.deserialize(f)
        self.sha256 = None
        self.hash = None

    def serialize(self):
        r = b""
        nVersion = self.nVersion
        is_dyna = False
        if not self.m_dynafed_params.is_null():
            nVersion -= HEADER_HF_BIT
            is_dyna = True

        r += struct.pack("<i", nVersion)
        r += ser_uint256(self.hashPrevBlock)
        r += ser_uint256(self.hashMerkleRoot)
        r += struct.pack("<I", self.nTime)
        r += struct.pack("<I", self.block_height)
        if is_dyna:
            r += self.m_dynafed_params.serialize()
            r += ser_string_vector(self.m_signblock_witness.stack)
        else:
            r += self.proof.serialize()
        return r

    def calc_sha256(self):
        if self.sha256 is None:
            nVersion = self.nVersion
            is_dyna = False
            if not self.m_dynafed_params.is_null():
                nVersion -= HEADER_HF_BIT
                is_dyna = True

            r = b""
            r += struct.pack("<i", nVersion)
            r += ser_uint256(self.hashPrevBlock)
            r += ser_uint256(self.hashMerkleRoot)
            r += struct.pack("<I", self.nTime)
            r += struct.pack("<I", self.block_height)
            if is_dyna:
                r += self.m_dynafed_params.serialize()
            else:
                r += self.proof.serialize_for_hash()
            self.sha256 = uint256_from_str(hash256(r))
            self.hash = encode(hash256(r)[::-1], 'hex_codec').decode('ascii')

    def rehash(self):
        self.sha256 = None
        self.calc_sha256()
        return self.sha256

    def __repr__(self):
        return "CBlockHeader(nVersion=%i hashPrevBlock=%064x hashMerkleRoot=%064x ntime=%s block_height=%s)" \
            % (self.nVersion, self.hashPrevBlock, self.hashMerkleRoot,
               time.ctime(self.nTime), self.block_height)

BLOCK_HEADER_SIZE = len(CBlockHeader().serialize())
assert_equal(BLOCK_HEADER_SIZE, 79)

class CBlock(CBlockHeader):
    __slots__ = ("vtx",)

    def __init__(self, header=None):
        super().__init__(header)
        self.vtx = []

    def deserialize(self, f):
        super().deserialize(f)
        self.vtx = deser_vector(f, CTransaction)

    def serialize(self, with_witness=True):
        r = b""
        r += super().serialize()
        if with_witness:
            r += ser_vector(self.vtx, "serialize_with_witness")
        else:
            r += ser_vector(self.vtx, "serialize_without_witness")
        return r

    # Calculate the merkle root given a vector of transaction hashes
    @classmethod
    def get_merkle_root(cls, hashes):
        while len(hashes) > 1:
            newhashes = []
            for i in range(0, len(hashes), 2):
                i2 = min(i+1, len(hashes)-1)
                newhashes.append(hash256(hashes[i] + hashes[i2]))
            hashes = newhashes
        return uint256_from_str(hashes[0])

    def calc_merkle_root(self):
        hashes = []
        for tx in self.vtx:
            tx.calc_sha256()
            hashes.append(ser_uint256(tx.sha256))
        return self.get_merkle_root(hashes)

    def calc_witness_merkle_root(self):
        hashes = []
        for tx in self.vtx:
            # Calculate the hashes with witness data
            hashes.append(tx.calc_witness_hash())

        # returns bitcoin hash print order hex string
        return calcfastmerkleroot(hashes)

    def is_valid(self):
        self.calc_sha256()
# TODO: check signatures
#        target = uint256_from_compact(self.nBits)
#        if self.sha256 > target:
#            return False
        for tx in self.vtx:
            if not tx.is_valid():
                return False
        if self.calc_merkle_root() != self.hashMerkleRoot:
            return False
        return True

    def solve(self):
        self.rehash()
#        target = uint256_from_compact(self.nBits)
#        while self.sha256 > target:
#            self.nNonce += 1
#            self.rehash()

    def __repr__(self):
        return "CBlock(nVersion=%i hashPrevBlock=%064x hashMerkleRoot=%064x nTime=%s vtx=%s m_dynafed_params=%s)" \
            % (self.nVersion, self.hashPrevBlock, self.hashMerkleRoot,
               time.ctime(self.nTime), repr(self.vtx), self.m_dynafed_params)


class PrefilledTransaction:
    __slots__ = ("index", "tx")

    def __init__(self, index=0, tx = None):
        self.index = index
        self.tx = tx

    def deserialize(self, f):
        self.index = deser_compact_size(f)
        self.tx = CTransaction()
        self.tx.deserialize(f)

    def serialize(self, with_witness=True):
        r = b""
        r += ser_compact_size(self.index)
        if with_witness:
            r += self.tx.serialize_with_witness()
        else:
            r += self.tx.serialize_without_witness()
        return r

    def serialize_without_witness(self):
        return self.serialize(with_witness=False)

    def serialize_with_witness(self):
        return self.serialize(with_witness=True)

    def __repr__(self):
        return "PrefilledTransaction(index=%d, tx=%s)" % (self.index, repr(self.tx))


# This is what we send on the wire, in a cmpctblock message.
class P2PHeaderAndShortIDs:
    __slots__ = ("header", "nonce", "prefilled_txn", "prefilled_txn_length",
                 "shortids", "shortids_length")

    def __init__(self):
        self.header = CBlockHeader()
        self.nonce = 0
        self.shortids_length = 0
        self.shortids = []
        self.prefilled_txn_length = 0
        self.prefilled_txn = []

    def deserialize(self, f):
        self.header.deserialize(f)
        self.nonce = struct.unpack("<Q", f.read(8))[0]
        self.shortids_length = deser_compact_size(f)
        for _ in range(self.shortids_length):
            # shortids are defined to be 6 bytes in the spec, so append
            # two zero bytes and read it in as an 8-byte number
            self.shortids.append(struct.unpack("<Q", f.read(6) + b'\x00\x00')[0])
        self.prefilled_txn = deser_vector(f, PrefilledTransaction)
        self.prefilled_txn_length = len(self.prefilled_txn)

    # When using version 2 compact blocks, we must serialize with_witness.
    def serialize(self, with_witness=False):
        r = b""
        r += self.header.serialize()
        r += struct.pack("<Q", self.nonce)
        r += ser_compact_size(self.shortids_length)
        for x in self.shortids:
            # We only want the first 6 bytes
            r += struct.pack("<Q", x)[0:6]
        if with_witness:
            r += ser_vector(self.prefilled_txn, "serialize_with_witness")
        else:
            r += ser_vector(self.prefilled_txn, "serialize_without_witness")
        return r

    def __repr__(self):
        return "P2PHeaderAndShortIDs(header=%s, nonce=%d, shortids_length=%d, shortids=%s, prefilled_txn_length=%d, prefilledtxn=%s" % (repr(self.header), self.nonce, self.shortids_length, repr(self.shortids), self.prefilled_txn_length, repr(self.prefilled_txn))


# P2P version of the above that will use witness serialization (for compact
# block version 2)
class P2PHeaderAndShortWitnessIDs(P2PHeaderAndShortIDs):
    __slots__ = ()
    def serialize(self):
        return super().serialize(with_witness=True)

# Calculate the BIP 152-compact blocks shortid for a given transaction hash
def calculate_shortid(k0, k1, tx_hash):
    expected_shortid = siphash256(k0, k1, tx_hash)
    expected_shortid &= 0x0000ffffffffffff
    return expected_shortid


# This version gets rid of the array lengths, and reinterprets the differential
# encoding into indices that can be used for lookup.
class HeaderAndShortIDs:
    __slots__ = ("header", "nonce", "prefilled_txn", "shortids", "use_witness")

    def __init__(self, p2pheaders_and_shortids = None):
        self.header = CBlockHeader()
        self.nonce = 0
        self.shortids = []
        self.prefilled_txn = []
        self.use_witness = False

        if p2pheaders_and_shortids is not None:
            self.header = p2pheaders_and_shortids.header
            self.nonce = p2pheaders_and_shortids.nonce
            self.shortids = p2pheaders_and_shortids.shortids
            last_index = -1
            for x in p2pheaders_and_shortids.prefilled_txn:
                self.prefilled_txn.append(PrefilledTransaction(x.index + last_index + 1, x.tx))
                last_index = self.prefilled_txn[-1].index

    def to_p2p(self):
        if self.use_witness:
            ret = P2PHeaderAndShortWitnessIDs()
        else:
            ret = P2PHeaderAndShortIDs()
        ret.header = self.header
        ret.nonce = self.nonce
        ret.shortids_length = len(self.shortids)
        ret.shortids = self.shortids
        ret.prefilled_txn_length = len(self.prefilled_txn)
        ret.prefilled_txn = []
        last_index = -1
        for x in self.prefilled_txn:
            ret.prefilled_txn.append(PrefilledTransaction(x.index - last_index - 1, x.tx))
            last_index = x.index
        return ret

    def get_siphash_keys(self):
        header_nonce = self.header.serialize()
        header_nonce += struct.pack("<Q", self.nonce)
        hash_header_nonce_as_str = sha256(header_nonce)
        key0 = struct.unpack("<Q", hash_header_nonce_as_str[0:8])[0]
        key1 = struct.unpack("<Q", hash_header_nonce_as_str[8:16])[0]
        return [ key0, key1 ]

    # Version 2 compact blocks use wtxid in shortids (rather than txid)
    def initialize_from_block(self, block, nonce=0, prefill_list=None, use_witness=False):
        if prefill_list is None:
            prefill_list = [0]
        self.header = CBlockHeader(block)
        self.nonce = nonce
        self.prefilled_txn = [ PrefilledTransaction(i, block.vtx[i]) for i in prefill_list ]
        self.shortids = []
        self.use_witness = use_witness
        [k0, k1] = self.get_siphash_keys()
        for i in range(len(block.vtx)):
            if i not in prefill_list:
                tx_hash = block.vtx[i].sha256
                if use_witness:
                    tx_hash = block.vtx[i].calc_sha256(with_witness=True)
                self.shortids.append(calculate_shortid(k0, k1, tx_hash))

    def __repr__(self):
        return "HeaderAndShortIDs(header=%s, nonce=%d, shortids=%s, prefilledtxn=%s" % (repr(self.header), self.nonce, repr(self.shortids), repr(self.prefilled_txn))


class BlockTransactionsRequest:
    __slots__ = ("blockhash", "indexes")

    def __init__(self, blockhash=0, indexes = None):
        self.blockhash = blockhash
        self.indexes = indexes if indexes is not None else []

    def deserialize(self, f):
        self.blockhash = deser_uint256(f)
        indexes_length = deser_compact_size(f)
        for _ in range(indexes_length):
            self.indexes.append(deser_compact_size(f))

    def serialize(self):
        r = b""
        r += ser_uint256(self.blockhash)
        r += ser_compact_size(len(self.indexes))
        for x in self.indexes:
            r += ser_compact_size(x)
        return r

    # helper to set the differentially encoded indexes from absolute ones
    def from_absolute(self, absolute_indexes):
        self.indexes = []
        last_index = -1
        for x in absolute_indexes:
            self.indexes.append(x-last_index-1)
            last_index = x

    def to_absolute(self):
        absolute_indexes = []
        last_index = -1
        for x in self.indexes:
            absolute_indexes.append(x+last_index+1)
            last_index = absolute_indexes[-1]
        return absolute_indexes

    def __repr__(self):
        return "BlockTransactionsRequest(hash=%064x indexes=%s)" % (self.blockhash, repr(self.indexes))


class BlockTransactions:
    __slots__ = ("blockhash", "transactions")

    def __init__(self, blockhash=0, transactions = None):
        self.blockhash = blockhash
        self.transactions = transactions if transactions is not None else []

    def deserialize(self, f):
        self.blockhash = deser_uint256(f)
        self.transactions = deser_vector(f, CTransaction)

    def serialize(self, with_witness=True):
        r = b""
        r += ser_uint256(self.blockhash)
        if with_witness:
            r += ser_vector(self.transactions, "serialize_with_witness")
        else:
            r += ser_vector(self.transactions, "serialize_without_witness")
        return r

    def __repr__(self):
        return "BlockTransactions(hash=%064x transactions=%s)" % (self.blockhash, repr(self.transactions))


class CPartialMerkleTree:
    __slots__ = ("nTransactions", "vBits", "vHash")

    def __init__(self):
        self.nTransactions = 0
        self.vHash = []
        self.vBits = []

    def deserialize(self, f):
        self.nTransactions = struct.unpack("<i", f.read(4))[0]
        self.vHash = deser_uint256_vector(f)
        vBytes = deser_string(f)
        self.vBits = []
        for i in range(len(vBytes) * 8):
            self.vBits.append(vBytes[i//8] & (1 << (i % 8)) != 0)

    def serialize(self):
        r = b""
        r += struct.pack("<i", self.nTransactions)
        r += ser_uint256_vector(self.vHash)
        vBytesArray = bytearray([0x00] * ((len(self.vBits) + 7)//8))
        for i in range(len(self.vBits)):
            vBytesArray[i // 8] |= self.vBits[i] << (i % 8)
        r += ser_string(bytes(vBytesArray))
        return r

    def __repr__(self):
        return "CPartialMerkleTree(nTransactions=%d, vHash=%s, vBits=%s)" % (self.nTransactions, repr(self.vHash), repr(self.vBits))


class CMerkleBlock:
    __slots__ = ("header", "txn")

    def __init__(self):
        self.header = CBlockHeader()
        self.txn = CPartialMerkleTree()

    def deserialize(self, f):
        self.header.deserialize(f)
        self.txn.deserialize(f)

    def serialize(self):
        r = b""
        r += self.header.serialize()
        r += self.txn.serialize()
        return r

    def __repr__(self):
        return "CMerkleBlock(header=%s, txn=%s)" % (repr(self.header), repr(self.txn))


# Objects that correspond to messages on the wire
class msg_version:
    __slots__ = ("addrFrom", "addrTo", "nNonce", "nRelay", "nServices",
                 "nStartingHeight", "nTime", "nVersion", "strSubVer")
    msgtype = b"version"

    def __init__(self):
        self.nVersion = MY_VERSION
        self.nServices = NODE_NETWORK | NODE_WITNESS
        self.nTime = int(time.time())
        self.addrTo = CAddress()
        self.addrFrom = CAddress()
        self.nNonce = random.getrandbits(64)
        self.strSubVer = MY_SUBVERSION
        self.nStartingHeight = -1
        self.nRelay = MY_RELAY

    def deserialize(self, f):
        self.nVersion = struct.unpack("<i", f.read(4))[0]
        self.nServices = struct.unpack("<Q", f.read(8))[0]
        self.nTime = struct.unpack("<q", f.read(8))[0]
        self.addrTo = CAddress()
        self.addrTo.deserialize(f, with_time=False)

        self.addrFrom = CAddress()
        self.addrFrom.deserialize(f, with_time=False)
        self.nNonce = struct.unpack("<Q", f.read(8))[0]
        self.strSubVer = deser_string(f)

        self.nStartingHeight = struct.unpack("<i", f.read(4))[0]

        if self.nVersion >= 70001:
            # Relay field is optional for version 70001 onwards
            try:
                self.nRelay = struct.unpack("<b", f.read(1))[0]
            except:
                self.nRelay = 0
        else:
            self.nRelay = 0

    def serialize(self):
        r = b""
        r += struct.pack("<i", self.nVersion)
        r += struct.pack("<Q", self.nServices)
        r += struct.pack("<q", self.nTime)
        r += self.addrTo.serialize(with_time=False)
        r += self.addrFrom.serialize(with_time=False)
        r += struct.pack("<Q", self.nNonce)
        r += ser_string(self.strSubVer)
        r += struct.pack("<i", self.nStartingHeight)
        r += struct.pack("<b", self.nRelay)
        return r

    def __repr__(self):
        return 'msg_version(nVersion=%i nServices=%i nTime=%s addrTo=%s addrFrom=%s nNonce=0x%016X strSubVer=%s nStartingHeight=%i nRelay=%i)' \
            % (self.nVersion, self.nServices, time.ctime(self.nTime),
               repr(self.addrTo), repr(self.addrFrom), self.nNonce,
               self.strSubVer, self.nStartingHeight, self.nRelay)


class msg_verack:
    __slots__ = ()
    msgtype = b"verack"

    def __init__(self):
        pass

    def deserialize(self, f):
        pass

    def serialize(self):
        return b""

    def __repr__(self):
        return "msg_verack()"


class msg_addr:
    __slots__ = ("addrs",)
    msgtype = b"addr"

    def __init__(self):
        self.addrs = []

    def deserialize(self, f):
        self.addrs = deser_vector(f, CAddress)

    def serialize(self):
        return ser_vector(self.addrs)

    def __repr__(self):
        return "msg_addr(addrs=%s)" % (repr(self.addrs))


class msg_addrv2:
    __slots__ = ("addrs",)
    msgtype = b"addrv2"

    def __init__(self):
        self.addrs = []

    def deserialize(self, f):
        self.addrs = deser_vector(f, CAddress, "deserialize_v2")

    def serialize(self):
        return ser_vector(self.addrs, "serialize_v2")

    def __repr__(self):
        return "msg_addrv2(addrs=%s)" % (repr(self.addrs))


class msg_sendaddrv2:
    __slots__ = ()
    msgtype = b"sendaddrv2"

    def __init__(self):
        pass

    def deserialize(self, f):
        pass

    def serialize(self):
        return b""

    def __repr__(self):
        return "msg_sendaddrv2()"


class msg_inv:
    __slots__ = ("inv",)
    msgtype = b"inv"

    def __init__(self, inv=None):
        if inv is None:
            self.inv = []
        else:
            self.inv = inv

    def deserialize(self, f):
        self.inv = deser_vector(f, CInv)

    def serialize(self):
        return ser_vector(self.inv)

    def __repr__(self):
        return "msg_inv(inv=%s)" % (repr(self.inv))


class msg_getdata:
    __slots__ = ("inv",)
    msgtype = b"getdata"

    def __init__(self, inv=None):
        self.inv = inv if inv is not None else []

    def deserialize(self, f):
        self.inv = deser_vector(f, CInv)

    def serialize(self):
        return ser_vector(self.inv)

    def __repr__(self):
        return "msg_getdata(inv=%s)" % (repr(self.inv))


class msg_getblocks:
    __slots__ = ("locator", "hashstop")
    msgtype = b"getblocks"

    def __init__(self):
        self.locator = CBlockLocator()
        self.hashstop = 0

    def deserialize(self, f):
        self.locator = CBlockLocator()
        self.locator.deserialize(f)
        self.hashstop = deser_uint256(f)

    def serialize(self):
        r = b""
        r += self.locator.serialize()
        r += ser_uint256(self.hashstop)
        return r

    def __repr__(self):
        return "msg_getblocks(locator=%s hashstop=%064x)" \
            % (repr(self.locator), self.hashstop)


class msg_tx:
    __slots__ = ("tx",)
    msgtype = b"tx"

    def __init__(self, tx=CTransaction()):
        self.tx = tx

    def deserialize(self, f):
        self.tx.deserialize(f)

    def serialize(self):
        return self.tx.serialize_with_witness()

    def __repr__(self):
        return "msg_tx(tx=%s)" % (repr(self.tx))

class msg_wtxidrelay:
    __slots__ = ()
    msgtype = b"wtxidrelay"

    def __init__(self):
        pass

    def deserialize(self, f):
        pass

    def serialize(self):
        return b""

    def __repr__(self):
        return "msg_wtxidrelay()"


class msg_no_witness_tx(msg_tx):
    __slots__ = ()

    def serialize(self):
        return self.tx.serialize_without_witness()


class msg_block:
    __slots__ = ("block",)
    msgtype = b"block"

    def __init__(self, block=None):
        if block is None:
            self.block = CBlock()
        else:
            self.block = block

    def deserialize(self, f):
        self.block.deserialize(f)

    def serialize(self):
        return self.block.serialize()

    def __repr__(self):
        return "msg_block(block=%s)" % (repr(self.block))


# for cases where a user needs tighter control over what is sent over the wire
# note that the user must supply the name of the msgtype, and the data
class msg_generic:
    __slots__ = ("msgtype", "data")

    def __init__(self, msgtype, data=None):
        self.msgtype = msgtype
        self.data = data

    def serialize(self):
        return self.data

    def __repr__(self):
        return "msg_generic()"


class msg_no_witness_block(msg_block):
    __slots__ = ()
    def serialize(self):
        return self.block.serialize(with_witness=False)


class msg_getaddr:
    __slots__ = ()
    msgtype = b"getaddr"

    def __init__(self):
        pass

    def deserialize(self, f):
        pass

    def serialize(self):
        return b""

    def __repr__(self):
        return "msg_getaddr()"


class msg_ping:
    __slots__ = ("nonce",)
    msgtype = b"ping"

    def __init__(self, nonce=0):
        self.nonce = nonce

    def deserialize(self, f):
        self.nonce = struct.unpack("<Q", f.read(8))[0]

    def serialize(self):
        r = b""
        r += struct.pack("<Q", self.nonce)
        return r

    def __repr__(self):
        return "msg_ping(nonce=%08x)" % self.nonce


class msg_pong:
    __slots__ = ("nonce",)
    msgtype = b"pong"

    def __init__(self, nonce=0):
        self.nonce = nonce

    def deserialize(self, f):
        self.nonce = struct.unpack("<Q", f.read(8))[0]

    def serialize(self):
        r = b""
        r += struct.pack("<Q", self.nonce)
        return r

    def __repr__(self):
        return "msg_pong(nonce=%08x)" % self.nonce


class msg_mempool:
    __slots__ = ()
    msgtype = b"mempool"

    def __init__(self):
        pass

    def deserialize(self, f):
        pass

    def serialize(self):
        return b""

    def __repr__(self):
        return "msg_mempool()"


class msg_notfound:
    __slots__ = ("vec", )
    msgtype = b"notfound"

    def __init__(self, vec=None):
        self.vec = vec or []

    def deserialize(self, f):
        self.vec = deser_vector(f, CInv)

    def serialize(self):
        return ser_vector(self.vec)

    def __repr__(self):
        return "msg_notfound(vec=%s)" % (repr(self.vec))


class msg_sendheaders:
    __slots__ = ()
    msgtype = b"sendheaders"

    def __init__(self):
        pass

    def deserialize(self, f):
        pass

    def serialize(self):
        return b""

    def __repr__(self):
        return "msg_sendheaders()"


# getheaders message has
# number of entries
# vector of hashes
# hash_stop (hash of last desired block header, 0 to get as many as possible)
class msg_getheaders:
    __slots__ = ("hashstop", "locator",)
    msgtype = b"getheaders"

    def __init__(self):
        self.locator = CBlockLocator()
        self.hashstop = 0

    def deserialize(self, f):
        self.locator = CBlockLocator()
        self.locator.deserialize(f)
        self.hashstop = deser_uint256(f)

    def serialize(self):
        r = b""
        r += self.locator.serialize()
        r += ser_uint256(self.hashstop)
        return r

    def __repr__(self):
        return "msg_getheaders(locator=%s, stop=%064x)" \
            % (repr(self.locator), self.hashstop)


# headers message has
# <count> <vector of block headers>
class msg_headers:
    __slots__ = ("headers",)
    msgtype = b"headers"

    def __init__(self, headers=None):
        self.headers = headers if headers is not None else []

    def deserialize(self, f):
        # comment in bitcoind indicates these should be deserialized as blocks
        blocks = deser_vector(f, CBlock)
        for x in blocks:
            self.headers.append(CBlockHeader(x))

    def serialize(self):
        blocks = [CBlock(x) for x in self.headers]
        return ser_vector(blocks)

    def __repr__(self):
        return "msg_headers(headers=%s)" % repr(self.headers)


class msg_merkleblock:
    __slots__ = ("merkleblock",)
    msgtype = b"merkleblock"

    def __init__(self, merkleblock=None):
        if merkleblock is None:
            self.merkleblock = CMerkleBlock()
        else:
            self.merkleblock = merkleblock

    def deserialize(self, f):
        self.merkleblock.deserialize(f)

    def serialize(self):
        return self.merkleblock.serialize()

    def __repr__(self):
        return "msg_merkleblock(merkleblock=%s)" % (repr(self.merkleblock))


class msg_filterload:
    __slots__ = ("data", "nHashFuncs", "nTweak", "nFlags")
    msgtype = b"filterload"

    def __init__(self, data=b'00', nHashFuncs=0, nTweak=0, nFlags=0):
        self.data = data
        self.nHashFuncs = nHashFuncs
        self.nTweak = nTweak
        self.nFlags = nFlags

    def deserialize(self, f):
        self.data = deser_string(f)
        self.nHashFuncs = struct.unpack("<I", f.read(4))[0]
        self.nTweak = struct.unpack("<I", f.read(4))[0]
        self.nFlags = struct.unpack("<B", f.read(1))[0]

    def serialize(self):
        r = b""
        r += ser_string(self.data)
        r += struct.pack("<I", self.nHashFuncs)
        r += struct.pack("<I", self.nTweak)
        r += struct.pack("<B", self.nFlags)
        return r

    def __repr__(self):
        return "msg_filterload(data={}, nHashFuncs={}, nTweak={}, nFlags={})".format(
            self.data, self.nHashFuncs, self.nTweak, self.nFlags)


class msg_filteradd:
    __slots__ = ("data")
    msgtype = b"filteradd"

    def __init__(self, data):
        self.data = data

    def deserialize(self, f):
        self.data = deser_string(f)

    def serialize(self):
        r = b""
        r += ser_string(self.data)
        return r

    def __repr__(self):
        return "msg_filteradd(data={})".format(self.data)


class msg_filterclear:
    __slots__ = ()
    msgtype = b"filterclear"

    def __init__(self):
        pass

    def deserialize(self, f):
        pass

    def serialize(self):
        return b""

    def __repr__(self):
        return "msg_filterclear()"


class msg_feefilter:
    __slots__ = ("feerate",)
    msgtype = b"feefilter"

    def __init__(self, feerate=0):
        self.feerate = feerate

    def deserialize(self, f):
        self.feerate = struct.unpack("<Q", f.read(8))[0]

    def serialize(self):
        r = b""
        r += struct.pack("<Q", self.feerate)
        return r

    def __repr__(self):
        return "msg_feefilter(feerate=%08x)" % self.feerate


class msg_sendcmpct:
    __slots__ = ("announce", "version")
    msgtype = b"sendcmpct"

    def __init__(self, announce=False, version=1):
        self.announce = announce
        self.version = version

    def deserialize(self, f):
        self.announce = struct.unpack("<?", f.read(1))[0]
        self.version = struct.unpack("<Q", f.read(8))[0]

    def serialize(self):
        r = b""
        r += struct.pack("<?", self.announce)
        r += struct.pack("<Q", self.version)
        return r

    def __repr__(self):
        return "msg_sendcmpct(announce=%s, version=%lu)" % (self.announce, self.version)


class msg_cmpctblock:
    __slots__ = ("header_and_shortids",)
    msgtype = b"cmpctblock"

    def __init__(self, header_and_shortids = None):
        self.header_and_shortids = header_and_shortids

    def deserialize(self, f):
        self.header_and_shortids = P2PHeaderAndShortIDs()
        self.header_and_shortids.deserialize(f)

    def serialize(self):
        r = b""
        r += self.header_and_shortids.serialize()
        return r

    def __repr__(self):
        return "msg_cmpctblock(HeaderAndShortIDs=%s)" % repr(self.header_and_shortids)


class msg_getblocktxn:
    __slots__ = ("block_txn_request",)
    msgtype = b"getblocktxn"

    def __init__(self):
        self.block_txn_request = None

    def deserialize(self, f):
        self.block_txn_request = BlockTransactionsRequest()
        self.block_txn_request.deserialize(f)

    def serialize(self):
        r = b""
        r += self.block_txn_request.serialize()
        return r

    def __repr__(self):
        return "msg_getblocktxn(block_txn_request=%s)" % (repr(self.block_txn_request))


class msg_blocktxn:
    __slots__ = ("block_transactions",)
    msgtype = b"blocktxn"

    def __init__(self):
        self.block_transactions = BlockTransactions()

    def deserialize(self, f):
        self.block_transactions.deserialize(f)

    def serialize(self):
        r = b""
        r += self.block_transactions.serialize()
        return r

    def __repr__(self):
        return "msg_blocktxn(block_transactions=%s)" % (repr(self.block_transactions))


class msg_no_witness_blocktxn(msg_blocktxn):
    __slots__ = ()

    def serialize(self):
        return self.block_transactions.serialize(with_witness=False)


class msg_getcfilters:
    __slots__ = ("filter_type", "start_height", "stop_hash")
    msgtype =  b"getcfilters"

    def __init__(self, filter_type, start_height, stop_hash):
        self.filter_type = filter_type
        self.start_height = start_height
        self.stop_hash = stop_hash

    def deserialize(self, f):
        self.filter_type = struct.unpack("<B", f.read(1))[0]
        self.start_height = struct.unpack("<I", f.read(4))[0]
        self.stop_hash = deser_uint256(f)

    def serialize(self):
        r = b""
        r += struct.pack("<B", self.filter_type)
        r += struct.pack("<I", self.start_height)
        r += ser_uint256(self.stop_hash)
        return r

    def __repr__(self):
        return "msg_getcfilters(filter_type={:#x}, start_height={}, stop_hash={:x})".format(
            self.filter_type, self.start_height, self.stop_hash)

class msg_cfilter:
    __slots__ = ("filter_type", "block_hash", "filter_data")
    msgtype =  b"cfilter"

    def __init__(self, filter_type=None, block_hash=None, filter_data=None):
        self.filter_type = filter_type
        self.block_hash = block_hash
        self.filter_data = filter_data

    def deserialize(self, f):
        self.filter_type = struct.unpack("<B", f.read(1))[0]
        self.block_hash = deser_uint256(f)
        self.filter_data = deser_string(f)

    def serialize(self):
        r = b""
        r += struct.pack("<B", self.filter_type)
        r += ser_uint256(self.block_hash)
        r += ser_string(self.filter_data)
        return r

    def __repr__(self):
        return "msg_cfilter(filter_type={:#x}, block_hash={:x})".format(
            self.filter_type, self.block_hash)

class msg_getcfheaders:
    __slots__ = ("filter_type", "start_height", "stop_hash")
    msgtype =  b"getcfheaders"

    def __init__(self, filter_type, start_height, stop_hash):
        self.filter_type = filter_type
        self.start_height = start_height
        self.stop_hash = stop_hash

    def deserialize(self, f):
        self.filter_type = struct.unpack("<B", f.read(1))[0]
        self.start_height = struct.unpack("<I", f.read(4))[0]
        self.stop_hash = deser_uint256(f)

    def serialize(self):
        r = b""
        r += struct.pack("<B", self.filter_type)
        r += struct.pack("<I", self.start_height)
        r += ser_uint256(self.stop_hash)
        return r

    def __repr__(self):
        return "msg_getcfheaders(filter_type={:#x}, start_height={}, stop_hash={:x})".format(
            self.filter_type, self.start_height, self.stop_hash)

class msg_cfheaders:
    __slots__ = ("filter_type", "stop_hash", "prev_header", "hashes")
    msgtype =  b"cfheaders"

    def __init__(self, filter_type=None, stop_hash=None, prev_header=None, hashes=None):
        self.filter_type = filter_type
        self.stop_hash = stop_hash
        self.prev_header = prev_header
        self.hashes = hashes

    def deserialize(self, f):
        self.filter_type = struct.unpack("<B", f.read(1))[0]
        self.stop_hash = deser_uint256(f)
        self.prev_header = deser_uint256(f)
        self.hashes = deser_uint256_vector(f)

    def serialize(self):
        r = b""
        r += struct.pack("<B", self.filter_type)
        r += ser_uint256(self.stop_hash)
        r += ser_uint256(self.prev_header)
        r += ser_uint256_vector(self.hashes)
        return r

    def __repr__(self):
        return "msg_cfheaders(filter_type={:#x}, stop_hash={:x})".format(
            self.filter_type, self.stop_hash)

class msg_getcfcheckpt:
    __slots__ = ("filter_type", "stop_hash")
    msgtype =  b"getcfcheckpt"

    def __init__(self, filter_type, stop_hash):
        self.filter_type = filter_type
        self.stop_hash = stop_hash

    def deserialize(self, f):
        self.filter_type = struct.unpack("<B", f.read(1))[0]
        self.stop_hash = deser_uint256(f)

    def serialize(self):
        r = b""
        r += struct.pack("<B", self.filter_type)
        r += ser_uint256(self.stop_hash)
        return r

    def __repr__(self):
        return "msg_getcfcheckpt(filter_type={:#x}, stop_hash={:x})".format(
            self.filter_type, self.stop_hash)

class msg_cfcheckpt:
    __slots__ = ("filter_type", "stop_hash", "headers")
    msgtype =  b"cfcheckpt"

    def __init__(self, filter_type=None, stop_hash=None, headers=None):
        self.filter_type = filter_type
        self.stop_hash = stop_hash
        self.headers = headers

    def deserialize(self, f):
        self.filter_type = struct.unpack("<B", f.read(1))[0]
        self.stop_hash = deser_uint256(f)
        self.headers = deser_uint256_vector(f)

    def serialize(self):
        r = b""
        r += struct.pack("<B", self.filter_type)
        r += ser_uint256(self.stop_hash)
        r += ser_uint256_vector(self.headers)
        return r

    def __repr__(self):
        return "msg_cfcheckpt(filter_type={:#x}, stop_hash={:x})".format(
            self.filter_type, self.stop_hash)
