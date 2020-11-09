#!/usr/bin/env python3
# Copyright (c) 2017 Pieter Wuille
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Reference implementation for Blech32 and segwit addresses."""


CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"

def blech32_polymod(values):
    """Internal function that computes the blech32 checksum."""
    generator = [0x7d52fba40bd886, 0x5e8dbf1a03950c, 0x1c3a3c74072a18, 0x385d72fa0e5139, 0x7093e5a608865b] # new generators, 7 bytes
    chk = 1
    for value in values:
        top = chk >> 55 # 25->55
        chk = ((chk & 0x7fffffffffffff) << 5) ^ value # 0x1ffffff->0x7fffffffffffff
        for i in range(5):
            chk ^= generator[i] if ((top >> i) & 1) else 0
    return chk


def blech32_hrp_expand(hrp):
    """Expand the HRP into values for checksum computation."""
    return [ord(x) >> 5 for x in hrp] + [0] + [ord(x) & 31 for x in hrp]


def blech32_verify_checksum(hrp, data):
    """Verify a checksum given HRP and converted data characters."""
    return blech32_polymod(blech32_hrp_expand(hrp) + data) == 1


def blech32_create_checksum(hrp, data):
    """Compute the checksum values given HRP and data."""
    values = blech32_hrp_expand(hrp) + data
    polymod = blech32_polymod(values + [0]*12) ^ 1 # 6->12
    return [(polymod >> 5 * (11 - i)) & 31 for i in range(12)]
#                            ^ 5                          ^ 6

def blech32_encode(hrp, data):
    """Compute a blech32 string given HRP and data values."""
    combined = data + blech32_create_checksum(hrp, data)
    return hrp + '1' + ''.join([CHARSET[d] for d in combined])


def blech32_decode(bech):
    """Validate a blech32 string, and determine HRP and data."""
    if ((any(ord(x) < 33 or ord(x) > 126 for x in bech)) or
            (bech.lower() != bech and bech.upper() != bech)):
        return (None, None)
    bech = bech.lower()
    pos = bech.rfind('1')
    if pos < 1 or pos + 13 > len(bech) or len(bech) > 1000: # 7->13 90->1000
        return (None, None)
    if not all(x in CHARSET for x in bech[pos+1:]):
        return (None, None)
    hrp = bech[:pos]
    data = [CHARSET.find(x) for x in bech[pos+1:]]
    if not blech32_verify_checksum(hrp, data):
        return (None, None)
    return (hrp, data[:-12]) # 6->12


def convertbits(data, frombits, tobits, pad=True):
    """General power-of-2 base conversion."""
    acc = 0
    bits = 0
    ret = []
    maxv = (1 << tobits) - 1
    max_acc = (1 << (frombits + tobits - 1)) - 1
    for value in data:
        if value < 0 or (value >> frombits):
            return None
        acc = ((acc << frombits) | value) & max_acc
        bits += frombits
        while bits >= tobits:
            bits -= tobits
            ret.append((acc >> bits) & maxv)
    if pad:
        if bits:
            ret.append((acc << (tobits - bits)) & maxv)
    elif bits >= frombits or ((acc << (tobits - bits)) & maxv):
        return None
    return ret


def decode(hrp, addr):
    """Decode a segwit confidential address.
    Its payload is longer than the payload for unconfidential address
    by 33 bytes (the length of blinding pubkey)"""

    hrpgot, data = blech32_decode(addr)
    if hrpgot != hrp:
        return (None, None)
    decoded = convertbits(data[1:], 5, 8, False)
    if decoded is None or len(decoded) < 2 or len(decoded) > 40+33:
        return (None, None)
    if data[0] > 16:
        return (None, None)
    if data[0] == 0 and len(decoded) != 20+33 and len(decoded) != 32+33:
        return (None, None)
    return (data[0], decoded)


def encode(hrp, witver, witprog):
    """Encode a segwit address."""
    ret = blech32_encode(hrp, [witver] + convertbits(witprog, 8, 5))
    if decode(hrp, ret) == (None, None):
        return None
    return ret
