// Copyright (c) 2009-2014 The Bitcoin developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "pubkey.h"

#include <secp256k1.h>
#include <secp256k1_rangeproof.h>
#include <secp256k1_schnorr.h>

secp256k1_context_t* secp256k1_bitcoin_verify_context = NULL;
static secp256k1_context_t*& secp256k1_context = secp256k1_bitcoin_verify_context;

bool CPubKey::Verify(const uint256 &hash, const std::vector<unsigned char>& vchSig) const {
    if (!IsValid())
        return false;
    if (vchSig.size() != 64)
        return false;
    secp256k1_pubkey_t pubkey;
    if (!secp256k1_ec_pubkey_parse(secp256k1_context, &pubkey, begin(), size()))
        return false;
    if (secp256k1_schnorr_verify(secp256k1_context, (const unsigned char*)&hash, &vchSig[0], &pubkey) != 1)
        return false;
    return true;
}

bool CPubKey::RecoverCompact(const uint256 &hash, const std::vector<unsigned char>& vchSig) {
    if (vchSig.size() != 65)
        return false;
    int recid = (vchSig[0] - 27) & 3;
    bool fComp = ((vchSig[0] - 27) & 4) != 0;
    secp256k1_pubkey_t pubkey;
    secp256k1_ecdsa_signature_t sig;
    if (!secp256k1_ecdsa_signature_parse_compact(secp256k1_context, &sig, &vchSig[1], recid)) {
        return false;
    }
    if (!secp256k1_ecdsa_recover(secp256k1_context, hash.begin(), &sig, &pubkey)) {
        return false;
    }
    unsigned char pub[65];
    int publen = 0;
    secp256k1_ec_pubkey_serialize(secp256k1_context, pub, &publen, &pubkey, fComp);
    Set(pub, pub + publen);
    return true;
}

bool CPubKey::IsFullyValid() const {
    if (!IsValid())
        return false;
    secp256k1_pubkey_t pubkey;
    if (!secp256k1_ec_pubkey_parse(secp256k1_context, &pubkey, begin(), size()))
        return false;
    return true;
}

bool CPubKey::Decompress() {
    if (!IsValid())
        return false;
    secp256k1_pubkey_t pubkey;
    if (!secp256k1_ec_pubkey_parse(secp256k1_context, &pubkey, &(*this)[0], size())) {
        return false;
    }
    unsigned char pub[65];
    int publen = 0;
    secp256k1_ec_pubkey_serialize(secp256k1_context, pub, &publen, &pubkey, false);
    Set(pub, pub + publen);
    return true;
}

bool CPubKey::Derive(CPubKey& pubkeyChild, unsigned char ccChild[32], unsigned int nChild, const unsigned char cc[32]) const {
    assert(IsValid());
    assert((nChild >> 31) == 0);
    assert(begin() + 33 == end());
    unsigned char out[64];
    BIP32Hash(cc, nChild, *begin(), begin()+1, out);
    memcpy(ccChild, out+32, 32);
    secp256k1_pubkey_t pubkey;
    if (!secp256k1_ec_pubkey_parse(secp256k1_context, &pubkey, &(*this)[0], size())) {
        return false;
    }
    if (!secp256k1_ec_pubkey_tweak_add(secp256k1_context, &pubkey, out)) {
        return false;
    }
    unsigned char pub[33];
    int publen = 0;
    secp256k1_ec_pubkey_serialize(secp256k1_context, pub, &publen, &pubkey, 1);
    pubkeyChild.Set(pub, pub + publen);
    return true;
}

void CExtPubKey::Encode(unsigned char code[74]) const {
    code[0] = nDepth;
    memcpy(code+1, vchFingerprint, 4);
    code[5] = (nChild >> 24) & 0xFF; code[6] = (nChild >> 16) & 0xFF;
    code[7] = (nChild >>  8) & 0xFF; code[8] = (nChild >>  0) & 0xFF;
    memcpy(code+9, vchChainCode, 32);
    assert(pubkey.size() == 33);
    memcpy(code+41, pubkey.begin(), 33);
}

void CExtPubKey::Decode(const unsigned char code[74]) {
    nDepth = code[0];
    memcpy(vchFingerprint, code+1, 4);
    nChild = (code[5] << 24) | (code[6] << 16) | (code[7] << 8) | code[8];
    memcpy(vchChainCode, code+9, 32);
    pubkey.Set(code+41, code+74);
}

bool CExtPubKey::Derive(CExtPubKey &out, unsigned int nChild) const {
    out.nDepth = nDepth + 1;
    CKeyID id = pubkey.GetID();
    memcpy(&out.vchFingerprint[0], &id, 4);
    out.nChild = nChild;
    return pubkey.Derive(out.pubkey, out.vchChainCode, nChild, vchChainCode);
}

void ECC_Verify_Start() {
    assert(secp256k1_context == NULL);

    secp256k1_context_t *ctx = secp256k1_context_create(SECP256K1_CONTEXT_VERIFY);
    assert(ctx != NULL);
    secp256k1_pedersen_context_initialize(ctx);
    secp256k1_rangeproof_context_initialize(ctx);

    secp256k1_context = ctx;
}

void ECC_Verify_Stop() {
    secp256k1_context_t *ctx = secp256k1_context;
    secp256k1_context = NULL;

    if (ctx) {
        secp256k1_context_destroy(ctx);
    }
}
