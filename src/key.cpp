// Copyright (c) 2009-2014 The Bitcoin developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "key.h"

#include "crypto/common.h"
#include "crypto/hmac_sha512.h"
#include "crypto/rfc6979_hmac_sha256.h"
#include "eccryptoverify.h"
#include "pubkey.h"
#include "random.h"

#include <secp256k1.h>
#include <secp256k1_ecdh.h>
#include <secp256k1_schnorr.h>

static secp256k1_context_t* secp256k1_context = NULL;

bool CKey::Check(const unsigned char *vch) {
    return eccrypto::Check(vch);
}

void CKey::MakeNewKey(bool fCompressedIn) {
    do {
        GetRandBytes(vch, sizeof(vch));
    } while (!Check(vch));
    fValid = true;
    fCompressed = fCompressedIn;
}

bool CKey::SetPrivKey(const CPrivKey &privkey, bool fCompressedIn) {
    if (!secp256k1_ec_privkey_import(secp256k1_context, (unsigned char*)begin(), &privkey[0], privkey.size()))
        return false;
    fCompressed = fCompressedIn;
    fValid = true;
    return true;
}

CPrivKey CKey::GetPrivKey() const {
    assert(fValid);
    CPrivKey privkey;
    int privkeylen, ret;
    privkey.resize(279);
    privkeylen = 279;
    ret = secp256k1_ec_privkey_export(secp256k1_context, begin(), (unsigned char*)&privkey[0], &privkeylen, fCompressed);
    assert(ret);
    privkey.resize(privkeylen);
    return privkey;
}

CPubKey CKey::GetPubKey() const {
    assert(fValid);
    CPubKey result;
    int clen = 65;
    secp256k1_pubkey_t pubkey;
    int ret = secp256k1_ec_pubkey_create(secp256k1_context, &pubkey, begin());
    secp256k1_ec_pubkey_serialize(secp256k1_context, (unsigned char*)result.begin(), &clen, &pubkey, fCompressed);
    assert((int)result.size() == clen);
    assert(ret);
    assert(result.IsValid());
    return result;
}

uint256 CKey::ECDH(const CPubKey& pubkey) const {
    assert(fValid);
    uint256 result;
    secp256k1_pubkey_t pkey;
    assert(secp256k1_ec_pubkey_parse(secp256k1_context, &pkey, pubkey.begin(), pubkey.size()));
    assert(secp256k1_ecdh(secp256k1_context, result.begin(), &pkey, begin()));
    return result;
}

bool CKey::Sign(const uint256 &hash, std::vector<unsigned char>& vchSig, uint32_t test_case) const {
    if (!fValid)
        return false;
    vchSig.resize(72);
    int nSigLen = 64;
    unsigned char extra_entropy[32] = {0};
    WriteLE32(extra_entropy, test_case);
    int ret = secp256k1_schnorr_sign(secp256k1_context, hash.begin(), (unsigned char*)&vchSig[0], begin(), secp256k1_nonce_function_rfc6979, test_case ? extra_entropy : NULL);
    assert(ret);
    vchSig.resize(nSigLen);
    return true;
}

bool CKey::VerifyPubKey(const CPubKey& pubkey) const {
    if (pubkey.IsCompressed() != fCompressed) {
        return false;
    }
    unsigned char rnd[8];
    std::string str = "Bitcoin key verification\n";
    GetRandBytes(rnd, sizeof(rnd));
    uint256 hash;
    CHash256().Write((unsigned char*)str.data(), str.size()).Write(rnd, sizeof(rnd)).Finalize((unsigned char*)&hash);
    std::vector<unsigned char> vchSig;
    Sign(hash, vchSig);
    return pubkey.Verify(hash, vchSig);
}

bool CKey::SignCompact(const uint256 &hash, std::vector<unsigned char>& vchSig) const {
    if (!fValid)
        return false;
    vchSig.resize(65);
    int rec = -1;
    secp256k1_ecdsa_signature_t sig;
    assert(secp256k1_ecdsa_sign(secp256k1_context, hash.begin(), &sig, begin(), secp256k1_nonce_function_rfc6979, NULL));
    assert(secp256k1_ecdsa_signature_serialize_compact(secp256k1_context, &vchSig[1], &rec, &sig));
    vchSig[0] = 27 + rec + (fCompressed ? 4 : 0);
    return true;
}

bool CKey::Load(CPrivKey &privkey, CPubKey &vchPubKey, bool fSkipCheck=false) {
    if (!secp256k1_ec_privkey_import(secp256k1_context, (unsigned char*)begin(), &privkey[0], privkey.size()))
        return false;
    fCompressed = vchPubKey.IsCompressed();
    fValid = true;

    if (fSkipCheck)
        return true;

    return VerifyPubKey(vchPubKey);
}

bool CKey::Derive(CKey& keyChild, unsigned char ccChild[32], unsigned int nChild, const unsigned char cc[32]) const {
    assert(IsValid());
    assert(IsCompressed());
    unsigned char out[64];
    LockObject(out);
    if ((nChild >> 31) == 0) {
        CPubKey pubkey = GetPubKey();
        assert(pubkey.begin() + 33 == pubkey.end());
        BIP32Hash(cc, nChild, *pubkey.begin(), pubkey.begin()+1, out);
    } else {
        assert(begin() + 32 == end());
        BIP32Hash(cc, nChild, 0, begin(), out);
    }
    memcpy(ccChild, out+32, 32);
    memcpy((unsigned char*)keyChild.begin(), begin(), 32);
    bool ret = secp256k1_ec_privkey_tweak_add(secp256k1_context, (unsigned char*)keyChild.begin(), out);
    UnlockObject(out);
    keyChild.fCompressed = true;
    keyChild.fValid = ret;
    return ret;
}

bool CKey::PartialSigningNonce(const uint256& hash, std::vector<unsigned char>& pubnonceout) const {
    if (!fValid)
        return false;
    secp256k1_pubkey_t pubnonce;
    unsigned char secnonce[32];
    LockObject(secnonce);
    int ret = secp256k1_schnorr_generate_nonce_pair(secp256k1_context, hash.begin(), begin(), secp256k1_nonce_function_rfc6979, NULL, &pubnonce, secnonce);
    UnlockObject(secnonce);
    if (!ret)
        return false;
    pubnonceout.resize(33 + 64);
    int publen = 33;
    secp256k1_ec_pubkey_serialize(secp256k1_context, &pubnonceout[0], &publen, &pubnonce, true);
    // Sign the hash + pubnonce with a full signature, to prove possession of the corresponding private key.
    uint256 hash2;
    CSHA256().Write(hash.begin(), 32).Write(&pubnonceout[0], 33).Finalize(hash2.begin());
    return secp256k1_schnorr_sign(secp256k1_context, hash2.begin(), &pubnonceout[33], begin(), secp256k1_nonce_function_rfc6979, NULL);
}

static bool CombinePubNonces(const uint256& hash, const std::vector<std::vector<unsigned char> >& pubnonces, const std::vector<CPubKey>& pubkeys, secp256k1_pubkey_t& out) {
    bool ret = pubnonces.size() > 0;
    ret = ret && (pubnonces.size() == pubkeys.size());
    std::vector<secp256k1_pubkey_t> parsed_pubnonces;
    std::vector<const secp256k1_pubkey_t*> parsed_pubnonce_pointers;
    parsed_pubnonces.reserve(pubnonces.size());
    parsed_pubnonce_pointers.reserve(pubnonces.size());
    std::vector<CPubKey>::const_iterator pit = pubkeys.begin();
    for (std::vector<std::vector<unsigned char> >::const_iterator it = pubnonces.begin(); it != pubnonces.end(); ++it, ++pit) {
        secp256k1_pubkey_t other_pubnonce;
        ret = ret && (it->size() == 33 + 64);
        ret = ret && secp256k1_ec_pubkey_parse(secp256k1_context, &other_pubnonce, &(*it)[0], 33);
        // Verify the signature on the pubnonce.
        uint256 hash2;
        secp256k1_pubkey_t pubkey;
        CSHA256().Write(hash.begin(), 32).Write(&(*it)[0], 33).Finalize(hash2.begin());
        ret = ret && secp256k1_ec_pubkey_parse(secp256k1_context, &pubkey, &(*pit)[0], pit->size());
        ret = ret && secp256k1_schnorr_verify(secp256k1_context, hash2.begin(), &(*it)[33], &pubkey);
        if (ret) {
            parsed_pubnonces.push_back(other_pubnonce);
            parsed_pubnonce_pointers.push_back(&parsed_pubnonces.back());
        }
    }
    return (ret && secp256k1_ec_pubkey_combine(secp256k1_context, &out, parsed_pubnonces.size(), &parsed_pubnonce_pointers[0]));
}

bool CKey::PartialSign(const uint256& hash, const std::vector<std::vector<unsigned char> >& other_pubnonces_in, const std::vector<CPubKey>& other_pubkeys_in, const std::vector<unsigned char>& my_pubnonce_in, std::vector<unsigned char>& vchPartialSig) const {
    if (!fValid)
        return false;
    secp256k1_pubkey_t pubnonce, my_pubnonce, other_pubnonces;
    unsigned char secnonce[32];
    LockObject(secnonce);
    int ret = my_pubnonce_in.size() == 33 + 64 && secp256k1_ec_pubkey_parse(secp256k1_context, &my_pubnonce, &my_pubnonce_in[0], 33);
    ret = ret && secp256k1_schnorr_generate_nonce_pair(secp256k1_context, hash.begin(), begin(), secp256k1_nonce_function_rfc6979, NULL, &pubnonce, secnonce);
    ret = ret && memcmp(&pubnonce, &my_pubnonce, sizeof(pubnonce)) == 0;
    ret = ret && CombinePubNonces(hash, other_pubnonces_in, other_pubkeys_in, other_pubnonces);
    if (ret) {
        vchPartialSig.resize(64);
        ret = secp256k1_schnorr_partial_sign(secp256k1_context, hash.begin(), &vchPartialSig[0], begin(), secnonce, &other_pubnonces);
    }
    UnlockObject(secnonce);
    return ret;
}

bool CombinePartialSignatures(const std::vector<std::vector<unsigned char> >& input, std::vector<unsigned char>& output) {
    std::vector<const unsigned char*> sig_pointers;
    sig_pointers.reserve(input.size());
    for (std::vector<std::vector<unsigned char> >::const_iterator it = input.begin(); it != input.end(); ++it) {
        if (it->size() != 64) return false;
        sig_pointers.push_back(&((*it)[0]));
    }
    output.resize(64);
    bool ret = !!secp256k1_schnorr_partial_combine(secp256k1_context, &output[0], sig_pointers.size(), &sig_pointers[0]);
    return ret;
}

bool CExtKey::Derive(CExtKey &out, unsigned int nChild) const {
    out.nDepth = nDepth + 1;
    CKeyID id = key.GetPubKey().GetID();
    memcpy(&out.vchFingerprint[0], &id, 4);
    out.nChild = nChild;
    return key.Derive(out.key, out.vchChainCode, nChild, vchChainCode);
}

void CExtKey::SetMaster(const unsigned char *seed, unsigned int nSeedLen) {
    static const unsigned char hashkey[] = {'B','i','t','c','o','i','n',' ','s','e','e','d'};
    unsigned char out[64];
    LockObject(out);
    CHMAC_SHA512(hashkey, sizeof(hashkey)).Write(seed, nSeedLen).Finalize(out);
    key.Set(&out[0], &out[32], true);
    memcpy(vchChainCode, &out[32], 32);
    UnlockObject(out);
    nDepth = 0;
    nChild = 0;
    memset(vchFingerprint, 0, sizeof(vchFingerprint));
}

CExtPubKey CExtKey::Neuter() const {
    CExtPubKey ret;
    ret.nDepth = nDepth;
    memcpy(&ret.vchFingerprint[0], &vchFingerprint[0], 4);
    ret.nChild = nChild;
    ret.pubkey = key.GetPubKey();
    memcpy(&ret.vchChainCode[0], &vchChainCode[0], 32);
    return ret;
}

void CExtKey::Encode(unsigned char code[74]) const {
    code[0] = nDepth;
    memcpy(code+1, vchFingerprint, 4);
    code[5] = (nChild >> 24) & 0xFF; code[6] = (nChild >> 16) & 0xFF;
    code[7] = (nChild >>  8) & 0xFF; code[8] = (nChild >>  0) & 0xFF;
    memcpy(code+9, vchChainCode, 32);
    code[41] = 0;
    assert(key.size() == 32);
    memcpy(code+42, key.begin(), 32);
}

void CExtKey::Decode(const unsigned char code[74]) {
    nDepth = code[0];
    memcpy(vchFingerprint, code+1, 4);
    nChild = (code[5] << 24) | (code[6] << 16) | (code[7] << 8) | code[8];
    memcpy(vchChainCode, code+9, 32);
    key.Set(code+42, code+74, true);
}

bool ECC_InitSanityCheck() {
    CKey key;
    key.MakeNewKey(true);
    CPubKey pubkey = key.GetPubKey();
    return key.VerifyPubKey(pubkey);
}


void ECC_Start() {
    assert(secp256k1_context == NULL);

    secp256k1_context_t *ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);
    assert(ctx != NULL);

    {
        // Pass in a random blinding seed to the secp256k1 context.
        unsigned char seed[32];
        LockObject(seed);
        GetRandBytes(seed, 32);
        bool ret = secp256k1_context_randomize(ctx, seed);
        assert(ret);
        UnlockObject(seed);
    }

    secp256k1_context = ctx;
}

void ECC_Stop() {
    secp256k1_context_t *ctx = secp256k1_context;
    secp256k1_context = NULL;

    if (ctx) {
        secp256k1_context_destroy(ctx);
    }
}
