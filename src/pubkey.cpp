// Copyright (c) 2009-2014 The Bitcoin developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "pubkey.h"

#include <secp256k1.h>

secp256k1_context_t* secp256k1_bitcoin_verify_context = NULL;
static secp256k1_context_t*& secp256k1_context = secp256k1_bitcoin_verify_context;

bool CPubKey::Verify(const uint256 &hash, const std::vector<unsigned char>& vchSig) const {
    if (!IsValid())
        return false;
    if (vchSig.size() != 64)
        return false;
    if (secp256k1_schnorr_verify(secp256k1_context, (const unsigned char*)&hash, &vchSig[0], begin(), size()) != 1)
        return false;
    return true;
}

bool CPubKey::RecoverCompact(const uint256 &hash, const std::vector<unsigned char>& vchSig) {
    if (vchSig.size() != 65)
        return false;
    int recid = (vchSig[0] - 27) & 3;
    bool fComp = ((vchSig[0] - 27) & 4) != 0;
    int pubkeylen = 65;
    if (!secp256k1_ecdsa_recover_compact(secp256k1_context, (const unsigned char*)&hash, &vchSig[1], (unsigned char*)begin(), &pubkeylen, fComp, recid))
        return false;
    assert((int)size() == pubkeylen);
    return true;
}

bool CPubKey::IsFullyValid() const {
    if (!IsValid())
        return false;
    if (!secp256k1_ec_pubkey_verify(secp256k1_context, begin(), size()))
        return false;
    return true;
}

bool CPubKey::Decompress() {
    if (!IsValid())
        return false;
    int clen = size();
    int ret = secp256k1_ec_pubkey_decompress(secp256k1_context, (unsigned char*)begin(), &clen);
    assert(ret);
    assert(clen == (int)size());
    return true;
}

bool CPubKey::Derive(CPubKey& pubkeyChild, unsigned char ccChild[32], unsigned int nChild, const unsigned char cc[32]) const {
    assert(IsValid());
    assert((nChild >> 31) == 0);
    assert(begin() + 33 == end());
    unsigned char out[64];
    BIP32Hash(cc, nChild, *begin(), begin()+1, out);
    memcpy(ccChild, out+32, 32);
    pubkeyChild = *this;
    bool ret = secp256k1_ec_pubkey_tweak_add(secp256k1_context, (unsigned char*)pubkeyChild.begin(), pubkeyChild.size(), out);
    return ret;
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

int PubKeyTree::Walk(std::vector<unsigned char> *pmerkleroot, size_t pos, std::vector<std::vector<unsigned char> >* pvMerklePath)
{
    std::vector<std::vector<unsigned char> > vMerkleLevel;

    assert(pubkeys.size() >= (1 << 1) && pubkeys.size() <= (1 << 16));
    assert(pos < pubkeys.size());

    for (size_t i = 0; i < pubkeys.size(); i++) {
        std::vector<unsigned char> node;
        node.resize(32);
        CSHA256().Write(&pubkeys[i][0], pubkeys[i].size()).Finalize(&node[0]);
        vMerkleLevel.push_back(node);
    }

    int levels = 0;
    while (vMerkleLevel.size() > 1) {
       std::vector<std::vector<unsigned char> > vNewMerkleLevel;
       if (vMerkleLevel.size() % 2 == 1) {
           vMerkleLevel.push_back(std::vector<unsigned char>(1, 1));
       }
       for (size_t  p = 0; p < vMerkleLevel.size(); p += 2) {
           std::vector<unsigned char> node;
           node.resize(32);
           CSHA256().Write(&vMerkleLevel[p][0], vMerkleLevel[p].size()).Write(&vMerkleLevel[p + 1][0], vMerkleLevel[p + 1].size()).Finalize(&node[0]);
           vNewMerkleLevel.push_back(node);
           if (pvMerklePath && (p == pos || p + 1 == pos)) {
               pvMerklePath->push_back(vMerkleLevel[p + (p == pos)]);
           }
       }
       pos >>= 1;
       levels++;
       vNewMerkleLevel.swap(vMerkleLevel);
    }

    if (pmerkleroot) {
        pmerkleroot->swap(vMerkleLevel[0]);
    }

    return levels;
}


void ECC_Verify_Start() {
    assert(secp256k1_context == NULL);

    secp256k1_context_t *ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY | SECP256K1_CONTEXT_COMMIT | SECP256K1_CONTEXT_RANGEPROOF);
    assert(ctx != NULL);

    secp256k1_context = ctx;
}

void ECC_Verify_Stop() {
    secp256k1_context_t *ctx = secp256k1_context;
    secp256k1_context = NULL;

    if (ctx) {
        secp256k1_context_destroy(ctx);
    }
}
