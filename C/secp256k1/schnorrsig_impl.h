/**********************************************************************
 * Copyright (c) 2018 Andrew Poelstra                                 *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef SECP256K1_SCHNORRSIG_IMPL_H
#define SECP256K1_SCHNORRSIG_IMPL_H

#include "secp256k1.h"
#include "schnorrsig.h"
#include "../sha256.h"

#if 0
static void secp256k1_schnorrsig_serialize(unsigned char *out64, const secp256k1_schnorrsig* sig) {
    ARG_CHECK(out64 != NULL);
    ARG_CHECK(sig != NULL);
    memcpy(out64, sig->data, 64);
}
#endif

static void secp256k1_schnorrsig_parse(secp256k1_schnorrsig* sig, const unsigned char *in64) {
    ARG_CHECK(sig != NULL);
    ARG_CHECK(in64 != NULL);
    memcpy(sig->data, in64, 64);
}

/* Initializes SHA256 with fixed midstate. This midstate was computed by applying
 * SHA256 to SHA256("BIPSchnorr")||SHA256("BIPSchnorr"). */
static sha256_context secp256k1_schnorrsig_sha256_tagged(sha256_midstate *sha) {
    sha->s[0] = 0x048d9a59ul;
    sha->s[1] = 0xfe39fb05ul;
    sha->s[2] = 0x28479648ul;
    sha->s[3] = 0xe4a660f9ul;
    sha->s[4] = 0x814b9e66ul;
    sha->s[5] = 0x0469e801ul;
    sha->s[6] = 0x83909280ul;
    sha->s[7] = 0xb329e454ul;
    return (sha256_context){ .output = sha->s, .counter = 64 };
}

/* Helper function for verification and batch verification.
 * Computes R = sG - eP. */
static int secp256k1_schnorrsig_real_verify(const secp256k1_ecmult_context* ecmult_ctx, secp256k1_gej *rj, const secp256k1_scalar *s, const secp256k1_scalar *e, const secp256k1_xonly_pubkey *pk) {
    secp256k1_scalar nege;
    secp256k1_ge pkp;
    secp256k1_gej pkj;

    secp256k1_scalar_negate(&nege, e);

    if (!secp256k1_pubkey_load(&pkp, (const secp256k1_pubkey *) pk)) {
        return 0;
    }
    secp256k1_gej_set_ge(&pkj, &pkp);

    /* rj =  s*G + (-e)*pkj */
    secp256k1_ecmult(ecmult_ctx, rj, &pkj, &nege, s);
    return 1;
}

static int secp256k1_schnorrsig_verify(const secp256k1_ecmult_context* ecmult_ctx, const secp256k1_schnorrsig *sig, const unsigned char *msg32, const secp256k1_xonly_pubkey *pk) {
    secp256k1_scalar s;
    secp256k1_scalar e;
    secp256k1_gej rj;
    secp256k1_fe rx;
    sha256_midstate sha_buf;
    unsigned char buf[32];
    int overflow;

    VERIFY_CHECK(ecmult_ctx != NULL);
    ARG_CHECK(secp256k1_ecmult_context_is_built(ecmult_ctx));
    ARG_CHECK(sig != NULL);
    ARG_CHECK(msg32 != NULL);
    ARG_CHECK(pk != NULL);

    if (!secp256k1_fe_set_b32(&rx, &sig->data[0])) {
        return 0;
    }

    secp256k1_scalar_set_b32(&s, &sig->data[32], &overflow);
    if (overflow) {
        return 0;
    }

    {
      sha256_context sha_ctx = secp256k1_schnorrsig_sha256_tagged(&sha_buf);
      sha256_uchars(&sha_ctx, &sig->data[0], 32);
      secp256k1_xonly_pubkey_serialize(buf, pk);
      sha256_uchars(&sha_ctx, buf, sizeof(buf));
      sha256_uchars(&sha_ctx, msg32, 32);
      sha256_finalize(&sha_ctx);
    }

    /* Note: the sha256_fromMidstate call could be eliminated by implementng a secp256k1_scalar_set function that operates on arrays of uint32_t */
    sha256_fromMidstate(buf, sha_buf.s);
    secp256k1_scalar_set_b32(&e, buf, NULL);

    if (!secp256k1_schnorrsig_real_verify(ecmult_ctx, &rj, &s, &e, pk)
        || !secp256k1_gej_has_quad_y_var(&rj) /* fails if rj is infinity */
        || !secp256k1_gej_eq_x_var(&rx, &rj)) {
        return 0;
    }

    return 1;
}

#endif
