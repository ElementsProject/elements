/**********************************************************************
 * Copyright (c) 2020-2021 Jonas Nick, Jesse Posner                   *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef SECP256K1_MODULE_ECDSA_ADAPTOR_MAIN_H
#define SECP256K1_MODULE_ECDSA_ADAPTOR_MAIN_H

#include <stdint.h>

#include "../../../include/secp256k1_ecdsa_adaptor.h"
#include "dleq_impl.h"

#include "../../../src/eckey.h"
#include "../../../src/ecmult.h"
#include "../../../src/ecmult_const.h"
#include "../../../src/group.h"
#include "../../../src/hash.h"
#include "../../../src/scalar.h"

/* (R, R', s', dleq_proof) */
static void secp256k1_ecdsa_adaptor_sig_serialize(unsigned char *adaptor_sig162, secp256k1_ge *r, secp256k1_ge *rp, const secp256k1_scalar *sp, const secp256k1_scalar *dleq_proof_e, const secp256k1_scalar *dleq_proof_s) {
    secp256k1_eckey_pubkey_serialize33(r, adaptor_sig162);
    secp256k1_eckey_pubkey_serialize33(rp, &adaptor_sig162[33]);
    secp256k1_scalar_get_b32(&adaptor_sig162[66], sp);
    secp256k1_scalar_get_b32(&adaptor_sig162[98], dleq_proof_e);
    secp256k1_scalar_get_b32(&adaptor_sig162[130], dleq_proof_s);
}

static int secp256k1_ecdsa_adaptor_sig_deserialize(secp256k1_ge *r, secp256k1_scalar *sigr, secp256k1_ge *rp, secp256k1_scalar *sp, secp256k1_scalar *dleq_proof_e, secp256k1_scalar *dleq_proof_s, const unsigned char *adaptor_sig162) {
    /* If r is deserialized, require that a sigr is provided to receive
     * the X-coordinate */
    VERIFY_CHECK((r == NULL) || (r != NULL && sigr != NULL));
    if (r != NULL) {
        if (!secp256k1_eckey_pubkey_parse(r, &adaptor_sig162[0], 33)) {
            return 0;
        }
    }
    if (sigr != NULL) {
        secp256k1_scalar_set_b32(sigr, &adaptor_sig162[1], NULL);
        if (secp256k1_scalar_is_zero(sigr)) {
            return 0;
        }
    }
    if (rp != NULL) {
        if (!secp256k1_eckey_pubkey_parse(rp, &adaptor_sig162[33], 33)) {
            return 0;
        }
    }
    if (sp != NULL) {
        if (!secp256k1_scalar_set_b32_seckey(sp, &adaptor_sig162[66])) {
            return 0;
        }
    }
    if (dleq_proof_e != NULL) {
        secp256k1_scalar_set_b32(dleq_proof_e, &adaptor_sig162[98], NULL);
    }
    if (dleq_proof_s != NULL) {
        int overflow;
        secp256k1_scalar_set_b32(dleq_proof_s, &adaptor_sig162[130], &overflow);
        if (overflow) {
            return 0;
        }
    }
    return 1;
}

/* Initializes SHA256 with fixed midstate. This midstate was computed by applying
 * SHA256 to SHA256("ECDSAadaptor/non")||SHA256("ECDSAadaptor/non"). */
static void secp256k1_nonce_function_ecdsa_adaptor_sha256_tagged(secp256k1_sha256 *sha) {
    static const uint32_t midstate[8] = {
        0x791dae43ul, 0xe52d3b44ul, 0x37f9edeaul, 0x9bfd2ab1ul,
        0xcfb0f44dul, 0xccf1d880ul, 0xd18f2c13ul, 0xa37b9024ul
    };
    secp256k1_sha256_initialize_midstate(sha, 64, midstate);
}

/* Initializes SHA256 with fixed midstate. This midstate was computed by applying
 * SHA256 to SHA256("ECDSAadaptor/aux")||SHA256("ECDSAadaptor/aux"). */
static void secp256k1_nonce_function_ecdsa_adaptor_sha256_tagged_aux(secp256k1_sha256 *sha) {
    static const uint32_t midstate[8] = {
        0xd14c7bd9ul, 0x095d35e6ul, 0xb8490a88ul, 0xfb00ef74ul,
        0x0baa488ful, 0x69366693ul, 0x1c81c5baul, 0xc33b296aul
    };
    secp256k1_sha256_initialize_midstate(sha, 64, midstate);
}

/* algo argument for nonce_function_ecdsa_adaptor to derive the nonce using a tagged hash function. */
static const unsigned char ecdsa_adaptor_algo[] = {'E', 'C', 'D', 'S', 'A', 'a', 'd', 'a', 'p', 't', 'o', 'r', '/', 'n', 'o', 'n'};

/* Modified BIP-340 nonce function */
static int nonce_function_ecdsa_adaptor_impl(const secp256k1_hash_ctx *hash_ctx, unsigned char *nonce32, const unsigned char *msg32, const unsigned char *key32, const unsigned char *pk33, const unsigned char *algo, size_t algolen, void *data) {
    secp256k1_sha256 sha;
    unsigned char masked_key[32];
    int i;

    if (algo == NULL) {
        return 0;
    }

    if (data != NULL) {
        secp256k1_nonce_function_ecdsa_adaptor_sha256_tagged_aux(&sha);
        secp256k1_sha256_write(hash_ctx, &sha, data, 32);
        secp256k1_sha256_finalize(hash_ctx, &sha, masked_key);
        secp256k1_sha256_clear(&sha);
        for (i = 0; i < 32; i++) {
            masked_key[i] ^= key32[i];
        }
    }

    /* Tag the hash with algo which is important to avoid nonce reuse across
     * algorithims. An optimized tagging implementation is used if the default
     * tag is provided. */
    if (algolen == sizeof(ecdsa_adaptor_algo)
            && secp256k1_memcmp_var(algo, ecdsa_adaptor_algo, algolen) == 0) {
        secp256k1_nonce_function_ecdsa_adaptor_sha256_tagged(&sha);
    } else if (algolen == sizeof(dleq_algo)
            && secp256k1_memcmp_var(algo, dleq_algo, algolen) == 0) {
        secp256k1_nonce_function_dleq_sha256_tagged(&sha);
    } else {
        secp256k1_sha256_initialize_tagged(hash_ctx, &sha, algo, algolen);
    }

    /* Hash (masked-)key||pk||msg using the tagged hash as per BIP-340 */
    if (data != NULL) {
        secp256k1_sha256_write(hash_ctx, &sha, masked_key, 32);
    } else {
        secp256k1_sha256_write(hash_ctx, &sha, key32, 32);
    }
    secp256k1_sha256_write(hash_ctx, &sha, pk33, 33);
    secp256k1_sha256_write(hash_ctx, &sha, msg32, 32);
    secp256k1_sha256_finalize(hash_ctx, &sha, nonce32);
    secp256k1_sha256_clear(&sha);
    return 1;
}

static int nonce_function_ecdsa_adaptor(
    unsigned char *nonce32,
    const unsigned char *msg32,
    const unsigned char *key32,
    const unsigned char *pk33,
    const unsigned char *algo,
    size_t algolen,
    void *data)
{
    return nonce_function_ecdsa_adaptor_impl(secp256k1_get_hash_context(secp256k1_context_static),nonce32, msg32, key32, pk33, algo, algolen, data);
}

const secp256k1_nonce_function_hardened_ecdsa_adaptor secp256k1_nonce_function_ecdsa_adaptor = nonce_function_ecdsa_adaptor;

int secp256k1_ecdsa_adaptor_encrypt(const secp256k1_context* ctx, unsigned char *adaptor_sig162, unsigned char *seckey32, const secp256k1_pubkey *enckey, const unsigned char *msg32, secp256k1_nonce_function_hardened_ecdsa_adaptor noncefp, void *ndata) {
    const secp256k1_hash_ctx *hash_ctx;
    secp256k1_scalar k;
    secp256k1_ge r[2];               /* R, R' */
    secp256k1_gej rj[2];             /* R, R' */
    secp256k1_ge enckey_ge;          /* Y */
    secp256k1_scalar dleq_proof_s;
    secp256k1_scalar dleq_proof_e;
    secp256k1_scalar sk;
    secp256k1_scalar msg;
    secp256k1_scalar sp;
    secp256k1_scalar sigr;
    secp256k1_scalar n;
    unsigned char nonce32[32] = { 0 };
    unsigned char buf33[33];
    int ret = 1;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(secp256k1_ecmult_gen_context_is_built(&ctx->ecmult_gen_ctx));
    ARG_CHECK(adaptor_sig162 != NULL);
    ARG_CHECK(seckey32 != NULL);
    ARG_CHECK(enckey != NULL);
    ARG_CHECK(msg32 != NULL);

    secp256k1_scalar_clear(&dleq_proof_e);
    secp256k1_scalar_clear(&dleq_proof_s);

    if (!secp256k1_pubkey_load(ctx, &enckey_ge, enckey)) {
        return 0;
    }

    hash_ctx = secp256k1_get_hash_context(ctx);

    secp256k1_eckey_pubkey_serialize33(&enckey_ge, buf33);
    if (noncefp == NULL || noncefp == secp256k1_nonce_function_ecdsa_adaptor) {
        ret &= nonce_function_ecdsa_adaptor_impl(hash_ctx, nonce32, msg32, seckey32, buf33, ecdsa_adaptor_algo, sizeof(ecdsa_adaptor_algo), ndata);
    } else {
        ret &= !!noncefp(nonce32, msg32, seckey32, buf33, ecdsa_adaptor_algo, sizeof(ecdsa_adaptor_algo), ndata);
    }

    secp256k1_scalar_set_b32(&k, nonce32, NULL);
    ret &= !secp256k1_scalar_is_zero(&k);
    secp256k1_scalar_cmov(&k, &secp256k1_scalar_one, !ret);

    /* R := k*Y */
    secp256k1_ecmult_const(&rj[0], &enckey_ge, &k);
    /* R' := k*G */
    secp256k1_ecmult_gen(&ctx->ecmult_gen_ctx, &rj[1], &k);

    secp256k1_ge_set_all_gej(r, rj, 2);

    /* We declassify the non-secret nonce values to allow using them as branch points. */
    secp256k1_declassify(ctx, &r[0], sizeof(r[0]));
    secp256k1_declassify(ctx, &r[1], sizeof(r[1]));

    /* dleq_proof = DLEQ_prove(k, (R', Y, R)) */
    if (!secp256k1_dleq_prove(ctx, &dleq_proof_s, &dleq_proof_e, &k, &r[1], &enckey_ge, &r[0], noncefp, ndata)) {
        memset(adaptor_sig162, 0, 162);
        secp256k1_memclear_explicit(nonce32, sizeof(nonce32));
        secp256k1_scalar_clear(&k);
        return 0;
    }
    ret &= secp256k1_scalar_set_b32_seckey(&sk, seckey32);
    secp256k1_scalar_cmov(&sk, &secp256k1_scalar_one, !ret);
    secp256k1_scalar_set_b32(&msg, msg32, NULL);
    secp256k1_fe_normalize(&r[0].x);
    secp256k1_fe_get_b32(buf33, &r[0].x);
    secp256k1_scalar_set_b32(&sigr, buf33, NULL);
    ret &= !secp256k1_scalar_is_zero(&sigr);
    /* s' = k⁻¹(m + R.x * x) */
    secp256k1_scalar_mul(&n, &sigr, &sk);
    secp256k1_scalar_add(&n, &n, &msg);
    secp256k1_scalar_inverse(&sp, &k);
    secp256k1_scalar_mul(&sp, &sp, &n);
    ret &= !secp256k1_scalar_is_zero(&sp);

    /* return (R, R', s', dleq_proof) */
    secp256k1_ecdsa_adaptor_sig_serialize(adaptor_sig162, &r[0], &r[1], &sp, &dleq_proof_e, &dleq_proof_s);

    secp256k1_memczero(adaptor_sig162, 162, !ret);
    secp256k1_memclear_explicit(nonce32, sizeof(nonce32));
    secp256k1_scalar_clear(&n);
    secp256k1_scalar_clear(&k);
    secp256k1_scalar_clear(&sk);

    return ret;
}

int secp256k1_ecdsa_adaptor_verify(const secp256k1_context* ctx, const unsigned char *adaptor_sig162, const secp256k1_pubkey *pubkey, const unsigned char *msg32, const secp256k1_pubkey *enckey) {
    secp256k1_scalar dleq_proof_s, dleq_proof_e;
    secp256k1_scalar msg;
    secp256k1_ge pubkey_ge;
    secp256k1_ge r, rp;
    secp256k1_scalar sp;
    secp256k1_scalar sigr;
    secp256k1_ge enckey_ge;
    secp256k1_gej derived_rp;
    secp256k1_scalar sn, u1, u2;
    secp256k1_gej pubkeyj;
    const secp256k1_hash_ctx *hash_ctx = secp256k1_get_hash_context(ctx);

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(adaptor_sig162 != NULL);
    ARG_CHECK(pubkey != NULL);
    ARG_CHECK(msg32 != NULL);
    ARG_CHECK(enckey != NULL);

    if (!secp256k1_ecdsa_adaptor_sig_deserialize(&r, &sigr, &rp, &sp, &dleq_proof_e, &dleq_proof_s, adaptor_sig162)) {
        return 0;
    }
    if (!secp256k1_pubkey_load(ctx, &enckey_ge, enckey)) {
        return 0;
    }
    /* DLEQ_verify((R', Y, R), dleq_proof) */
    if(!secp256k1_dleq_verify(hash_ctx, &dleq_proof_s, &dleq_proof_e, &rp, &enckey_ge, &r)) {
        return 0;
    }
    secp256k1_scalar_set_b32(&msg, msg32, NULL);
    if (!secp256k1_pubkey_load(ctx, &pubkey_ge, pubkey)) {
        return 0;
    }

    /* return R' == s'⁻¹(m * G + R.x * X) */
    secp256k1_scalar_inverse_var(&sn, &sp);
    secp256k1_scalar_mul(&u1, &sn, &msg);
    secp256k1_scalar_mul(&u2, &sn, &sigr);
    secp256k1_gej_set_ge(&pubkeyj, &pubkey_ge);
    secp256k1_ecmult(&derived_rp, &pubkeyj, &u2, &u1);
    if (secp256k1_gej_is_infinity(&derived_rp)) {
        return 0;
    }
    secp256k1_gej_neg(&derived_rp, &derived_rp);
    secp256k1_gej_add_ge_var(&derived_rp, &derived_rp, &rp, NULL);
    return secp256k1_gej_is_infinity(&derived_rp);
}

int secp256k1_ecdsa_adaptor_decrypt(const secp256k1_context* ctx, secp256k1_ecdsa_signature *sig, const unsigned char *deckey32, const unsigned char *adaptor_sig162) {
    secp256k1_scalar deckey;
    secp256k1_scalar sp;
    secp256k1_scalar s;
    secp256k1_scalar sigr;
    int overflow;
    int high;
    int ret = 1;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(sig != NULL);
    ARG_CHECK(deckey32 != NULL);
    ARG_CHECK(adaptor_sig162 != NULL);

    secp256k1_scalar_clear(&sp);
    secp256k1_scalar_set_b32(&deckey, deckey32, &overflow);
    ret &= !overflow;
    ret &= secp256k1_ecdsa_adaptor_sig_deserialize(NULL, &sigr, NULL, &sp, NULL, NULL, adaptor_sig162);
    ret &= !secp256k1_scalar_is_zero(&deckey);
    secp256k1_scalar_inverse(&s, &deckey);
    /* s = s' * y⁻¹ */
    secp256k1_scalar_mul(&s, &s, &sp);
    high = secp256k1_scalar_is_high(&s);
    secp256k1_scalar_cond_negate(&s, high);
    secp256k1_ecdsa_signature_save(sig, &sigr, &s);

    secp256k1_memczero(&sig->data[0], 64, !ret);
    secp256k1_scalar_clear(&deckey);
    secp256k1_scalar_clear(&sp);
    secp256k1_scalar_clear(&s);

    return ret;
}

int secp256k1_ecdsa_adaptor_recover(const secp256k1_context* ctx, unsigned char *deckey32, const secp256k1_ecdsa_signature *sig, const unsigned char *adaptor_sig162, const secp256k1_pubkey *enckey) {
    secp256k1_scalar sp, adaptor_sigr;
    secp256k1_scalar s, r;
    secp256k1_scalar deckey;
    secp256k1_ge enckey_expected_ge;
    secp256k1_ge enckey_ge;
    secp256k1_gej enckey_expected_gej;
    unsigned char enckey33[33];
    unsigned char enckey_expected33[33];
    int ret = 1;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(secp256k1_ecmult_gen_context_is_built(&ctx->ecmult_gen_ctx));
    ARG_CHECK(deckey32 != NULL);
    ARG_CHECK(sig != NULL);
    ARG_CHECK(adaptor_sig162 != NULL);
    ARG_CHECK(enckey != NULL);

    if (!secp256k1_ecdsa_adaptor_sig_deserialize(NULL, &adaptor_sigr, NULL, &sp, NULL, NULL, adaptor_sig162)) {
        return 0;
    }
    secp256k1_ecdsa_signature_load(ctx, &r, &s, sig);
    /* Check that we're not looking at some unrelated signature */
    ret &= secp256k1_scalar_eq(&adaptor_sigr, &r);
    /* y = s⁻¹ * s' */
    ret &= !secp256k1_scalar_is_zero(&s);
    secp256k1_scalar_inverse(&deckey, &s);
    secp256k1_scalar_mul(&deckey, &deckey, &sp);

    /* Deal with ECDSA malleability */
    secp256k1_ecmult_gen(&ctx->ecmult_gen_ctx, &enckey_expected_gej, &deckey);
    secp256k1_ge_set_gej(&enckey_expected_ge, &enckey_expected_gej);
    /* We declassify non-secret enckey_expected_ge to allow using it as a
     * branch point. */
    secp256k1_declassify(ctx, &enckey_expected_ge, sizeof(enckey_expected_ge));
    /* enckey_expected_ge cannot be infinity:
     *
     * Proof:
     *     enckey_expected_ge is infinity <=> deckey = 0
     *     deckey = 0 <=> s^-1 = 0 or sp = 0
     *     case 1: s^-1 = 0 impossible by the definition of multiplicative
     *             inverse and because the scalar_inverse implementation
     *             VERIFY_CHECKs that the inputs are valid scalars.
     *     case 2: sp = 0 impossible because ecdsa_adaptor_sig_deserialize would have already failed
     */
    secp256k1_eckey_pubkey_serialize33(&enckey_expected_ge, enckey_expected33);
    if (!secp256k1_pubkey_load(ctx, &enckey_ge, enckey)) {
        return 0;
    }
    secp256k1_eckey_pubkey_serialize33(&enckey_ge, enckey33);
    if (secp256k1_memcmp_var(&enckey_expected33[1], &enckey33[1], 32) != 0) {
        return 0;
    }
    if (enckey_expected33[0] != enckey33[0]) {
        /* try Y_implied == -Y */
        secp256k1_scalar_negate(&deckey, &deckey);
    }
    secp256k1_scalar_get_b32(deckey32, &deckey);

    secp256k1_scalar_clear(&deckey);
    secp256k1_scalar_clear(&sp);
    secp256k1_scalar_clear(&s);

    return ret;
}

#endif
