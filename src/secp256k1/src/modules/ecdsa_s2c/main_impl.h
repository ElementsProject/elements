/**********************************************************************
 * Copyright (c) 2019-2020 Marko Bencun, Jonas Nick                   *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef SECP256K1_MODULE_ECDSA_S2C_MAIN_H
#define SECP256K1_MODULE_ECDSA_S2C_MAIN_H

#include "../../../include/secp256k1.h"
#include "../../../include/secp256k1_ecdsa_s2c.h"

static void secp256k1_ecdsa_s2c_opening_save(secp256k1_ecdsa_s2c_opening* opening, secp256k1_ge* ge) {
    secp256k1_pubkey_save((secp256k1_pubkey*) opening, ge);
}

static int secp256k1_ecdsa_s2c_opening_load(const secp256k1_context* ctx, secp256k1_ge* ge, const secp256k1_ecdsa_s2c_opening* opening) {
    return secp256k1_pubkey_load(ctx, ge, (const secp256k1_pubkey*) opening);
}

int secp256k1_ecdsa_s2c_opening_parse(const secp256k1_context* ctx, secp256k1_ecdsa_s2c_opening* opening, const unsigned char* input33) {
    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(opening != NULL);
    ARG_CHECK(input33 != NULL);
    return secp256k1_ec_pubkey_parse(ctx, (secp256k1_pubkey*) opening, input33, 33);
}

int secp256k1_ecdsa_s2c_opening_serialize(const secp256k1_context* ctx, unsigned char* output33, const secp256k1_ecdsa_s2c_opening* opening) {
    size_t out_len = 33;
    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(output33 != NULL);
    ARG_CHECK(opening != NULL);
    return secp256k1_ec_pubkey_serialize(ctx, output33, &out_len, (const secp256k1_pubkey*) opening, SECP256K1_EC_COMPRESSED);
}

/* Initializes SHA256 with fixed midstate. This midstate was computed by applying
 * SHA256 to SHA256("s2c/ecdsa/point")||SHA256("s2c/ecdsa/point"). */
static void secp256k1_s2c_ecdsa_point_sha256_tagged(secp256k1_sha256 *sha) {
    static const uint32_t midstate[8] = {
        0xa9b21c7bul, 0x358c3e3eul, 0x0b6863d1ul, 0xc62b2035ul,
        0xb44b40ceul, 0x254a8912ul, 0x0f85d0d4ul, 0x8a5bf91cul
    };
    secp256k1_sha256_initialize_midstate(sha, 64, midstate);
}

/* Initializes SHA256 with fixed midstate. This midstate was computed by applying
 * SHA256 to SHA256("s2c/ecdsa/data")||SHA256("s2c/ecdsa/data"). */
static void secp256k1_s2c_ecdsa_data_sha256_tagged(secp256k1_sha256 *sha) {
    static const uint32_t midstate[8] = {
        0xfeefd675ul, 0x73166c99ul, 0xe2309cb8ul, 0x6d458113ul,
        0x01d3a512ul, 0x00e18112ul, 0x37ee0874ul, 0x421fc55ful
    };
    secp256k1_sha256_initialize_midstate(sha, 64, midstate);
}

int secp256k1_ecdsa_s2c_sign(const secp256k1_context* ctx, secp256k1_ecdsa_signature* signature, secp256k1_ecdsa_s2c_opening* s2c_opening, const unsigned char
 *msg32, const unsigned char *seckey, const unsigned char* s2c_data32) {
    const secp256k1_hash_ctx *hash_ctx = secp256k1_get_hash_context(ctx);
    secp256k1_scalar r, s;
    int ret;
    unsigned char ndata[32];
    secp256k1_sha256 s2c_sha;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(secp256k1_ecmult_gen_context_is_built(&ctx->ecmult_gen_ctx));
    ARG_CHECK(msg32 != NULL);
    ARG_CHECK(signature != NULL);
    ARG_CHECK(seckey != NULL);
    ARG_CHECK(s2c_data32 != NULL);

    /* Provide `s2c_data32` to the nonce function as additional data to
     * derive the nonce. It is first hashed because it should be possible
     * to derive nonces even if only a SHA256 commitment to the data is
     * known.  This is important in the ECDSA anti-exfil protocol. */
    secp256k1_s2c_ecdsa_data_sha256_tagged(&s2c_sha);
    secp256k1_sha256_write(hash_ctx, &s2c_sha, s2c_data32, 32);
    secp256k1_sha256_finalize(hash_ctx, &s2c_sha, ndata);
    secp256k1_sha256_clear(&s2c_sha);

    secp256k1_s2c_ecdsa_point_sha256_tagged(&s2c_sha);
    ret = secp256k1_ecdsa_sign_inner(ctx, &r, &s, NULL, &s2c_sha, s2c_opening, s2c_data32, msg32, seckey, NULL, ndata);
    secp256k1_scalar_cmov(&r, &secp256k1_scalar_zero, !ret);
    secp256k1_scalar_cmov(&s, &secp256k1_scalar_zero, !ret);
    secp256k1_ecdsa_signature_save(signature, &r, &s);
    return ret;
}

int secp256k1_ecdsa_s2c_verify_commit(const secp256k1_context* ctx, const secp256k1_ecdsa_signature* sig, const unsigned char* data32, const secp256k1_ecdsa_s2c_opening* opening) {
    const secp256k1_hash_ctx *hash_ctx = secp256k1_get_hash_context(ctx);
    secp256k1_ge commitment_ge;
    secp256k1_ge original_pubnonce_ge;
    unsigned char x_bytes[32];
    secp256k1_scalar sigr, sigs, x_scalar;
    secp256k1_sha256 s2c_sha;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(sig != NULL);
    ARG_CHECK(data32 != NULL);
    ARG_CHECK(opening != NULL);

    if (!secp256k1_ecdsa_s2c_opening_load(ctx, &original_pubnonce_ge, opening)) {
        return 0;
    }
    secp256k1_s2c_ecdsa_point_sha256_tagged(&s2c_sha);
    if (!secp256k1_ec_commit(hash_ctx, &commitment_ge, &original_pubnonce_ge, &s2c_sha, data32, 32)) {
        return 0;
    }

    /* Check that sig_r == commitment_x (mod n)
     * sig_r is the x coordinate of R represented by a scalar.
     * commitment_x is the x coordinate of the commitment (field element).
     *
     * Note that we are only checking the x-coordinate -- this is because the y-coordinate
     * is not part of the ECDSA signature (and therefore not part of the commitment!)
     */
    secp256k1_ecdsa_signature_load(ctx, &sigr, &sigs, sig);

    secp256k1_fe_normalize(&commitment_ge.x);
    secp256k1_fe_get_b32(x_bytes, &commitment_ge.x);
    /* Do not check overflow; overflowing a scalar does not affect whether
     * or not the R value is a cryptographic commitment, only whether it
     * is a valid R value for an ECDSA signature. If users care about that
     * they should use `ecdsa_verify` or `anti_exfil_host_verify`. In other
     * words, this check would be (at best) unnecessary, and (at worst)
     * insufficient. */
    secp256k1_scalar_set_b32(&x_scalar, x_bytes, NULL);
    return secp256k1_scalar_eq(&sigr, &x_scalar);
}

/*** anti-exfil ***/
int secp256k1_ecdsa_anti_exfil_host_commit(const secp256k1_context* ctx, unsigned char* rand_commitment32, const unsigned char* rand32) {
    secp256k1_sha256 sha;
    const secp256k1_hash_ctx *hash_ctx = secp256k1_get_hash_context(ctx);

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(rand_commitment32 != NULL);
    ARG_CHECK(rand32 != NULL);

    secp256k1_s2c_ecdsa_data_sha256_tagged(&sha);
    secp256k1_sha256_write(hash_ctx, &sha, rand32, 32);
    secp256k1_sha256_finalize(hash_ctx, &sha, rand_commitment32);
    secp256k1_sha256_clear(&sha);
    return 1;
}

int secp256k1_ecdsa_anti_exfil_signer_commit(const secp256k1_context* ctx, secp256k1_ecdsa_s2c_opening* opening, const unsigned char* msg32, const unsigned char* seckey32, const unsigned char* rand_commitment32) {
    unsigned char nonce32[32];
    secp256k1_scalar k;
    secp256k1_gej rj;
    secp256k1_ge r;
    unsigned int count = 0;
    int is_nonce_valid = 0;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(secp256k1_ecmult_gen_context_is_built(&ctx->ecmult_gen_ctx));
    ARG_CHECK(opening != NULL);
    ARG_CHECK(msg32 != NULL);
    ARG_CHECK(seckey32 != NULL);
    ARG_CHECK(rand_commitment32 != NULL);

    memset(nonce32, 0, 32);
    while (!is_nonce_valid) {
        /* cast to void* removes const qualifier, but secp256k1_nonce_function_default does not modify it */
        if (!secp256k1_nonce_function_default(nonce32, msg32, seckey32, NULL, (void*)rand_commitment32, count)) {
            secp256k1_callback_call(&ctx->error_callback, "(cryptographically unreachable) generated bad nonce");
        }
        is_nonce_valid = secp256k1_scalar_set_b32_seckey(&k, nonce32);
        /* The nonce is still secret here, but it being invalid is is less likely than 1:2^255. */
        secp256k1_declassify(ctx, &is_nonce_valid, sizeof(is_nonce_valid));
        count++;
    }

    secp256k1_ecmult_gen(&ctx->ecmult_gen_ctx, &rj, &k);
    secp256k1_ge_set_gej(&r, &rj);
    secp256k1_ecdsa_s2c_opening_save(opening, &r);
    secp256k1_memclear_explicit(nonce32, 32);
    secp256k1_scalar_clear(&k);
    return 1;
}

int secp256k1_anti_exfil_sign(const secp256k1_context* ctx, secp256k1_ecdsa_signature* sig, const unsigned char* msg32, const unsigned char* seckey, const unsigned char* host_data32) {
    return secp256k1_ecdsa_s2c_sign(ctx, sig, NULL, msg32, seckey, host_data32);
}

int secp256k1_anti_exfil_host_verify(const secp256k1_context* ctx, const secp256k1_ecdsa_signature *sig, const unsigned char *msg32, const secp256k1_pubkey *pubkey, const unsigned char *host_data32, const secp256k1_ecdsa_s2c_opening *opening) {
    return secp256k1_ecdsa_s2c_verify_commit(ctx, sig, host_data32, opening) &&
        secp256k1_ecdsa_verify(ctx, sig, msg32, pubkey);
}

#endif /* SECP256K1_ECDSA_S2C_MAIN_H */
