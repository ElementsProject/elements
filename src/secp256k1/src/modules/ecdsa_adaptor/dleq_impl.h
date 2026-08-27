#ifndef SECP256K1_DLEQ_IMPL_H
#define SECP256K1_DLEQ_IMPL_H

#include <stdint.h>

#include "../../../include/secp256k1_ecdsa_adaptor.h"

#include "../../../src/eckey.h"
#include "../../../src/ecmult_const.h"
#include "../../../src/group.h"
#include "../../../src/hash.h"
#include "../../../src/scalar.h"

/* Initializes SHA256 with fixed midstate. This midstate was computed by applying
 * SHA256 to SHA256("DLEQ")||SHA256("DLEQ"). */
static void secp256k1_nonce_function_dleq_sha256_tagged(secp256k1_sha256 *sha) {
    static const uint32_t midstate[8] = {
        0x8cc4beacul, 0x2e011f3ful, 0x355c75fbul, 0x3ba6a2c5ul,
        0xe96f3aeful, 0x180530fdul, 0x94582499ul, 0x577fd564ul
    };
    secp256k1_sha256_initialize_midstate(sha, 64, midstate);
}

/* algo argument for nonce_function_ecdsa_adaptor to derive the nonce using a tagged hash function. */
static const unsigned char dleq_algo[] = {'D','L','E','Q'};

static int nonce_function_ecdsa_adaptor_impl(const secp256k1_hash_ctx *hash_ctx, unsigned char *nonce32, const unsigned char *msg32, const unsigned char *key32, const unsigned char *pk33, const unsigned char *algo, size_t algolen, void *data);

static void secp256k1_dleq_hash_point(const secp256k1_hash_ctx *hash_ctx, secp256k1_sha256 *sha, secp256k1_ge *p) {
    unsigned char buf[33];

    secp256k1_eckey_pubkey_serialize33(p, buf);
    secp256k1_sha256_write(hash_ctx, sha, buf, 33);
}

static int secp256k1_dleq_nonce(const secp256k1_hash_ctx *hash_ctx, secp256k1_scalar *k, const unsigned char *sk32, const unsigned char *gen2_33, const unsigned char *p1_33, const unsigned char *p2_33, secp256k1_nonce_function_hardened_ecdsa_adaptor noncefp, void *ndata) {
    secp256k1_sha256 sha;
    unsigned char buf[32];
    unsigned char nonce[32];

    secp256k1_sha256_initialize(&sha);
    secp256k1_sha256_write(hash_ctx, &sha, p1_33, 33);
    secp256k1_sha256_write(hash_ctx, &sha, p2_33, 33);
    secp256k1_sha256_finalize(hash_ctx, &sha, buf);
    secp256k1_sha256_clear(&sha);

    if (noncefp == NULL || noncefp == secp256k1_nonce_function_ecdsa_adaptor) {
        if (!nonce_function_ecdsa_adaptor_impl(hash_ctx, nonce, buf, sk32, gen2_33, dleq_algo, sizeof(dleq_algo), ndata)) {
            return 0;
        }
    } else if (!noncefp(nonce, buf, sk32, gen2_33, dleq_algo, sizeof(dleq_algo), ndata)) {
        return 0;
    }
    secp256k1_scalar_set_b32(k, nonce, NULL);
    secp256k1_memclear_explicit(nonce, sizeof(nonce));
    if (secp256k1_scalar_is_zero(k)) {
        return 0;
    }

    return 1;
}

/* Generates a challenge as defined in the DLC Specification at
 * https://github.com/discreetlogcontracts/dlcspecs */
static void secp256k1_dleq_challenge(const secp256k1_hash_ctx *hash_ctx, secp256k1_scalar *e, secp256k1_ge *gen2, secp256k1_ge *r1, secp256k1_ge *r2, secp256k1_ge *p1, secp256k1_ge *p2) {
    unsigned char buf[32];
    secp256k1_sha256 sha;

    secp256k1_nonce_function_dleq_sha256_tagged(&sha);
    secp256k1_dleq_hash_point(hash_ctx, &sha, p1);
    secp256k1_dleq_hash_point(hash_ctx, &sha, gen2);
    secp256k1_dleq_hash_point(hash_ctx, &sha, p2);
    secp256k1_dleq_hash_point(hash_ctx, &sha, r1);
    secp256k1_dleq_hash_point(hash_ctx, &sha, r2);
    secp256k1_sha256_finalize(hash_ctx, &sha, buf);
    secp256k1_sha256_clear(&sha);

    secp256k1_scalar_set_b32(e, buf, NULL);
}

/* p[0] = x*G, p[1] = x*Y */
static void secp256k1_dleq_pair(const secp256k1_ecmult_gen_context *ecmult_gen_ctx, secp256k1_ge *p, const secp256k1_scalar *sk, const secp256k1_ge *gen2) {
    secp256k1_gej pj[2];

    secp256k1_ecmult_gen_gej(ecmult_gen_ctx, &pj[0], sk);
    secp256k1_ecmult_const(&pj[1], gen2, sk);
    secp256k1_ge_set_all_gej(p, pj, 2);

    secp256k1_gej_clear(&pj[0]);
    secp256k1_gej_clear(&pj[1]);
}

/* Generates a proof that the discrete logarithm of P1 to the secp256k1 base G is the
 * same as the discrete logarithm of P2 to the base Y */
static int secp256k1_dleq_prove(const secp256k1_context* ctx, secp256k1_scalar *s, secp256k1_scalar *e, const secp256k1_scalar *sk, secp256k1_ge *p1, secp256k1_ge *gen2, secp256k1_ge *p2, secp256k1_nonce_function_hardened_ecdsa_adaptor noncefp, void *ndata) {
    /* Note: r[2] and k are local to the DLEQ proof, and they differ from the
     * values with the same identifiers in main_impl.h. */
    const secp256k1_hash_ctx *hash_ctx = secp256k1_get_hash_context(ctx);
    secp256k1_ge r[2];
    secp256k1_scalar k = { 0 };
    unsigned char sk32[32];
    unsigned char gen2_33[33];
    unsigned char p1_33[33];
    unsigned char p2_33[33];
    int ret;

    secp256k1_eckey_pubkey_serialize33(gen2, gen2_33);
    secp256k1_eckey_pubkey_serialize33(p1, p1_33);
    secp256k1_eckey_pubkey_serialize33(p2, p2_33);

    secp256k1_scalar_get_b32(sk32, sk);

    ret = secp256k1_dleq_nonce(hash_ctx, &k, sk32, gen2_33, p1_33, p2_33, noncefp, ndata);
    secp256k1_declassify(ctx, &ret, sizeof(ret));
    if (!ret) {
        secp256k1_memclear_explicit(sk32, sizeof(sk32));
        return 0;
    }
    /* R1 = k*G, R2 = k*Y */
    secp256k1_dleq_pair(&ctx->ecmult_gen_ctx, r, &k, gen2);
    /* We declassify the non-secret values r[0] and r[1] to allow using them as
     * branch points. */
    secp256k1_declassify(ctx, &r[0], sizeof(r[0]));
    secp256k1_declassify(ctx, &r[1], sizeof(r[1]));

    /* e = tagged hash(p1, gen2, p2, r[0], r[1]) */
    /* s = k + e * sk */
    secp256k1_dleq_challenge(hash_ctx, e, gen2, &r[0], &r[1], p1, p2);
    secp256k1_scalar_mul(s, e, sk);
    secp256k1_scalar_add(s, s, &k);

    secp256k1_scalar_clear(&k);
    secp256k1_memclear_explicit(sk32, sizeof(sk32));
    return 1;
}

static int secp256k1_dleq_verify(const secp256k1_hash_ctx *hash_ctx, const secp256k1_scalar *s, const secp256k1_scalar *e, secp256k1_ge *p1, secp256k1_ge *gen2, secp256k1_ge *p2) {
    secp256k1_scalar e_neg;
    secp256k1_scalar e_expected;
    secp256k1_gej gen2j;
    secp256k1_gej p1j, p2j;
    secp256k1_gej rj[2];
    secp256k1_ge r[2];
    secp256k1_gej tmpj;

    secp256k1_gej_set_ge(&p1j, p1);
    secp256k1_gej_set_ge(&p2j, p2);

    secp256k1_scalar_negate(&e_neg, e);
    /* R1 = s*G  - e*P1 */
    secp256k1_ecmult(&rj[0], &p1j, &e_neg, s);
    /* R2 = s*gen2 - e*P2 */
    secp256k1_ecmult(&tmpj, &p2j, &e_neg, &secp256k1_scalar_zero);
    secp256k1_gej_set_ge(&gen2j, gen2);
    secp256k1_ecmult(&rj[1], &gen2j, s, &secp256k1_scalar_zero);
    secp256k1_gej_add_var(&rj[1], &rj[1], &tmpj, NULL);

    if (secp256k1_gej_is_infinity(&rj[0]) || secp256k1_gej_is_infinity(&rj[1])) {
        return 0;
    }

    secp256k1_ge_set_all_gej_var(r, rj, 2);

    secp256k1_dleq_challenge(hash_ctx, &e_expected, gen2, &r[0], &r[1], p1, p2);

    secp256k1_scalar_add(&e_expected, &e_expected, &e_neg);
    return secp256k1_scalar_is_zero(&e_expected);
}

#endif
