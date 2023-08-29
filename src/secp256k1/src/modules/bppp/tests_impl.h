/**********************************************************************
 * Copyright (c) 2020 Andrew Poelstra                                 *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef SECP256K1_MODULE_BPPP_TEST_H
#define SECP256K1_MODULE_BPPP_TEST_H

#include <stdint.h>

#include "../../../include/secp256k1_bppp.h"
#include "bppp_norm_product_impl.h"
#include "bppp_util.h"
#include "bppp_transcript_impl.h"
#include "test_vectors/verify.h"
#include "test_vectors/prove.h"

static void test_bppp_generators_api(void) {
    secp256k1_bppp_generators *gens;
    secp256k1_bppp_generators *gens_orig;
    unsigned char gens_ser[330];
    size_t len = sizeof(gens_ser);

    int32_t ecount = 0;

    /* The BP generator API requires no precomp */
    secp256k1_context_set_error_callback(CTX, counting_illegal_callback_fn, &ecount);
    secp256k1_context_set_illegal_callback(CTX, counting_illegal_callback_fn, &ecount);

    /* Create */
    gens = secp256k1_bppp_generators_create(CTX, 10);
    CHECK(gens != NULL && ecount == 0);
    gens_orig = gens; /* Preserve for round-trip test */

    /* Serialize */
    ecount = 0;
    CHECK(!secp256k1_bppp_generators_serialize(CTX, NULL, gens_ser, &len));
    CHECK(ecount == 1);
    CHECK(!secp256k1_bppp_generators_serialize(CTX, gens, NULL, &len));
    CHECK(ecount == 2);
    CHECK(!secp256k1_bppp_generators_serialize(CTX, gens, gens_ser, NULL));
    CHECK(ecount == 3);
    len = 0;
    CHECK(!secp256k1_bppp_generators_serialize(CTX, gens, gens_ser, &len));
    CHECK(ecount == 4);
    len = sizeof(gens_ser) - 1;
    CHECK(!secp256k1_bppp_generators_serialize(CTX, gens, gens_ser, &len));
    CHECK(ecount == 5);
    len = sizeof(gens_ser);
    {
        /* Output buffer can be greater than minimum needed */
        unsigned char gens_ser_tmp[331];
        size_t len_tmp = sizeof(gens_ser_tmp);
        CHECK(secp256k1_bppp_generators_serialize(CTX, gens, gens_ser_tmp, &len_tmp));
        CHECK(len_tmp == sizeof(gens_ser_tmp) - 1);
        CHECK(ecount == 5);
    }

    /* Parse */
    CHECK(secp256k1_bppp_generators_serialize(CTX, gens, gens_ser, &len));
    ecount = 0;
    gens = secp256k1_bppp_generators_parse(CTX, NULL, sizeof(gens_ser));
    CHECK(gens == NULL && ecount == 1);
    /* Not a multiple of 33 */
    gens = secp256k1_bppp_generators_parse(CTX, gens_ser, sizeof(gens_ser) - 1);
    CHECK(gens == NULL && ecount == 1);
    gens = secp256k1_bppp_generators_parse(CTX, gens_ser, sizeof(gens_ser));
    CHECK(gens != NULL && ecount == 1);
    /* Not valid generators */
    memset(gens_ser, 1, sizeof(gens_ser));
    CHECK(secp256k1_bppp_generators_parse(CTX, gens_ser, sizeof(gens_ser)) == NULL);
    CHECK(ecount == 1);

    /* Check that round-trip succeeded */
    CHECK(gens->n == gens_orig->n);
    for (len = 0; len < gens->n; len++) {
        ge_equals_ge(&gens->gens[len], &gens_orig->gens[len]);
    }

    /* Destroy (we allow destroying a NULL context, it's just a noop. like free().) */
    ecount = 0;
    secp256k1_bppp_generators_destroy(CTX, NULL);
    secp256k1_bppp_generators_destroy(CTX, gens);
    secp256k1_bppp_generators_destroy(CTX, gens_orig);
    CHECK(ecount == 0);

    secp256k1_context_set_error_callback(CTX, NULL, NULL);
    secp256k1_context_set_illegal_callback(CTX, NULL, NULL);
}

static void test_bppp_generators_fixed(void) {
    secp256k1_bppp_generators *gens = secp256k1_bppp_generators_create(CTX, 3);
    unsigned char gens_ser[330];
    const unsigned char fixed_first_3[99] = {
        0x0b,
        0xb3, 0x4d, 0x5f, 0xa6, 0xb8, 0xf3, 0xd1, 0x38,
        0x49, 0xce, 0x51, 0x91, 0xb7, 0xf6, 0x76, 0x18,
        0xfe, 0x5b, 0xd1, 0x2a, 0x88, 0xb2, 0x0e, 0xac,
        0x33, 0x89, 0x45, 0x66, 0x7f, 0xb3, 0x30, 0x56,
        0x0a,
        0x62, 0x86, 0x15, 0x16, 0x92, 0x42, 0x10, 0x9e,
        0x9e, 0x64, 0xd4, 0xcb, 0x28, 0x81, 0x60, 0x9c,
        0x24, 0xb9, 0x89, 0x51, 0x2a, 0xd9, 0x01, 0xae,
        0xff, 0x75, 0x64, 0x9c, 0x37, 0x5d, 0xbd, 0x79,
        0x0a,
        0xed, 0xe0, 0x6e, 0x07, 0x5e, 0x79, 0xd0, 0xf7,
        0x7b, 0x03, 0x3e, 0xb9, 0xa9, 0x21, 0xa4, 0x5b,
        0x99, 0xf3, 0x9b, 0xee, 0xfe, 0xa0, 0x37, 0xa2,
        0x1f, 0xe9, 0xd7, 0x4f, 0x95, 0x8b, 0x10, 0xe2,
    };
    size_t len;

    len = 99;
    CHECK(secp256k1_bppp_generators_serialize(CTX, gens, gens_ser, &len));
    CHECK(memcmp(gens_ser, fixed_first_3, sizeof(fixed_first_3)) == 0);

    len = sizeof(gens_ser);
    CHECK(secp256k1_bppp_generators_serialize(CTX, gens, gens_ser, &len));
    CHECK(memcmp(gens_ser, fixed_first_3, sizeof(fixed_first_3)) == 0);

    secp256k1_bppp_generators_destroy(CTX, gens);
}

static void test_bppp_tagged_hash(void) {
    unsigned char tag_data[29] = "Bulletproofs_pp/v0/commitment";
    secp256k1_sha256 sha;
    secp256k1_sha256 sha_cached;
    unsigned char output[32];
    unsigned char output_cached[32];
    secp256k1_scalar s;

    secp256k1_sha256_initialize_tagged(&sha, tag_data, sizeof(tag_data));
    secp256k1_bppp_sha256_tagged_commitment_init(&sha_cached);
    secp256k1_sha256_finalize(&sha, output);
    secp256k1_sha256_finalize(&sha_cached, output_cached);
    CHECK(secp256k1_memcmp_var(output, output_cached, 32) == 0);

    {
        unsigned char expected[32] = { 0x21, 0x2F, 0xB6, 0x4F, 0x9D, 0x8C, 0x3B, 0xC5,
                                       0xF6, 0x91, 0x15, 0xEE, 0x74, 0xF5, 0x12, 0x67,
                                       0x8A, 0x41, 0xC6, 0x85, 0x1A, 0x79, 0x14, 0xFC,
                                       0x48, 0x15, 0xC7, 0x2D, 0xF8, 0x63, 0x8F, 0x1B };
        secp256k1_bppp_sha256_tagged_commitment_init(&sha);
        secp256k1_bppp_challenge_scalar(&s, &sha, 0);
        secp256k1_scalar_get_b32(output, &s);
        CHECK(memcmp(output, expected, sizeof(output)) == 0);
    }

    {
        unsigned char tmp[3] = {0, 1, 2};
        unsigned char expected[32] = { 0x8D, 0xAA, 0xB7, 0x7E, 0x3C, 0x6A, 0x9E, 0xEC,
                                       0x72, 0x7E, 0x3E, 0xB7, 0x10, 0x03, 0xF0, 0xE9,
                                       0x69, 0x4D, 0xAA, 0x96, 0xCE, 0x98, 0xBB, 0x39,
                                       0x1C, 0x2F, 0x7C, 0x2E, 0x1C, 0x17, 0x78, 0x6D };
        secp256k1_sha256_write(&sha, tmp, sizeof(tmp));
        secp256k1_bppp_challenge_scalar(&s, &sha, 0);
        secp256k1_scalar_get_b32(output, &s);
        CHECK(memcmp(output, expected, sizeof(output)) == 0);
    }
}

static void test_log_exp(void) {
    CHECK(secp256k1_is_power_of_two(0) == 0);
    CHECK(secp256k1_is_power_of_two(1) == 1);
    CHECK(secp256k1_is_power_of_two(2) == 1);
    CHECK(secp256k1_is_power_of_two(64) == 1);
    CHECK(secp256k1_is_power_of_two(63) == 0);
    CHECK(secp256k1_is_power_of_two(256) == 1);

    CHECK(secp256k1_bppp_log2(1) == 0);
    CHECK(secp256k1_bppp_log2(2) == 1);
    CHECK(secp256k1_bppp_log2(255) == 7);
    CHECK(secp256k1_bppp_log2(256) == 8);
    CHECK(secp256k1_bppp_log2(257) == 8);
}

static void test_norm_util_helpers(void) {
    secp256k1_scalar a_vec[4], b_vec[4], rho_pows[4], res, res2, mu, rho;
    int i;
    /* a = {1, 2, 3, 4} b = {5, 6, 7, 8}, mu = 4, rho = 2 */
    for (i = 0; i < 4; i++) {
        secp256k1_scalar_set_int(&a_vec[i], i + 1);
        secp256k1_scalar_set_int(&b_vec[i], i + 5);
    }
    secp256k1_scalar_set_int(&mu, 4);
    secp256k1_scalar_set_int(&rho, 2);
    secp256k1_scalar_inner_product(&res, a_vec, 0, b_vec, 0, 1, 4);
    secp256k1_scalar_set_int(&res2, 70);
    CHECK(secp256k1_scalar_eq(&res2, &res) == 1);

    secp256k1_scalar_inner_product(&res, a_vec, 0, b_vec, 1, 2, 2);
    secp256k1_scalar_set_int(&res2, 30);
    CHECK(secp256k1_scalar_eq(&res2, &res) == 1);

    secp256k1_scalar_inner_product(&res, a_vec, 1, b_vec, 0, 2, 2);
    secp256k1_scalar_set_int(&res2, 38);
    CHECK(secp256k1_scalar_eq(&res2, &res) == 1);

    secp256k1_scalar_inner_product(&res, a_vec, 1, b_vec, 1, 2, 2);
    secp256k1_scalar_set_int(&res2, 44);
    CHECK(secp256k1_scalar_eq(&res2, &res) == 1);

    secp256k1_weighted_scalar_inner_product(&res, a_vec, 0, a_vec, 0, 1, 4, &mu);
    secp256k1_scalar_set_int(&res2, 4740); /*i*i*4^(i+1) */
    CHECK(secp256k1_scalar_eq(&res2, &res) == 1);

    secp256k1_bppp_powers_of_rho(rho_pows, &rho, 4);
    secp256k1_scalar_set_int(&res, 2); CHECK(secp256k1_scalar_eq(&res, &rho_pows[0]));
    secp256k1_scalar_set_int(&res, 4); CHECK(secp256k1_scalar_eq(&res, &rho_pows[1]));
    secp256k1_scalar_set_int(&res, 16); CHECK(secp256k1_scalar_eq(&res, &rho_pows[2]));
    secp256k1_scalar_set_int(&res, 256); CHECK(secp256k1_scalar_eq(&res, &rho_pows[3]));
}


static void test_serialize_two_points_roundtrip(secp256k1_ge *X, secp256k1_ge *R) {
    secp256k1_ge X_tmp, R_tmp;
    unsigned char buf[65];
    secp256k1_bppp_serialize_points(buf, X, R);
    CHECK(secp256k1_bppp_parse_one_of_points(&X_tmp, buf, 0));
    CHECK(secp256k1_bppp_parse_one_of_points(&R_tmp, buf, 1));
    ge_equals_ge(X, &X_tmp);
    ge_equals_ge(R, &R_tmp);
}

static void test_serialize_two_points(void) {
    secp256k1_ge X, R;
    int i;

    for (i = 0; i < COUNT; i++) {
        random_group_element_test(&X);
        random_group_element_test(&R);
        test_serialize_two_points_roundtrip(&X, &R);
    }

    for (i = 0; i < COUNT; i++) {
        random_group_element_test(&X);
        secp256k1_ge_set_infinity(&R);
        test_serialize_two_points_roundtrip(&X, &R);
    }

    for (i = 0; i < COUNT; i++) {
        secp256k1_ge_set_infinity(&X);
        random_group_element_test(&R);
        test_serialize_two_points_roundtrip(&X, &R);
    }

    secp256k1_ge_set_infinity(&X);
    secp256k1_ge_set_infinity(&R);
    test_serialize_two_points_roundtrip(&X, &R);

    /* Test invalid sign byte */
    {
        secp256k1_ge X_tmp, R_tmp;
        unsigned char buf[65];
        random_group_element_test(&X);
        random_group_element_test(&R);
        secp256k1_bppp_serialize_points(buf, &X, &R);

        /* buf is valid if 0 <= buf[0] < 4. */
        buf[0] = (unsigned char)secp256k1_testrandi64(4, 255);
        CHECK(!secp256k1_bppp_parse_one_of_points(&X_tmp, buf, 0));
        CHECK(!secp256k1_bppp_parse_one_of_points(&R_tmp, buf, 0));
    }
    /* Check that sign bit is 0 for point at infinity */
    for (i = 0; i < COUNT; i++) {
        secp256k1_ge X_tmp, R_tmp;
        unsigned char buf[65];
        int expect;
        random_group_element_test(&X);
        random_group_element_test(&R);
        secp256k1_bppp_serialize_points(buf, &X, &R);
        memset(&buf[1], 0, 32);
        if ((buf[0] & 2) == 0) {
            expect = 1;
        } else {
            expect = 0;
        }
        CHECK(secp256k1_bppp_parse_one_of_points(&X_tmp, buf, 0) == expect);
        CHECK(secp256k1_bppp_parse_one_of_points(&R_tmp, buf, 1));
        memset(&buf[33], 0, 32);
        if ((buf[0] & 1) == 0) {
            expect = 1;
        } else {
            expect = 0;
        }
        CHECK(secp256k1_bppp_parse_one_of_points(&R_tmp, buf, 1) == expect);
    }
}

static void secp256k1_norm_arg_commit_initial_data(
    secp256k1_sha256* transcript,
    const secp256k1_scalar* rho,
    const secp256k1_bppp_generators* gens_vec,
    size_t g_len, /* Same as n_vec_len, g_len + c_vec_len = gens->n */
    const secp256k1_scalar* c_vec,
    size_t c_vec_len,
    const secp256k1_ge* commit
) {
    /* Commit to the initial public values */
    unsigned char ser_commit[33], ser_scalar[32], ser_le64[8];
    size_t i;
    secp256k1_ge comm = *commit;
    secp256k1_bppp_sha256_tagged_commitment_init(transcript);
    secp256k1_fe_normalize(&comm.x);
    secp256k1_fe_normalize(&comm.y);
    CHECK(secp256k1_ge_is_infinity(&comm) == 0);
    CHECK(secp256k1_bppp_serialize_pt(&ser_commit[0], &comm));
    secp256k1_sha256_write(transcript, ser_commit, 33);
    secp256k1_scalar_get_b32(ser_scalar, rho);
    secp256k1_sha256_write(transcript, ser_scalar, 32);
    secp256k1_bppp_le64(ser_le64, g_len);
    secp256k1_sha256_write(transcript, ser_le64, 8);
    secp256k1_bppp_le64(ser_le64, gens_vec->n);
    secp256k1_sha256_write(transcript, ser_le64, 8);
    for (i = 0; i < gens_vec->n; i++) {
        secp256k1_fe_normalize(&gens_vec->gens[i].x);
        secp256k1_fe_normalize(&gens_vec->gens[i].y);
        CHECK(secp256k1_bppp_serialize_pt(&ser_commit[0], &gens_vec->gens[i]));
        secp256k1_sha256_write(transcript, ser_commit, 33);
    }
    secp256k1_bppp_le64(ser_le64, c_vec_len);
    secp256k1_sha256_write(transcript, ser_le64, 8);
    for (i = 0; i < c_vec_len; i++) {
        secp256k1_scalar_get_b32(ser_scalar, &c_vec[i]);
        secp256k1_sha256_write(transcript, ser_scalar, 32);
    }
}

static void copy_vectors_into_scratch(secp256k1_scratch_space* scratch,
                                      secp256k1_scalar **ns,
                                      secp256k1_scalar **ls,
                                      secp256k1_scalar **cs,
                                      secp256k1_ge **gs,
                                      const secp256k1_scalar *n_vec,
                                      const secp256k1_scalar *l_vec,
                                      const secp256k1_scalar *c_vec,
                                      const secp256k1_ge *gens_vec,
                                      size_t g_len,
                                      size_t h_len) {
    *ns = (secp256k1_scalar*)secp256k1_scratch_alloc(&CTX->error_callback, scratch, g_len * sizeof(secp256k1_scalar));
    *ls = (secp256k1_scalar*)secp256k1_scratch_alloc(&CTX->error_callback, scratch, h_len * sizeof(secp256k1_scalar));
    *cs = (secp256k1_scalar*)secp256k1_scratch_alloc(&CTX->error_callback, scratch, h_len * sizeof(secp256k1_scalar));
    *gs = (secp256k1_ge*)secp256k1_scratch_alloc(&CTX->error_callback, scratch, (g_len + h_len) * sizeof(secp256k1_ge));
    CHECK(ns != NULL && ls != NULL && cs != NULL && gs != NULL);
    memcpy(*ns, n_vec, g_len * sizeof(secp256k1_scalar));
    memcpy(*ls, l_vec, h_len * sizeof(secp256k1_scalar));
    memcpy(*cs, c_vec, h_len * sizeof(secp256k1_scalar));
    memcpy(*gs, gens_vec, (g_len + h_len) * sizeof(secp256k1_ge));
}

/* Same as secp256k1_bppp_rangeproof_norm_product_prove but does not modify the inputs */
static int secp256k1_bppp_rangeproof_norm_product_prove_const(
    secp256k1_scratch_space* scratch,
    unsigned char* proof,
    size_t *proof_len,
    secp256k1_sha256 *transcript,
    const secp256k1_scalar* rho,
    const secp256k1_ge* g_vec,
    size_t g_vec_len,
    const secp256k1_scalar* n_vec,
    size_t n_vec_len,
    const secp256k1_scalar* l_vec,
    size_t l_vec_len,
    const secp256k1_scalar* c_vec,
    size_t c_vec_len
) {
    secp256k1_scalar *ns, *ls, *cs;
    secp256k1_ge *gs;
    size_t scratch_checkpoint;
    size_t g_len = n_vec_len, h_len = l_vec_len;
    int res;

    scratch_checkpoint = secp256k1_scratch_checkpoint(&CTX->error_callback, scratch);
    copy_vectors_into_scratch(scratch, &ns, &ls, &cs, &gs, n_vec, l_vec, c_vec, g_vec, g_len, h_len);
    res = secp256k1_bppp_rangeproof_norm_product_prove(
        CTX,
        scratch,
        proof,
        proof_len,
        transcript, /* Transcript hash of the parent protocol */
        rho,
        gs,
        g_vec_len,
        ns,
        n_vec_len,
        ls,
        l_vec_len,
        cs,
        c_vec_len
    );
    secp256k1_scratch_apply_checkpoint(&CTX->error_callback, scratch, scratch_checkpoint);
    return res;
}

/* A complete norm argument. In contrast to secp256k1_bppp_rangeproof_norm_product_prove, this is meant
   to be used as a standalone norm argument.
   This is a simple wrapper around secp256k1_bppp_rangeproof_norm_product_prove
   that also commits to the initial public values used in the protocol. In this case, these public
   values are commitment.
*/
static int secp256k1_norm_arg_prove(
    secp256k1_scratch_space* scratch,
    unsigned char* proof,
    size_t *proof_len,
    const secp256k1_scalar* rho,
    const secp256k1_bppp_generators* gens_vec,
    const secp256k1_scalar* n_vec,
    size_t n_vec_len,
    const secp256k1_scalar* l_vec,
    size_t l_vec_len,
    const secp256k1_scalar* c_vec,
    size_t c_vec_len,
    const secp256k1_ge* commit
) {
    secp256k1_sha256 transcript;
    secp256k1_norm_arg_commit_initial_data(&transcript, rho, gens_vec, n_vec_len, c_vec, c_vec_len, commit);

    return secp256k1_bppp_rangeproof_norm_product_prove_const(scratch, proof, proof_len, &transcript, rho, gens_vec->gens, gens_vec->n, n_vec, n_vec_len, l_vec, l_vec_len, c_vec, c_vec_len);
}

/* Verify the proof */
static int secp256k1_norm_arg_verify(
    secp256k1_scratch_space* scratch,
    const unsigned char* proof,
    size_t proof_len,
    const secp256k1_scalar* rho,
    const secp256k1_bppp_generators* gens_vec,
    size_t g_len,
    const secp256k1_scalar* c_vec,
    size_t c_vec_len,
    const secp256k1_ge* commit
) {
    secp256k1_ge comm = *commit;
    int res;
    secp256k1_sha256 transcript;

    /* Commit to the initial public values */
    secp256k1_norm_arg_commit_initial_data(&transcript, rho, gens_vec, g_len, c_vec, c_vec_len, &comm);

    res = secp256k1_bppp_rangeproof_norm_product_verify(
        CTX,
        scratch,
        proof,
        proof_len,
        &transcript,
        rho,
        gens_vec,
        g_len,
        c_vec,
        c_vec_len,
        commit
    );
    return res;
}

/* Verify |c| = 0 */
static void norm_arg_verify_zero_len(void) {
    secp256k1_scalar n_vec[64], l_vec[64], c_vec[64];
    secp256k1_scalar rho, mu;
    secp256k1_ge commit;
    secp256k1_scratch *scratch = secp256k1_scratch_space_create(CTX, 1000*10); /* shouldn't need much */
    unsigned char proof[1000];
    unsigned int n_vec_len = 1;
    unsigned int c_vec_len = 1;
    secp256k1_bppp_generators *gs = secp256k1_bppp_generators_create(CTX, n_vec_len + c_vec_len);
    size_t plen = sizeof(proof);

    random_scalar_order(&rho);
    secp256k1_scalar_sqr(&mu, &rho);

    random_scalar_order(&n_vec[0]);
    random_scalar_order(&c_vec[0]);
    random_scalar_order(&l_vec[0]);
    CHECK(secp256k1_bppp_commit(CTX, scratch, &commit, gs, n_vec, n_vec_len, l_vec, c_vec_len, c_vec, c_vec_len, &mu));
    CHECK(secp256k1_norm_arg_prove(scratch, proof, &plen, &rho, gs, n_vec, n_vec_len, l_vec, c_vec_len, c_vec, c_vec_len, &commit));
    CHECK(secp256k1_norm_arg_verify(scratch, proof, plen, &rho, gs, n_vec_len, c_vec, c_vec_len, &commit));
    CHECK(!secp256k1_norm_arg_verify(scratch, proof, plen, &rho, gs, n_vec_len, c_vec, 0, &commit));

    secp256k1_bppp_generators_destroy(CTX, gs);

    secp256k1_scratch_space_destroy(CTX, scratch);
}

static void norm_arg_test(unsigned int n, unsigned int m) {
    secp256k1_scalar n_vec[64], l_vec[64], c_vec[64];
    secp256k1_scalar rho, mu;
    secp256k1_ge commit;
    size_t i, plen;
    int res;
    secp256k1_bppp_generators *gs = secp256k1_bppp_generators_create(CTX, n + m);
    secp256k1_scratch *scratch = secp256k1_scratch_space_create(CTX, 1000*1000); /* shouldn't need much */
    unsigned char proof[1000];
    plen = 1000;
    random_scalar_order(&rho);
    secp256k1_scalar_sqr(&mu, &rho);

    for (i = 0; i < n; i++) {
        random_scalar_order(&n_vec[i]);
    }

    for (i = 0; i < m; i++) {
        random_scalar_order(&l_vec[i]);
        random_scalar_order(&c_vec[i]);
    }

    res = secp256k1_bppp_commit(CTX, scratch, &commit, gs, n_vec, n, l_vec, m, c_vec, m, &mu);
    CHECK(res == 1);
    res = secp256k1_norm_arg_prove(scratch, proof, &plen, &rho, gs, n_vec, n, l_vec, m, c_vec, m, &commit);
    CHECK(res == 1);

    res = secp256k1_norm_arg_verify(scratch, proof, plen, &rho, gs, n, c_vec, m, &commit);
    CHECK(res == 1);

    /* Changing any of last two scalars should break the proof */
    proof[plen - 1] ^= 1;
    res = secp256k1_norm_arg_verify(scratch, proof, plen, &rho, gs, n, c_vec, m, &commit);
    CHECK(res == 0);
    proof[plen - 1 - 32] ^= 1;
    res = secp256k1_norm_arg_verify(scratch, proof, plen, &rho, gs, n, c_vec, m, &commit);
    CHECK(res == 0);

    secp256k1_scratch_space_destroy(CTX, scratch);
    secp256k1_bppp_generators_destroy(CTX, gs);
}

/* Parses generators from points compressed as pubkeys */
secp256k1_bppp_generators* bppp_generators_parse_regular(const unsigned char* data, size_t data_len) {
    size_t n = data_len / 33;
    secp256k1_bppp_generators* ret;

    if (data_len % 33 != 0) {
        return NULL;
    }

    ret = (secp256k1_bppp_generators *)checked_malloc(&CTX->error_callback, sizeof(*ret));
    if (ret == NULL) {
        return NULL;
    }
    ret->n = n;
    ret->gens = (secp256k1_ge*)checked_malloc(&CTX->error_callback, n * sizeof(*ret->gens));
    if (ret->gens == NULL) {
        free(ret);
        return NULL;
    }

    while (n--) {
        if (!secp256k1_eckey_pubkey_parse(&ret->gens[n], &data[33 * n], 33)) {
            free(ret->gens);
            free(ret);
            return NULL;
        }
    }
    return ret;
}

int norm_arg_verify_vectors_helper(secp256k1_scratch *scratch, const unsigned char *gens, const unsigned char *proof, size_t plen, const unsigned char *r32, size_t n_vec_len, const unsigned char c_vec32[][32], secp256k1_scalar *c_vec, size_t c_vec_len, const unsigned char *commit33) {
    secp256k1_sha256 transcript;
    secp256k1_bppp_generators *gs = bppp_generators_parse_regular(gens, 33*(n_vec_len + c_vec_len));
    secp256k1_scalar rho;
    secp256k1_ge commit;
    int overflow;
    int i;
    int ret;

    CHECK(gs != NULL);
    secp256k1_sha256_initialize(&transcript);

    secp256k1_scalar_set_b32(&rho, r32, &overflow);
    CHECK(!overflow);

    for (i = 0; i < (int)c_vec_len; i++) {
        secp256k1_scalar_set_b32(&c_vec[i], c_vec32[i], &overflow);
        CHECK(!overflow);
    }
    CHECK(secp256k1_ge_parse_ext(&commit, commit33));
    ret = secp256k1_bppp_rangeproof_norm_product_verify(CTX, scratch, proof, plen, &transcript, &rho, gs, n_vec_len, c_vec, c_vec_len, &commit);

    secp256k1_bppp_generators_destroy(CTX, gs);
    return ret;
}

#define IDX_TO_TEST(i) (norm_arg_verify_vectors_helper(scratch, verify_vector_gens, verify_vector_##i##_proof, sizeof(verify_vector_##i##_proof), verify_vector_##i##_r32, verify_vector_##i##_n_vec_len, verify_vector_##i##_c_vec32, verify_vector_##i##_c_vec, sizeof(verify_vector_##i##_c_vec)/sizeof(secp256k1_scalar), verify_vector_##i##_commit33) == verify_vector_##i##_result)

static void norm_arg_verify_vectors(void) {
    secp256k1_scratch *scratch = secp256k1_scratch_space_create(CTX, 1000*1000); /* shouldn't need much */
    size_t alloc = scratch->alloc_size;

    CHECK(IDX_TO_TEST(0));
    CHECK(IDX_TO_TEST(1));
    CHECK(IDX_TO_TEST(2));
    CHECK(IDX_TO_TEST(3));
    CHECK(IDX_TO_TEST(4));
    CHECK(IDX_TO_TEST(5));
    CHECK(IDX_TO_TEST(6));
    CHECK(IDX_TO_TEST(7));
    CHECK(IDX_TO_TEST(8));
    CHECK(IDX_TO_TEST(9));
    CHECK(IDX_TO_TEST(10));
    CHECK(IDX_TO_TEST(11));
    CHECK(IDX_TO_TEST(12));

    CHECK(alloc == scratch->alloc_size);
    secp256k1_scratch_space_destroy(CTX, scratch);
}
#undef IDX_TO_TEST

static void norm_arg_prove_vectors_helper(secp256k1_scratch *scratch, const unsigned char *gens, const unsigned char *proof, size_t plen, const unsigned char *r32, const unsigned char n_vec32[][32], secp256k1_scalar *n_vec, size_t n_vec_len, const unsigned char l_vec32[][32], secp256k1_scalar *l_vec, const unsigned char c_vec32[][32], secp256k1_scalar *c_vec, size_t c_vec_len, int result) {
    secp256k1_sha256 transcript;
    secp256k1_bppp_generators *gs = bppp_generators_parse_regular(gens, 33*(n_vec_len + c_vec_len));
    secp256k1_scalar rho, mu;
    secp256k1_ge commit;
    unsigned char myproof[1024];
    size_t myplen = sizeof(myproof);
    int overflow;
    int i;

    CHECK(gs != NULL);
    secp256k1_sha256_initialize(&transcript);
    secp256k1_scalar_set_b32(&rho, r32, &overflow);
    CHECK(!overflow);
    secp256k1_scalar_sqr(&mu, &rho);

    for (i = 0; i < (int)n_vec_len; i++) {
        secp256k1_scalar_set_b32(&n_vec[i], n_vec32[i], &overflow);
        CHECK(!overflow);
    }
    for (i = 0; i < (int)c_vec_len; i++) {
        secp256k1_scalar_set_b32(&l_vec[i], l_vec32[i], &overflow);
        CHECK(!overflow);
        secp256k1_scalar_set_b32(&c_vec[i], c_vec32[i], &overflow);
        CHECK(!overflow);
    }

    CHECK(secp256k1_bppp_rangeproof_norm_product_prove_const(scratch, myproof, &myplen, &transcript, &rho, gs->gens, gs->n, n_vec, n_vec_len, l_vec, c_vec_len, c_vec, c_vec_len) == result);
    if (!result) {
        secp256k1_bppp_generators_destroy(CTX, gs);
        return;
    }
    CHECK(plen == myplen);
    CHECK(secp256k1_memcmp_var(proof, myproof, plen) == 0);

    CHECK(secp256k1_bppp_commit(CTX, scratch, &commit, gs, n_vec, n_vec_len, l_vec, c_vec_len, c_vec, c_vec_len, &mu));
    secp256k1_sha256_initialize(&transcript);
    CHECK(secp256k1_bppp_rangeproof_norm_product_verify(CTX, scratch, proof, plen, &transcript, &rho, gs, n_vec_len, c_vec, c_vec_len, &commit));
    secp256k1_bppp_generators_destroy(CTX, gs);
}


#define IDX_TO_TEST(i) (norm_arg_prove_vectors_helper(scratch, prove_vector_gens, prove_vector_##i##_proof, sizeof(prove_vector_##i##_proof), prove_vector_##i##_r32,\
    prove_vector_##i##_n_vec32, prove_vector_##i##_n_vec, sizeof(prove_vector_##i##_n_vec)/sizeof(secp256k1_scalar),\
    prove_vector_##i##_l_vec32, prove_vector_##i##_l_vec,\
    prove_vector_##i##_c_vec32, prove_vector_##i##_c_vec, sizeof(prove_vector_##i##_c_vec)/sizeof(secp256k1_scalar), \
    prove_vector_##i##_result))

static void norm_arg_prove_vectors(void) {
    secp256k1_scratch *scratch = secp256k1_scratch_space_create(CTX, 1000*1000); /* shouldn't need much */
    size_t alloc = scratch->alloc_size;

    IDX_TO_TEST(0);
    IDX_TO_TEST(1);
    IDX_TO_TEST(2);
    IDX_TO_TEST(3);
    IDX_TO_TEST(4);

    CHECK(alloc == scratch->alloc_size);
    secp256k1_scratch_space_destroy(CTX, scratch);
}

#undef IDX_TO_TEST

static void run_bppp_tests(void) {
    test_log_exp();
    test_norm_util_helpers();
    test_serialize_two_points();
    test_bppp_generators_api();
    test_bppp_generators_fixed();
    test_bppp_tagged_hash();

    norm_arg_verify_zero_len();
    norm_arg_test(1, 1);
    norm_arg_test(1, 64);
    norm_arg_test(64, 1);
    norm_arg_test(32, 32);
    norm_arg_test(32, 64);
    norm_arg_test(64, 32);
    norm_arg_test(64, 64);

    norm_arg_verify_vectors();
    norm_arg_prove_vectors();
}

#endif
