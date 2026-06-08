/**********************************************************************
 * Copyright (c) 2019-2020 Marko Bencun, Jonas Nick                   *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef SECP256K1_MODULE_ECDSA_S2C_TESTS_H
#define SECP256K1_MODULE_ECDSA_S2C_TESTS_H

#include "../../../include/secp256k1_ecdsa_s2c.h"
#include "../../unit_test.h"

static void test_ecdsa_s2c_tagged_hash(void) {
    const secp256k1_hash_ctx *hash_ctx = secp256k1_get_hash_context(CTX);
    unsigned char tag_data[] = {'s', '2', 'c', '/', 'e', 'c', 'd', 's', 'a', '/', 'd', 'a', 't', 'a'};
    unsigned char tag_point[] = {'s', '2', 'c', '/', 'e', 'c', 'd', 's', 'a', '/', 'p', 'o', 'i', 'n', 't'};
    secp256k1_sha256 sha;
    secp256k1_sha256 sha_optimized;
    unsigned char output[32];
    unsigned char output_optimized[32];

    secp256k1_sha256_initialize_tagged(hash_ctx, &sha, tag_data, sizeof(tag_data));
    secp256k1_s2c_ecdsa_data_sha256_tagged(&sha_optimized);
    secp256k1_sha256_finalize(hash_ctx, &sha, output);
    secp256k1_sha256_finalize(hash_ctx, &sha_optimized, output_optimized);
    CHECK(secp256k1_memcmp_var(output, output_optimized, 32) == 0);

    secp256k1_sha256_initialize_tagged(hash_ctx, &sha, tag_point, sizeof(tag_point));
    secp256k1_s2c_ecdsa_point_sha256_tagged(&sha_optimized);
    secp256k1_sha256_finalize(hash_ctx, &sha, output);
    secp256k1_sha256_finalize(hash_ctx, &sha_optimized, output_optimized);
    CHECK(secp256k1_memcmp_var(output, output_optimized, 32) == 0);
}

static void run_s2c_opening_test(void) {
    int i = 0;
    unsigned char output[33];
    unsigned char input[33] = {
            0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x02
    };
    secp256k1_ecdsa_s2c_opening opening;

    /* First parsing, then serializing works */
    CHECK(secp256k1_ecdsa_s2c_opening_parse(CTX, &opening, input) == 1);
    CHECK(secp256k1_ecdsa_s2c_opening_serialize(CTX, output, &opening) == 1);
    CHECK(secp256k1_ecdsa_s2c_opening_parse(CTX, &opening, input) == 1);

    CHECK_ILLEGAL(CTX, secp256k1_ecdsa_s2c_opening_parse(CTX, NULL, input));
    CHECK_ILLEGAL(CTX, secp256k1_ecdsa_s2c_opening_parse(CTX, &opening, NULL));
    CHECK(secp256k1_ecdsa_s2c_opening_parse(CTX, &opening, input) == 1);

    CHECK_ILLEGAL(CTX, secp256k1_ecdsa_s2c_opening_serialize(CTX, NULL, &opening));
    CHECK_ILLEGAL(CTX, secp256k1_ecdsa_s2c_opening_serialize(CTX, output, NULL));

    /* Invalid pubkey makes parsing fail but they are not API errors */
    input[0] = 0;  /* bad oddness bit */
    CHECK(secp256k1_ecdsa_s2c_opening_parse(CTX, &opening, input) == 0);
    input[0] = 2;
    input[31] = 1; /* point not on the curve */
    CHECK(secp256k1_ecdsa_s2c_opening_parse(CTX, &opening, input) == 0);

    /* Try parsing and serializing a bunch of openings */
    for (i = 0; i < COUNT; i++) {
        /* This is expected to fail in about 50% of iterations because the
         * points' x-coordinates are uniformly random */
        if (secp256k1_ecdsa_s2c_opening_parse(CTX, &opening, input) == 1) {
            CHECK(secp256k1_ecdsa_s2c_opening_serialize(CTX, output, &opening) == 1);
            CHECK(secp256k1_memcmp_var(output, input, sizeof(output)) == 0);
        }
        testrand256(&input[1]);
        /* Set pubkey oddness tag to first bit of input[1] */
        input[0] = (input[1] & 1) + 2;
    }
}

static void test_ecdsa_s2c_api(void) {
    secp256k1_ecdsa_s2c_opening s2c_opening;
    secp256k1_ecdsa_signature sig;
    const unsigned char msg[] = {'m', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm', 'm'};
    const unsigned char sec[] = {'s', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's', 's'};
    const unsigned char s2c_data[] = {'d', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd', 'd'};
    const unsigned char hostrand[] = {'h', 'r', 'h', 'r', 'h', 'r', 'h', 'r', 'h', 'r', 'h', 'r', 'h', 'r', 'h', 'r', 'h', 'r', 'h', 'r', 'h', 'r', 'h', 'r', 'h', 'r', 'h', 'r', 'h', 'r', 'h', 'r'};
    unsigned char hostrand_commitment[32];
    secp256k1_pubkey pk;

    CHECK(secp256k1_ec_pubkey_create(CTX, &pk, sec));

    CHECK_ILLEGAL(CTX, secp256k1_ecdsa_s2c_sign(CTX, NULL, &s2c_opening, msg, sec, s2c_data));
    /* NULL opening is not an API error */
    CHECK(secp256k1_ecdsa_s2c_sign(CTX, &sig, NULL, msg, sec, s2c_data) == 1);
    CHECK_ILLEGAL(CTX, secp256k1_ecdsa_s2c_sign(CTX, &sig, &s2c_opening, NULL, sec, s2c_data));
    CHECK_ILLEGAL(CTX, secp256k1_ecdsa_s2c_sign(CTX, &sig, &s2c_opening, msg, NULL, s2c_data));
    CHECK_ILLEGAL(CTX, secp256k1_ecdsa_s2c_sign(CTX, &sig, &s2c_opening, msg, sec, NULL));
    CHECK(secp256k1_ecdsa_s2c_sign(CTX, &sig, &s2c_opening, msg, sec, s2c_data) == 1);
    CHECK_ILLEGAL(STATIC_CTX, secp256k1_ecdsa_s2c_sign(STATIC_CTX, &sig, &s2c_opening, msg, sec, s2c_data));

    CHECK(secp256k1_ecdsa_verify(CTX, &sig, msg, &pk) == 1);

    CHECK_ILLEGAL(CTX, secp256k1_ecdsa_s2c_verify_commit(CTX, NULL, s2c_data, &s2c_opening));
    CHECK_ILLEGAL(CTX, secp256k1_ecdsa_s2c_verify_commit(CTX, &sig, NULL, &s2c_opening));
    CHECK_ILLEGAL(CTX, secp256k1_ecdsa_s2c_verify_commit(CTX, &sig, s2c_data, NULL));
    CHECK(secp256k1_ecdsa_s2c_verify_commit(CTX, &sig, s2c_data, &s2c_opening) == 1);
    /* wrong data is not an API error */
    CHECK(secp256k1_ecdsa_s2c_verify_commit(CTX, &sig, sec, &s2c_opening) == 0);

    /* Signing with NULL s2c_opening gives the same result */
    CHECK(secp256k1_ecdsa_s2c_sign(CTX, &sig, NULL, msg, sec, s2c_data) == 1);
    CHECK(secp256k1_ecdsa_s2c_verify_commit(CTX, &sig, s2c_data, &s2c_opening) == 1);

    /* anti-exfil */
    CHECK_ILLEGAL(CTX, secp256k1_ecdsa_anti_exfil_host_commit(CTX, NULL, hostrand));
    CHECK_ILLEGAL(CTX, secp256k1_ecdsa_anti_exfil_host_commit(CTX, hostrand_commitment, NULL));
    CHECK(secp256k1_ecdsa_anti_exfil_host_commit(CTX, hostrand_commitment, hostrand) == 1);

    CHECK_ILLEGAL(CTX, secp256k1_ecdsa_anti_exfil_signer_commit(CTX, NULL, msg, sec, hostrand_commitment));
    CHECK_ILLEGAL(CTX, secp256k1_ecdsa_anti_exfil_signer_commit(CTX, &s2c_opening, NULL, sec, hostrand_commitment));
    CHECK_ILLEGAL(CTX, secp256k1_ecdsa_anti_exfil_signer_commit(CTX, &s2c_opening, msg, NULL, hostrand_commitment));
    CHECK_ILLEGAL(CTX, secp256k1_ecdsa_anti_exfil_signer_commit(CTX, &s2c_opening, msg, sec, NULL));
    CHECK(secp256k1_ecdsa_anti_exfil_signer_commit(CTX, &s2c_opening, msg, sec, hostrand_commitment) == 1);
    CHECK_ILLEGAL(STATIC_CTX, secp256k1_ecdsa_anti_exfil_signer_commit(STATIC_CTX, &s2c_opening, msg, sec, hostrand_commitment));

    CHECK_ILLEGAL(CTX, secp256k1_anti_exfil_sign(CTX, NULL, msg, sec, hostrand));
    CHECK_ILLEGAL(CTX, secp256k1_anti_exfil_sign(CTX, &sig, NULL, sec, hostrand));
    CHECK_ILLEGAL(CTX, secp256k1_anti_exfil_sign(CTX, &sig, msg, NULL, hostrand));
    CHECK_ILLEGAL(CTX, secp256k1_anti_exfil_sign(CTX, &sig, msg, sec, NULL));
    CHECK(secp256k1_anti_exfil_sign(CTX, &sig, msg, sec, hostrand) == 1);
    CHECK_ILLEGAL(STATIC_CTX, secp256k1_anti_exfil_sign(STATIC_CTX, &sig, msg, sec, hostrand));

    CHECK_ILLEGAL(CTX, secp256k1_anti_exfil_host_verify(CTX, NULL, msg, &pk, hostrand, &s2c_opening));
    CHECK_ILLEGAL(CTX, secp256k1_anti_exfil_host_verify(CTX, &sig, NULL, &pk, hostrand, &s2c_opening));
    CHECK_ILLEGAL(CTX, secp256k1_anti_exfil_host_verify(CTX, &sig, msg, NULL, hostrand, &s2c_opening));
    CHECK_ILLEGAL(CTX, secp256k1_anti_exfil_host_verify(CTX, &sig, msg, &pk, NULL, &s2c_opening));
    CHECK_ILLEGAL(CTX, secp256k1_anti_exfil_host_verify(CTX, &sig, msg, &pk, hostrand, NULL));
    CHECK(secp256k1_anti_exfil_host_verify(CTX, &sig, msg, &pk, hostrand, &s2c_opening) == 1);
}

/* When using sign-to-contract commitments, the nonce function is fixed, so we can use fixtures to test. */
typedef struct {
    /* Data to commit to */
    unsigned char s2c_data[32];
    /* Original nonce */
    unsigned char expected_s2c_opening[33];
    /* Original nonce (anti-exfil protocol, which mixes in host randomness) */
    unsigned char expected_s2c_exfil_opening[33];
} ecdsa_s2c_test;

static ecdsa_s2c_test ecdsa_s2c_tests[] = {
    {
        {0x1b, 0xf6, 0xfb, 0x42, 0xf4, 0x1e, 0xb8, 0x76, 0xc4, 0xd7, 0xaa, 0x0d, 0x67, 0x24, 0x2b, 0x00, 0xba, 0xab, 0x99, 0xdc, 0x20, 0x84, 0x49, 0x3e, 0x4e, 0x63, 0x27, 0x7f, 0xa1, 0xf7, 0x7f, 0x22},
        {0x03, 0xf0, 0x30, 0xde, 0xf3, 0x18, 0x8c, 0x0f, 0x56, 0xfc, 0xea, 0x87, 0x43, 0x5b, 0x30, 0x76, 0x43, 0xf4, 0x5d, 0xaf, 0xe2, 0x2c, 0xbc, 0x82, 0xfd, 0x56, 0x03, 0x4f, 0xae, 0x97, 0x41, 0x7d, 0x3a},
        {0x02, 0xdf, 0x63, 0x75, 0x5d, 0x1f, 0x32, 0x92, 0xbf, 0xfe, 0xd8, 0x29, 0x86, 0xb1, 0x06, 0x49, 0x7c, 0x93, 0xb1, 0xf8, 0xbd, 0xc0, 0x45, 0x4b, 0x6b, 0x0b, 0x0a, 0x47, 0x79, 0xc0, 0xef, 0x71, 0x88},
    },
    {
        {0x35, 0x19, 0x9a, 0x8f, 0xbf, 0x84, 0xad, 0x6e, 0xf6, 0x9a, 0x18, 0x4c, 0x1b, 0x19, 0x28, 0x5b, 0xef, 0xbe, 0x06, 0xe6, 0x0b, 0x62, 0x64, 0xe6, 0xd3, 0x73, 0x89, 0x3f, 0x68, 0x55, 0xe2, 0x4a},
        {0x03, 0x90, 0x17, 0x17, 0xce, 0x7c, 0x74, 0x84, 0xa2, 0xce, 0x1b, 0x7d, 0xc7, 0x40, 0x3b, 0x14, 0xe0, 0x35, 0x49, 0x71, 0x39, 0x3e, 0xc0, 0x92, 0xa7, 0xf3, 0xe0, 0xc8, 0xe4, 0xe2, 0xd2, 0x63, 0x9d},
        {0x02, 0xc0, 0x4a, 0xc7, 0xf7, 0x71, 0xe8, 0xeb, 0xdb, 0xf3, 0x15, 0xff, 0x5e, 0x58, 0xb7, 0xfe, 0x95, 0x16, 0x10, 0x21, 0x03, 0x50, 0x00, 0x66, 0x17, 0x2c, 0x4f, 0xac, 0x5b, 0x20, 0xf9, 0xe0, 0xea},
    },
};

static void test_ecdsa_s2c_fixed_vectors(void) {
    const unsigned char privkey[32] = {
        0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55,
        0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55,
    };
    const unsigned char message[32] = {
        0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88,
        0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88,
    };
    size_t i;

    for (i = 0; i < ARRAY_SIZE(ecdsa_s2c_tests); i++) {
        secp256k1_ecdsa_s2c_opening s2c_opening;
        unsigned char opening_ser[33];
        const ecdsa_s2c_test *test = &ecdsa_s2c_tests[i];
        secp256k1_ecdsa_signature signature;
        CHECK(secp256k1_ecdsa_s2c_sign(CTX, &signature, &s2c_opening, message, privkey, test->s2c_data) == 1);
        CHECK(secp256k1_ecdsa_s2c_opening_serialize(CTX, opening_ser, &s2c_opening) == 1);
        CHECK(secp256k1_memcmp_var(test->expected_s2c_opening, opening_ser, sizeof(opening_ser)) == 0);
        CHECK(secp256k1_ecdsa_s2c_verify_commit(CTX, &signature, test->s2c_data, &s2c_opening) == 1);
    }
}

static void test_ecdsa_s2c_sign_verify(void) {
    unsigned char privkey[32];
    secp256k1_pubkey pubkey;
    unsigned char message[32];
    unsigned char noncedata[32];
    unsigned char s2c_data[32];
    unsigned char s2c_data2[32];
    secp256k1_ecdsa_signature signature;
    secp256k1_ecdsa_s2c_opening s2c_opening;

    /* Generate a random key, message, noncedata and s2c_data. */
    {
        secp256k1_scalar key;
        testutil_random_scalar_order_test(&key);
        secp256k1_scalar_get_b32(privkey, &key);
        CHECK(secp256k1_ec_pubkey_create(CTX, &pubkey, privkey) == 1);

        testrand256_test(message);
        testrand256_test(noncedata);
        testrand256_test(s2c_data);
        testrand256_test(s2c_data2);
    }

    { /* invalid privkeys */
        unsigned char zero_privkey[32] = {0};
        unsigned char overflow_privkey[32] = {0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff};
        CHECK(secp256k1_ecdsa_s2c_sign(CTX, &signature, NULL, message, zero_privkey, s2c_data) == 0);
        CHECK(secp256k1_ecdsa_s2c_sign(CTX, &signature, NULL, message, overflow_privkey, s2c_data) == 0);
    }
    /* Check that the sign-to-contract signature is valid, with s2c_data. Also check the commitment. */
    {
        CHECK(secp256k1_ecdsa_s2c_sign(CTX, &signature, &s2c_opening, message, privkey, s2c_data) == 1);
        CHECK(secp256k1_ecdsa_verify(CTX, &signature, message, &pubkey) == 1);
        CHECK(secp256k1_ecdsa_s2c_verify_commit(CTX, &signature, s2c_data, &s2c_opening) == 1);
    }
    /* Check that an invalid commitment does not verify */
    {
        unsigned char sigbytes[64];
        size_t i;
        CHECK(secp256k1_ecdsa_s2c_sign(CTX, &signature, &s2c_opening, message, privkey, s2c_data) == 1);
        CHECK(secp256k1_ecdsa_verify(CTX, &signature, message, &pubkey) == 1);

        CHECK(secp256k1_ecdsa_signature_serialize_compact(CTX, sigbytes, &signature) == 1);
        for(i = 0; i < 32; i++) {
            /* change one byte */
            sigbytes[i] = (((int)sigbytes[i]) + 1) % 256;
            CHECK(secp256k1_ecdsa_signature_parse_compact(CTX, &signature, sigbytes) == 1);
            CHECK(secp256k1_ecdsa_s2c_verify_commit(CTX, &signature, s2c_data, &s2c_opening) == 0);
            /* revert */
            sigbytes[i] = (((int)sigbytes[i]) + 255) % 256;
        }
    }
}

static void test_ecdsa_anti_exfil_signer_commit(void) {
    size_t i;
    unsigned char privkey[32] = {
        0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55,
        0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55,
    };
    unsigned char message[32] = {
        0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88,
        0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88,
    };
    /* Check that original pubnonce is derived from s2c_data */
    for (i = 0; i < ARRAY_SIZE(ecdsa_s2c_tests); i++) {
        secp256k1_ecdsa_s2c_opening s2c_opening;
        unsigned char buf[33];
        const ecdsa_s2c_test *test = &ecdsa_s2c_tests[i];
        CHECK(secp256k1_ecdsa_anti_exfil_signer_commit(CTX, &s2c_opening, message, privkey, test->s2c_data) == 1);
        CHECK(secp256k1_ecdsa_s2c_opening_serialize(CTX, buf, &s2c_opening) == 1);
        CHECK(secp256k1_memcmp_var(test->expected_s2c_exfil_opening, buf, sizeof(buf)) == 0);
    }
}

/* This tests the full ECDSA Anti-Exfil Protocol */
static void test_ecdsa_anti_exfil(void) {
    unsigned char signer_privkey[32];
    unsigned char host_msg[32];
    unsigned char host_commitment[32];
    unsigned char host_nonce_contribution[32];
    secp256k1_pubkey signer_pubkey;
    secp256k1_ecdsa_signature signature;
    secp256k1_ecdsa_s2c_opening s2c_opening;

    /* Generate a random key, message. */
    {
        secp256k1_scalar key;
        testutil_random_scalar_order_test(&key);
        secp256k1_scalar_get_b32(signer_privkey, &key);
        CHECK(secp256k1_ec_pubkey_create(CTX, &signer_pubkey, signer_privkey) == 1);
        testrand256_test(host_msg);
        testrand256_test(host_nonce_contribution);
    }

    /* Protocol step 1. */
    CHECK(secp256k1_ecdsa_anti_exfil_host_commit(CTX, host_commitment, host_nonce_contribution) == 1);
    /* Protocol step 2. */
    CHECK(secp256k1_ecdsa_anti_exfil_signer_commit(CTX, &s2c_opening, host_msg, signer_privkey, host_commitment) == 1);
    /* Protocol step 3: host_nonce_contribution send to signer to be used in step 4. */
    /* Protocol step 4. */
    CHECK(secp256k1_anti_exfil_sign(CTX, &signature, host_msg, signer_privkey, host_nonce_contribution) == 1);
    /* Protocol step 5. */
    CHECK(secp256k1_anti_exfil_host_verify(CTX, &signature, host_msg, &signer_pubkey, host_nonce_contribution, &s2c_opening) == 1);
    /* Protocol step 5 (explicitly) */
    CHECK(secp256k1_ecdsa_s2c_verify_commit(CTX, &signature, host_nonce_contribution, &s2c_opening) == 1);
    CHECK(secp256k1_ecdsa_verify(CTX, &signature, host_msg, &signer_pubkey) == 1);

    { /* host_verify: commitment does not match */
        unsigned char sigbytes[64];
        size_t i;
        CHECK(secp256k1_ecdsa_signature_serialize_compact(CTX, sigbytes, &signature) == 1);
        for(i = 0; i < 32; i++) {
            /* change one byte */
            sigbytes[i] += 1;
            CHECK(secp256k1_ecdsa_signature_parse_compact(CTX, &signature, sigbytes) == 1);
            CHECK(secp256k1_ecdsa_s2c_verify_commit(CTX, &signature, host_nonce_contribution, &s2c_opening) == 0);
            CHECK(secp256k1_anti_exfil_host_verify(CTX, &signature, host_msg, &signer_pubkey, host_nonce_contribution, &s2c_opening) == 0);
            /* revert */
            sigbytes[i] -= 1;
        }
        CHECK(secp256k1_ecdsa_signature_parse_compact(CTX, &signature, sigbytes) == 1);
    }
    { /* host_verify: message does not match */
        unsigned char bad_msg[32];
        testrand256_test(bad_msg);
        CHECK(secp256k1_anti_exfil_host_verify(CTX, &signature, host_msg, &signer_pubkey, host_nonce_contribution, &s2c_opening) == 1);
        CHECK(secp256k1_anti_exfil_host_verify(CTX, &signature, bad_msg, &signer_pubkey, host_nonce_contribution, &s2c_opening) == 0);
    }
    { /* s2c_sign: host provided data that didn't match commitment */
        secp256k1_ecdsa_s2c_opening orig_opening = s2c_opening;
        unsigned char bad_nonce_contribution[32] = { 1, 2, 3, 4 };
        CHECK(secp256k1_ecdsa_s2c_sign(CTX, &signature, &s2c_opening, host_msg, signer_privkey, bad_nonce_contribution) == 1);
        /* good signature but the opening (original public nonce does not match the original */
        CHECK(secp256k1_ecdsa_verify(CTX, &signature, host_msg, &signer_pubkey) == 1);
        CHECK(secp256k1_anti_exfil_host_verify(CTX, &signature, host_msg, &signer_pubkey, host_nonce_contribution, &s2c_opening) == 0);
        CHECK(secp256k1_anti_exfil_host_verify(CTX, &signature, host_msg, &signer_pubkey, bad_nonce_contribution, &s2c_opening) == 1);
        CHECK(secp256k1_memcmp_var(&s2c_opening, &orig_opening, sizeof(s2c_opening)) != 0);
    }
}

/* --- Test registry --- */
static const struct tf_test_entry tests_ecdsa_s2c[] = {
    CASE1(run_s2c_opening_test),
    CASE1(test_ecdsa_s2c_tagged_hash),
    CASE1(test_ecdsa_s2c_api),
    CASE1(test_ecdsa_s2c_fixed_vectors),
    CASE1(test_ecdsa_s2c_sign_verify),
    CASE1(test_ecdsa_anti_exfil_signer_commit),
    CASE1(test_ecdsa_anti_exfil)
};

#endif /* SECP256K1_MODULE_ECDSA_S2C_TESTS_H */
