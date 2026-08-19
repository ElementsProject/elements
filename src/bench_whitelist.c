/**********************************************************************
 * Copyright (c) 2017 Jonas Nick                                      *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/
#include <stdio.h>
#include <stdlib.h>

#include "../include/secp256k1.h"

#include "../include/secp256k1_whitelist.h"
#include "util.h"
#include "bench.h"
#include "hash_impl.h"
#include "int128_impl.h"
#include "scalar_impl.h"

#define MAX_N_KEYS 30

typedef struct {
    secp256k1_context* ctx;
    unsigned char online_seckey[MAX_N_KEYS][32];
    unsigned char summed_seckey[MAX_N_KEYS][32];
    secp256k1_pubkey online_pubkeys[MAX_N_KEYS];
    secp256k1_pubkey offline_pubkeys[MAX_N_KEYS];
    unsigned char csub[32];
    secp256k1_pubkey sub_pubkey;
    secp256k1_whitelist_signature sig;
    size_t n_keys;
} bench_data;

static void bench_whitelist(void* arg, int iters) {
    bench_data* data = (bench_data*)arg;
    int i;
    for (i = 0; i < iters; i++) {
        CHECK(secp256k1_whitelist_verify(data->ctx, &data->sig, data->online_pubkeys, data->offline_pubkeys, data->n_keys, &data->sub_pubkey) == 1);
    }
}

static void bench_whitelist_setup(void* arg) {
    bench_data* data = (bench_data*)arg;
    int i = 0;
    CHECK(secp256k1_whitelist_sign(data->ctx, &data->sig, data->online_pubkeys, data->offline_pubkeys, data->n_keys, &data->sub_pubkey, data->online_seckey[i], data->summed_seckey[i], i));
}

static void run_test(bench_data* data, int iters) {
    char str[32];
    sprintf(str, "whitelist_%i", (int)data->n_keys);
    run_benchmark(str, bench_whitelist, bench_whitelist_setup, NULL, data, 100, iters);
}

static void generate_scalar(secp256k1_scalar *scalar, unsigned char *seckey, uint32_t num) {
    secp256k1_sha256 sha256;
    secp256k1_hash_ctx hash_ctx;
    unsigned char c[13] = {'w','h','i','t','e','l','i','s','t', 0, 0, 0, 0};
    int is_valid;
    secp256k1_hash_ctx_init(&hash_ctx);
    c[9] = num;
    c[10] = num >> 8;
    c[11] = num >> 16;
    c[12] = num >> 24;
    secp256k1_sha256_initialize(&sha256);
    secp256k1_sha256_write(&hash_ctx, &sha256, c, sizeof(c));
    secp256k1_sha256_finalize(&hash_ctx, &sha256, seckey);
    is_valid = secp256k1_scalar_set_b32_seckey(scalar, seckey);
    CHECK(is_valid);
}

int main(void) {
    bench_data data;
    size_t i;
    size_t n_keys = 30;
    secp256k1_scalar ssub;
    int iters = get_iters(5);
    if (iters == 0) {
        return EXIT_FAILURE;
    }

    data.ctx = secp256k1_context_create(SECP256K1_CONTEXT_NONE);

    /* Start with subkey */
    generate_scalar(&ssub, data.csub, 0);
    CHECK(secp256k1_ec_seckey_verify(data.ctx, data.csub) == 1);
    CHECK(secp256k1_ec_pubkey_create(data.ctx, &data.sub_pubkey, data.csub) == 1);
    /* Then offline and online whitelist keys */
    for (i = 0; i < n_keys; i++) {
        secp256k1_scalar son, soff;

        /* Create two keys using different counter values to ensure different keys */
        generate_scalar(&son, data.online_seckey[i], i + 1);
        CHECK(secp256k1_ec_seckey_verify(data.ctx, data.online_seckey[i]) == 1);
        CHECK(secp256k1_ec_pubkey_create(data.ctx, &data.online_pubkeys[i], data.online_seckey[i]) == 1);

        generate_scalar(&soff, data.summed_seckey[i], i + 1 + n_keys);
        CHECK(secp256k1_ec_seckey_verify(data.ctx, data.summed_seckey[i]) == 1);
        CHECK(secp256k1_ec_pubkey_create(data.ctx, &data.offline_pubkeys[i], data.summed_seckey[i]) == 1);

        /* Make summed_seckey correspond to the sum of offline_pubkey and sub_pubkey */
        secp256k1_scalar_add(&soff, &soff, &ssub);
        secp256k1_scalar_get_b32(data.summed_seckey[i], &soff);
        CHECK(secp256k1_ec_seckey_verify(data.ctx, data.summed_seckey[i]) == 1);
    }

    /* Run test */
    for (i = 1; i <= n_keys; ++i) {
        data.n_keys = i;
        run_test(&data, iters);
    }

    secp256k1_context_destroy(data.ctx);
    return EXIT_SUCCESS;
}
