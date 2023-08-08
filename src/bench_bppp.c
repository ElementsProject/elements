/**********************************************************************
 * Copyright (c) 2020 Andrew Poelstra                                 *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#include <stdint.h>

#include "../include/secp256k1_bppp.h"
#include "util.h"
#include "bench.h"

typedef struct {
    secp256k1_context* ctx;
} bench_bppp_data;

static void bench_bppp_setup(void* arg) {
    (void) arg;
}

static void bench_bppp(void* arg, int iters) {
    bench_bppp_data *data = (bench_bppp_data*)arg;

    (void) data;
    (void) iters;
}

int main(void) {
    bench_bppp_data data;
    int iters = get_iters(32);

    data.ctx = secp256k1_context_create(SECP256K1_CONTEXT_NONE);

    run_benchmark("bppp_verify_bit", bench_bppp, bench_bppp_setup, NULL, &data, 10, iters);

    secp256k1_context_destroy(data.ctx);
    return 0;
}
