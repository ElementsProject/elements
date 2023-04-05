/**********************************************************************
 * Copyright (c) 2020 Andrew Poelstra                                 *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef _SECP256K1_MODULE_BPPP_UTIL_
#define _SECP256K1_MODULE_BPPP_UTIL_

#include "field.h"
#include "group.h"
#include "hash.h"
#include "eckey.h"

/* Outputs a pair of points, amortizing the parity byte between them
 * Assumes both points' coordinates have been normalized.
 */
static void secp256k1_bppp_serialize_points(unsigned char *output, const secp256k1_ge *lpt, const secp256k1_ge *rpt) {
    output[0] = (secp256k1_fe_is_odd(&lpt->y) << 1) + secp256k1_fe_is_odd(&rpt->y);
    secp256k1_fe_get_b32(&output[1], &lpt->x);
    secp256k1_fe_get_b32(&output[33], &rpt->x);
}

/* Outputs a serialized point in compressed form. Returns 0 at point at infinity.
*/
static int secp256k1_bppp_serialize_pt(unsigned char *output, secp256k1_ge *lpt) {
    size_t size;
    return secp256k1_eckey_pubkey_serialize(lpt, output, &size, 1 /*compressed*/);
}

/* little-endian encodes a uint64 */
static void secp256k1_bppp_le64(unsigned char *output, const uint64_t n) {
    output[0] = n;
    output[1] = n >> 8;
    output[2] = n >> 16;
    output[3] = n >> 24;
    output[4] = n >> 32;
    output[5] = n >> 40;
    output[6] = n >> 48;
    output[7] = n >> 56;
}

/* Check if n is power of two*/
static int secp256k1_is_power_of_two(size_t n) {
    return n > 0 && (n & (n - 1)) == 0;
}

/* Compute the log2 of n. n must NOT be 0. If n is not a power of two, it
 * returns the largest `k` such that 2^k <= n. Assumes 0 < n < 2^64. In
 * Bulletproofs, this is bounded by len of input vectors which can be safely
 * assumed to be less than 2^64.
*/
static size_t secp256k1_bppp_log2(size_t n) {
    return 64 - 1 - secp256k1_clz64_var((uint64_t)n);
}

#endif
