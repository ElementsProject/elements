/**********************************************************************
 * Copyright (c) 2014 Pieter Wuille                                   *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef SECP256K1_SCALAR_IMPL_H
#define SECP256K1_SCALAR_IMPL_H

#include "scalar.h"
#include "util.h"

#include "scalar_8x32_impl.h"

#if 0
static void secp256k1_scalar_inverse(secp256k1_scalar *r, const secp256k1_scalar *x) {
    secp256k1_scalar *t;
    int i;
    /* First compute xN as x ^ (2^N - 1) for some values of N,
     * and uM as x ^ M for some values of M. */
    secp256k1_scalar x2, x3, x6, x8, x14, x28, x56, x112, x126;
    secp256k1_scalar u2, u5, u9, u11, u13;

    secp256k1_scalar_sqr(&u2, x);
    secp256k1_scalar_mul(&x2, &u2,  x);
    secp256k1_scalar_mul(&u5, &u2, &x2);
    secp256k1_scalar_mul(&x3, &u5,  &u2);
    secp256k1_scalar_mul(&u9, &x3, &u2);
    secp256k1_scalar_mul(&u11, &u9, &u2);
    secp256k1_scalar_mul(&u13, &u11, &u2);

    secp256k1_scalar_sqr(&x6, &u13);
    secp256k1_scalar_sqr(&x6, &x6);
    secp256k1_scalar_mul(&x6, &x6, &u11);

    secp256k1_scalar_sqr(&x8, &x6);
    secp256k1_scalar_sqr(&x8, &x8);
    secp256k1_scalar_mul(&x8, &x8,  &x2);

    secp256k1_scalar_sqr(&x14, &x8);
    for (i = 0; i < 5; i++) {
        secp256k1_scalar_sqr(&x14, &x14);
    }
    secp256k1_scalar_mul(&x14, &x14, &x6);

    secp256k1_scalar_sqr(&x28, &x14);
    for (i = 0; i < 13; i++) {
        secp256k1_scalar_sqr(&x28, &x28);
    }
    secp256k1_scalar_mul(&x28, &x28, &x14);

    secp256k1_scalar_sqr(&x56, &x28);
    for (i = 0; i < 27; i++) {
        secp256k1_scalar_sqr(&x56, &x56);
    }
    secp256k1_scalar_mul(&x56, &x56, &x28);

    secp256k1_scalar_sqr(&x112, &x56);
    for (i = 0; i < 55; i++) {
        secp256k1_scalar_sqr(&x112, &x112);
    }
    secp256k1_scalar_mul(&x112, &x112, &x56);

    secp256k1_scalar_sqr(&x126, &x112);
    for (i = 0; i < 13; i++) {
        secp256k1_scalar_sqr(&x126, &x126);
    }
    secp256k1_scalar_mul(&x126, &x126, &x14);

    /* Then accumulate the final result (t starts at x126). */
    t = &x126;
    for (i = 0; i < 3; i++) {
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &u5); /* 101 */
    for (i = 0; i < 4; i++) { /* 0 */
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &x3); /* 111 */
    for (i = 0; i < 4; i++) { /* 0 */
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &u5); /* 101 */
    for (i = 0; i < 5; i++) { /* 0 */
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &u11); /* 1011 */
    for (i = 0; i < 4; i++) {
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &u11); /* 1011 */
    for (i = 0; i < 4; i++) { /* 0 */
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &x3); /* 111 */
    for (i = 0; i < 5; i++) { /* 00 */
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &x3); /* 111 */
    for (i = 0; i < 6; i++) { /* 00 */
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &u13); /* 1101 */
    for (i = 0; i < 4; i++) { /* 0 */
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &u5); /* 101 */
    for (i = 0; i < 3; i++) {
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &x3); /* 111 */
    for (i = 0; i < 5; i++) { /* 0 */
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &u9); /* 1001 */
    for (i = 0; i < 6; i++) { /* 000 */
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &u5); /* 101 */
    for (i = 0; i < 10; i++) { /* 0000000 */
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &x3); /* 111 */
    for (i = 0; i < 4; i++) { /* 0 */
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &x3); /* 111 */
    for (i = 0; i < 9; i++) { /* 0 */
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &x8); /* 11111111 */
    for (i = 0; i < 5; i++) { /* 0 */
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &u9); /* 1001 */
    for (i = 0; i < 6; i++) { /* 00 */
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &u11); /* 1011 */
    for (i = 0; i < 4; i++) {
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &u13); /* 1101 */
    for (i = 0; i < 5; i++) {
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &x2); /* 11 */
    for (i = 0; i < 6; i++) { /* 00 */
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &u13); /* 1101 */
    for (i = 0; i < 10; i++) { /* 000000 */
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &u13); /* 1101 */
    for (i = 0; i < 4; i++) {
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, &u9); /* 1001 */
    for (i = 0; i < 6; i++) { /* 00000 */
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(t, t, x); /* 1 */
    for (i = 0; i < 8; i++) { /* 00 */
        secp256k1_scalar_sqr(t, t);
    }
    secp256k1_scalar_mul(r, t, &x6); /* 111111 */
}

SECP256K1_INLINE static int secp256k1_scalar_is_even(const secp256k1_scalar *a) {
    return !(a->d[0] & 1);
}

static void secp256k1_scalar_inverse_var(secp256k1_scalar *r, const secp256k1_scalar *x) {
    secp256k1_scalar_inverse(r, x);
}
#endif

#endif /* SECP256K1_SCALAR_IMPL_H */
