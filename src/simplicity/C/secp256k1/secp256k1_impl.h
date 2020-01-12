/**********************************************************************
 * Copyright (c) 2013-2015 Pieter Wuille                              *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef SECP256K1_IMPL_H
#define SECP256K1_IMPL_H

#include "secp256k1.h"

#include "util.h"
#include "field_impl.h"
#include "scalar_impl.h"
#include "group_impl.h"
#include "ecmult_impl.h"
#include "eckey_impl.h"

#define ARG_CHECK VERIFY_CHECK

static int secp256k1_pubkey_load(secp256k1_ge* ge, const secp256k1_pubkey* pubkey) {
    if (sizeof(secp256k1_ge_storage) == 64) {
        /* When the secp256k1_ge_storage type is exactly 64 byte, use its
         * representation inside secp256k1_pubkey, as conversion is very fast.
         * Note that secp256k1_pubkey_save must use the same representation. */
        secp256k1_ge_storage s;
        memcpy(&s, &pubkey->data[0], sizeof(s));
        secp256k1_ge_from_storage(ge, &s);
    } else {
        /* Otherwise, fall back to 32-byte big endian for X and Y. */
        secp256k1_fe x, y;
        secp256k1_fe_set_b32(&x, pubkey->data);
        secp256k1_fe_set_b32(&y, pubkey->data + 32);
        secp256k1_ge_set_xy(ge, &x, &y);
    }
    ARG_CHECK(!secp256k1_fe_is_zero(&ge->x));
    return 1;
}

static void secp256k1_pubkey_save(secp256k1_pubkey* pubkey, secp256k1_ge* ge) {
    if (sizeof(secp256k1_ge_storage) == 64) {
        secp256k1_ge_storage s;
        secp256k1_ge_to_storage(&s, ge);
        memcpy(&pubkey->data[0], &s, sizeof(s));
    } else {
        VERIFY_CHECK(!secp256k1_ge_is_infinity(ge));
        secp256k1_fe_normalize_var(&ge->x);
        secp256k1_fe_normalize_var(&ge->y);
        secp256k1_fe_get_b32(pubkey->data, &ge->x);
        secp256k1_fe_get_b32(pubkey->data + 32, &ge->y);
    }
}

static int secp256k1_ec_pubkey_parse(secp256k1_pubkey* pubkey, const unsigned char *input, size_t inputlen) {
    secp256k1_ge Q;

    ARG_CHECK(pubkey != NULL);
    memset(pubkey, 0, sizeof(*pubkey));
    ARG_CHECK(input != NULL);
    if (!secp256k1_eckey_pubkey_parse(&Q, input, inputlen)) {
        return 0;
    }
    secp256k1_pubkey_save(pubkey, &Q);
    secp256k1_ge_clear(&Q);
    return 1;
}

static int secp256k1_ec_pubkey_serialize(unsigned char *output, size_t *outputlen, const secp256k1_pubkey* pubkey) {
    secp256k1_ge Q;
    size_t len;
    int ret = 0;

    ARG_CHECK(outputlen != NULL);
    ARG_CHECK(*outputlen >= 33);
    len = *outputlen;
    *outputlen = 0;
    ARG_CHECK(output != NULL);
    memset(output, 0, len);
    ARG_CHECK(pubkey != NULL);
    if (secp256k1_pubkey_load(&Q, pubkey)) {
        ret = secp256k1_eckey_pubkey_serialize(&Q, output, &len);
        if (ret) {
            *outputlen = len;
        }
    }
    return ret;
}

/* Converts the point encoded by a secp256k1_pubkey into its absolute value,
 * i.e. keeps it as is if it is positive and otherwise negates it. Sign is set
 * to 1 if the input point was negative and set to 0 otherwise. */
static void secp256k1_ec_pubkey_absolute(secp256k1_pubkey *pubkey, int *sign) {
   secp256k1_ge ge;
    secp256k1_pubkey_load(&ge, pubkey);
    if (sign != NULL) {
        *sign = 0;
    }
    if (!secp256k1_fe_is_quad_var(&ge.y)) {
        secp256k1_ge_neg(&ge, &ge);
        if (sign != NULL) {
            *sign = 1;
        }
    }
    secp256k1_pubkey_save(pubkey, &ge);
}

static int secp256k1_xonly_pubkey_parse(secp256k1_xonly_pubkey* pubkey, const unsigned char *input32) {
    /* TODO parse directly from 32 byte buffer */
    unsigned char buf[33];
    ARG_CHECK(pubkey != NULL);
    ARG_CHECK(input32 != NULL);

    buf[0] = SECP256K1_TAG_PUBKEY_EVEN;
    memcpy(&buf[1], input32, 32);
    if (!secp256k1_ec_pubkey_parse((secp256k1_pubkey *) pubkey, buf, sizeof(buf))) {
        return 0;
    }
    secp256k1_ec_pubkey_absolute((secp256k1_pubkey *) pubkey, NULL);
    return 1;
}

static int secp256k1_xonly_pubkey_serialize(unsigned char *output32, const secp256k1_xonly_pubkey* pubkey) {
    /* TODO serialize directly into 32 byte buffer */
    unsigned char buf[33];
    size_t outputlen = sizeof(buf);
    ARG_CHECK(pubkey != NULL);
    ARG_CHECK(output32 != NULL);

    if (!secp256k1_ec_pubkey_serialize(buf, &outputlen, (const secp256k1_pubkey *) pubkey)) {
        return 0;
    }
    memcpy(output32, &buf[1], 32);
    return 1;
}


#include "schnorrsig_impl.h"

#endif
