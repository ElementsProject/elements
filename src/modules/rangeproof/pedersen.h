/**********************************************************************
 * Copyright (c) 2014, 2015 Gregory Maxwell                          *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef _SECP256K1_PEDERSEN_H_
#define _SECP256K1_PEDERSEN_H_

#include "group.h"
#include "scalar.h"

#include <stdint.h>

typedef struct {
    secp256k1_ge_storage_t (*prec)[16][16]; /* prec[j][i] = 16^j * i * G + U_i */
} secp256k1_pedersen_context_t;

static void secp256k1_pedersen_context_init(secp256k1_pedersen_context_t* ctx);
static void secp256k1_pedersen_context_build(secp256k1_pedersen_context_t* ctx, const callback_t* cb);
static void secp256k1_pedersen_context_clone(secp256k1_pedersen_context_t *dst,
                                               const secp256k1_pedersen_context_t* src, const callback_t* cb);
static void secp256k1_pedersen_context_clear(secp256k1_pedersen_context_t* ctx);

static int secp256k1_pedersen_context_is_built(const secp256k1_pedersen_context_t* ctx);

/** Multiply a small number with the generator: r = gn*G2 */
static void secp256k1_pedersen_ecmult_small(const secp256k1_pedersen_context_t *ctx, secp256k1_gej_t *r, uint64_t gn);

/* sec * G + value * G2. */
static void secp256k1_pedersen_ecmult(const secp256k1_ecmult_gen_context_t *ecmult_gen_ctx,
 const secp256k1_pedersen_context_t *pedersen_ctx, secp256k1_gej_t *rj, const secp256k1_scalar_t *sec, uint64_t value);

#endif
