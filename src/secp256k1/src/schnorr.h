/***********************************************************************
 * Copyright (c) 2015 Pieter Wuille                                    *
 * Distributed under the MIT software license, see the accompanying    *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php. *
 ***********************************************************************/

#ifndef _SECP256K1_SCHNORR_
#define _SECP256K1_SCHNORR_

#include "scalar.h"
#include "group.h"

typedef void (*secp256k1_schnorr_msghash_t)(unsigned char *h32, const unsigned char *r32, const unsigned char *msg32);

#define SECP256K1_SCHNORR_MAX_BATCH (((SECP256K1_ECMULT_MAX_POINTS) + 1) / 2)

static int secp256k1_schnorr_sig_sign(const secp256k1_ecmult_gen_context_t* ctx, unsigned char *sig64, const secp256k1_scalar_t *key, const secp256k1_scalar_t *nonce, secp256k1_schnorr_msghash_t hash, const unsigned char *msg32);
static int secp256k1_schnorr_sig_verify(const secp256k1_ecmult_context_t* ctx, const unsigned char *sig64, const secp256k1_ge_t *pubkey, secp256k1_schnorr_msghash_t hash, const unsigned char *msg32);
static int secp256k1_schnorr_sig_verify_batch(const secp256k1_ecmult_context_t* ctx, int n, unsigned char (* const sig64)[64], const secp256k1_ge_t *pubkey, secp256k1_schnorr_msghash_t hash, const unsigned char *msg32);

#endif
