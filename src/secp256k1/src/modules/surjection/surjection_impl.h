/**********************************************************************
 * Copyright (c) 2016 Andrew Poelstra                                 *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef SECP256K1_SURJECTION_IMPL_H
#define SECP256K1_SURJECTION_IMPL_H

#include <assert.h>
#include <string.h>

#include "../../eckey.h"
#include "../../group.h"
#include "../../scalar.h"
#include "../../hash.h"

SECP256K1_INLINE static void secp256k1_surjection_genmessage(const secp256k1_hash_ctx *hash_ctx, unsigned char *msg32, const secp256k1_generator *ephemeral_input_tags, size_t n_input_tags, const secp256k1_generator *ephemeral_output_tag) {
    /* compute message */
    size_t i;
    unsigned char pk_ser[33];
    size_t pk_len = sizeof(pk_ser);
    secp256k1_sha256 sha256_en;

    secp256k1_sha256_initialize(&sha256_en);
    for (i = 0; i < n_input_tags; i++) {
        pk_ser[0] = 2 + (ephemeral_input_tags[i].data[63] & 1);
        memcpy(&pk_ser[1], &ephemeral_input_tags[i].data[0], 32);
        secp256k1_sha256_write(hash_ctx, &sha256_en, pk_ser, pk_len);
    }
    pk_ser[0] = 2 + (ephemeral_output_tag->data[63] & 1);
    memcpy(&pk_ser[1], &ephemeral_output_tag->data[0], 32);
    secp256k1_sha256_write(hash_ctx, &sha256_en, pk_ser, pk_len);
    secp256k1_sha256_finalize(hash_ctx, &sha256_en, msg32);
    secp256k1_sha256_clear(&sha256_en);
}

/* Derive the ring's s-values, one of which is used as the signing nonce, from a
 * seed that hashes the passed-in arguments. See the call site for how these
 * correspond to the proof inputs. */
SECP256K1_INLINE static int secp256k1_surjection_genrand(const secp256k1_hash_ctx *hash_ctx, secp256k1_scalar *s, size_t ns, size_t n_inputs, const unsigned char *used_inputs, const unsigned char *msg32, size_t input_index, const unsigned char *input_blinding_key, const unsigned char *output_blinding_key) {
    size_t i;
    size_t used_inputs_len;
    unsigned char n_inputs_ser[4];
    unsigned char index_ser[4];
    unsigned char counter[4];
    unsigned char seed[32];
    unsigned char out[32];
    secp256k1_sha256 sha256_en;

    used_inputs_len = (n_inputs + 7) / 8;
    secp256k1_write_be32(n_inputs_ser, (uint32_t)n_inputs);
    secp256k1_write_be32(index_ser, (uint32_t)input_index);

    /* Hash the arguments into the seed. */
    secp256k1_sha256_initialize(&sha256_en);
    secp256k1_sha256_write(hash_ctx, &sha256_en, n_inputs_ser, 4);
    secp256k1_sha256_write(hash_ctx, &sha256_en, used_inputs, used_inputs_len);
    secp256k1_sha256_write(hash_ctx, &sha256_en, msg32, 32);
    secp256k1_sha256_write(hash_ctx, &sha256_en, index_ser, 4);
    secp256k1_sha256_write(hash_ctx, &sha256_en, input_blinding_key, 32);
    secp256k1_sha256_write(hash_ctx, &sha256_en, output_blinding_key, 32);
    secp256k1_sha256_finalize(hash_ctx, &sha256_en, seed);
    secp256k1_sha256_clear(&sha256_en);

    /* compute s values */
    for (i = 0; i < ns; i++) {
        int overflow = 0;
        secp256k1_write_be32(counter, (uint32_t)i);
        secp256k1_sha256_initialize(&sha256_en);
        secp256k1_sha256_write(hash_ctx, &sha256_en, counter, 4);
        secp256k1_sha256_write(hash_ctx, &sha256_en, seed, 32);
        secp256k1_sha256_finalize(hash_ctx, &sha256_en, out);
        secp256k1_sha256_clear(&sha256_en);
        secp256k1_scalar_set_b32(&s[i], out, &overflow);
        if (overflow == 1) {
            secp256k1_memclear_explicit(out, sizeof(out));
            secp256k1_memclear_explicit(seed, sizeof(seed));
            return 0;
        }
    }
    secp256k1_memclear_explicit(out, sizeof(out));
    secp256k1_memclear_explicit(seed, sizeof(seed));
    return 1;
}

SECP256K1_INLINE static int secp256k1_surjection_compute_public_keys(secp256k1_gej *pubkeys, size_t n_pubkeys, const secp256k1_generator *input_tags, size_t n_input_tags, const unsigned char *used_tags, const secp256k1_generator *output_tag, size_t input_index, size_t *ring_input_index) {
    size_t i;
    size_t j = 0;
    for (i = 0; i < n_input_tags; i++) {
        if (used_tags[i / 8] & (1 << (i % 8))) {
            secp256k1_ge tmpge;
            secp256k1_generator_load(&tmpge, &input_tags[i]);
            secp256k1_ge_neg(&tmpge, &tmpge);

            VERIFY_CHECK(j < SECP256K1_SURJECTIONPROOF_MAX_USED_INPUTS);
            VERIFY_CHECK(j < n_pubkeys);
            secp256k1_gej_set_ge(&pubkeys[j], &tmpge);

            secp256k1_generator_load(&tmpge, output_tag);
            secp256k1_gej_add_ge_var(&pubkeys[j], &pubkeys[j], &tmpge, NULL);
            if (ring_input_index != NULL && input_index == i) {
                *ring_input_index = j;
            }
            j++;
        }
    }
#ifdef VERIFY
    /* Caller needs to ensure that the number of set bits in used_tags (which we counted in j) equals n_pubkeys. */
    VERIFY_CHECK(j == n_pubkeys);
#else
    (void)n_pubkeys;
#endif
    return 1;
}


#endif
