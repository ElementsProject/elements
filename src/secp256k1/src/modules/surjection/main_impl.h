/**********************************************************************
 * Copyright (c) 2016 Andrew Poelstra                                 *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/
#ifndef SECP256K1_MODULE_SURJECTION_MAIN
#define SECP256K1_MODULE_SURJECTION_MAIN

#include <assert.h>
#include <string.h>

#include "modules/rangeproof/borromean.h"
#include "modules/surjection/surjection_impl.h"
#include "hash.h"
#include "include/secp256k1_rangeproof.h"
#include "include/secp256k1_surjectionproof.h"

static size_t secp256k1_count_bits_set(const unsigned char* data, size_t count) {
    size_t ret = 0;
    size_t i;
    for (i = 0; i < count; i++) {
#ifdef HAVE_BUILTIN_POPCOUNT
	ret += __builtin_popcount(data[i]);
#else
        ret += !!(data[i] & 0x1);
        ret += !!(data[i] & 0x2);
        ret += !!(data[i] & 0x4);
        ret += !!(data[i] & 0x8);
        ret += !!(data[i] & 0x10);
        ret += !!(data[i] & 0x20);
        ret += !!(data[i] & 0x40);
        ret += !!(data[i] & 0x80);
#endif
    }
    return ret;
}

int secp256k1_surjectionproof_parse(const secp256k1_context* ctx, secp256k1_surjectionproof *proof, const unsigned char *input, size_t inputlen) {
    size_t n_inputs;
    size_t signature_len;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(proof != NULL);
    ARG_CHECK(input != NULL);
    (void) ctx;

    if (inputlen < 2) {
        return 0;
    }
    n_inputs = ((size_t) (input[1] << 8)) + input[0];
    if (n_inputs > SECP256K1_SURJECTIONPROOF_MAX_N_INPUTS) {
        return 0;
    }
    if (inputlen < 2 + (n_inputs + 7) / 8) {
        return 0;
    }

    signature_len = 32 * (1 + secp256k1_count_bits_set(&input[2], (n_inputs + 7) / 8));
    if (inputlen < 2 + (n_inputs + 7) / 8 + signature_len) {
        return 0;
    }
    proof->n_inputs = n_inputs;
    memcpy(proof->used_inputs, &input[2], (n_inputs + 7) / 8);
    memcpy(proof->data, &input[2 + (n_inputs + 7) / 8], signature_len);

    return 1;
}

int secp256k1_surjectionproof_serialize(const secp256k1_context* ctx, unsigned char *output, size_t *outputlen, const secp256k1_surjectionproof *proof) {
    size_t signature_len;
    size_t serialized_len;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(output != NULL);
    ARG_CHECK(outputlen != NULL);
    ARG_CHECK(proof != NULL);
    (void) ctx;

    signature_len = 32 * (1 + secp256k1_count_bits_set(proof->used_inputs, (proof->n_inputs + 7) / 8));
    serialized_len = 2 + (proof->n_inputs + 7) / 8 + signature_len;
    if (*outputlen < serialized_len) {
        return 0;
    }

    output[0] = proof->n_inputs % 0x100;
    output[1] = proof->n_inputs / 0x100;
    memcpy(&output[2], proof->used_inputs, (proof->n_inputs + 7) / 8);
    memcpy(&output[2 + (proof->n_inputs + 7) / 8], proof->data, signature_len);
    *outputlen = serialized_len;

    return 1;
}

size_t secp256k1_surjectionproof_n_total_inputs(const secp256k1_context* ctx, const secp256k1_surjectionproof* proof) {
    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(proof != NULL);
    (void) ctx;
    return proof->n_inputs;
}

size_t secp256k1_surjectionproof_n_used_inputs(const secp256k1_context* ctx, const secp256k1_surjectionproof* proof) {
    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(proof != NULL);
    (void) ctx;
    return secp256k1_count_bits_set(proof->used_inputs, (proof->n_inputs + 7) / 8);
}

size_t secp256k1_surjectionproof_serialized_size(const secp256k1_context* ctx, const secp256k1_surjectionproof* proof) {
    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(proof != NULL);
    return 2 + (proof->n_inputs + 7) / 8 + 32 * (1 + secp256k1_surjectionproof_n_used_inputs(ctx, proof));
}

typedef struct {
    unsigned char state[32];
    size_t state_i;
} secp256k1_surjectionproof_csprng;

static void secp256k1_surjectionproof_csprng_init(secp256k1_surjectionproof_csprng *csprng, const unsigned char* state) {
    memcpy(csprng->state, state, 32);
    csprng->state_i = 0;
}

static size_t secp256k1_surjectionproof_csprng_next(secp256k1_surjectionproof_csprng *csprng, size_t rand_max) {
    /* The number of random bytes to read for each random sample */
    const size_t increment = rand_max > 256 ? 2 : 1;
    /* The maximum value expressable by the number of random bytes we read */
    const size_t selection_range = rand_max > 256 ? 0xffff : 0xff;
    /* The largest multiple of rand_max that fits within selection_range */
    const size_t limit = ((selection_range + 1) / rand_max) * rand_max;

    while (1) {
        size_t val;
        if (csprng->state_i + increment >= 32) {
            secp256k1_sha256_t sha;
            secp256k1_sha256_initialize(&sha);
            secp256k1_sha256_write(&sha, csprng->state, 32);
            secp256k1_sha256_finalize(&sha, csprng->state);
            csprng->state_i = 0;
        }
        val = csprng->state[csprng->state_i];
        if (increment > 1) {
            val = (val << 8) + csprng->state[csprng->state_i + 1];
        }
        csprng->state_i += increment;
        /* Accept only values below our limit. Values equal to or above the limit are
         * biased because they comprise only a subset of the range (0, rand_max - 1) */
        if (val < limit) {
            return val % rand_max;
        }
    }
}

int secp256k1_surjectionproof_initialize(const secp256k1_context* ctx, secp256k1_surjectionproof* proof, size_t *input_index, const secp256k1_fixed_asset_tag* fixed_input_tags, const size_t n_input_tags, const size_t n_input_tags_to_use, const secp256k1_fixed_asset_tag* fixed_output_tag, const size_t n_max_iterations, const unsigned char *random_seed32) {
    secp256k1_surjectionproof_csprng csprng;
    size_t n_iterations = 0;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(proof != NULL);
    ARG_CHECK(input_index != NULL);
    ARG_CHECK(fixed_input_tags != NULL);
    ARG_CHECK(fixed_output_tag != NULL);
    ARG_CHECK(random_seed32 != NULL);
    ARG_CHECK(n_input_tags <= SECP256K1_SURJECTIONPROOF_MAX_N_INPUTS);
    ARG_CHECK(n_input_tags_to_use <= n_input_tags);
    (void) ctx;

    secp256k1_surjectionproof_csprng_init(&csprng, random_seed32);
    memset(proof->data, 0, sizeof(proof->data));
    proof->n_inputs = n_input_tags;

    while (1) {
        int has_output_tag = 0;
        size_t i;

        /* obtain a random set of indices */
        memset(proof->used_inputs, 0, sizeof(proof->used_inputs));
        for (i = 0; i < n_input_tags_to_use; i++) {
            while (1) {
                size_t next_input_index;
                next_input_index = secp256k1_surjectionproof_csprng_next(&csprng, n_input_tags);
                if (memcmp(&fixed_input_tags[next_input_index], fixed_output_tag, sizeof(*fixed_output_tag)) == 0) {
                    *input_index = next_input_index;
                    has_output_tag = 1;
                }

                if (!(proof->used_inputs[next_input_index / 8] & (1 << (next_input_index  % 8)))) {
                    proof->used_inputs[next_input_index / 8] |= (1 << (next_input_index % 8));
                    break;
                }
            }
        }

        /* Check if we succeeded */
        n_iterations++;
        if (has_output_tag) {
#ifdef VERIFY
            proof->initialized = 1;
#endif
            return n_iterations;
        }
        if (n_iterations >= n_max_iterations) {
#ifdef VERIFY
            proof->initialized = 0;
#endif
            return 0;
        }
    }
}

int secp256k1_surjectionproof_generate(const secp256k1_context* ctx, secp256k1_surjectionproof* proof, const secp256k1_generator* ephemeral_input_tags, size_t n_ephemeral_input_tags, const secp256k1_generator* ephemeral_output_tag, size_t input_index, const unsigned char *input_blinding_key, const unsigned char *output_blinding_key) {
    secp256k1_scalar blinding_key;
    secp256k1_scalar tmps;
    secp256k1_scalar nonce;
    int overflow = 0;
    size_t rsizes[1];    /* array needed for borromean sig API */
    size_t indices[1];   /* array needed for borromean sig API */
    size_t i;
    size_t n_total_pubkeys;
    size_t n_used_pubkeys;
    size_t ring_input_index = 0;
    secp256k1_gej ring_pubkeys[SECP256K1_SURJECTIONPROOF_MAX_N_INPUTS];
    secp256k1_scalar borromean_s[SECP256K1_SURJECTIONPROOF_MAX_N_INPUTS];
    secp256k1_ge inputs[SECP256K1_SURJECTIONPROOF_MAX_N_INPUTS];
    secp256k1_ge output;
    unsigned char msg32[32];

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(secp256k1_ecmult_context_is_built(&ctx->ecmult_ctx));
    ARG_CHECK(secp256k1_ecmult_gen_context_is_built(&ctx->ecmult_gen_ctx));
    ARG_CHECK(proof != NULL);
    ARG_CHECK(ephemeral_input_tags != NULL);
    ARG_CHECK(ephemeral_output_tag != NULL);
    ARG_CHECK(input_blinding_key != NULL);
    ARG_CHECK(output_blinding_key != NULL);
#ifdef VERIFY
    CHECK(proof->initialized == 1);
#endif

    /* Compute secret key */
    secp256k1_scalar_set_b32(&tmps, input_blinding_key, &overflow);
    if (overflow) {
        return 0;
    }
    secp256k1_scalar_set_b32(&blinding_key, output_blinding_key, &overflow);
    if (overflow) {
        return 0;
    }
    /* The only time the input may equal the output is if neither one was blinded in the first place,
     * i.e. both blinding keys are zero. Otherwise this is a privacy leak. */
    if (secp256k1_scalar_eq(&tmps, &blinding_key) && !secp256k1_scalar_is_zero(&blinding_key)) {
        return 0;
    }
    secp256k1_scalar_negate(&tmps, &tmps);
    secp256k1_scalar_add(&blinding_key, &blinding_key, &tmps);

    /* Compute public keys */
    n_total_pubkeys = secp256k1_surjectionproof_n_total_inputs(ctx, proof);
    n_used_pubkeys = secp256k1_surjectionproof_n_used_inputs(ctx, proof);
    if (n_used_pubkeys > n_total_pubkeys || n_total_pubkeys != n_ephemeral_input_tags) {
        return 0;
    }

    secp256k1_generator_load(&output, ephemeral_output_tag);
    for (i = 0; i < n_total_pubkeys; i++) {
        secp256k1_generator_load(&inputs[i], &ephemeral_input_tags[i]);
    }

    secp256k1_surjection_compute_public_keys(ring_pubkeys, n_used_pubkeys, inputs, n_total_pubkeys, proof->used_inputs, &output, input_index, &ring_input_index);

    /* Produce signature */
    rsizes[0] = (int) n_used_pubkeys;
    indices[0] = (int) ring_input_index;
    secp256k1_surjection_genmessage(msg32, inputs, n_total_pubkeys, proof->used_inputs, &output);
    if (secp256k1_surjection_genrand(borromean_s, n_used_pubkeys, &blinding_key) == 0) {
        return 0;
    }
    /* Borromean sign will overwrite one of the s values we just generated, so use
     * it as a nonce instead. This avoids extra random generation and also is an
     * homage to the rangeproof code which does this very cleverly to encode messages. */
    nonce = borromean_s[ring_input_index];
    secp256k1_scalar_clear(&borromean_s[ring_input_index]);
    if (secp256k1_borromean_sign(&ctx->ecmult_ctx, &ctx->ecmult_gen_ctx, &proof->data[0], borromean_s, ring_pubkeys, &nonce, &blinding_key, rsizes, indices, 1, msg32, 32) == 0) {
        return 0;
    }
    for (i = 0; i < n_used_pubkeys; i++) {
        secp256k1_scalar_get_b32(&proof->data[32 + 32 * i], &borromean_s[i]);
    }
    return 1;
}

static int secp256k1_tag_cmp(const void *in1, const void *in2) {
    secp256k1_context *ctx = secp256k1_context_create(SECP256K1_CONTEXT_NONE);
    const secp256k1_fixed_asset_tag* tag1 = in1;
    const secp256k1_fixed_asset_tag* tag2 = in2;
    secp256k1_generator gen1;
    secp256k1_generator gen2;
    if (secp256k1_generator_generate(ctx, &gen1, tag1->data) == 0 ||
        secp256k1_generator_generate(ctx, &gen2, tag2->data) == 0) {
        return 1;
    }
    secp256k1_context_destroy(ctx);
    return memcmp(gen1.data, gen2.data, sizeof(gen1.data));
}

int secp256k1_surjectionproof_sort_tags(const secp256k1_context* ctx, secp256k1_fixed_asset_tag* tags, size_t n_tags) {
    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(tags != NULL);
    (void) ctx;
    qsort(tags, n_tags, sizeof(*tags), secp256k1_tag_cmp);
    return 1;
}

int secp256k1_surjectionproof_combine(const secp256k1_context* ctx, secp256k1_generator* tags, size_t *n_tags, secp256k1_surjectionproof* proof1, secp256k1_surjectionproof* proof2, const secp256k1_generator* input_tags1, size_t n_input_tags1, const secp256k1_generator* input_tags2, size_t n_input_tags2) {
    size_t l_idx, r_idx, o_idx;
    unsigned char used_inputs1[SECP256K1_SURJECTIONPROOF_MAX_N_INPUTS / 8] = { 0 };
    unsigned char used_inputs2[SECP256K1_SURJECTIONPROOF_MAX_N_INPUTS / 8] = { 0 };

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(tags != NULL);
    ARG_CHECK(n_tags != NULL);
    ARG_CHECK(proof1 != NULL);
    ARG_CHECK(proof2 != NULL);
    ARG_CHECK(input_tags1 != NULL);
    ARG_CHECK(n_input_tags1 <= SECP256K1_SURJECTIONPROOF_MAX_N_INPUTS);
    ARG_CHECK(n_input_tags2 <= SECP256K1_SURJECTIONPROOF_MAX_N_INPUTS);
    ARG_CHECK(input_tags2 != NULL);
    (void) ctx;

    l_idx = r_idx = o_idx = 0;
    while (1) {
        enum { USE_NONE, USE_L, USE_R, USE_BOTH } use = USE_NONE;

        if (l_idx < n_input_tags1 && r_idx < n_input_tags2) {
            int res = memcmp(input_tags1[l_idx].data, input_tags2[r_idx].data, sizeof(input_tags1[l_idx].data));
            if (res < 0) {
                use = USE_L;
            } else if (res > 0) {
                use = USE_R;
            } else {
                use = USE_BOTH;
            }
        } else if (l_idx < n_input_tags1) {
            use = USE_L;
        } else if (r_idx < n_input_tags1) {
            use = USE_R;
        } else {
            break;
        }

        if (o_idx >= *n_tags) {
            return 0;
        }

        switch (use) {
            case USE_NONE:
                VERIFY_CHECK(0);
                break;
            case USE_L:
            case USE_BOTH:
                if (proof1->used_inputs[l_idx / 8] & (1 << (l_idx % 8))) {
                    used_inputs1[o_idx / 8] |= 1 << (o_idx % 8);
                }
                memcpy(&tags[o_idx], &input_tags1[l_idx], sizeof(input_tags1[l_idx]));
                l_idx++;
                if (use == USE_BOTH) {
                    if (proof2->used_inputs[r_idx / 8] & (1 << (r_idx % 8))) {
                        used_inputs2[o_idx / 8] |= 1 << (o_idx % 8);
                    }
                    r_idx++;
                }
                break;
            case USE_R:
                if (proof2->used_inputs[r_idx / 8] & (1 << (r_idx % 8))) {
                    used_inputs2[o_idx / 8] |= 1 << (o_idx % 8);
                }
                memcpy(&tags[o_idx], &input_tags2[r_idx], sizeof(input_tags2[r_idx]));
                r_idx++;
                break;
        }
        o_idx++;
    }
    memcpy(proof1->used_inputs, used_inputs1, sizeof(used_inputs1));
    memcpy(proof2->used_inputs, used_inputs2, sizeof(used_inputs2));
    proof1->n_inputs = o_idx;
    proof2->n_inputs = o_idx;
    *n_tags = o_idx;

    return 1;
}


int secp256k1_surjectionproof_verify(const secp256k1_context* ctx, const secp256k1_surjectionproof* proof, const secp256k1_generator* ephemeral_input_tags, size_t n_ephemeral_input_tags, const secp256k1_generator* ephemeral_output_tag) {
    size_t rsizes[1];    /* array needed for borromean sig API */
    size_t i;
    size_t n_total_pubkeys;
    size_t n_used_pubkeys;
    secp256k1_gej ring_pubkeys[SECP256K1_SURJECTIONPROOF_MAX_N_INPUTS];
    secp256k1_scalar borromean_s[SECP256K1_SURJECTIONPROOF_MAX_N_INPUTS];
    secp256k1_ge inputs[SECP256K1_SURJECTIONPROOF_MAX_N_INPUTS];
    secp256k1_ge output;
    unsigned char msg32[32];

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(secp256k1_ecmult_context_is_built(&ctx->ecmult_ctx));
    ARG_CHECK(proof != NULL);
    ARG_CHECK(ephemeral_input_tags != NULL);
    ARG_CHECK(ephemeral_output_tag != NULL);

    /* Compute public keys */
    n_total_pubkeys = secp256k1_surjectionproof_n_total_inputs(ctx, proof);
    n_used_pubkeys = secp256k1_surjectionproof_n_used_inputs(ctx, proof);
    if (n_used_pubkeys == 0 || n_used_pubkeys > n_total_pubkeys || n_total_pubkeys != n_ephemeral_input_tags) {
        return 0;
    }

    secp256k1_generator_load(&output, ephemeral_output_tag);
    for (i = 0; i < n_total_pubkeys; i++) {
        secp256k1_generator_load(&inputs[i], &ephemeral_input_tags[i]);
    }

    if (secp256k1_surjection_compute_public_keys(ring_pubkeys, n_used_pubkeys, inputs, n_total_pubkeys, proof->used_inputs, &output, 0, NULL) == 0) {
        return 0;
    }

    /* Verify signature */
    rsizes[0] = (int) n_used_pubkeys;
    for (i = 0; i < n_used_pubkeys; i++) {
        int overflow = 0;
        secp256k1_scalar_set_b32(&borromean_s[i], &proof->data[32 + 32 * i], &overflow);
        if (overflow == 1) {
            return 0;
        }
    }
    secp256k1_surjection_genmessage(msg32, inputs, n_total_pubkeys, proof->used_inputs, &output);
    return secp256k1_borromean_verify(&ctx->ecmult_ctx, NULL, &proof->data[0], borromean_s, ring_pubkeys, rsizes, 1, msg32, 32);
}

#endif
