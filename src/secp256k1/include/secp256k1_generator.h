#ifndef SECP256K1_GENERATOR_H
# define SECP256K1_GENERATOR_H

# include "secp256k1.h"

# ifdef __cplusplus
extern "C" {
# endif

#include <stdint.h>

/** Opaque data structure that stores a base point
 *
 *  The exact representation of data inside is implementation defined and not
 *  guaranteed to be portable between different platforms or versions. It is
 *  however guaranteed to be 64 bytes in size, and can be safely copied/moved.
 *  If you need to convert to a format suitable for storage, transmission, or
 *  comparison, use secp256k1_generator_serialize and secp256k1_generator_parse.
 */
typedef struct {
    unsigned char data[64];
} secp256k1_generator;

/**
 * Static constant generator 'h' maintained for historical reasons.
 */
SECP256K1_API const secp256k1_generator *secp256k1_generator_h;

/** Parse a 33-byte generator byte sequence into a generator object.
 *
 *  Returns: 1 if input contains a valid generator.
 *  Args: ctx:      a secp256k1 context object.
 *  Out:  gen:      pointer to the output generator object
 *  In:   input:    pointer to a 33-byte serialized generator
 */
SECP256K1_API SECP256K1_WARN_UNUSED_RESULT int secp256k1_generator_parse(
    const secp256k1_context *ctx,
    secp256k1_generator *gen,
    const unsigned char *input
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3);

/** Serialize a 33-byte generator into a serialized byte sequence.
 *
 *  Returns: 1 always.
 *  Args:   ctx:        a secp256k1 context object.
 *  Out:    output:     a pointer to a 33-byte byte array
 *  In:     gen:        a pointer to a generator
 */
SECP256K1_API int secp256k1_generator_serialize(
    const secp256k1_context *ctx,
    unsigned char *output,
    const secp256k1_generator *gen
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3);

/** Generate a generator for the curve.
 *
 *  Returns: 0 in the highly unlikely case the seed is not acceptable,
 *           1 otherwise.
 *  Args: ctx:     a secp256k1 context object
 *  Out:  gen:     a generator object
 *  In:   seed32:  a 32-byte seed
 *
 *  If successful a valid generator will be placed in gen. The produced
 *  generators are distributed uniformly over the curve, and will not have a
 *  known discrete logarithm with respect to any other generator produced,
 *  or to the base generator G.
 */
SECP256K1_API SECP256K1_WARN_UNUSED_RESULT int secp256k1_generator_generate(
    const secp256k1_context *ctx,
    secp256k1_generator *gen,
    const unsigned char *seed32
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3);

/** Generate a blinded generator for the curve.
 *
 *  Returns: 0 in the highly unlikely case the seed is not acceptable or when
 *           blind is out of range. 1 otherwise.
 *  Args: ctx:     a secp256k1 context object (not secp256k1_context_static)
 *  Out:  gen:     a generator object
 *  In:   seed32:  a 32-byte seed
 *        blind32: a 32-byte secret value to blind the generator with.
 *
 *  The result is equivalent to first calling secp256k1_generator_generate,
 *  converting the result to a public key, calling secp256k1_ec_pubkey_tweak_add,
 *  and then converting back to generator form.
 */
SECP256K1_API SECP256K1_WARN_UNUSED_RESULT int secp256k1_generator_generate_blinded(
    const secp256k1_context *ctx,
    secp256k1_generator *gen,
    const unsigned char *seed32,
    const unsigned char *blind32
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3) SECP256K1_ARG_NONNULL(4);

/** Opaque data structure that stores a Pedersen commitment
 *
 *  The exact representation of data inside is implementation defined and not
 *  guaranteed to be portable between different platforms or versions. It is
 *  however guaranteed to be 64 bytes in size, and can be safely copied/moved.
 *  If you need to convert to a format suitable for storage, transmission, or
 *  comparison, use secp256k1_pedersen_commitment_serialize and
 *  secp256k1_pedersen_commitment_parse.
 */
typedef struct {
    unsigned char data[64];
} secp256k1_pedersen_commitment;

/** Parse a 33-byte commitment into a commitment object.
 *
 *  Returns: 1 if input contains a valid commitment.
 *  Args: ctx:      a secp256k1 context object.
 *  Out:  commit:   pointer to the output commitment object
 *  In:   input:    pointer to a 33-byte serialized commitment key
 */
SECP256K1_API SECP256K1_WARN_UNUSED_RESULT int secp256k1_pedersen_commitment_parse(
    const secp256k1_context *ctx,
    secp256k1_pedersen_commitment *commit,
    const unsigned char *input
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3);

/** Serialize a commitment object into a serialized byte sequence.
 *
 *  Returns: 1 always.
 *  Args:   ctx:        a secp256k1 context object.
 *  Out:    output:     a pointer to a 33-byte byte array
 *  In:     commit:     a pointer to a secp256k1_pedersen_commitment containing an
 *                      initialized commitment
 */
SECP256K1_API int secp256k1_pedersen_commitment_serialize(
    const secp256k1_context *ctx,
    unsigned char *output,
    const secp256k1_pedersen_commitment *commit
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3);

/** Generate a pedersen commitment.
 *  Returns 1: Commitment successfully created.
 *          0: Error. The blinding factor is larger than the group order
 *             (probability for random 32 byte number < 2^-127) or results in the
 *             point at infinity. Retry with a different factor.
 *  In:     ctx:        pointer to a context object (not secp256k1_context_static)
 *          blind:      pointer to a 32-byte blinding factor (cannot be NULL)
 *          value:      unsigned 64-bit integer value to commit to.
 *          gen:        additional generator 'h'
 *  Out:    commit:     pointer to the commitment (cannot be NULL)
 *
 *  Blinding factors can be generated and verified in the same way as secp256k1 private keys for ECDSA.
 */
SECP256K1_API SECP256K1_WARN_UNUSED_RESULT int secp256k1_pedersen_commit(
  const secp256k1_context *ctx,
  secp256k1_pedersen_commitment *commit,
  const unsigned char *blind,
  uint64_t value,
  const secp256k1_generator *gen
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3) SECP256K1_ARG_NONNULL(5);

/** Computes the sum of multiple positive and negative blinding factors.
 *  Returns 1: Sum successfully computed.
 *          0: Error. A blinding factor is larger than the group order
 *             (probability for random 32 byte number < 2^-127). Retry with
 *             different factors.
 *  In:     ctx:        pointer to a context object (cannot be NULL)
 *          blinds:     pointer to pointers to 32-byte character arrays for blinding factors. (cannot be NULL)
 *          n:          number of factors pointed to by blinds.
 *          npositive:       how many of the initial factors should be treated with a positive sign.
 *  Out:    blind_out:  pointer to a 32-byte array for the sum (cannot be NULL)
 */
SECP256K1_API SECP256K1_WARN_UNUSED_RESULT int secp256k1_pedersen_blind_sum(
  const secp256k1_context *ctx,
  unsigned char *blind_out,
  const unsigned char * const *blinds,
  size_t n,
  size_t npositive
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3);

/** Verify a tally of pedersen commitments
 * Returns 1: commitments successfully sum to zero.
 *         0: Commitments do not sum to zero or other error.
 * In:     ctx:        pointer to a context object (cannot be NULL)
 *         commits:    pointer to array of pointers to the commitments. (cannot be NULL if pcnt is non-zero)
 *         pcnt:       number of commitments pointed to by commits.
 *         ncommits:   pointer to array of pointers to the negative commitments. (cannot be NULL if ncnt is non-zero)
 *         ncnt:       number of commitments pointed to by ncommits.
 *
 * This computes sum(commit[0..pcnt)) - sum(ncommit[0..ncnt)) == 0.
 *
 * A pedersen commitment is xG + vA where G and A are generators for the secp256k1 group and x is a blinding factor,
 * while v is the committed value. For a collection of commitments to sum to zero, for each distinct generator
 * A all blinding factors and all values must sum to zero.
 *
 */
SECP256K1_API SECP256K1_WARN_UNUSED_RESULT int secp256k1_pedersen_verify_tally(
  const secp256k1_context *ctx,
  const secp256k1_pedersen_commitment * const *commits,
  size_t pcnt,
  const secp256k1_pedersen_commitment * const *ncommits,
  size_t ncnt
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(4);

/** Sets the final Pedersen blinding factor correctly when the generators themselves
 *  have blinding factors.
 *
 * Consider a generator of the form A' = A + rG, where A is the "real" generator
 * but A' is the generator provided to verifiers. Then a Pedersen commitment
 * P = vA' + r'G really has the form vA + (vr + r')G. To get all these (vr + r')
 * to sum to zero for multiple commitments, we take three arrays consisting of
 * the `v`s, `r`s, and `r'`s, respectively called `value`s, `generator_blind`s
 * and `blinding_factor`s, and sum them.
 *
 * The function then subtracts the sum of all (vr + r') from the last element
 * of the `blinding_factor` array, setting the total sum to zero.
 *
 * Returns 1: Blinding factor successfully computed.
 *         0: Error. A blinding_factor or generator_blind are larger than the group
 *            order (probability for random 32 byte number < 2^-127). Retry with
 *            different values.
 *
 * In:                 ctx: pointer to a context object
 *                   value: array of asset values, `v` in the above paragraph.
 *                          May not be NULL unless `n_total` is 0.
 *         generator_blind: array of asset blinding factors, `r` in the above paragraph
 *                          May not be NULL unless `n_total` is 0.
 *                 n_total: Total size of the above arrays
 *                n_inputs: How many of the initial array elements represent commitments that
 *                          will be negated in the final sum
 * In/Out: blinding_factor: array of commitment blinding factors, `r'` in the above paragraph
 *                          May not be NULL unless `n_total` is 0.
 *                          the last value will be modified to get the total sum to zero.
 */
SECP256K1_API SECP256K1_WARN_UNUSED_RESULT int secp256k1_pedersen_blind_generator_blind_sum(
  const secp256k1_context *ctx,
  const uint64_t *value,
  const unsigned char * const *generator_blind,
  unsigned char * const *blinding_factor,
  size_t n_total,
  size_t n_inputs
);

# ifdef __cplusplus
}
# endif

#endif
