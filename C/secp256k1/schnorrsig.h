#ifndef SCHNORRSIG_H
#define SCHNORRSIG_H

#include "secp256k1.h"

/** This module implements a variant of Schnorr signatures compliant with
 * BIP-schnorr
 * (https://github.com/sipa/bips/blob/bip-schnorr/bip-schnorr.mediawiki).
 */

/** Opaque data structure that holds a parsed Schnorr signature.
 *
 *  The exact representation of data inside is implementation defined and not
 *  guaranteed to be portable between different platforms or versions. It is
 *  however guaranteed to be 64 bytes in size, and can be safely copied/moved.
 *  If you need to convert to a format suitable for storage, transmission, or
 *  comparison, use the `secp256k1_schnorrsig_serialize` and
 *  `secp256k1_schnorrsig_parse` functions.
 */
typedef struct {
    unsigned char data[64];
} secp256k1_schnorrsig;

#if 0
/** Serialize a Schnorr signature.
 *
 *  Out:   out64: pointer to a 64-byte array to store the serialized signature
 *  In:      sig: pointer to the signature
 *
 *  See secp256k1_schnorrsig_parse for details about the encoding.
 */
static void secp256k1_schnorrsig_serialize(
    unsigned char *out64,
    const secp256k1_schnorrsig* sig
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2);
#endif

/** Parse a Schnorr signature.
 *
 *  Out:     sig: pointer to a signature object
 *  In:     in64: pointer to the 64-byte signature to be parsed
 *
 * The signature is serialized in the form R||s, where R is a 32-byte public
 * key (x-coordinate only; the y-coordinate is considered to be the unique
 * y-coordinate satisfying the curve equation that is a quadratic residue)
 * and s is a 32-byte big-endian scalar.
 */
static void secp256k1_schnorrsig_parse(
    secp256k1_schnorrsig* sig,
    const unsigned char *in64
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2);

/** Verify a Schnorr signature.
 *
 *  Returns: 1: correct signature
 *           0: incorrect or unparseable signature
 *  Args:    ctx: a secp256k1 ecmult context object.
 *  In:      sig: the signature being verified (cannot be NULL)
 *         msg32: the 32-byte message being verified (cannot be NULL)
 *        pubkey: pointer to an x-only public key to verify with (cannot be NULL)
 */
static SECP256K1_WARN_UNUSED_RESULT int secp256k1_schnorrsig_verify(
    const secp256k1_ecmult_context* ecmult_ctx,
    const secp256k1_schnorrsig *sig,
    const unsigned char *msg32,
    const secp256k1_xonly_pubkey *pubkey
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3) SECP256K1_ARG_NONNULL(4);

#endif /* SCHNORRSIG_H */
