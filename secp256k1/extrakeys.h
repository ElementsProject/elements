#ifndef SECP256K1_EXTRAKEYS_H
#define SECP256K1_EXTRAKEYS_H

#include "secp256k1.h"

/** Opaque data structure that holds a parsed and valid "x-only" public key.
 *  An x-only pubkey encodes a point whose Y coordinate is even. It is
 *  serialized using only its X coordinate (32 bytes). See BIP-340 for more
 *  information about x-only pubkeys.
 *
 *  The exact representation of data inside is implementation defined and not
 *  guaranteed to be portable between different platforms or versions. It is
 *  however guaranteed to be 64 bytes in size, and can be safely copied/moved.
 *  If you need to convert to a format suitable for storage, transmission, use
 *  use secp256k1_xonly_pubkey_serialize and secp256k1_xonly_pubkey_parse. To
 *  compare keys, use secp256k1_xonly_pubkey_cmp.
 */
typedef struct {
    unsigned char data[64];
} secp256k1_xonly_pubkey;

/** Parse a 32-byte sequence into a xonly_pubkey object.
 *
 *  Returns: 1 if the public key was fully valid.
 *           0 if the public key could not be parsed or is invalid.
 *
 *  Out: pubkey: pointer to a pubkey object. If 1 is returned, it is set to a
 *               parsed version of input. If not, it's set to an invalid value.
 *  In: input32: pointer to a serialized xonly_pubkey.
 */
static SECP256K1_WARN_UNUSED_RESULT int secp256k1_xonly_pubkey_parse(
    secp256k1_xonly_pubkey* pubkey,
    const unsigned char *input32
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2);

#endif /* SECP256K1_EXTRAKEYS_H */
