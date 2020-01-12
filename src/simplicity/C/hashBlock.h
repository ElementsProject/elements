#ifndef HASHBLOCK_H
#define HASHBLOCK_H

#include <stddef.h>
#include <stdint.h>

/* A length-prefixed encoding of the SHA-256 compression function written in Simplicity.
 *
 * Invariant: unsigned char hashBlock[sizeof_hashBlock]
 */
extern const unsigned char hashBlock[];
extern const size_t sizeof_hashBlock;

/* The commitment Merkle root of the above hashBlock Simplicity expression. */
extern const uint32_t hashBlock_cmr[];

/* The witness Merkle root of the above hashBlock Simplicity expression. */
extern const uint32_t hashBlock_wmr[];

#endif
