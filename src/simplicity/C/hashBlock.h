#ifndef SIMPLICITY_HASHBLOCK_H
#define SIMPLICITY_HASHBLOCK_H

#include <stddef.h>
#include <stdint.h>

/* A length-prefixed encoding of the following Simplicity program:
 *     hashBlock
 */
extern const unsigned char hashBlock[];
extern const size_t sizeof_hashBlock;

/* The commitment Merkle root of the above hashBlock Simplicity expression. */
extern const uint32_t hashBlock_cmr[];

/* The identity Merkle root of the above hashBlock Simplicity expression. */
extern const uint32_t hashBlock_imr[];

/* The annotated Merkle root of the above hashBlock Simplicity expression. */
extern const uint32_t hashBlock_amr[];

#endif
