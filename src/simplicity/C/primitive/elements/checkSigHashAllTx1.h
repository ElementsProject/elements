#ifndef PRIMITIVE_ELEMENTS_CHECKSIGHASHALLTX1_H
#define PRIMITIVE_ELEMENTS_CHECKSIGHASHALLTX1_H

#include <stddef.h>
#include <stdint.h>

/* A length-prefixed encoding of the following Simplicity program:
 *       (Simplicity.Elements.Programs.CheckSigHashAll.Lib.pkwCheckSigHashAll
 *         (PubKey 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63)
 *         (Sig 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63
 *              0x7d0fbcf693ee43460b86b587111e5087d9f7386c1c49284fb2f8e5c096a339b8
 *       ) )
 * with jets.
 */
extern const unsigned char elementsCheckSigHashAllTx1[];
extern const size_t sizeof_elementsCheckSigHashAllTx1;


/* The commitment Merkle root of the above elementsCheckSigHashAllTx1 Simplicity expression. */
extern const uint32_t elementsCheckSigHashAllTx1_cmr[];

/* The witness Merkle root of the above elementsCheckSigHashAllTx1 Simplicity expression. */
extern const uint32_t elementsCheckSigHashAllTx1_wmr[];

#endif
