#ifndef SCHNORR0_H
#define SCHNORR0_H

#include <stddef.h>
#include <stdint.h>

/* A length-prefixed encoding of the following Simplicity program:
 *     (scribe (toWord256 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798) &&&
 *      zero word256) &&&
 *      witness (toWord512 0x528F745793E8472C0329742A463F59E58F3A3F1A4AC09C28F6F8514D4D0322A258BD08398F82CF67B812AB2C7717CE566F877C2F8795C846146978E8F04782AE) >>>
 *     schnorrAssert
 * with jets.
 */
extern const unsigned char schnorr0[];
extern const size_t sizeof_schnorr0;

/* The commitment Merkle root of the above schnorr0 Simplicity expression. */
extern const uint32_t schnorr0_cmr[];

/* The annotated Merkle root of the above schnorr0 Simplicity expression. */
extern const uint32_t schnorr0_amr[];

#endif
