#ifndef SIMPLICITY_PRIMITIVE_ELEMENTS_CHECKSIGHASHALLTX1_H
#define SIMPLICITY_PRIMITIVE_ELEMENTS_CHECKSIGHASHALLTX1_H

#include <stddef.h>
#include <stdint.h>
#include "../../bounded.h"

/* A length-prefixed encoding of the following Simplicity program:
 *     Simplicity.Programs.CheckSig.Lib.checkSigVerify' Simplicity.Elements.Programs.SigHash.Lib.sigAllHash
 *     (Simplicity.LibSecp256k1.Spec.PubKey 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63)
 *     (Simplicity.LibSecp256k1.Spec.Sig 0x00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c63
 *                                       0xc39e232878352e9964f8b6bcae5a0cbc079320819bd1c2c23278d8c9e155e6f4)
 * with jets.
 */
extern const unsigned char elementsCheckSigHashAllTx1[];
extern const size_t sizeof_elementsCheckSigHashAllTx1;
extern const unsigned char elementsCheckSigHashAllTx1_witness[];
extern const size_t sizeof_elementsCheckSigHashAllTx1_witness;

/* The commitment Merkle root of the above elementsCheckSigHashAllTx1 Simplicity expression. */
extern const uint32_t elementsCheckSigHashAllTx1_cmr[];

/* The identity Merkle root of the above elementsCheckSigHashAllTx1 Simplicity expression. */
extern const uint32_t elementsCheckSigHashAllTx1_imr[];

/* The annotated Merkle root of the above elementsCheckSigHashAllTx1 Simplicity expression. */
extern const uint32_t elementsCheckSigHashAllTx1_amr[];

/* The cost of the above elementsCheckSigHashAllTx1 Simplicity expression in milli weight units. */
extern const ubounded elementsCheckSigHashAllTx1_cost;

#endif
