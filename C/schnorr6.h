#ifndef SCHNORR6_H
#define SCHNORR6_H

#include <stddef.h>
#include <stdint.h>

/* A length-prefixed encoding of the following Simplicity program:
 *     (scribe (toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659) &&&
 *      scribe (toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89)) &&&
 *      witness (toWord512 0xF9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9935554D1AA5F0374E5CDAACB3925035C7C169B27C4426DF0A6B19AF3BAEAB138) >>>
 *     schnorrAssert
 * with jets.
 */
extern const unsigned char schnorr6[];
extern const size_t sizeof_schnorr6;

/* The commitment Merkle root of the above schnorr6 Simplicity expression. */
extern const uint32_t schnorr6_cmr[];

/* The annotated Merkle root of the above schnorr6 Simplicity expression. */
extern const uint32_t schnorr6_amr[];

#endif
