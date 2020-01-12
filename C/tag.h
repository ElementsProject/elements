#ifndef TAG_H
#define TAG_H

#include <string.h>
#include "sha256/compression.h"
#include "ascii.h"

/* The length of a string literal is one less than its sizeof due to the terminating 'NULL' character. */
#define LENGTH_OF(s) (sizeof("" s) - 1)

/* The number of bytes that fits in a single SHA-256 block is 55 bytes.
 * This leaves one byte for the '0x80' terminator and eight bytes for the 64-bit length field.
 */
#define MAX_TAG_LEN 55

/* Compute the SHA-256 value (with padding) of a 'tagName' and return the SHA-256 midstate for that hash.
 * The 'tagName' must fit into a single SHA-256 block meaning it cannot exceed 55 ('MAX_TAG_LEN') bytes.
 * The 'tagName' is not expected to be 'NULL' terminated.
 * This function should only be called through the 'MK_TAG' macro.
 *
 * Precondition: uint32 midstate[8];
 *               unsigned char tagName[len];
 *               len <= MAX_TAG_LEN (= 55)
 */
static inline void mkTag(uint32_t* midstate, const unsigned char* tagName, const size_t len) {
  unsigned char block[64] = {0};

  memcpy(block, tagName, len);
  block[len] = 0x80;
  /* The length of tag (in bits) is guarenteed to fit within two bytes. */
  block[63] = (len << 3) & 0xff;
  block[62] = (len >> 5) & 0xff;

  sha256_iv(midstate);
  sha256_compression_uchar(midstate, block);
}

/* TAG_NAME(s) takes a string literal, verifies its length is less than 'MAX_TAG_LEN', and removes the trailing NULL character. */
#define TAG_NAME(s) (((struct { const unsigned char name[LENGTH_OF(s)]; _Static_assert(LENGTH_OF(s) <= MAX_TAG_LEN, "Tag Name too long: " s); }){ .name = "" s }).name)

/* MK_TAG(midstate, s) takes a string literal, 's', and fills in the 'tag' and 'len' arguments of 'mkTag' appropriately. */
#define MK_TAG(midstate, s) (mkTag((midstate), TAG_NAME(s), LENGTH_OF(s)))

#endif
