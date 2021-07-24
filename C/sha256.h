#ifndef SIMPLICITY_SHA256_H
#define SIMPLICITY_SHA256_H

#include <stdint.h>
#include <string.h>
#include "bitstring.h"

/* A struct holding the 256-bit array of a SHA-256 hash or midstate.
 */
typedef struct sha256_midstate {
  uint32_t s[8];
} sha256_midstate;

/* Packs (the 8 least significant bits of) 8 'unsigned char's into a 'uint_fast64_t' in "big endian" order.
 *
 * Precondition: unsigned char b[8]
 */
static inline uint_fast64_t ReadBE64(const unsigned char* b) {
  return (uint_fast64_t)(b[0] & 0xff) << 56
       | (uint_fast64_t)(b[1] & 0xff) << 48
       | (uint_fast64_t)(b[2] & 0xff) << 40
       | (uint_fast64_t)(b[3] & 0xff) << 32
       | (uint_fast64_t)(b[4] & 0xff) << 24
       | (uint_fast64_t)(b[5] & 0xff) << 16
       | (uint_fast64_t)(b[6] & 0xff) << 8
       | (uint_fast64_t)(b[7] & 0xff);
}

/* Packs (the 8 least significant bits of) 4 'unsigned char's into a 'uint32_t' in "big endian" order.
 *
 * Precondition: unsigned char b[4]
 */
static inline uint32_t ReadBE32(const unsigned char* b) {
  return (uint32_t)(b[0]) << 24
       | (uint32_t)(b[1] & 0xff) << 16
       | (uint32_t)(b[2] & 0xff) << 8
       | (uint32_t)(b[3] & 0xff);
}

/* Unpacks the 8 least significant bytes from a 'uint_fast64_t' into an 'unsigned char' array in "big endian" order.
 *
 * Precondition: unsigned char ptr[8]
 */
static inline void WriteBE64(unsigned char* ptr, uint_fast64_t x) {
  ptr[0] = (unsigned char)(0xff & x >> 56);
  ptr[1] = 0xff & x >> 48;
  ptr[2] = 0xff & x >> 40;
  ptr[3] = 0xff & x >> 32;
  ptr[4] = 0xff & x >> 24;
  ptr[5] = 0xff & x >> 16;
  ptr[6] = 0xff & x >> 8;
  ptr[7] = 0xff & x;
}

/* Unpacks 4 bytes from a 'uint32_t' into an 'unsigned char' array in "big endian" order.
 *
 * Precondition: unsigned char ptr[4]
 */
static inline void WriteBE32(unsigned char* ptr, uint32_t x) {
  ptr[0] = (unsigned char)(x >> 24);
  ptr[1] = (x >> 16) & 0xff;
  ptr[2] = (x >> 8) & 0xff;
  ptr[3] = x & 0xff;
}

/* Unpacks 4 bytes from a 'uint64_t' into an 'unsigned char' array in "little endian" order.
 *
 * Precondition: unsigned char ptr[4]
 */
static inline void WriteLE32(unsigned char* ptr, uint_fast32_t x) {
  ptr[3] = (unsigned char)(0xff & x >> 24);
  ptr[2] = 0xff & x >> 16;
  ptr[1] = 0xff & x >> 8;
  ptr[0] = 0xff & x;
}

/* Coverts a given 'midstate' value to a 'hash' value as 32 bytes stored in an unsigned char array.
 *
 * Precondition: unsigned char hash[32];
 *               uint32_t midstate[8]
 */
static inline void sha256_fromMidstate(unsigned char* hash, const uint32_t* midstate) {
  WriteBE32(hash + 0*4, midstate[0]);
  WriteBE32(hash + 1*4, midstate[1]);
  WriteBE32(hash + 2*4, midstate[2]);
  WriteBE32(hash + 3*4, midstate[3]);
  WriteBE32(hash + 4*4, midstate[4]);
  WriteBE32(hash + 5*4, midstate[5]);
  WriteBE32(hash + 6*4, midstate[6]);
  WriteBE32(hash + 7*4, midstate[7]);
}

/* Coverts a given 'hash' value as 32 bytes stored in an unsigned char array to a 'midstate' value.
 *
 * Precondition: uint32_t midstate[8];
 *               unsigned char hash[32]
 */
static inline void sha256_toMidstate(uint32_t* midstate, const unsigned char* hash) {
  midstate[0] = ReadBE32(hash + 0*4);
  midstate[1] = ReadBE32(hash + 1*4);
  midstate[2] = ReadBE32(hash + 2*4);
  midstate[3] = ReadBE32(hash + 3*4);
  midstate[4] = ReadBE32(hash + 4*4);
  midstate[5] = ReadBE32(hash + 5*4);
  midstate[6] = ReadBE32(hash + 6*4);
  midstate[7] = ReadBE32(hash + 7*4);
}

/* Sets the value of 'iv' to SHA-256's initial value.
 *
 * Precondition: uint32_t iv[8]
 */
static inline void sha256_iv(uint32_t* iv) {
    iv[0] = 0x6a09e667ul;
    iv[1] = 0xbb67ae85ul;
    iv[2] = 0x3c6ef372ul;
    iv[3] = 0xa54ff53aul;
    iv[4] = 0x510e527ful;
    iv[5] = 0x9b05688cul;
    iv[6] = 0x1f83d9abul;
    iv[7] = 0x5be0cd19ul;
}

/* Given a 256-bit 'midstate' and a 512-bit 'block', then 'midstate' becomes the value of the SHA-256 compression function ("added" to the original 'midstate' value).
 *
 * Precondition: uint32_t midstate[8];
 *               uint32_t block[16]
 */
void sha256_compression(uint32_t* midstate, const uint32_t* block);

/* Compute the SHA-256 hash, 'h', of the bitstring represented by 's'.
 *
 * Precondition: uint32_t h[8];
 *               '*s' is a valid bitstring;
 */
void sha256_bitstring(uint32_t* h, const bitstring* s);

/* Given a 256-bit 's' and a 512-bit 'chunk', then 's' becomes the value of the SHA-256 compression function ("added" to the original 's' value).
 *
 * Precondition: uint32_t s[8];
 *               unsigned char chunk[64]
 */
static void sha256_compression_uchar(uint32_t* s, const unsigned char* chunk) {
  sha256_compression(s, (const uint32_t[16])
    { ReadBE32(chunk + 4*0)
    , ReadBE32(chunk + 4*1)
    , ReadBE32(chunk + 4*2)
    , ReadBE32(chunk + 4*3)
    , ReadBE32(chunk + 4*4)
    , ReadBE32(chunk + 4*5)
    , ReadBE32(chunk + 4*6)
    , ReadBE32(chunk + 4*7)
    , ReadBE32(chunk + 4*8)
    , ReadBE32(chunk + 4*9)
    , ReadBE32(chunk + 4*10)
    , ReadBE32(chunk + 4*11)
    , ReadBE32(chunk + 4*12)
    , ReadBE32(chunk + 4*13)
    , ReadBE32(chunk + 4*14)
    , ReadBE32(chunk + 4*15)
    });
}

/* This next section implements a (typical) byte-oriented interface to SHA-256 that consumes the 8 least significant bits of
 * an 'unsigned char' in big endian order.
 */

/* This is the context structure for an ongoing SHA-256 evaluation.
 * It has a pointer to the output buffer, which is modified during evaluation to also hold the current SHA-256 midstate.
 * It has a counter to track the number of bytes consumed so far.
 * It has a block of bytes that are queued up that have been consumed but not digested.
 *
 * Invariant: uint32_t output[8]
 */
typedef struct sha256_context {
  uint32_t* const output;
  uint_fast64_t counter;
  unsigned char block[64];
} sha256_context;

/* Initialize a sha256_context given a buffer in which the final output will be written to.
 * Note that the 'output' buffer may be updated during the computation to hold a SHA-256 midstate.
 *
 * Precondition: unit32_t output[8]
 */
static inline sha256_context sha256_init(uint32_t* output) {
  sha256_iv(output);
  return (sha256_context){ .output = output };
}

/* Add an array of bytes to be consumed by an ongoing SHA-256 evaluation.
 *
 * Precondition: NULL != ctx;
 *               if 0 < len then unsigned char arr[len];
 */
static inline void sha256_uchars(sha256_context* ctx, const unsigned char* arr, size_t len) {
  size_t delta = 64 - ctx->counter % 64;
  unsigned char *block = ctx->block + ctx->counter % 64;
  ctx->counter += len;

  while (delta <= len) {
    memcpy(block, arr, delta);
    arr += delta;
    len -= delta;
    sha256_compression_uchar(ctx->output, ctx->block);
    block = ctx->block;
    delta = 64;
  }

  if (len) memcpy(block, arr, len);
}

/* Add one bytes to be consumed by an ongoing SHA-256 evaluation.
 *
 * Precondition: NULL != ctx;
 */
static inline void sha256_uchar(sha256_context* ctx, unsigned char x) {
  sha256_uchars(ctx, &x, 1);
}

/* Add a 64-bit word to be consumed in big endian order by an ongoing SHA-256 evaluation.
 * For greater certainty, only the least 64 bits of 'x' are consumed.
 *
 * Precondition: NULL != ctx;
 */
static inline void sha256_u64be(sha256_context* ctx, uint_fast64_t x) {
  unsigned char buf[8];
  WriteBE64(buf, x);
  sha256_uchars(ctx, buf, sizeof(buf));
}

/* Add a 32-bit word to be consumed in little endian byte-order by an ongoing SHA-256 evaluation.
 * For greater certainty, only the least 32 bits of 'x' are consumed.
 * Furthermore the bits within each byte are consumed in big endian order.
 *
 * Precondition: NULL != ctx;
 */
static inline void sha256_u32le(sha256_context* ctx, uint_fast32_t x) {
  unsigned char buf[4];
  WriteLE32(buf, x);
  sha256_uchars(ctx, buf, sizeof(buf));
}

/* Finish the SHA-256 computation by consuming and digesting the SHA-256 padding.
 * The final result is stored in the original 'output' buffer that was given to 'sha256_init'.
 *
 * Precondition: NULL != ctx;
 */
static inline void sha256_finalize(sha256_context* ctx) {
  uint_fast64_t length = ctx->counter * 8;
  sha256_uchars(ctx, (const unsigned char[64]){0x80}, 1 + (64 + 56 - ctx->counter % 64 - 1) % 64);
  sha256_u64be(ctx, length);
}
#endif
