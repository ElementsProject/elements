#ifndef SHA256_H
#define SHA256_H

#include <stdint.h>
#include <string.h>
#include <sha256/compression.h>
#include "bitstring.h"

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

/* A struct holding the 256-bit array of a SHA-256 hash or midstate.
 */
typedef struct sha256_midstate {
  uint32_t s[8];
} sha256_midstate;

/* Compute the SHA-256 hash, 'h', of the bitstring represented by 's'.
 *
 * Precondition: uint32_t h[8];
 *               '*s' is a valid bitstring;
 */
void sha256_bitstring(uint32_t* h, const bitstring* s);

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
