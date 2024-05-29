#include "frame.h"

#define READ_(bits)                                                                                                           \
/* Given a read frame, return the value of the bits cells after the cursor and advance the frame's cursor by bits##.          \
 * The cell values are returned with the first cell in the MSB of the result and the last cell in the LSB of the result.      \
 *                                                                                                                            \
 * Precondition: '*frame' is a valid read frame for bits more cells.                                                          \
 */                                                                                                                           \
uint_fast##bits##_t read##bits(frameItem* frame) {                                                                            \
  uint_fast##bits##_t result = 0;                                                                                             \
  /* Pointers to the UWORD of the read frame that contains the frame's cursor (or is immediately after the cursor). */        \
  UWORD* frame_ptr = frame->edge - 1 - frame->offset / UWORD_BIT;                                                             \
  /* The specific bit within the above UWORD that is immediately in front of the cursor.                                      \
   * That bit is specifically '1 << (frame_shift - 1)'.                                                                       \
   */                                                                                                                         \
  size_t frame_shift = UWORD_BIT - (frame->offset % UWORD_BIT);                                                               \
  size_t n = bits;                                                                                                            \
  if (frame_shift < n) {                                                                                                      \
    /* We may only want part of the LSBs from the read frame's current UWORD.                                                 \
     * Copy that data to 'x', and move the frame_ptr to the frame's next UWORD.                                               \
     */                                                                                                                       \
    result |= (uint_fast##bits##_t)((uint_fast##bits##_t)LSBkeep(*frame_ptr, frame_shift) << (n - frame_shift));              \
    frame->offset += frame_shift;                                                                                             \
    n -= frame_shift;                                                                                                         \
    frame_shift = UWORD_BIT;                                                                                                  \
    frame_ptr--;                                                                                                              \
    while (UWORD_BIT < n) {                                                                                                   \
      /* Copy the entire read frame's current UWORD to 'x', and move the frame_ptr to the frame's next UWORD. */              \
      result |= (uint_fast##bits##_t)((uint_fast##bits##_t)(*frame_ptr) << (n - UWORD_BIT));                                  \
      frame->offset += UWORD_BIT;                                                                                             \
      n -= UWORD_BIT;                                                                                                         \
      frame_ptr--;                                                                                                            \
    }                                                                                                                         \
  }                                                                                                                           \
  /* We may only want part of the bits from the middle of the read frame's current UWORD.                                     \
   * Copy that data to fill the remainder of 'x'.                                                                             \
   */                                                                                                                         \
  result |= (uint_fast##bits##_t)(LSBkeep((UWORD)(*frame_ptr >> (frame_shift - n)), n));                                      \
  frame->offset += n;                                                                                                         \
  return result;                                                                                                              \
}
READ_(8)
READ_(16)
READ_(32)
READ_(64)

#define WRITE_(bits)                                                                                                          \
/* Given a write frame, set the value of the bits cells after the cursor and advance the frame's cursor by bits##.            \
 * The first cell is set to the value of the MSB of 'x' and the last cell is set to the LSB of 'x'.                           \
 * Cells in front of the cursor's final position may be overwritten.                                                          \
 *                                                                                                                            \
 * Precondition: '*frame' is a valid write frame for bits more cells.                                                         \
 */                                                                                                                           \
void write##bits(frameItem* frame, uint_fast##bits##_t x) {                                                                   \
  /* Pointers to the UWORD of the write frame that contains the frame's cursor (or is immediately after the cursor). */       \
  UWORD* frame_ptr = frame->edge + (frame->offset - 1) / UWORD_BIT;                                                           \
  /* The specific bit within the above UWORD that is immediately in front of the cursor.                                      \
   * That bit is specifically '1 << (frame_shift - 1)'.                                                                       \
   */                                                                                                                         \
  size_t frame_shift = (frame->offset - 1) % UWORD_BIT + 1;                                                                   \
  size_t n = bits;                                                                                                            \
  if (frame_shift < n) {                                                                                                      \
    /* The write frame's current UWORD may be partially filled.                                                               \
     * Fill the rest of it with data from 'x', and move the frame_ptr to the frame's next UWORD.                              \
     */                                                                                                                       \
    *frame_ptr = LSBclear(*frame_ptr, frame_shift) | LSBkeep((UWORD)(x >> (n - frame_shift)), frame_shift);                   \
    frame->offset -= frame_shift;                                                                                             \
    n -= frame_shift;                                                                                                         \
    frame_shift = UWORD_BIT;                                                                                                  \
    frame_ptr--;                                                                                                              \
    while (UWORD_BIT < n) {                                                                                                   \
      /* Fill the write frame's entire current UWORD with data from 'x', and move the frame_ptr to the frame's next UWORD. */ \
      *frame_ptr = (UWORD)(x >> (n - UWORD_BIT));                                                                             \
      frame->offset -= UWORD_BIT;                                                                                             \
      n -= UWORD_BIT;                                                                                                         \
      frame_ptr--;                                                                                                            \
    }                                                                                                                         \
  }                                                                                                                           \
  /* The current write frame's UWORD may be partially filled.                                                                 \
   * Fill the UWORD with the last of the data from 'x', which may or may not be enough to fill the rest of the UWORD.         \
   */                                                                                                                         \
  *frame_ptr = (UWORD)(LSBclear(*frame_ptr, frame_shift) | (LSBkeep((UWORD)x, n) << (frame_shift - n)));                      \
  frame->offset -= n;                                                                                                         \
}
WRITE_(8)
WRITE_(16)
WRITE_(32)
WRITE_(64)

/* Read bytes from a Simplicity buffer of type (TWO^8)^<2^(n+1) into 'buf'.
 * Set 'len' to the number of bytes read from the buffer.
 * Advance the 'src' frame to the end of the buffer type.
 *
 * The notation X^<2 is notation for the type (S X)
 * The notation X^<(2*n) is notation for the type S (X^n) * X^<n
 *
 * Precondition: unsigned char buf[2^(n+1)-1];
 *               NULL != len;
 *               '*src' is a valid read frame for 8*(2^(n+1)-1)+n+1 more cells;
 *               0 <= n < 16
 */
void read_buffer8(unsigned char* buf, size_t* len, frameItem* src, int n) {
  simplicity_debug_assert(0 <= n && n < 16);
  *len = 0;

  for (size_t i = (size_t)1 << n; 0 < i; i /= 2) {
    if (readBit(src)) {
      read8s(buf, i, src);
      buf += i; *len += i;
    } else {
      forwardBits(src, i*8);
    }
  }
}

/* Write 'len' bytes to a Simplicity buffer of type (TWO^8)^<2^(n+1) from 'buf'.
 * Advance the 'dst' frame to the end of the buffer type.
 *
 * The notation X^<2 is notation for the type (S X)
 * The notation X^<(2*n) is notation for the type S (X^n) * X^<n
 *
 * Precondition: '*dst' is a valid write frame for 8*(2^(n+1)-1)+n+1 more cells;
 *               unsigned char buf[len];
 *               len < 2^(n+1);
 *               0 <= n < 16;
 */
void write_buffer8(frameItem* dst, const unsigned char* buf, size_t len, int n) {
  simplicity_debug_assert(0 <= n && n < 16);
  simplicity_debug_assert(len < ((size_t)1<<(n+1)));
  for (size_t i = (size_t)1 << n; 0 < i; i /= 2) {
    if (writeBit(dst, i <= len)) {
      write8s(dst, buf, i);
      buf += i; len -= i;
    } else {
      skipBits(dst, i*8);
    }
  }
}

/* Read data from a Simplicity CTX8 type (TWO^8)^<2^64 * TWO^64 * TWO^256 and fill in a sha256_context value.
 * Advance the 'src' frame to the end of the CTX8 type.
 * Returns false if the context's counter is too large (i.e. the compression count is greater than or equal to 2^55).
 *
 * The notation X^<2 is notation for the type (S X)
 * The notation X^<(2*n) is notation for the type S (X^n) * X^<n
 *
 * Precondition: NULL != ctx->output;
 *               '*src' is a valid read frame for 838 more cells;
 */
bool read_sha256_context(sha256_context* ctx, frameItem* src) {
  size_t len;
  uint_fast64_t compressionCount;

  read_buffer8(ctx->block, &len, src, 5);
  compressionCount = read64(src);
  ctx->counter = ((compressionCount*1U) << 6) + len;
  read32s(ctx->output, 8, src);
  ctx->overflow = (sha256_max_counter >> 6) <= compressionCount;
  return !ctx->overflow;
}

/* Write data to a Simplicity CTX8 type (TWO^8)^<2^64 * TWO^64 * TWO^256 from a sha256_context value.
 * Advance the 'dst' frame to the end of the CTX8 type.
 * Returns false if the ctx had overflowed.
 *
 * The notation X^<2 is notation for the type (S X)
 * The notation X^<(2*n) is notation for the type S (X^n) * X^<n
 *
 * Precondition: '*dst' is a valid write frame for 838 more cells;
 *               NULL != ctx->output;
 *               ctx->counter < 2^61;
 */
bool write_sha256_context(frameItem* dst, const sha256_context* ctx) {
  write_buffer8(dst, ctx->block, ctx->counter % 64, 5);
  write64(dst, ctx->counter >> 6);
  write32s(dst, ctx->output, 8);
  return !ctx->overflow;
}
