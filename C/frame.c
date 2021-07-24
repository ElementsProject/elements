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
