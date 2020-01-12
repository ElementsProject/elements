#include "sha256.h"

#include <assert.h>
#include <limits.h>

/* Given a SHA-256 midstate, 'h', of '*count / 512' blocks, and
 * a 'block' with 'len % 512' bits set and with the remaining bits set to 0,
 * finalize the SHA-256 computation by adding SHA-256 padding and set 'h' to the resulting SHA-256 hash.
 *
 * Precondition: uint32_t h[8];
 *               uint32_t block[16];
 */
static void sha256_end(uint32_t* h, uint32_t* block, const size_t len) {
  block[len / 32 % 16] |= (uint32_t)1 << (31 - len % 32);
  if (448 <= len % 512) {
    sha256_compression(h, block);
    memset(block, 0, sizeof(uint32_t[14]));
  }
  block[14] = (uint32_t)(len >> 32);
  block[15] = (uint32_t)len;
  sha256_compression(h, block);
}

/* Compute the SHA-256 hash, 'h', of the bitstring represented by 's'.
 *
 * Precondition: uint32_t h[8];
 *               '*s' is a valid bitstring;
 */
void sha256_bitstring(uint32_t* h, const bitstring* s) {
  /* This static assert should never fail if uint32_t exists.
   * But for more certainty, we note that the correctness of this implementation depends on CHAR_BIT being no more than 32.
   */
  static_assert(CHAR_BIT <= 32, "CHAR_BIT has to be less than 32 for uint32_t to even exist.");

  uint32_t block[16] = { 0 };
  size_t count = 0;
  sha256_iv(h);
  if (s->len) {
    block[0] = s->arr[s->offset / CHAR_BIT];
    if (s->len < CHAR_BIT - s->offset % CHAR_BIT) {
      /* s->len is so short that we don't even use a whole char.
       * Zero out the low bits.
       */
      block[0] = block[0] >> (CHAR_BIT - s->offset % CHAR_BIT - s->len)
                          << (CHAR_BIT - s->offset % CHAR_BIT - s->len);
      count = s->len;
    } else {
      count = CHAR_BIT - s->offset % CHAR_BIT;
    }
    block[0] = 1U * block[0] << (32 - CHAR_BIT + s->offset % CHAR_BIT);

    while (count < s->len) {
      unsigned char ch = s->arr[(s->offset + count)/CHAR_BIT];
      size_t delta = CHAR_BIT;
      if (s->len - count < CHAR_BIT) {
        delta = s->len - count;
        /* Zero out any extra low bits that 'ch' may have. */
        ch = (unsigned char)(ch >> (CHAR_BIT - delta) << (CHAR_BIT - delta));
      }

      if (count / 32 != (count + CHAR_BIT) / 32) {
        /* The next character from s->arr straddles (or almost straddles) the boundary of two elements of the block array. */
        block[count / 32 % 16] |= (uint32_t)(ch >> (count + CHAR_BIT) % 32);
        if (count / 512 != (count + delta) / 512) {
          sha256_compression(h, block);
          memset(block, 0, sizeof(uint32_t[16]));
        }
      }
      if ((count + CHAR_BIT) % 32) {
        block[(count + CHAR_BIT) / 32 % 16] |= 1U * ch << (32 - (count + CHAR_BIT) % 32);
      }
      count += delta;
    }
  }
  assert(count == s->len);
  sha256_end(h, block, s->len);
}
