/* This modules defines a structure representing bit strings. */
#ifndef SIMPLICITY_BITSTRING_H
#define SIMPLICITY_BITSTRING_H

#include <assert.h>
#include <limits.h>
#include <stdbool.h>

/* Represents a bitstring of length 'len' bits using an array of unsigned char.
 * The bit at index 'n', where 0 <= 'n' < 'len', is located at bit '1 << (CHAR_BIT - 1 - (offset + n) % CHAR_BIT)' of
 * array element 'arr[(offset + n) / CHAR_BIT]'.
 * Other bits in the array may be any value.
 *
 * Invariant: len <= 2^31
 *            offset + length <= SIZE_MAX
 *            0 < len implies unsigned char arr[(offset + len - 1) / CHAR_BIT + 1];
 */
typedef struct bitstring {
  const unsigned char* arr;
  size_t len;
  size_t offset;
} bitstring;

/* Return the nth bit from a bitstring.
 *
 * Precondition: NULL != s
 *               n < s->len;
 */
static inline bool getBit(const bitstring *s, size_t n) {
  size_t total_offset = s->offset + n;
  assert(n < s->len);
  return 1 & (s->arr[total_offset / CHAR_BIT] >> (CHAR_BIT - 1 - (total_offset % CHAR_BIT)));
}

#endif
