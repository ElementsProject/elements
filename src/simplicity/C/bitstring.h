/* This modules defines a structure representing bit strings. */
#ifndef SIMPLICITY_BITSTRING_H
#define SIMPLICITY_BITSTRING_H

#include <stdlib.h>

/* Represents a bitstring of length 'len' bits using an array of unsigned char.
 * The bit at index 'n', where 0 <= 'n' < 'len', is located at bit '1 << (CHAR_BIT - 1 - (offset + n) % CHAR_BIT)' of
 * array element 'arr[(offset + n) / CHAR_BIT]'.
 * Other bits in the array may be any value.
 *
 * Invariant: 0 < len implies
 *              unsigned char arr[(offset + len - 1) / CHAR_BIT + 1];
 *            len == 0 implies arr == NULL;
 */
typedef struct bitstring {
  const unsigned char* arr;
  size_t len;
  size_t offset;
} bitstring;

#endif
