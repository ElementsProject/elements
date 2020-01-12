#include "bitstream.h"

#include <assert.h>
#include <limits.h>
#include <stdlib.h>

/* Ensure a non-zero amount of bits are 'available'.
 * If no more bits are available in the 'stream', returns 'ERR_BISTREAM_EOF'.
 * If an I/O error occurs when reading from the 'stream', 'ERR_BISTRING_ERROR' is returned.
 * Returns 0 if successful.
 *
 * Precondition: NULL != stream
 */
static int32_t ensureBuffer(bitstream* stream) {
  if (stream->available <= 0) {
    int ch = fgetc(stream->file);
    if (ch == EOF) {
      if (ferror(stream->file)) return ERR_BITSTREAM_ERROR;
      if (feof(stream->file)) return ERR_BITSTREAM_EOF;
    }
    stream->byte = (unsigned char)ch;
    stream->available = CHAR_BIT;
  }
  return 0;
}

/* Fetches up to 31 bits from 'stream' as the 'n' least significant bits of return value.
 * The 'n' bits are set from the MSB to the LSB.
 * Returns 'ERR_BITSTREAM_EOF' if not enough bits are available.
 * Returns 'ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
 *
 * Precondition: 0 <= n < 32
 *               NULL != stream
 */
int32_t getNBits(int n, bitstream* stream) {
  if (0 < n) {
    int32_t err = ensureBuffer(stream);
    if (err < 0) return err;
  } else {
    return 0;
  }
  assert(n < 32);

  uint32_t result = 0;
  while (stream->available < n) {
    n -= stream->available;
    result |= (stream->byte & (((uint32_t)1 << stream->available) - 1)) << n;
    stream->available = 0;
    int32_t err = ensureBuffer(stream);
    if (err < 0) return err;
  }
  stream->available -= n;
  result |= (uint32_t)(stream->byte >> stream->available) & (((uint32_t)1 << n) - 1);
  return (int32_t)result;
}

/* Allocates a 'bitstring' containing 'n' bits from 'stream'.
 * Returns 'ERR_BITSTREAM_EOF' if not enough bits are available.
 * Returns 'ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
 * Returns 'ERR_MALLOC' if malloc fails.
 * If successful, '*result' is set to a bitstring with 'n' bits read from 'stream',
 *                '*allocation' points to memory allocated for this bitstring,
 *                and 0 is returned.
 *
 * If an error is returned '*allocation' is set to 'NULL' and '*result' might be modified.
 *
 * Precondition: NULL != allocation
 *               NULL != result;
 *               NULL != stream;
 *
 * Postcondition: if the function returns '0'
 *                  '*result' represents a some bitstring with 'result->len' = n
 *                   and '*allocation' points to allocated memory sufficient for at least the 'result->arr' array.
 *                       (Note that '*allocation' may be 'NULL' if 'n == 0')
 *                if the function returns a negative value then '*allocation == NULL'
 */
int32_t getMallocBitstring(void** allocation, bitstring* result, size_t n, bitstream* stream) {
  *allocation = NULL;

  if (0 == n) {
    *result = (bitstring){0};
    return 0;
  } else {
    int32_t err = ensureBuffer(stream);
    if (err < 0) return err;
  }

  size_t offset = (size_t)(CHAR_BIT - stream->available);
  size_t arrayLen = (n - 1 + offset) / CHAR_BIT + 1;
  unsigned char* arr = malloc(arrayLen);
  if (!arr) return ERR_MALLOC;

  arr[0] = stream->byte;
  size_t charRead = fread(arr + 1, 1, arrayLen - 1, stream->file);
  if (charRead != arrayLen - 1) {
    free(arr);
    return ferror(stream->file) ? ERR_BITSTREAM_ERROR : ERR_BITSTREAM_EOF;
  }

  /* Rebuild 'stream's structure as if we read 'n' bits from the stream */
  stream->byte = arr[arrayLen - 1];
  /* Set stream->available to (stream->available - n) mod CHAR_BIT. */
  stream->available = (stream->available + CHAR_BIT - 1 - (int)((n - 1) % CHAR_BIT)) % CHAR_BIT;

  *allocation = arr;
  *result = (bitstring)
          { .arr = arr
          , .offset = offset
          , .len = n
          };
  return 0;
}
