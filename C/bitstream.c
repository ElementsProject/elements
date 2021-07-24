#include "bitstream.h"

#include <assert.h>
#include <limits.h>
#include <stdlib.h>

/* Ensure a non-zero amount of bits are 'available'.
 * If no more bits are available in the 'stream', returns 'SIMPLICITY_ERR_BISTREAM_EOF'.
 * If an I/O error occurs when reading from the 'stream', 'SIMPLICITY_ERR_BISTRING_ERROR' is returned.
 * Returns 0 if successful.
 *
 * Precondition: NULL != stream
 */
static int32_t ensureBuffer(bitstream* stream) {
  if (stream->available <= 0) {
    int ch = fgetc(stream->file);
    if (ch == EOF) {
      if (ferror(stream->file)) return SIMPLICITY_ERR_BITSTREAM_ERROR;
      if (feof(stream->file)) return SIMPLICITY_ERR_BITSTREAM_EOF;
    }
    stream->byte = (unsigned char)ch;
    stream->available = CHAR_BIT;
  }
  return 0;
}

/* Fetches up to 31 bits from 'stream' as the 'n' least significant bits of return value.
 * The 'n' bits are set from the MSB to the LSB.
 * Returns 'SIMPLICITY_ERR_BITSTREAM_EOF' if not enough bits are available.
 * Returns 'SIMPLICITY_ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
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
/* Decode an encoded bitstring up to length 1.
 * If successful returns the length of the bitstring and 'result' contains the decoded bits.
 * The decoded bitstring is stored in the LSBs of 'result', with the LSB being the last bit decoded.
 * Any remaining bits in 'result' are reset to 0.
 * If the decoded bitstring would be too long 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' is returned ('result' may be modified).
 * If more bits are needed than available in the 'stream', 'SIMPLICITY_ERR_BITSTRING_EOF' is returned ('result' may be modified).
 * If an I/O error occurs when reading from the 'stream', 'SIMPLICITY_ERR_BISTRING_ERROR' is returned ('result' may be modified).
 *
 * Precondition: NULL != result
 *               NULL != stream
 */
static int32_t decodeUpto1Bit(int32_t* result, bitstream* stream) {
  *result = getBit(stream);
  if (*result <= 0) return *result;

  *result = getBit(stream);
  if (*result < 0) return *result;
  if (0 != *result) return SIMPLICITY_ERR_DATA_OUT_OF_RANGE;

  *result = getBit(stream);
  if (*result < 0) return *result;
  return 1;
}

/* Decode an encoded number between 1 and 3 inclusive.
 * When successful returns the decoded result.
 * If the decoded value would be too large, 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' is returned.
 * If more bits are needed than available in the 'stream', 'SIMPLICITY_ERR_BITSTRING_EOF' is returned.
 * If an I/O error occurs when reading from the 'stream', 'SIMPLICITY_ERR_BISTRING_ERROR' is returned.
 *
 * Precondition: NULL != stream
 */
static int32_t decodeUpto3(bitstream* stream) {
  int32_t result;
  int32_t len = decodeUpto1Bit(&result, stream);
  if (len < 0) return len;
  result |= 1 << len;
  return result;
}

/* Decode an encoded bitstring up to length 3.
 * If successful returns the length of the bitstring and 'result' contains the decoded bits.
 * The decoded bitstring is stored in the LSBs of 'result', with the LSB being the last bit decoded.
 * Any remaining bits in 'result' are reset to 0.
 * If the decoded bitstring would be too long 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' is returned ('result' may be modified).
 * If more bits are needed than available in the 'stream', 'SIMPLICITY_ERR_BITSTRING_EOF' is returned ('result' may be modified).
 * If an I/O error occurs when reading from the 'stream', 'SIMPLICITY_ERR_BISTRING_ERROR' is returned ('result' may be modified).
 *
 * Precondition: NULL != result
 *               NULL != stream
 */
static int32_t decodeUpto3Bits(int32_t* result, bitstream* stream) {
  int32_t bit = getBit(stream);
  if (bit < 0) return bit;

  *result = 0;
  if (0 == bit) {
    return 0;
  } else {
    int32_t n = decodeUpto3(stream);
    if (0 <= n) {
      *result = getNBits(n, stream);
      if (*result < 0) return *result;
    }
    return n;
  }
}

/* Decode an encoded number between 1 and 15 inclusive.
 * When successful returns the decoded result.
 * If the decoded value would be too large, 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' is returned.
 * If more bits are needed than available in the 'stream', 'SIMPLICITY_ERR_BITSTRING_EOF' is returned.
 * If an I/O error occurs when reading from the 'stream', 'SIMPLICITY_ERR_BISTRING_ERROR' is returned.
 *
 * Precondition: NULL != stream
 */
static int32_t decodeUpto15(bitstream* stream) {
  int32_t result;
  int32_t len = decodeUpto3Bits(&result, stream);
  if (len < 0) return len;
  result |= 1 << len;
  return result;
}

/* Decode an encoded bitstring up to length 15.
 * If successful returns the length of the bitstring and 'result' contains the decoded bits.
 * The decoded bitstring is stored in the LSBs of 'result', with the LSB being the last bit decoded.
 * Any remaining bits in 'result' are reset to 0.
 * If the decoded bitstring would be too long 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' is returned ('result' may be modified).
 * If more bits are needed than available in the 'stream', 'SIMPLICITY_ERR_BITSTRING_EOF' is returned ('result' may be modified).
 * If an I/O error occurs when reading from the 'stream', 'SIMPLICITY_ERR_BISTRING_ERROR' is returned ('result' may be modified).
 *
 * Precondition: NULL != result
 *               NULL != stream
 */
static int32_t decodeUpto15Bits(int32_t* result, bitstream* stream) {
  int32_t bit = getBit(stream);
  if (bit < 0) return bit;

  *result = 0;
  if (0 == bit) {
    return 0;
  } else {
    int32_t n = decodeUpto15(stream);
    if (0 <= n) {
      *result = getNBits(n, stream);
      if (*result < 0) return *result;
    }
    return n;
  }
}

/* Decode an encoded number between 1 and 65535 inclusive.
 * When successful returns the decoded result.
 * If the decoded value would be too large, 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' is returned.
 * If more bits are needed than available in the 'stream', 'SIMPLICITY_ERR_BITSTRING_EOF' is returned.
 * If an I/O error occurs when reading from the 'stream', 'SIMPLICITY_ERR_BISTRING_ERROR' is returned.
 *
 * Precondition: NULL != stream
 */
static int32_t decodeUpto65535(bitstream* stream) {
  int32_t result;
  int32_t len = decodeUpto15Bits(&result, stream);
  if (len < 0) return len;
  result |= 1 << len;
  return result;
}

/* Decode an encoded number between 1 and 2^31 - 1 inclusive.
 * When successful returns the decoded result.
 * If the decoded value would be too large, 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' is returned.
 * If more bits are needed than available in the 'stream', 'SIMPLICITY_ERR_BITSTRING_EOF' is returned.
 * If an I/O error occurs when reading from the 'stream', 'SIMPLICITY_ERR_BISTRING_ERROR' is returned.
 *
 * Precondition: NULL != stream
 */
int32_t decodeUptoMaxInt(bitstream* stream) {
  int32_t bit = getBit(stream);
  if (bit < 0) return bit;
  if (0 == bit) {
    return 1;
  } else {
    int32_t n = decodeUpto65535(stream);
    if (n < 0) return n;
    if (30 < n) return SIMPLICITY_ERR_DATA_OUT_OF_RANGE;
    {
      int32_t result = getNBits(n, stream);
      if (result < 0) return result;
      return ((1 << n) | result);
    }
  }
}

/* Allocates a 'bitstring' containing 'n' bits from 'stream'.
 * Returns 'SIMPLICITY_ERR_BITSTREAM_EOF' if not enough bits are available.
 * Returns 'SIMPLICITY_ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
 * Returns 'SIMPLICITY_ERR_MALLOC' if malloc fails.
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
  if (!arr) return SIMPLICITY_ERR_MALLOC;

  arr[0] = stream->byte;
  size_t charRead = fread(arr + 1, 1, arrayLen - 1, stream->file);
  if (charRead != arrayLen - 1) {
    free(arr);
    return ferror(stream->file) ? SIMPLICITY_ERR_BITSTREAM_ERROR : SIMPLICITY_ERR_BITSTREAM_EOF;
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
