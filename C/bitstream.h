/* This module provides functions for initializing and reading from a stream of bits from a 'FILE'. */
#ifndef SIMPLICITY_BITSTREAM_H
#define SIMPLICITY_BITSTREAM_H

#include <stdio.h>
#include <stdint.h>
#include "bitstring.h"
#include "errorCodes.h"

/* :TODO: consider adding an 'invalid' state that can be set when parsing has failed and should not be resumed. */
/* Datatype representing a bit stream.
 * Bits are streamed from MSB to LSB.
 *
 * Invariant: NULL != file
 *            0 <= available <= CHAR_BIT
 */
typedef struct bitstream {
  FILE* file;          /* Underlying byte stream */
  int available;       /* Number of bits unparsed from 'byte' */
  unsigned char byte;  /* Current, partially parsed byte */
} bitstream;

/* Initialize a bit stream, 'stream', from a given byte stream, 'file'.
 * Precondition: NULL != file
 */
static inline bitstream initializeBitstream(FILE* file) {
  return (bitstream){ .file = file, .available = 0 };
}

/* Fetches up to 31 bits from 'stream' as the 'n' least significant bits of return value.
 * The 'n' bits are set from the MSB to the LSB.
 * Returns 'SIMPLICITY_ERR_BITSTREAM_EOF' if not enough bits are available.
 * Returns 'SIMPLICITY_ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
 *
 * Precondition: 0 <= n < 32
 *               NULL != stream
 */
int32_t getNBits(int n, bitstream* stream);

/* Returns one bit from 'stream', 0 or 1.
 * Returns 'SIMPLICITY_ERR_BITSTREAM_EOF' if no bits are available.
 * Returns 'SIMPLICITY_ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
 *
 * Precondition: NULL != stream
 */
static inline int32_t getBit(bitstream* stream) {
  return getNBits(1, stream);
}

/* Decode an encoded number between 1 and 2^31 - 1 inclusive.
 * When successful returns the decoded result.
 * If the decoded value would be too large, 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' is returned.
 * If more bits are needed than available in the 'stream', 'SIMPLICITY_ERR_BITSTRING_EOF' is returned.
 * If an I/O error occurs when reading from the 'stream', 'SIMPLICITY_ERR_BISTRING_ERROR' is returned.
 *
 * Precondition: NULL != stream
 */
int32_t decodeUptoMaxInt(bitstream* stream);

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
int32_t getMallocBitstring(void** allocation, bitstring* result, size_t n, bitstream* stream);
#endif
