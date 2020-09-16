/* This module provides functions for deserializing Simplicity's bit-wise prefix coding. */
#ifndef DESERIALIZE_H
#define DESERIALIZE_H

#include "bitstream.h"
#include "dag.h"
#include "errorCodes.h"

/* Decode an encoded number between 1 and 2^31 - 1 inclusive.
 * When successful returns the decoded result.
 * If the decoded value would be too large, 'ERR_DATA_OUT_OF_RANGE' is returned.
 * If more bits are needed than available in the 'stream', 'ERR_BITSTRING_EOF' is returned.
 * If an I/O error occurs when reading from the 'stream', 'ERR_BISTRING_ERROR' is returned.
 *
 * Precondition: NULL != stream
 */
int32_t decodeUptoMaxInt(bitstream* stream);

/* Decode a length-prefixed Simplicity DAG from 'stream'.
 * Returns 'ERR_DATA_OUT_OF_RANGE' the length prefix's value is too large.
 * Returns 'ERR_DATA_OUT_OF_RANGE' if some node's child isn't a reference to one of the preceding nodes.
 * Returns 'ERR_FAIL_CODE' if the encoding of a fail expression is encountered
 *  (all fail subexpressions ought to have been pruned prior to deserialization).
 * Returns 'ERR_STOP_CODE' if the encoding of a stop tag is encountered.
 * Returns 'ERR_HIDDEN' if there are illegal HIDDEN children in the DAG.
 * Returns 'ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * Returns 'ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
 * Returns 'ERR_MALLOC' if malloc fails.
 * In the above error cases, '*dag' is set to NULL.
 * If successful, returns a positive value equal to the length of an allocated array of (*dag).
 *
 * Precondition: NULL != dag
 *               NULL != stream
 *
 * Postcondition: if the return value of the function is positive
 *                  then (dag_node (*dag)[return_value] and '*dag' is a well-formed dag without witness data);
 *                '*census' contains a tally of the different tags that occur in 'dag' when the return value
 *                          of the function is positive and when NULL != census;
 *                NULL == *dag when the return value is negative.
 */
int32_t decodeMallocDag(dag_node** dag, combinator_counters* census, bitstream* stream);

/* Decode a string of up to 2^31 - 1 bits from 'stream'.
 * This is the format in which the data for 'WITNESS' nodes are encoded.
 * Returns 'ERR_DATA_OUT_OF_RANGE' if the encoded string of bits exceeds this decoder's limits.
 * Returns 'ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * Returns 'ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
 * Returns 'ERR_MALLOC' if malloc fails.
 * If successful, '*witness' is set to the decoded bitstring,
 *                '*allocation' points to memory allocated for this bitstring,
 *                and 0 is returned.
 *
 * If an error is returned '*allocation' is set to 'NULL' and '*witness' might be modified.
 *
 * Precondition: NULL != allocation;
 *               NULL != witness;
 *               NULL != stream;
 *
 * Postcondition: if the function returns '0'
 *                  '*witness' represents a some bitstring
 *                   and '*allocation' points to allocated memory sufficient for at least the 'witness->arr' array.
 *                       (Note that '*allocation' may be 'NULL' if 'n == 0')
 *                if the function returns a negative value then '*allocation == NULL'
 */
int32_t decodeMallocWitnessData(void** allocation, bitstring* witness, bitstream* stream);

#endif
