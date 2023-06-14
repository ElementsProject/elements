/* This module provides functions for deserializing Simplicity's bit-wise prefix coding. */
#ifndef SIMPLICITY_DESERIALIZE_H
#define SIMPLICITY_DESERIALIZE_H

#include <simplicity/errorCodes.h>
#include "bitstream.h"
#include "dag.h"

/* Decode a length-prefixed Simplicity DAG from 'stream'.
 * Returns 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' the length prefix's value is too large.
 * Returns 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' if some node's child isn't a reference to one of the preceding nodes.
 * Returns 'SIMPLICITY_ERR_FAIL_CODE' if the encoding of a fail expression is encountered
 *  (all fail subexpressions ought to have been pruned prior to deserialization).
 * Returns 'SIMPLICITY_ERR_STOP_CODE' if the encoding of a stop tag is encountered.
 * Returns 'SIMPLICITY_ERR_HIDDEN' if there are illegal HIDDEN children in the DAG.
 * Returns 'SIMPLICITY_ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * Returns 'SIMPLICITY_ERR_MALLOC' if malloc fails.
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
 * Returns 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' if the encoded string of bits exceeds this decoder's limits.
 * Returns 'SIMPLICITY_ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * If successful, '*witness' is set to the decoded bitstring,
 *                and 'SIMPLICITY_NO_ERR' is returned.
 *
 * If an error is returned '*witness' might be modified.
 *
 * Precondition: NULL != witness;
 *               NULL != stream;
 */
simplicity_err decodeWitnessData(bitstring* witness, bitstream* stream);

#endif
