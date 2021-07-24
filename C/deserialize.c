#include "deserialize.h"

#include <assert.h>
#include <limits.h>
#include "primitive.h"
#include "unreachable.h"

/* Fetches 'len' 'uint32_t's from 'stream' into 'result'.
 * The bits in each 'uint32_t' are set from the MSB to the LSB and the 'uint32_t's of 'result' are set from 0 up to 'len'.
 * Returns 'SIMPLICITY_ERR_BITSTREAM_EOF' if not enough bits are available ('result' may be modified).
 * Returns 'SIMPLICITY_ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream' ('result' may be modified).
 * Returns 0 if successful.
 *
 * Precondition: uint32_t result[len];
 *               NULL != stream
 */
static int32_t getWord32Array(uint32_t* result, const size_t len, bitstream* stream) {
  for (size_t i = 0; i < len; ++i) {
    /* Due to error codes, getNBits cannot fetch 32 bits at once. Instead we fetch two groups of 16 bits. */
    int32_t bits16 = getNBits(16, stream);
    if (bits16 < 0) return bits16;
    result[i] = (uint32_t)bits16 << 16;
    bits16 = getNBits(16, stream);
    if (bits16 < 0) return bits16;
    result[i] |= (uint32_t)bits16;
  }
  return 0;
}

/* Fetches a 256-bit hash value from 'stream' into 'result'.
 * Returns 'SIMPLICITY_ERR_BITSTREAM_EOF' if not enough bits are available ('result' may be modified).
 * Returns 'SIMPLICITY_ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream' ('result' may be modified).
 * Returns 0 if successful.
 *
 * Precondition: NULL != result
 *               NULL != stream
 */
static int32_t getHash(sha256_midstate* result, bitstream* stream) {
  return getWord32Array(result->s, 8, stream);
}


/* Decode a single node of a Simplicity dag from 'stream' into 'dag'['i'].
 * Returns 'SIMPLICITY_ERR_FAIL_CODE' if the encoding of a fail expression is encountered
 *   (all fail subexpressions ought to have been pruned prior to serialization).
 * Returns 'SIMPLICITY_ERR_STOP_CODE' if the encoding of a stop tag is encountered.
 * Returns 'SIMPLICITY_ERR_HIDDEN' if the decoded node has illegal HIDDEN children.
 * Returns 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' if the node's child isn't a reference to one of the preceding nodes.
 *                                            or some encoding for a non-existent jet is encountered.
 * Returns 'SIMPLICITY_ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * Returns 'SIMPLICITY_ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
 * In the above error cases, 'dag' may be modified.
 * Returns 0 if successful.
 *
 * Precondition: dag_node dag[i + 1];
 *               i < 2^31 - 1
 *               NULL != stream
 */
static int32_t decodeNode(dag_node* dag, size_t i, bitstream* stream) {
  int32_t bit = getBit(stream);
  if (bit < 0) return bit;
  dag[i] = (dag_node){0};
  if (bit) {
    return decodeJet(&dag[i], stream);
  } else {
    int32_t code = getNBits(2, stream);
    if (code < 0) return code;
    int32_t subcode = getNBits(code < 3 ? 2 : 1, stream);
    if (subcode < 0) return subcode;
    for (int32_t j = 0; j < 2 - code; ++j) {
      int32_t ix = decodeUptoMaxInt(stream);
      if (ix < 0) return ix;
      if (i < (uint32_t)ix) return SIMPLICITY_ERR_DATA_OUT_OF_RANGE;
      dag[i].child[j] = i - (uint32_t)ix;
    }
    switch (code) {
     case 0:
      switch (subcode) {
       case 0: dag[i].tag = COMP; break;
       case 1:
        dag[i].tag = (HIDDEN == dag[dag[i].child[0]].tag) ? ASSERTR
                   : (HIDDEN == dag[dag[i].child[1]].tag) ? ASSERTL
                   : CASE;
        break;
       case 2: dag[i].tag = PAIR; break;
       case 3: dag[i].tag = DISCONNECT; break;
      }
      break;
     case 1:
      switch (subcode) {
       case 0: dag[i].tag = INJL; break;
       case 1: dag[i].tag = INJR; break;
       case 2: dag[i].tag = TAKE; break;
       case 3: dag[i].tag = DROP; break;
      }
      break;
     case 2:
      switch (subcode) {
       case 0: dag[i].tag = IDEN; break;
       case 1: dag[i].tag = UNIT; break;
       case 2: return SIMPLICITY_ERR_FAIL_CODE;
       case 3: return SIMPLICITY_ERR_STOP_CODE;
      }
      break;
     case 3:
      switch (subcode) {
       case 0:
        dag[i].tag = HIDDEN;
        return getHash(&(dag[i].cmr), stream);
       case 1:
        dag[i].tag = WITNESS;
        break;
      }
      break;
    }

    /* Verify that there are no illegal HIDDEN children. */
    for (int32_t j = 0; j < 2 - code; ++j) {
       if (HIDDEN == dag[dag[i].child[j]].tag && dag[i].tag != (j ? ASSERTL : ASSERTR)) return SIMPLICITY_ERR_HIDDEN;
    }

    computeCommitmentMerkleRoot(dag, i);

    return 0;
  }
}

/* Decode a Simplicity DAG consisting of 'len' nodes from 'stream' into 'dag'.
 * Returns 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' if some node's child isn't a reference to one of the preceding nodes.
 * Returns 'SIMPLICITY_ERR_FAIL_CODE' if the encoding of a fail expression is encountered
 *   (all fail subexpressions ought to have been pruned prior to deserialization).
 * Returns 'SIMPLICITY_ERR_STOP_CODE' if the encoding of a stop tag is encountered.
 * Returns 'SIMPLICITY_ERR_HIDDEN' if there are illegal HIDDEN children in the DAG.
 * Returns 'SIMPLICITY_ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * Returns 'SIMPLICITY_ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
 * In the above error cases, 'dag' may be modified.
 * Returns 0 if successful.
 *
 * Precondition: dag_node dag[len];
 *               len < 2^31
 *               NULL != stream
 */
static int32_t decodeDag(dag_node* dag, const size_t len, combinator_counters* census, bitstream* stream) {
  for (size_t i = 0; i < len; ++i) {
    int32_t err = decodeNode(dag, i, stream);
    if (err < 0) return err;

    enumerator(census, dag[i].tag);
  }
  return 0;
}

/* Decode a length-prefixed Simplicity DAG from 'stream'.
 * Returns 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' the length prefix's value is too large.
 * Returns 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' if some node's child isn't a reference to one of the preceding nodes.
 * Returns 'SIMPLICITY_ERR_FAIL_CODE' if the encoding of a fail expression is encountered
 *  (all fail subexpressions ought to have been pruned prior to deserialization).
 * Returns 'SIMPLICITY_ERR_STOP_CODE' if the encoding of a stop tag is encountered.
 * Returns 'SIMPLICITY_ERR_HIDDEN' if there are illegal HIDDEN children in the DAG.
 * Returns 'SIMPLICITY_ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * Returns 'SIMPLICITY_ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
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
int32_t decodeMallocDag(dag_node** dag, combinator_counters* census, bitstream* stream) {
  *dag = NULL;
  int32_t dagLen = decodeUptoMaxInt(stream);
  if (dagLen <= 0) return dagLen;
  /* :TODO: a consensus parameter limiting the maximum length of a DAG needs to be enforced here */
  if (PTRDIFF_MAX / sizeof(dag_node) < (size_t)dagLen) return SIMPLICITY_ERR_DATA_OUT_OF_RANGE;
  *dag = malloc((size_t)dagLen * sizeof(dag_node));
  if (!*dag) return SIMPLICITY_ERR_MALLOC;

  if (census) *census = (combinator_counters){0};
  int32_t err = decodeDag(*dag, (size_t)dagLen, census, stream);

  if (0 <= err && !verifyCanonicalOrder(*dag, (size_t)(dagLen))) {
    err = SIMPLICITY_ERR_DATA_OUT_OF_ORDER;
  }

  if (err < 0) {
    free(*dag);
    *dag = NULL;
    return err;
  } else {
    return dagLen;
  }
}

/* Decode a string of up to 2^31 - 1 bits from 'stream'.
 * This is the format in which the data for 'WITNESS' nodes are encoded.
 * Returns 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' if the encoded string of bits exceeds this decoder's limits.
 * Returns 'SIMPLICITY_ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * Returns 'SIMPLICITY_ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
 * Returns 'SIMPLICITY_ERR_MALLOC' if malloc fails.
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
int32_t decodeMallocWitnessData(void** allocation, bitstring* witness, bitstream* stream) {
  *allocation = NULL;
  int32_t witnessLen = getBit(stream);
  if (witnessLen < 0) return witnessLen;
  if (0 < witnessLen) witnessLen = decodeUptoMaxInt(stream);
  if (witnessLen < 0) return witnessLen;
  /* :TODO: A consensus parameter limiting the maximum length of the witness data blob needs to be enforced here */
  if (PTRDIFF_MAX - 1 <= (size_t)witnessLen / CHAR_BIT) return SIMPLICITY_ERR_DATA_OUT_OF_RANGE;

  return getMallocBitstring(allocation, witness, (size_t)witnessLen, stream);
}
