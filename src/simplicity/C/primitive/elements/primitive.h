/* This module defines the environment ('txEnv') for Simplicity evaluation for Elements.
 * It includes the transaction data and input index of the input whose Simplicity program is being executed.
 * It also includes the commitment Merkle root of the program being executed.
 */
#ifndef SIMPLICITY_PRIMITIVE_ELEMENTS_H
#define SIMPLICITY_PRIMITIVE_ELEMENTS_H

#include "../../primitive.h"
#include "../../sha256.h"

/* An Elements 'outpoint' consists of a transaction id and output index within that transaction.
 * The transaction id can be a either a transaction within the chain, or the transaction id from another chain in case of a peg-in.
 */
typedef struct outpoint {
  sha256_midstate txid;
  uint_fast32_t ix;
} outpoint;

/* In Elements, many fields can optionally be blinded and encoded as a point on the secp256k1 curve.
 * This prefix determines the parity of the y-coordinate of that point point, or indicates the value is explicit.
 * Sometimes values are entirely optional, in which case 'NONE' is a possibility.
 */
typedef enum confPrefix {
  NONE = 0,
  EXPLICIT = 1,
  EVEN_Y = 2,
  ODD_Y = 3
} confPrefix;

/* A confidential (256-bit) hash.
 * When 'prefix' is either 'EVEN_Y' or 'ODD_Y' then 'data' contains the x-coordinate of the point on the secp256k1 curve
 * representing the blinded value.
 * When 'prefix' is 'EXPLICIT' then 'data' is the unblinded 256-bit hash.
 * When 'prefix' is 'NONE' the value is "NULL" and the 'data' field is unused.
 */
typedef struct confidential {
  sha256_midstate data;
  confPrefix prefix;
} confidential;

/* A confidential 64-bit value.
 * When 'prefix' is either 'EVEN_Y' or 'ODD_Y' then 'confidential' contains the x-coordinate of the point on the secp256k1 curve
 * representing the blinded value.
 * When 'prefix' is 'EXPLICIT' then 'explicit' is the unblinded 256-bit hash.
 * When 'prefix' is 'NONE' the value is "NULL" and the 'confidential' and 'explicit' fields are unused.
 */
typedef struct confAmount {
  union {
    sha256_midstate confidential;
    uint_fast64_t explicit;
  };
  confPrefix prefix;
} confAmount;

/* In Elements, a null-data scriptPubKey consists of an OP_RETURN followed by data only pushes (i.e. only opcodes less than OP_16).
 * This is an enumeration of all such data only push operation names.
 * OP_IMMEDIATE represents OP_0 and all the one-byte prefixes of data pushes upto 75 bytes.
 */
typedef enum opcodeType {
  OP_IMMEDIATE,
  OP_PUSHDATA,
  OP_PUSHDATA2,
  OP_PUSHDATA4,
  OP_1NEGATE,
  OP_RESERVED,
  OP_1,
  OP_2,
  OP_3,
  OP_4,
  OP_5,
  OP_6,
  OP_7,
  OP_8,
  OP_9,
  OP_10,
  OP_11,
  OP_12,
  OP_13,
  OP_14,
  OP_15,
  OP_16
} opcodeType;

/* In Elements, a null-data scriptPubKey consists of an OP_RETURN followed by data only pushes (i.e. only opcodes less than OP_16).
 * This is a structure represents a digest of all such operations.
 * 'code' represents the operation name.
 * If 'code' \in {OP_IMMEDIATE, OP_PUSHDATA, OP_PUSHDATA2, OP_PUSHDATA4} then 'dataHash' represents the SHA-256 hash of data pushed
 * by the push operation.
 */
typedef struct opcode {
  sha256_midstate dataHash;
  opcodeType code;
} opcode;

/* In Elements, a null-data scriptPubKey consists of an OP_RETURN followed by data only pushes (i.e. only opcodes less than OP_16).
 * This is an structure for an array of digets of null-data scriptPubKeys.
 * 'op' is an array of the (digests of) each data push.
 * Note that 'len' is 0 for a null-data scriptPubKey consisting of only an OP_RETURN.
 *
 * Invariant: opcode op[len] (or op == NULL and len == 0)
 */
typedef struct parsedNullData {
  const opcode* op;
  uint_fast32_t len;
} parsedNullData;

/* A structure representing data from one output from an Elements transaction.
 * 'scriptPubKey' is the SHA-256 hash of the outputs scriptPubKey.
 * 'isNullData' is true if the output has a null-data scriptPubKey.
 */
typedef struct sigOutput {
  confidential asset;
  confAmount amt;
  confidential nonce;
  sha256_midstate scriptPubKey;
  parsedNullData pnd;
  bool isNullData;
} sigOutput;

/* The data held by an Elements unspent transaction output database.
 * This 'scriptPubKey' of the unspent transaction output, which in our application is digested as a SHA-256 hash.
 * This also includes the asset and amout of the output, each of which may or may not be blinded.
 */
typedef struct utxo {
  sha256_midstate scriptPubKey;
  confidential asset;
  confAmount amt;
} utxo;

/* In Elements, a trasaction input can optionally issue a new asset or reissue an existing asset.
 * This enumerates those possibilities.
 */
typedef enum issuanceType {
  NO_ISSUANCE = 0,
  NEW_ISSUANCE,
  REISSUANCE
} issuanceType;

/* In Elements, a trasaction input can optionally issue a new asset or reissue an existing asset.
 * This structure contains data about such an issuance.
 *
 * Invariant: If 'type == NEW_ISSUANCE' then 'contractHash' and 'tokenAmt' are active;
 *            If 'type == REISSUANCE' then 'entropy' and 'blindingNonce' are active;
 */
typedef struct assetIssuance {
  union {
    struct {
      sha256_midstate contractHash;
      confAmount tokenAmt;
    };
    struct {
      sha256_midstate entropy;
      sha256_midstate blindingNonce;
    };
  };
  confAmount assetAmt;
  issuanceType type;
} assetIssuance;

/* A structure representing data from one input from an Elements transaction along with the utxo data of the output being redeemed.
 * When 'isPegin' then the 'prevOutpoint' represents an outpoint of another chain.
 */
typedef struct sigInput {
  outpoint prevOutpoint;
  utxo txo;
  uint_fast32_t sequence;
  assetIssuance issuance;
  bool isPegin;
} sigInput;

/* A structure representing data from an Elements transaction (along with the utxo data of the outputs being redeemed).
 * 'inputsHash' and 'outputsHash' are a cache of the hash of the input and output data respectively.
 */
typedef struct transaction {
  const sigInput* input;
  const sigOutput* output;
  sha256_midstate inputsHash;
  sha256_midstate outputsHash;
  uint_fast32_t numInputs;
  uint_fast32_t numOutputs;
  uint_fast32_t version;
  uint_fast32_t lockTime;
} transaction;

/* The 'txEnv' structure used by the Elements application of Simplcity.
 *
 * It includes
 * + the transaction data, which may be shared when Simplicity expressions are used for multiple inputs in the same transaction),
 * + the input index under consideration,
 * + and the commitment Merkle root of the Simplicity expression being executed.
 */
typedef struct txEnv {
  const transaction* tx;
  const uint32_t* scriptCMR;
  uint_fast32_t ix;
} txEnv;

#endif
