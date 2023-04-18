/* This module implements the 'primitive.h' interface for the Elements application of Simplicity.
 */
#include "primitive.h"

#include <stdlib.h>
#include "jets.h"
#include "../../limitations.h"
#include "../../prefix.h"
#include "../../primitive.h"
#include "../../unreachable.h"

/* An enumeration of all the types we need to construct to specify the input and output types of all jets created by 'decodeJet'. */
enum TypeNamesForJets {
#include "primitiveEnumTy.inc"
  NumberOfTypeNames
};

/* Allocate a fresh set of unification variables bound to at least all the types necessary
 * for all the jets that can be created by 'decodeJet', and also the type 'TWO^256',
 * and also allocate space for 'extra_var_len' many unification variables.
 * Return the number of non-trivial bindings created.
 *
 * However, if malloc fails, then return 0.
 *
 * Precondition: NULL != bound_var;
 *               NULL != word256_ix;
 *               NULL != extra_var_start;
 *               extra_var_len <= 6*DAG_LEN_MAX;
 *
 * Postcondition: Either '*bound_var == NULL' and the function returns 0
 *                or 'unification_var (*bound_var)[*extra_var_start + extra_var_len]' is an array of unification variables
 *                   such that for any 'jet : A |- B' there is some 'i < *extra_var_start' and 'j < *extra_var_start' such that
 *                      '(*bound_var)[i]' is bound to 'A' and '(*bound_var)[j]' is bound to 'B'
 *                   and, '*word256_ix < *extra_var_start' and '(*bound_var)[*word256_ix]' is bound the type 'TWO^256'
 */
size_t mallocBoundVars(unification_var** bound_var, size_t* word256_ix, size_t* extra_var_start, size_t extra_var_len) {
  static_assert(1 <= NumberOfTypeNames, "Missing TypeNamesForJets.");
  static_assert(NumberOfTypeNames <= NUMBER_OF_TYPENAMES_MAX, "Too many TypeNamesForJets.");
  static_assert(DAG_LEN_MAX <= (SIZE_MAX - NumberOfTypeNames) / 6, "NumberOfTypeNames + 6*DAG_LEN_MAX doesn't fit in size_t");
  static_assert(NumberOfTypeNames + 6*DAG_LEN_MAX <= SIZE_MAX/sizeof(unification_var) , "bound_var array too large");
  static_assert(NumberOfTypeNames + 6*DAG_LEN_MAX - 1 <= UINT32_MAX, "bound_var array index doesn't fit in uint32_t");
  assert(extra_var_len <= 6*DAG_LEN_MAX);
  *bound_var = malloc((NumberOfTypeNames + extra_var_len) * sizeof(unification_var));
  if (!(*bound_var)) return 0;
#include "primitiveInitTy.inc"
  *word256_ix = ty_w256;
  *extra_var_start = NumberOfTypeNames;

  /* 'ty_u' is a trivial binding, so we made 'NumberOfTypeNames - 1' non-trivial bindings. */
  return NumberOfTypeNames - 1;
};

/* An enumeration of the names of Elements specific jets and primitives. */
typedef enum jetName
{
#include "primitiveEnumJet.inc"
  NUMBER_OF_JET_NAMES
} jetName;

/* Decode an Elements specific jet name from 'stream' into 'result'.
 * All jets begin with a bit prefix of '1' which needs to have already been consumed from the 'stream'.
 * Returns 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' if the stream's prefix doesn't match any valid code for a jet.
 * Returns 'SIMPLICITY_ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * In the above error cases, 'result' may be modified.
 * Returns 0 if successful.
 *
 * Precondition: NULL != result
 *               NULL != stream
 */
static int32_t decodePrimitive(jetName* result, bitstream* stream) {
  int32_t bit = read1Bit(stream);
  if (bit < 0) return bit;
  if (!bit) {
    /* Core jets */
    int32_t code = decodeUptoMaxInt(stream);
    if (code < 0) return code;

    switch (code) {
     case 1: /* Word jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return code;
      switch (code) {
       case 1: /* Verify */
        *result = VERIFY; return 0;
       case 2: /* Low */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return code;
        switch (code) {
         case 5: *result = LOW_32; return 0;
        }
        break;
       case 13: /* Eq */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return code;
        switch (code) {
         case 5: *result = EQ_32; return 0;
         case 8: *result = EQ_256; return 0;
        }
        break;
      }
      break;
     case 2: /* Arith jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return code;

      switch (code) {
       case 1: /* One */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return code;
        switch (code) {
         case 5: *result = ONE_32; return 0;
        }
        break;
       case 2: /* FullAdd */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return code;
        switch (code) {
         case 5: *result = FULL_ADD_32; return 0;
        }
        break;
       case 3: /* Add */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return code;
        switch (code) {
         case 5: *result = ADD_32; return 0;
        }
        break;
       case 7: /* FullSubtract */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return code;
        switch (code) {
         case 5: *result = FULL_SUBTRACT_32; return 0;
        }
        break;
       case 8: /* Subtract */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return code;
        switch (code) {
         case 5: *result = SUBTRACT_32; return 0;
        }
        break;
       case 12: /* FullMultiply */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return code;
        switch (code) {
         case 5: *result = FULL_MULTIPLY_32; return 0;
        }
        break;
       case 13: /* Multiply */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return code;
        switch (code) {
         case 5: *result = MULTIPLY_32; return 0;
        }
        break;
       case 16: /* Le */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return code;
        switch (code) {
         case 5: *result = LE_32; return 0;
        }
        break;
      }
      break;
     case 3: /* Hash jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return code;
      switch (code) {
       case 1: /* SHA-256 section */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return code;
        switch (code) {
         case 1: *result = SHA_256_BLOCK; return 0;
         case 2: *result = SHA_256_IV; return 0;
         case 3: /* SHA-256-CTX-8-ADD-n subsection */
           code = decodeUptoMaxInt(stream);
           if (code < 0) return code;
           switch (code) {
             case 1: *result = SHA_256_CTX_8_ADD_1; return 0;
             case 2: *result = SHA_256_CTX_8_ADD_2; return 0;
             case 3: *result = SHA_256_CTX_8_ADD_4; return 0;
             case 4: *result = SHA_256_CTX_8_ADD_8; return 0;
             case 5: *result = SHA_256_CTX_8_ADD_16; return 0;
             case 6: *result = SHA_256_CTX_8_ADD_32; return 0;
             case 7: *result = SHA_256_CTX_8_ADD_64; return 0;
             case 8: *result = SHA_256_CTX_8_ADD_128; return 0;
             case 9: *result = SHA_256_CTX_8_ADD_256; return 0;
             case 10: *result = SHA_256_CTX_8_ADD_512; return 0;
           }
           break;
         case 4: *result = SHA_256_CTX_8_ADD_BUFFER_511; return 0;
         case 5: *result = SHA_256_CTX_8_FINALIZE; return 0;
         case 6: *result = SHA_256_CTX_8_INIT; return 0;
        }
        break;
      }
      break;
     case 4: /* Secp256k1 jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return code;
      switch (code) {
       case 1: /* point-verify */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return code;
        switch (code) {
         case 1: *result = POINT_VERIFY_1; return 0;
        }
        break;
       case 2: *result = DECOMPRESS; return 0;
       case 3: /* linear-verify */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return code;
        switch (code) {
         case 1: *result = LINEAR_VERIFY_1; return 0;
        }
        break;
       case 4: /* linear-combination */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return code;
        switch (code) {
         case 1: *result = LINEAR_COMBINATION_1; return 0;
        }
        break;
       case 5: *result = SCALE; return 0;
       case 6: *result = GENERATE; return 0;
       case 7: *result = GEJ_INFINITY; return 0;
       case 8: *result = GEJ_NORMALIZE; return 0;
       case 9: *result = GEJ_NEGATE; return 0;
       case 10: *result = GE_NEGATE; return 0;
       case 11: *result = GEJ_DOUBLE; return 0;
       case 12: *result = GEJ_ADD; return 0;
       case 13: *result = GEJ_GE_ADD_EX; return 0;
       case 14: *result = GEJ_GE_ADD; return 0;
       case 15: *result = GEJ_RESCALE; return 0;
       case 16: *result = GEJ_IS_INFINITY; return 0;

       case 19: *result = GEJ_X_EQUIV; return 0;
       case 20: *result = GEJ_Y_IS_ODD; return 0;
       case 21: *result = GEJ_IS_ON_CURVE; return 0;
       case 22: *result = GE_IS_ON_CURVE; return 0;
       case 23: *result = SCALAR_NORMALIZE; return 0;
       case 24: *result = SCALAR_NEGATE; return 0;
       case 25: *result = SCALAR_ADD; return 0;
       case 26: *result = SCALAR_SQUARE; return 0;
       case 27: *result = SCALAR_MULTIPLY; return 0;
       case 28: *result = SCALAR_MULTIPLY_LAMBDA; return 0;
       case 29: *result = SCALAR_INVERT; return 0;
       case 30: *result = SCALAR_IS_ZERO; return 0;

       case 35: *result = FE_NORMALIZE; return 0;
       case 36: *result = FE_NEGATE; return 0;
       case 37: *result = FE_ADD; return 0;
       case 38: *result = FE_SQUARE; return 0;
       case 39: *result = FE_MULTIPLY; return 0;
       case 40: *result = FE_MULTIPLY_BETA; return 0;
       case 41: *result = FE_INVERT; return 0;
       case 42: *result = FE_SQUARE_ROOT; return 0;
       case 43: *result = FE_IS_ZERO; return 0;
       case 44: *result = FE_IS_ODD; return 0;
      }
      break;
     case 5: /* Signature jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return code;
      switch (code) {
       case 1: *result = CHECK_SIG_VERIFY; return 0;
       case 2: *result = BIP_0340_VERIFY; return 0;
      }
      break;
     case 7: /* Bitcoin jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return code;
      switch (code) {
       case 1: *result = PARSE_LOCK; return 0;
       case 2: *result = PARSE_SEQUENCE; return 0;
      }
      break;
    }
    return SIMPLICITY_ERR_DATA_OUT_OF_RANGE;
  } else {
    /* Elements jets */
    int32_t code = decodeUptoMaxInt(stream);
    if (code < 0) return code;
    switch (code) {
     case 1: /* SigHash jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return code;
      switch (code) {
       case 1: *result = SIG_ALL_HASH; return 0;
       case 2: *result = TX_HASH; return 0;
       case 3: *result = TAP_ENV_HASH; return 0;
       case 4: *result = INPUTS_HASH; return 0;
       case 5: *result = OUTPUTS_HASH; return 0;
       case 6: *result = ISSUANCES_HASH; return 0;
       case 7: *result = INPUT_UTXOS_HASH; return 0;
       case 8: *result = OUTPUT_AMOUNTS_HASH; return 0;
       case 9: *result = OUTPUT_SCRIPTS_HASH; return 0;
       case 10: *result = OUTPUT_NONCES_HASH; return 0;
       case 11: *result = OUTPUT_RANGE_PROOFS_HASH; return 0;
       case 12: *result = OUTPUT_SURJECTION_PROOFS_HASH; return 0;
       case 13: *result = INPUT_OUTPOINTS_HASH; return 0;
       case 14: *result = INPUT_SEQUENCES_HASH; return 0;
       case 15: *result = INPUT_ANNEXES_HASH; return 0;
       case 16: *result = INPUT_SCRIPT_SIGS_HASH; return 0;
       case 17: *result = ISSUANCE_ASSET_AMOUNTS_HASH; return 0;
       case 18: *result = ISSUANCE_TOKEN_AMOUNTS_HASH; return 0;
       case 19: *result = ISSUANCE_RANGE_PROOFS_HASH; return 0;
       case 20: *result = ISSUANCE_BLINDING_ENTROPY_HASH; return 0;
       case 21: *result = INPUT_AMOUNTS_HASH; return 0;
       case 22: *result = INPUT_SCRIPTS_HASH; return 0;
       case 23: *result = TAPLEAF_HASH; return 0;
       case 24: *result = TAPBRANCH_HASH; return 0;
       case 25: *result = OUTPOINT_HASH; return 0;
       case 26: *result = ASSET_AMOUNT_HASH; return 0;
       case 27: *result = NONCE_HASH; return 0;
       case 28: *result = ANNEX_HASH; return 0;
       case 29: *result = BUILD_TAPLEAF_SIMPLICITY; return 0;
       case 30: *result = BUILD_TAPBRANCH; return 0;
      }
      break;
     case 2: /* Timelock jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return code;
      switch (code) {
       case 1: *result = CHECK_LOCK_HEIGHT; return 0;
       case 2: *result = CHECK_LOCK_TIME; return 0;
       case 3: *result = CHECK_LOCK_DISTANCE; return 0;
       case 4: *result = CHECK_LOCK_DURATION; return 0;
       case 5: *result = TX_LOCK_HEIGHT; return 0;
       case 6: *result = TX_LOCK_TIME; return 0;
       case 7: *result = TX_LOCK_DISTANCE; return 0;
       case 8: *result = TX_LOCK_DURATION; return 0;
       case 9: *result = TX_IS_FINAL; return 0;
      }
      break;
     case 3: /* Issuance jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return code;
      switch (code) {
       case 1: *result = ISSUANCE; return 0;
       case 2: *result = ISSUANCE_ASSET; return 0;
       case 3: *result = ISSUANCE_TOKEN; return 0;
       case 4: *result = ISSUANCE_ENTROPY; return 0;
       case 5: *result = CALCULATE_ISSUANCE_ENTROPY; return 0;
       case 6: *result = CALCULATE_ASSET; return 0;
       case 7: *result = CALCULATE_EXPLICIT_TOKEN; return 0;
       case 8: *result = CALCULATE_CONFIDENTIAL_TOKEN; return 0;
      }
      break;
     case 4: /* Transaction jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return code;
      switch (code) {
       case 1: *result = SCRIPT_CMR; return 0;
       case 2: *result = INTERNAL_KEY; return 0;
       case 3: *result = CURRENT_INDEX; return 0;
       case 4: *result = NUM_INPUTS; return 0;
       case 5: *result = NUM_OUTPUTS; return 0;
       case 6: *result = LOCK_TIME; return 0;
       case 7: *result = OUTPUT_ASSET; return 0;
       case 8: *result = OUTPUT_AMOUNT; return 0;
       case 9: *result = OUTPUT_NONCE; return 0;
       case 10: *result = OUTPUT_SCRIPT_HASH; return 0;
       case 11: *result = OUTPUT_NULL_DATUM; return 0;
       case 12: *result = OUTPUT_SURJECTION_PROOF; return 0;
       case 13: *result = OUTPUT_RANGE_PROOF; return 0;
       /* case 14: *result = TOTAL_FEE; return 0; */
       case 15: *result = CURRENT_PEGIN; return 0;
       case 16: *result = CURRENT_PREV_OUTPOINT; return 0;
       case 17: *result = CURRENT_ASSET; return 0;
       case 18: *result = CURRENT_AMOUNT; return 0;
       case 19: *result = CURRENT_SCRIPT_HASH; return 0;
       case 20: *result = CURRENT_SEQUENCE; return 0;
       case 21: *result = CURRENT_ANNEX_HASH; return 0;
       case 22: *result = CURRENT_SCRIPT_SIG_HASH; return 0;
       case 23: *result = CURRENT_REISSUANCE_BLINDING; return 0;
       case 24: *result = CURRENT_NEW_ISSUANCE_CONTRACT; return 0;
       case 25: *result = CURRENT_REISSUANCE_ENTROPY; return 0;
       case 26: *result = CURRENT_ISSUANCE_ASSET_AMOUNT; return 0;
       case 27: *result = CURRENT_ISSUANCE_TOKEN_AMOUNT; return 0;
       case 28: *result = CURRENT_ISSUANCE_ASSET_PROOF; return 0;
       case 29: *result = CURRENT_ISSUANCE_TOKEN_PROOF; return 0;
       case 30: *result = INPUT_PEGIN; return 0;
       case 31: *result = INPUT_PREV_OUTPOINT; return 0;
       case 32: *result = INPUT_ASSET; return 0;
       case 33: *result = INPUT_AMOUNT; return 0;
       case 34: *result = INPUT_SCRIPT_HASH; return 0;
       case 35: *result = INPUT_SEQUENCE; return 0;
       case 36: *result = INPUT_ANNEX_HASH; return 0;
       case 37: *result = INPUT_SCRIPT_SIG_HASH; return 0;
       case 38: *result = REISSUANCE_BLINDING; return 0;
       case 39: *result = NEW_ISSUANCE_CONTRACT; return 0;
       case 40: *result = REISSUANCE_ENTROPY; return 0;
       case 41: *result = ISSUANCE_ASSET_AMOUNT; return 0;
       case 42: *result = ISSUANCE_TOKEN_AMOUNT; return 0;
       case 43: *result = ISSUANCE_ASSET_PROOF; return 0;
       case 44: *result = ISSUANCE_TOKEN_PROOF; return 0;
       case 45: *result = TAPLEAF_VERSION; return 0;
       case 46: *result = TAPBRANCH; return 0;
       case 47: *result = VERSION; return 0;
       case 48: *result = GENESIS_BLOCK_HASH; return 0;
      }
      break;
    }
    return SIMPLICITY_ERR_DATA_OUT_OF_RANGE;
  }
}

/* Return a copy of the Simplicity node corresponding to the given Elements specific jet 'name'. */
static dag_node jetNode(jetName name) {
  static const dag_node jet_node[] = {
    #include "primitiveJetNode.inc"
  };

  return jet_node[name];
}

/* Decode an Elements specific jet from 'stream' into 'node'.
 * All jets begin with a bit prefix of '1' which needs to have already been consumed from the 'stream'.
 * Returns 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' if the stream's prefix doesn't match any valid code for a jet.
 * Returns 'SIMPLICITY_ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * In the above error cases, 'dag' may be modified.
 * Returns 0 if successful.
 *
 * Precondition: NULL != node
 *               NULL != stream
 */
int32_t decodeJet(dag_node* node, bitstream* stream) {
  jetName name;
  int32_t err = decodePrimitive(&name, stream);
  if (err < 0) return err;
  *node = jetNode(name);
  return 0;
}
