/* This module implements the 'primitive.h' interface for the Elements application of Simplicity.
 */
#include "primitive.h"

#include <stdlib.h>
#include "jets.h"
#include "../../limitations.h"
#include "../../prefix.h"
#include "../../primitive.h"
#include "../../simplicity_assert.h"

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
  simplicity_assert(extra_var_len <= 6*DAG_LEN_MAX);
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
 * Returns 'SIMPLICITY_NO_ERROR' if successful.
 *
 * Precondition: NULL != result
 *               NULL != stream
 */
static simplicity_err decodePrimitive(jetName* result, bitstream* stream) {
  int32_t bit = read1Bit(stream);
  if (bit < 0) return (simplicity_err)bit;
  if (!bit) {
    /* Core jets */
    int32_t code = decodeUptoMaxInt(stream);
    if (code < 0) return (simplicity_err)code;

    switch (code) {
     case 1: /* Word jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return (simplicity_err)code;
      switch (code) {
       case 1: /* Verify */
        *result = VERIFY; return SIMPLICITY_NO_ERROR;
       case 2: /* Low */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = LOW_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = LOW_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = LOW_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = LOW_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 3: /* High */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = HIGH_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = HIGH_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = HIGH_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = HIGH_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 4: /* Complement */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = COMPLEMENT_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = COMPLEMENT_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = COMPLEMENT_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = COMPLEMENT_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 5: /* And */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = AND_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = AND_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = AND_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = AND_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 6: /* Or */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = OR_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = OR_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = OR_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = OR_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 7: /* Xor */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = XOR_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = XOR_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = XOR_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = XOR_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 8: /* Maj */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = MAJ_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = MAJ_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = MAJ_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = MAJ_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 9: /* Xor_Xor */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = XOR_XOR_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = XOR_XOR_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = XOR_XOR_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = XOR_XOR_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 10: /* Ch */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = CH_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = CH_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = CH_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = CH_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 11: /* Some */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = SOME_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = SOME_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = SOME_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = SOME_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 12: /* All */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = ALL_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = ALL_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = ALL_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = ALL_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 13: /* Eq */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = EQ_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = EQ_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = EQ_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = EQ_64; return SIMPLICITY_NO_ERROR;
         case 8: *result = EQ_256; return SIMPLICITY_NO_ERROR;
        }
        break;
      }
      break;
     case 2: /* Arith jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return (simplicity_err)code;

      switch (code) {
       case 1: /* One */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = ONE_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = ONE_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = ONE_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = ONE_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 2: /* FullAdd */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = FULL_ADD_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = FULL_ADD_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = FULL_ADD_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = FULL_ADD_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 3: /* Add */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = ADD_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = ADD_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = ADD_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = ADD_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 4: /* FullIncrement */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = FULL_INCREMENT_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = FULL_INCREMENT_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = FULL_INCREMENT_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = FULL_INCREMENT_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 5: /* Increment */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = INCREMENT_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = INCREMENT_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = INCREMENT_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = INCREMENT_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 7: /* FullSubtract */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = FULL_SUBTRACT_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = FULL_SUBTRACT_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = FULL_SUBTRACT_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = FULL_SUBTRACT_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 8: /* Subtract */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = SUBTRACT_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = SUBTRACT_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = SUBTRACT_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = SUBTRACT_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 9: /* Negate */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = NEGATE_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = NEGATE_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = NEGATE_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = NEGATE_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 10: /* FullDecrement */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = FULL_DECREMENT_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = FULL_DECREMENT_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = FULL_DECREMENT_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = FULL_DECREMENT_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 11: /* Decrement */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = DECREMENT_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = DECREMENT_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = DECREMENT_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = DECREMENT_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 12: /* FullMultiply */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = FULL_MULTIPLY_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = FULL_MULTIPLY_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = FULL_MULTIPLY_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = FULL_MULTIPLY_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 13: /* Multiply */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = MULTIPLY_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = MULTIPLY_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = MULTIPLY_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = MULTIPLY_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 14: /* IsZero */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = IS_ZERO_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = IS_ZERO_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = IS_ZERO_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = IS_ZERO_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 15: /* IsOne */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = IS_ONE_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = IS_ONE_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = IS_ONE_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = IS_ONE_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 16: /* Le */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = LE_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = LE_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = LE_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = LE_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 17: /* Lt */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = LT_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = LT_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = LT_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = LT_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 18: /* Min */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = MIN_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = MIN_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = MIN_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = MIN_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 19: /* Max */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = MAX_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = MAX_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = MAX_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = MAX_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 20: /* Median */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = MEDIAN_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = MEDIAN_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = MEDIAN_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = MEDIAN_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 22: /* DivMod */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = DIV_MOD_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = DIV_MOD_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = DIV_MOD_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = DIV_MOD_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 23: /* Divide */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = DIVIDE_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = DIVIDE_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = DIVIDE_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = DIVIDE_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 24: /* Modulo */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = MODULO_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = MODULO_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = MODULO_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = MODULO_64; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 25: /* Divides */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 3: *result = DIVIDES_8; return SIMPLICITY_NO_ERROR;
         case 4: *result = DIVIDES_16; return SIMPLICITY_NO_ERROR;
         case 5: *result = DIVIDES_32; return SIMPLICITY_NO_ERROR;
         case 6: *result = DIVIDES_64; return SIMPLICITY_NO_ERROR;
        }
        break;
      }
      break;
     case 3: /* Hash jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return (simplicity_err)code;
      switch (code) {
       case 1: /* SHA-256 section */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 1: *result = SHA_256_BLOCK; return SIMPLICITY_NO_ERROR;
         case 2: *result = SHA_256_IV; return SIMPLICITY_NO_ERROR;
         case 3: /* SHA-256-CTX-8-ADD-n subsection */
           code = decodeUptoMaxInt(stream);
           if (code < 0) return (simplicity_err)code;
           switch (code) {
             case 1: *result = SHA_256_CTX_8_ADD_1; return SIMPLICITY_NO_ERROR;
             case 2: *result = SHA_256_CTX_8_ADD_2; return SIMPLICITY_NO_ERROR;
             case 3: *result = SHA_256_CTX_8_ADD_4; return SIMPLICITY_NO_ERROR;
             case 4: *result = SHA_256_CTX_8_ADD_8; return SIMPLICITY_NO_ERROR;
             case 5: *result = SHA_256_CTX_8_ADD_16; return SIMPLICITY_NO_ERROR;
             case 6: *result = SHA_256_CTX_8_ADD_32; return SIMPLICITY_NO_ERROR;
             case 7: *result = SHA_256_CTX_8_ADD_64; return SIMPLICITY_NO_ERROR;
             case 8: *result = SHA_256_CTX_8_ADD_128; return SIMPLICITY_NO_ERROR;
             case 9: *result = SHA_256_CTX_8_ADD_256; return SIMPLICITY_NO_ERROR;
             case 10: *result = SHA_256_CTX_8_ADD_512; return SIMPLICITY_NO_ERROR;
           }
           break;
         case 4: *result = SHA_256_CTX_8_ADD_BUFFER_511; return SIMPLICITY_NO_ERROR;
         case 5: *result = SHA_256_CTX_8_FINALIZE; return SIMPLICITY_NO_ERROR;
         case 6: *result = SHA_256_CTX_8_INIT; return SIMPLICITY_NO_ERROR;
        }
        break;
      }
      break;
     case 4: /* Secp256k1 jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return (simplicity_err)code;
      switch (code) {
       case 1: /* point-verify */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 1: *result = POINT_VERIFY_1; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 2: *result = DECOMPRESS; return SIMPLICITY_NO_ERROR;
       case 3: /* linear-verify */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 1: *result = LINEAR_VERIFY_1; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 4: /* linear-combination */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return (simplicity_err)code;
        switch (code) {
         case 1: *result = LINEAR_COMBINATION_1; return SIMPLICITY_NO_ERROR;
        }
        break;
       case 5: *result = SCALE; return SIMPLICITY_NO_ERROR;
       case 6: *result = GENERATE; return SIMPLICITY_NO_ERROR;
       case 7: *result = GEJ_INFINITY; return SIMPLICITY_NO_ERROR;
       case 8: *result = GEJ_NORMALIZE; return SIMPLICITY_NO_ERROR;
       case 9: *result = GEJ_NEGATE; return SIMPLICITY_NO_ERROR;
       case 10: *result = GE_NEGATE; return SIMPLICITY_NO_ERROR;
       case 11: *result = GEJ_DOUBLE; return SIMPLICITY_NO_ERROR;
       case 12: *result = GEJ_ADD; return SIMPLICITY_NO_ERROR;
       case 13: *result = GEJ_GE_ADD_EX; return SIMPLICITY_NO_ERROR;
       case 14: *result = GEJ_GE_ADD; return SIMPLICITY_NO_ERROR;
       case 15: *result = GEJ_RESCALE; return SIMPLICITY_NO_ERROR;
       case 16: *result = GEJ_IS_INFINITY; return SIMPLICITY_NO_ERROR;

       case 19: *result = GEJ_X_EQUIV; return SIMPLICITY_NO_ERROR;
       case 20: *result = GEJ_Y_IS_ODD; return SIMPLICITY_NO_ERROR;
       case 21: *result = GEJ_IS_ON_CURVE; return SIMPLICITY_NO_ERROR;
       case 22: *result = GE_IS_ON_CURVE; return SIMPLICITY_NO_ERROR;
       case 23: *result = SCALAR_NORMALIZE; return SIMPLICITY_NO_ERROR;
       case 24: *result = SCALAR_NEGATE; return SIMPLICITY_NO_ERROR;
       case 25: *result = SCALAR_ADD; return SIMPLICITY_NO_ERROR;
       case 26: *result = SCALAR_SQUARE; return SIMPLICITY_NO_ERROR;
       case 27: *result = SCALAR_MULTIPLY; return SIMPLICITY_NO_ERROR;
       case 28: *result = SCALAR_MULTIPLY_LAMBDA; return SIMPLICITY_NO_ERROR;
       case 29: *result = SCALAR_INVERT; return SIMPLICITY_NO_ERROR;
       case 30: *result = SCALAR_IS_ZERO; return SIMPLICITY_NO_ERROR;

       case 35: *result = FE_NORMALIZE; return SIMPLICITY_NO_ERROR;
       case 36: *result = FE_NEGATE; return SIMPLICITY_NO_ERROR;
       case 37: *result = FE_ADD; return SIMPLICITY_NO_ERROR;
       case 38: *result = FE_SQUARE; return SIMPLICITY_NO_ERROR;
       case 39: *result = FE_MULTIPLY; return SIMPLICITY_NO_ERROR;
       case 40: *result = FE_MULTIPLY_BETA; return SIMPLICITY_NO_ERROR;
       case 41: *result = FE_INVERT; return SIMPLICITY_NO_ERROR;
       case 42: *result = FE_SQUARE_ROOT; return SIMPLICITY_NO_ERROR;
       case 43: *result = FE_IS_ZERO; return SIMPLICITY_NO_ERROR;
       case 44: *result = FE_IS_ODD; return SIMPLICITY_NO_ERROR;
      }
      break;
     case 5: /* Signature jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return (simplicity_err)code;
      switch (code) {
       case 1: *result = CHECK_SIG_VERIFY; return SIMPLICITY_NO_ERROR;
       case 2: *result = BIP_0340_VERIFY; return SIMPLICITY_NO_ERROR;
      }
      break;
     case 7: /* Bitcoin jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return (simplicity_err)code;
      switch (code) {
       case 1: *result = PARSE_LOCK; return SIMPLICITY_NO_ERROR;
       case 2: *result = PARSE_SEQUENCE; return SIMPLICITY_NO_ERROR;
      }
      break;
    }
    return SIMPLICITY_ERR_DATA_OUT_OF_RANGE;
  } else {
    /* Elements jets */
    int32_t code = decodeUptoMaxInt(stream);
    if (code < 0) return (simplicity_err)code;
    switch (code) {
     case 1: /* SigHash jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return (simplicity_err)code;
      switch (code) {
       case 1: *result = SIG_ALL_HASH; return SIMPLICITY_NO_ERROR;
       case 2: *result = TX_HASH; return SIMPLICITY_NO_ERROR;
       case 3: *result = TAP_ENV_HASH; return SIMPLICITY_NO_ERROR;
       case 4: *result = INPUTS_HASH; return SIMPLICITY_NO_ERROR;
       case 5: *result = OUTPUTS_HASH; return SIMPLICITY_NO_ERROR;
       case 6: *result = ISSUANCES_HASH; return SIMPLICITY_NO_ERROR;
       case 7: *result = INPUT_UTXOS_HASH; return SIMPLICITY_NO_ERROR;
       case 8: *result = OUTPUT_AMOUNTS_HASH; return SIMPLICITY_NO_ERROR;
       case 9: *result = OUTPUT_SCRIPTS_HASH; return SIMPLICITY_NO_ERROR;
       case 10: *result = OUTPUT_NONCES_HASH; return SIMPLICITY_NO_ERROR;
       case 11: *result = OUTPUT_RANGE_PROOFS_HASH; return SIMPLICITY_NO_ERROR;
       case 12: *result = OUTPUT_SURJECTION_PROOFS_HASH; return SIMPLICITY_NO_ERROR;
       case 13: *result = INPUT_OUTPOINTS_HASH; return SIMPLICITY_NO_ERROR;
       case 14: *result = INPUT_SEQUENCES_HASH; return SIMPLICITY_NO_ERROR;
       case 15: *result = INPUT_ANNEXES_HASH; return SIMPLICITY_NO_ERROR;
       case 16: *result = INPUT_SCRIPT_SIGS_HASH; return SIMPLICITY_NO_ERROR;
       case 17: *result = ISSUANCE_ASSET_AMOUNTS_HASH; return SIMPLICITY_NO_ERROR;
       case 18: *result = ISSUANCE_TOKEN_AMOUNTS_HASH; return SIMPLICITY_NO_ERROR;
       case 19: *result = ISSUANCE_RANGE_PROOFS_HASH; return SIMPLICITY_NO_ERROR;
       case 20: *result = ISSUANCE_BLINDING_ENTROPY_HASH; return SIMPLICITY_NO_ERROR;
       case 21: *result = INPUT_AMOUNTS_HASH; return SIMPLICITY_NO_ERROR;
       case 22: *result = INPUT_SCRIPTS_HASH; return SIMPLICITY_NO_ERROR;
       case 23: *result = TAPLEAF_HASH; return SIMPLICITY_NO_ERROR;
       case 24: *result = TAPPATH_HASH; return SIMPLICITY_NO_ERROR;
       case 25: *result = OUTPOINT_HASH; return SIMPLICITY_NO_ERROR;
       case 26: *result = ASSET_AMOUNT_HASH; return SIMPLICITY_NO_ERROR;
       case 27: *result = NONCE_HASH; return SIMPLICITY_NO_ERROR;
       case 28: *result = ANNEX_HASH; return SIMPLICITY_NO_ERROR;
       case 29: *result = BUILD_TAPLEAF_SIMPLICITY; return SIMPLICITY_NO_ERROR;
       case 30: *result = BUILD_TAPBRANCH; return SIMPLICITY_NO_ERROR;
      }
      break;
     case 2: /* Timelock jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return (simplicity_err)code;
      switch (code) {
       case 1: *result = CHECK_LOCK_HEIGHT; return SIMPLICITY_NO_ERROR;
       case 2: *result = CHECK_LOCK_TIME; return SIMPLICITY_NO_ERROR;
       case 3: *result = CHECK_LOCK_DISTANCE; return SIMPLICITY_NO_ERROR;
       case 4: *result = CHECK_LOCK_DURATION; return SIMPLICITY_NO_ERROR;
       case 5: *result = TX_LOCK_HEIGHT; return SIMPLICITY_NO_ERROR;
       case 6: *result = TX_LOCK_TIME; return SIMPLICITY_NO_ERROR;
       case 7: *result = TX_LOCK_DISTANCE; return SIMPLICITY_NO_ERROR;
       case 8: *result = TX_LOCK_DURATION; return SIMPLICITY_NO_ERROR;
       case 9: *result = TX_IS_FINAL; return SIMPLICITY_NO_ERROR;
      }
      break;
     case 3: /* Issuance jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return (simplicity_err)code;
      switch (code) {
       case 1: *result = ISSUANCE; return SIMPLICITY_NO_ERROR;
       case 2: *result = ISSUANCE_ASSET; return SIMPLICITY_NO_ERROR;
       case 3: *result = ISSUANCE_TOKEN; return SIMPLICITY_NO_ERROR;
       case 4: *result = ISSUANCE_ENTROPY; return SIMPLICITY_NO_ERROR;
       case 5: *result = CALCULATE_ISSUANCE_ENTROPY; return SIMPLICITY_NO_ERROR;
       case 6: *result = CALCULATE_ASSET; return SIMPLICITY_NO_ERROR;
       case 7: *result = CALCULATE_EXPLICIT_TOKEN; return SIMPLICITY_NO_ERROR;
       case 8: *result = CALCULATE_CONFIDENTIAL_TOKEN; return SIMPLICITY_NO_ERROR;
      }
      break;
     case 4: /* Transaction jets chapter */
      code = decodeUptoMaxInt(stream);
      if (code < 0) return (simplicity_err)code;
      switch (code) {
       case 1: *result = SCRIPT_CMR; return SIMPLICITY_NO_ERROR;
       case 2: *result = INTERNAL_KEY; return SIMPLICITY_NO_ERROR;
       case 3: *result = CURRENT_INDEX; return SIMPLICITY_NO_ERROR;
       case 4: *result = NUM_INPUTS; return SIMPLICITY_NO_ERROR;
       case 5: *result = NUM_OUTPUTS; return SIMPLICITY_NO_ERROR;
       case 6: *result = LOCK_TIME; return SIMPLICITY_NO_ERROR;
       case 7: *result = OUTPUT_ASSET; return SIMPLICITY_NO_ERROR;
       case 8: *result = OUTPUT_AMOUNT; return SIMPLICITY_NO_ERROR;
       case 9: *result = OUTPUT_NONCE; return SIMPLICITY_NO_ERROR;
       case 10: *result = OUTPUT_SCRIPT_HASH; return SIMPLICITY_NO_ERROR;
       case 11: *result = OUTPUT_NULL_DATUM; return SIMPLICITY_NO_ERROR;
       case 12: *result = OUTPUT_IS_FEE; return SIMPLICITY_NO_ERROR;
       case 13: *result = OUTPUT_SURJECTION_PROOF; return SIMPLICITY_NO_ERROR;
       case 14: *result = OUTPUT_RANGE_PROOF; return SIMPLICITY_NO_ERROR;
       /* case 15: *result = TOTAL_FEE; return SIMPLICITY_NO_ERROR; */
       case 16: *result = CURRENT_PEGIN; return SIMPLICITY_NO_ERROR;
       case 17: *result = CURRENT_PREV_OUTPOINT; return SIMPLICITY_NO_ERROR;
       case 18: *result = CURRENT_ASSET; return SIMPLICITY_NO_ERROR;
       case 19: *result = CURRENT_AMOUNT; return SIMPLICITY_NO_ERROR;
       case 20: *result = CURRENT_SCRIPT_HASH; return SIMPLICITY_NO_ERROR;
       case 21: *result = CURRENT_SEQUENCE; return SIMPLICITY_NO_ERROR;
       case 22: *result = CURRENT_ANNEX_HASH; return SIMPLICITY_NO_ERROR;
       case 23: *result = CURRENT_SCRIPT_SIG_HASH; return SIMPLICITY_NO_ERROR;
       case 24: *result = CURRENT_REISSUANCE_BLINDING; return SIMPLICITY_NO_ERROR;
       case 25: *result = CURRENT_NEW_ISSUANCE_CONTRACT; return SIMPLICITY_NO_ERROR;
       case 26: *result = CURRENT_REISSUANCE_ENTROPY; return SIMPLICITY_NO_ERROR;
       case 27: *result = CURRENT_ISSUANCE_ASSET_AMOUNT; return SIMPLICITY_NO_ERROR;
       case 28: *result = CURRENT_ISSUANCE_TOKEN_AMOUNT; return SIMPLICITY_NO_ERROR;
       case 29: *result = CURRENT_ISSUANCE_ASSET_PROOF; return SIMPLICITY_NO_ERROR;
       case 30: *result = CURRENT_ISSUANCE_TOKEN_PROOF; return SIMPLICITY_NO_ERROR;
       case 31: *result = INPUT_PEGIN; return SIMPLICITY_NO_ERROR;
       case 32: *result = INPUT_PREV_OUTPOINT; return SIMPLICITY_NO_ERROR;
       case 33: *result = INPUT_ASSET; return SIMPLICITY_NO_ERROR;
       case 34: *result = INPUT_AMOUNT; return SIMPLICITY_NO_ERROR;
       case 35: *result = INPUT_SCRIPT_HASH; return SIMPLICITY_NO_ERROR;
       case 36: *result = INPUT_SEQUENCE; return SIMPLICITY_NO_ERROR;
       case 37: *result = INPUT_ANNEX_HASH; return SIMPLICITY_NO_ERROR;
       case 38: *result = INPUT_SCRIPT_SIG_HASH; return SIMPLICITY_NO_ERROR;
       case 39: *result = REISSUANCE_BLINDING; return SIMPLICITY_NO_ERROR;
       case 40: *result = NEW_ISSUANCE_CONTRACT; return SIMPLICITY_NO_ERROR;
       case 41: *result = REISSUANCE_ENTROPY; return SIMPLICITY_NO_ERROR;
       case 42: *result = ISSUANCE_ASSET_AMOUNT; return SIMPLICITY_NO_ERROR;
       case 43: *result = ISSUANCE_TOKEN_AMOUNT; return SIMPLICITY_NO_ERROR;
       case 44: *result = ISSUANCE_ASSET_PROOF; return SIMPLICITY_NO_ERROR;
       case 45: *result = ISSUANCE_TOKEN_PROOF; return SIMPLICITY_NO_ERROR;
       case 46: *result = TAPLEAF_VERSION; return SIMPLICITY_NO_ERROR;
       case 47: *result = TAPPATH; return SIMPLICITY_NO_ERROR;
       case 48: *result = VERSION; return SIMPLICITY_NO_ERROR;
       case 49: *result = GENESIS_BLOCK_HASH; return SIMPLICITY_NO_ERROR;
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
 * Returns 'SIMPLICITY_NO_ERR' if successful.
 *
 * Precondition: NULL != node
 *               NULL != stream
 */
simplicity_err decodeJet(dag_node* node, bitstream* stream) {
  jetName name;
  simplicity_err error = decodePrimitive(&name, stream);
  if (!IS_OK(error)) return error;
  *node = jetNode(name);
  return SIMPLICITY_NO_ERROR;
}
