/* This module implements the 'primitive.h' interface for the Elements application of Simplicity.
 */
#include "primitive.h"

#include "jets.h"
#include "../../callonce.h"
#include "../../prefix.h"
#include "../../tag.h"
#include "../../unreachable.h"

#define PRIMITIVE_TAG(s) SIMPLICITY_PREFIX "\x1F" "Primitive\x1F" "Elements\x1F" s
#define JET_TAG SIMPLICITY_PREFIX "\x1F" "Jet"

/* An enumeration of all the types we need to construct to specify the input and output types of all jets created by 'decodeJet'. */
enum TypeNamesForJets {
  one,
  two,
  word2,
  word4,
  word8,
  word16,
  word32,
  word64,
  word128,
  word256,
  word512, ge = word512,
  word1024,
  pubkey,
  sTwo,
  outpnt,
  sOutpnt,
  confWord256,
  sConfWord256,
  sSConfWord256,
  confWord64,
  sConfWord64,
  sSConfWord64,
  sWord256,
  sSWord256,
  sWord32,
  sWord512,
  word2TimesWord256,
  twoPlusWord4,
  word2TimesWord256PlusTwoPlusWord4,
  sWord2TimesWord256PlusTwoPlusWord4,
  sSWord2TimesWord256PlusTwoPlusWord4,
  twoTimesWord32,
  twoTimesWord64,
  twoTimesWord256, point = twoTimesWord256,
  word256TimesWord512, scalarTimesGe = word256TimesWord512,
  word512TimesWord256, gej = word512TimesWord256,
  scalarTimesPoint,
  gejTimesFe,
  gejTimesGe,
  feTimesGej, scalarTimesGej = feTimesGej,
  gejTimesGej,
  scalarTimesPointTimesScalar,
  scalarTimesGeTimesScalar,
  scalarTimesGejTimesScalar,
  scalarTimesPointTimesScalarTimesPoint,
  scalarTimesGeTimesScalarTimesGe,
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
 *
 * Postcondition: Either '*bound_var == NULL' and the function returns 0
 *                or 'unification_var (*bound_var)[*extra_var_start + extra_var_len]' is an array of unification variables
 *                   such that for any 'jet : A |- B' there is some 'i < *extra_var_start' and 'j < *extra_var_start' such that
 *                      '(*bound_var)[i]' is bound to 'A' and '(*bound_var)[j]' is bound to 'B'
 *                   and, '*word256_ix < *extra_var_start' and '(*bound_var)[*word256_ix]' is bound the type 'TWO^256'
 */
size_t mallocBoundVars(unification_var** bound_var, size_t* word256_ix, size_t* extra_var_start, size_t extra_var_len) {
  _Static_assert(NumberOfTypeNames <= SIZE_MAX / sizeof(unification_var), "NumberOfTypeNames is too large");
  *bound_var = extra_var_len <= SIZE_MAX / sizeof(unification_var) - NumberOfTypeNames
             ? malloc((NumberOfTypeNames + extra_var_len) * sizeof(unification_var))
             : NULL;
  if (!(*bound_var)) return 0;
  (*bound_var)[one] = (unification_var){ .isBound = true,
      .bound = { .kind = ONE } };
  (*bound_var)[two] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[one] } } };
  (*bound_var)[word2] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[two], &(*bound_var)[two] } } };
  (*bound_var)[word4] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word2], &(*bound_var)[word2] } } };
  (*bound_var)[word8] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word4], &(*bound_var)[word4] } } };
  (*bound_var)[word16] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word8], &(*bound_var)[word8] } } };
  (*bound_var)[word32] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word16], &(*bound_var)[word16] } } };
  (*bound_var)[word64] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word32], &(*bound_var)[word32] } } };
  (*bound_var)[word128] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word64], &(*bound_var)[word64] } } };
  (*bound_var)[word256] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word128], &(*bound_var)[word128] } } };
  (*bound_var)[word512] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word256], &(*bound_var)[word256] } } };
  (*bound_var)[word1024] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word512], &(*bound_var)[word512] } } };
  (*bound_var)[pubkey] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[two], &(*bound_var)[word256] } } };
  (*bound_var)[sTwo] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[two] } } };
  (*bound_var)[outpnt] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word256], &(*bound_var)[word32] } } };
  (*bound_var)[sOutpnt] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[outpnt] } } };
  (*bound_var)[confWord256] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[pubkey], &(*bound_var)[word256] } } };
  (*bound_var)[sConfWord256] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[confWord256] } } };
  (*bound_var)[sSConfWord256] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[sConfWord256] } } };
  (*bound_var)[confWord64] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[pubkey], &(*bound_var)[word64] } } };
  (*bound_var)[sConfWord64] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[confWord64] } } };
  (*bound_var)[sSConfWord64] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[sConfWord64] } } };
  (*bound_var)[sWord256] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[word256] } } };
  (*bound_var)[sSWord256] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[sWord256] } } };
  (*bound_var)[sWord32] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[word32] } } };
  (*bound_var)[sWord512] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[word512] } } };
  (*bound_var)[word2TimesWord256] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word2], &(*bound_var)[word256] } } };
  (*bound_var)[twoPlusWord4] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[two], &(*bound_var)[word4] } } };
  (*bound_var)[word2TimesWord256PlusTwoPlusWord4] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM, .arg = { &(*bound_var)[word2TimesWord256], &(*bound_var)[twoPlusWord4] } } };
  (*bound_var)[sWord2TimesWord256PlusTwoPlusWord4] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[word2TimesWord256PlusTwoPlusWord4] } } };
  (*bound_var)[sSWord2TimesWord256PlusTwoPlusWord4] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[sWord2TimesWord256PlusTwoPlusWord4] } } };
  (*bound_var)[twoTimesWord32] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[two], &(*bound_var)[word32] } } };
  (*bound_var)[twoTimesWord64] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[two], &(*bound_var)[word64] } } };
  (*bound_var)[twoTimesWord256] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[two], &(*bound_var)[word256] } } };
  (*bound_var)[word256TimesWord512] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word256], &(*bound_var)[word512] } } };
  (*bound_var)[word512TimesWord256] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word512], &(*bound_var)[word256] } } };
  (*bound_var)[scalarTimesPoint] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word256], &(*bound_var)[point] } } };
  (*bound_var)[gejTimesFe] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[gej], &(*bound_var)[word256] } } };
  (*bound_var)[gejTimesGe] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[gej], &(*bound_var)[ge] } } };
  (*bound_var)[feTimesGej] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word256], &(*bound_var)[gej] } } };
  (*bound_var)[gejTimesGej] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[gej], &(*bound_var)[gej] } } };
  (*bound_var)[scalarTimesPointTimesScalar] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[scalarTimesPoint], &(*bound_var)[word256] } } };
  (*bound_var)[scalarTimesGeTimesScalar] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[scalarTimesGe], &(*bound_var)[word256] } } };
  (*bound_var)[scalarTimesGejTimesScalar] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[scalarTimesGej], &(*bound_var)[word256] } } };
  (*bound_var)[scalarTimesPointTimesScalarTimesPoint] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[scalarTimesPointTimesScalar], &(*bound_var)[point] } } };
  (*bound_var)[scalarTimesGeTimesScalarTimesGe] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[scalarTimesGeTimesScalar], &(*bound_var)[ge] } } };

  *word256_ix = word256;
  *extra_var_start = NumberOfTypeNames;

  /* 'one' is a trivial binding, so we made 'NumberOfTypeNames - 1' non-trivial bindings. */
  return NumberOfTypeNames - 1;
};

/* An enumeration of the names of Elements specific jets and primitives. */
typedef enum jetName
{ ADD_32
, SUBTRACT_32
, MULTIPLY_32
, FULL_ADD_32
, FULL_SUBTRACT_32
, FULL_MULTIPLY_32
, SHA_256_BLOCK
, SHA_256_HASHBLOCK

, FE_NORMALIZE
, FE_NEGATE
, FE_ADD
, FE_SQUARE
, FE_MULTIPLY
, FE_MULTIPLY_BETA
, FE_INVERT
, FE_SQUARE_ROOT
, FE_IS_ZERO
, FE_IS_ODD
, SCALAR_NORMALIZE
, SCALAR_NEGATE
, SCALAR_ADD
, SCALAR_SQUARE
, SCALAR_MULTIPLY
, SCALAR_MULTIPLY_LAMBDA
, SCALAR_INVERT
, SCALAR_IS_ZERO
, GEJ_INFINITY
, GEJ_NORMALIZE
, GEJ_NEGATE
, GE_NEGATE
, GEJ_DOUBLE
, GEJ_ADD
, GEJ_GE_ADD_EX
, GEJ_GE_ADD
, GEJ_RESCALE
, GEJ_IS_INFINITY
, GEJ_X_EQUIV
, GEJ_Y_IS_ODD
, GEJ_IS_ON_CURVE
, GE_IS_ON_CURVE
, GENERATE
, SCALE
, LINEAR_COMBINATION_1
, LINEAR_VERIFY_1
, POINT_VERIFY_1
, DECOMPRESS

, BIP0340_VERIFY

, VERSION
, LOCKTIME
, INPUTISPEGIN
, INPUTPREVOUTPOINT
, INPUTASSET
, INPUTAMOUNT
, INPUTSCRIPTHASH
, INPUTSEQUENCE
, INPUTISSUANCEBLINDING
, INPUTISSUANCECONTRACT
, INPUTISSUANCEENTROPY
, INPUTISSUANCEASSETAMT
, INPUTISSUANCETOKENAMT
, OUTPUTASSET
, OUTPUTAMOUNT
, OUTPUTNONCE
, OUTPUTSCRIPTHASH
, OUTPUTNULLDATUM
, SCRIPTCMR
, CURRENTINDEX
, CURRENTISPEGIN
, CURRENTPREVOUTPOINT
, CURRENTASSET
, CURRENTAMOUNT
, CURRENTSCRIPTHASH
, CURRENTSEQUENCE
, CURRENTISSUANCEBLINDING
, CURRENTISSUANCECONTRACT
, CURRENTISSUANCEENTROPY
, CURRENTISSUANCEASSETAMT
, CURRENTISSUANCETOKENAMT
, INPUTSHASH
, OUTPUTSHASH
, NUMINPUTS
, NUMOUTPUTS
, FEE
, NUMBER_OF_JET_NAMES
} jetName;

static int32_t either(jetName* result, jetName a, jetName b, bitstream* stream) {
  int32_t bit = getBit(stream);
  if (bit < 0) return bit;
  *result = bit ? b : a;
  return 0;
}

/* Decode an Elements specific jet name from 'stream' into 'result'.
 * All jets begin with a bit prefix of '1' which needs to have already been consumed from the 'stream'.
 * Returns 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' if the stream's prefix doesn't match any valid code for a jet.
 * Returns 'SIMPLICITY_ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * Returns 'SIMPLICITY_ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
 * In the above error cases, 'result' may be modified.
 * Returns 0 if successful.
 *
 * Precondition: NULL != result
 *               NULL != stream
 */
static int32_t decodePrimitive(jetName* result, bitstream* stream) {
  int32_t bit = getBit(stream);
  if (bit < 0) return bit;
  if (!bit) {
    int32_t code = getNBits(5, stream);
    if (code < 0) return code;

    switch (code) {
     case 0x0: return either(result, VERSION, LOCKTIME, stream);
     case 0x1: *result = INPUTISPEGIN; return 0;
     case 0x2: *result = INPUTPREVOUTPOINT; return 0;
     case 0x3: *result = INPUTASSET; return 0;
     case 0x4: return either(result, INPUTAMOUNT, INPUTSCRIPTHASH, stream);
     case 0x5: *result = INPUTSEQUENCE; return 0;
     case 0x6: *result = INPUTISSUANCEBLINDING; return 0;
     case 0x7: *result = INPUTISSUANCECONTRACT; return 0;
     case 0x8: return either(result, INPUTISSUANCEENTROPY, INPUTISSUANCEASSETAMT, stream);
     case 0x9: *result = INPUTISSUANCETOKENAMT; return 0;
     case 0xa: *result = OUTPUTASSET; return 0;
     case 0xb: *result = OUTPUTAMOUNT; return 0;
     case 0xc: return either(result, OUTPUTNONCE, OUTPUTSCRIPTHASH, stream);
     case 0xd: *result = OUTPUTNULLDATUM; return 0;
     case 0xe: *result = SCRIPTCMR; return 0;
     case 0xf: *result = CURRENTINDEX; return 0;
     case 0x10: *result = CURRENTISPEGIN; return 0;
     case 0x11: *result = CURRENTPREVOUTPOINT; return 0;
     case 0x12: *result = CURRENTASSET; return 0;
     case 0x13: *result = CURRENTAMOUNT; return 0;
     case 0x14: *result = CURRENTSCRIPTHASH; return 0;
     case 0x15: *result = CURRENTSEQUENCE; return 0;
     case 0x16: *result = CURRENTISSUANCEBLINDING; return 0;
     case 0x17: *result = CURRENTISSUANCECONTRACT; return 0;
     case 0x18: *result = CURRENTISSUANCEENTROPY; return 0;
     case 0x19: *result = CURRENTISSUANCEASSETAMT; return 0;
     case 0x1a: *result = CURRENTISSUANCETOKENAMT; return 0;
     case 0x1b: *result = INPUTSHASH; return 0;
     case 0x1c: *result = OUTPUTSHASH; return 0;
     case 0x1d: *result = NUMINPUTS; return 0;
     case 0x1e: *result = NUMOUTPUTS; return 0;
     case 0x1f:
      /* FEE is not yet implemented.  Disable it. */
      *result = FEE; return SIMPLICITY_ERR_DATA_OUT_OF_RANGE;
    }
    assert(false);
    UNREACHABLE;
  } else {
    bit = getBit(stream);
    if (bit < 0) return bit;
    if (!bit) {
      /* Core jets */
      int32_t code = decodeUptoMaxInt(stream);
      if (code < 0) return code;

      switch (code) {
       case 2: /* Arith jets chapter */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return code;

        switch (code) {
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
         case 1: *result = BIP0340_VERIFY; return 0;
        }
        break;
      }
      return SIMPLICITY_ERR_DATA_OUT_OF_RANGE;

    } else {
      /* Elements specific jets go here */
      return SIMPLICITY_ERR_DATA_OUT_OF_RANGE;
    }
  }
}

/* Cached copy of each node for all the Elements specific jets.
 * Only to be accessed through 'jetNode'.
 */
static once_flag static_initialized = ONCE_FLAG_INIT;
static dag_node jet_node[] = {
 [ADD_32] =
    { .tag = JET
    , .jet = add_32
    , .sourceIx = word64
    , .targetIx = twoTimesWord32
    },
 [SUBTRACT_32] =
    { .tag = JET
    , .jet = subtract_32
    , .sourceIx = word64
    , .targetIx = twoTimesWord32
    },
 [MULTIPLY_32] =
    { .tag = JET
    , .jet = multiply_32
    , .sourceIx = word64
    , .targetIx = word64
    },
 [FULL_ADD_32] =
    { .tag = JET
    , .jet = full_add_32
    , .sourceIx = twoTimesWord64
    , .targetIx = twoTimesWord32
    },
 [FULL_SUBTRACT_32] =
    { .tag = JET
    , .jet = full_subtract_32
    , .sourceIx = twoTimesWord64
    , .targetIx = twoTimesWord32
    },
 [FULL_MULTIPLY_32] =
    { .tag = JET
    , .jet = full_multiply_32
    , .sourceIx = word128
    , .targetIx = word64
    },
 [SHA_256_BLOCK] =
    { .tag = JET
    , .jet = sha_256_block
    , .sourceIx = word256TimesWord512
    , .targetIx = word256
    },
 [FE_NORMALIZE] =
    { .tag = JET
    , .jet = fe_normalize
    , .sourceIx = word256
    , .targetIx = word256
    },
 [FE_NEGATE] =
    { .tag = JET
    , .jet = fe_negate
    , .sourceIx = word256
    , .targetIx = word256
    },
 [FE_ADD] =
    { .tag = JET
    , .jet = fe_add
    , .sourceIx = word512
    , .targetIx = word256
    },
 [FE_SQUARE] =
    { .tag = JET
    , .jet = fe_square
    , .sourceIx = word256
    , .targetIx = word256
    },
 [FE_MULTIPLY] =
    { .tag = JET
    , .jet = fe_multiply
    , .sourceIx = word512
    , .targetIx = word256
    },
 [FE_MULTIPLY_BETA] =
    { .tag = JET
    , .jet = fe_multiply_beta
    , .sourceIx = word256
    , .targetIx = word256
    },
 [FE_INVERT] =
    { .tag = JET
    , .jet = fe_invert
    , .sourceIx = word256
    , .targetIx = word256
    },
 [FE_SQUARE_ROOT] =
    { .tag = JET
    , .jet = fe_square_root
    , .sourceIx = word256
    , .targetIx = sWord256
    },
 [FE_IS_ZERO] =
    { .tag = JET
    , .jet = fe_is_zero
    , .sourceIx = word256
    , .targetIx = two
    },
 [FE_IS_ODD] =
    { .tag = JET
    , .jet = fe_is_odd
    , .sourceIx = word256
    , .targetIx = two
    },
 [SCALAR_NORMALIZE] =
    { .tag = JET
    , .jet = scalar_normalize
    , .sourceIx = word256
    , .targetIx = word256
    },
 [SCALAR_NEGATE] =
    { .tag = JET
    , .jet = scalar_negate
    , .sourceIx = word256
    , .targetIx = word256
    },
 [SCALAR_ADD] =
    { .tag = JET
    , .jet = scalar_add
    , .sourceIx = word512
    , .targetIx = word256
    },
 [SCALAR_SQUARE] =
    { .tag = JET
    , .jet = scalar_square
    , .sourceIx = word256
    , .targetIx = word256
    },
 [SCALAR_MULTIPLY] =
    { .tag = JET
    , .jet = scalar_multiply
    , .sourceIx = word512
    , .targetIx = word256
    },
 [SCALAR_MULTIPLY_LAMBDA] =
    { .tag = JET
    , .jet = scalar_multiply_lambda
    , .sourceIx = word256
    , .targetIx = word256
    },
 [SCALAR_INVERT] =
    { .tag = JET
    , .jet = scalar_invert
    , .sourceIx = word256
    , .targetIx = word256
    },
 [SCALAR_IS_ZERO] =
    { .tag = JET
    , .jet = scalar_is_zero
    , .sourceIx = word256
    , .targetIx = two
    },
 [GEJ_INFINITY] =
    { .tag = JET
    , .jet = gej_infinity
    , .sourceIx = one
    , .targetIx = gej
    },
 [GEJ_NORMALIZE] =
    { .tag = JET
    , .jet = gej_infinity
    , .sourceIx = gej
    , .targetIx = ge
    },
 [GEJ_NEGATE] =
    { .tag = JET
    , .jet = gej_negate
    , .sourceIx = gej
    , .targetIx = gej
    },
 [GE_NEGATE] =
    { .tag = JET
    , .jet = ge_negate
    , .sourceIx = ge
    , .targetIx = ge
    },
 [GEJ_DOUBLE] =
    { .tag = JET
    , .jet = gej_double
    , .sourceIx = gej
    , .targetIx = gej
    },
 [GEJ_ADD] =
    { .tag = JET
    , .jet = gej_add
    , .sourceIx = gejTimesGej
    , .targetIx = gej
    },
 [GEJ_GE_ADD_EX] =
    { .tag = JET
    , .jet = gej_ge_add_ex
    , .sourceIx = gejTimesGe
    , .targetIx = feTimesGej
    },
 [GEJ_GE_ADD] =
    { .tag = JET
    , .jet = gej_ge_add
    , .sourceIx = gejTimesGe
    , .targetIx = gej
    },
 [GEJ_RESCALE] =
    { .tag = JET
    , .jet = gej_ge_add
    , .sourceIx = gejTimesFe
    , .targetIx = gej
    },
 [GEJ_IS_INFINITY] =
    { .tag = JET
    , .jet = gej_is_infinity
    , .sourceIx = gej
    , .targetIx = two
    },
 [GEJ_X_EQUIV] =
    { .tag = JET
    , .jet = gej_x_equiv
    , .sourceIx = feTimesGej
    , .targetIx = two
    },
 [GEJ_Y_IS_ODD] =
    { .tag = JET
    , .jet = gej_y_is_odd
    , .sourceIx = gej
    , .targetIx = two
    },
 [GEJ_IS_ON_CURVE] =
    { .tag = JET
    , .jet = gej_is_on_curve
    , .sourceIx = gej
    , .targetIx = two
    },
 [GE_IS_ON_CURVE] =
    { .tag = JET
    , .jet = ge_is_on_curve
    , .sourceIx = ge
    , .targetIx = two
    },
 [GENERATE] =
    { .tag = JET
    , .jet = generate
    , .sourceIx = word256
    , .targetIx = gej
    },
 [SCALE] =
    { .tag = JET
    , .jet = scale
    , .sourceIx = scalarTimesGej
    , .targetIx = gej
    },
 [LINEAR_COMBINATION_1] =
    { .tag = JET
    , .jet = linear_combination_1
    , .sourceIx = scalarTimesGejTimesScalar
    , .targetIx = gej
    },
 [LINEAR_VERIFY_1] =
    { .tag = JET
    , .jet = linear_verify_1
    , .sourceIx = scalarTimesGeTimesScalarTimesGe
    , .targetIx = one
    },
 [POINT_VERIFY_1] =
    { .tag = JET
    , .jet = point_verify_1
    , .sourceIx = scalarTimesPointTimesScalarTimesPoint
    , .targetIx = one
    },
 [DECOMPRESS] =
    { .tag = JET
    , .jet = decompress
    , .sourceIx = point
    , .targetIx = sWord512
    },
 [BIP0340_VERIFY] =
    { .tag = JET
    , .jet = bip0340_verify
    , .sourceIx = word1024
    , .targetIx = one
    },
 [VERSION] =
    { .tag = JET
    , .jet = version
    , .sourceIx = one
    , .targetIx = word32
    },
 [LOCKTIME] =
    { .tag = JET
    , .jet = lockTime
    , .sourceIx = one
    , .targetIx = word32
    },
 [INPUTISPEGIN] =
    { .tag = JET
    , .jet = inputIsPegin
    , .sourceIx = word32
    , .targetIx = sTwo
    },
 [INPUTPREVOUTPOINT] =
    { .tag = JET
    , .jet = inputPrevOutpoint
    , .sourceIx = word32
    , .targetIx = sOutpnt
    },
 [INPUTASSET] =
    { .tag = JET
    , .jet = inputAsset
    , .sourceIx = word32
    , .targetIx = sConfWord256
    },
 [INPUTAMOUNT] =
    { .tag = JET
    , .jet = inputAmount
    , .sourceIx = word32
    , .targetIx = sConfWord64
    },
 [INPUTSCRIPTHASH] =
    { .tag = JET
    , .jet = inputScriptHash
    , .sourceIx = word32
    , .targetIx = sWord256
    },
 [INPUTSEQUENCE] =
    { .tag = JET
    , .jet = inputSequence
    , .sourceIx = word32
    , .targetIx = sWord32
    },
 [INPUTISSUANCEBLINDING] =
    { .tag = JET
    , .jet = inputIssuanceBlinding
    , .sourceIx = word32
    , .targetIx = sSWord256
    },
 [INPUTISSUANCECONTRACT] =
    { .tag = JET
    , .jet = inputIssuanceContract
    , .sourceIx = word32
    , .targetIx = sSWord256
    },
 [INPUTISSUANCEENTROPY] =
    { .tag = JET
    , .jet = inputIssuanceEntropy
    , .sourceIx = word32
    , .targetIx = sSWord256
    },
 [INPUTISSUANCEASSETAMT] =
    { .tag = JET
    , .jet = inputIssuanceAssetAmt
    , .sourceIx = word32
    , .targetIx = sSConfWord64
    },
 [INPUTISSUANCETOKENAMT] =
    { .tag = JET
    , .jet = inputIssuanceTokenAmt
    , .sourceIx = word32
    , .targetIx = sSConfWord64
    },
 [OUTPUTASSET] =
    { .tag = JET
    , .jet = outputAsset
    , .sourceIx = word32
    , .targetIx = sConfWord256
    },
 [OUTPUTAMOUNT] =
    { .tag = JET
    , .jet = outputAmount
    , .sourceIx = word32
    , .targetIx = sConfWord64
    },
 [OUTPUTNONCE] =
    { .tag = JET
    , .jet = outputNonce
    , .sourceIx = word32
    , .targetIx = sSConfWord256
    },
 [OUTPUTSCRIPTHASH] =
    { .tag = JET
    , .jet = outputScriptHash
    , .sourceIx = word32
    , .targetIx = sWord256
    },
 [OUTPUTNULLDATUM] =
    { .tag = JET
    , .jet = outputNullDatum
    , .sourceIx = word64
    , .targetIx = sSWord2TimesWord256PlusTwoPlusWord4
    },
 [SCRIPTCMR] =
    { .tag = JET
    , .jet = scriptCMR
    , .sourceIx = one
    , .targetIx = word256
    },
 [CURRENTINDEX] =
    { .tag = JET
    , .jet = currentIndex
    , .sourceIx = one
    , .targetIx = word32
    },
 [CURRENTISPEGIN] =
    { .tag = JET
    , .jet = currentIsPegin
    , .sourceIx = one
    , .targetIx = two
    },
 [CURRENTPREVOUTPOINT] =
    { .tag = JET
    , .jet = currentPrevOutpoint
    , .sourceIx = one
    , .targetIx = outpnt
    },
 [CURRENTASSET] =
    { .tag = JET
    , .jet = currentAsset
    , .sourceIx = one
    , .targetIx = confWord256
    },
 [CURRENTAMOUNT] =
    { .tag = JET
    , .jet = currentAmount
    , .sourceIx = one
    , .targetIx = confWord64
    },
 [CURRENTSCRIPTHASH] =
    { .tag = JET
    , .jet = currentScriptHash
    , .sourceIx = one
    , .targetIx = word256
    },
 [CURRENTSEQUENCE] =
    { .tag = JET
    , .jet = currentSequence
    , .sourceIx = one
    , .targetIx = word32
    },
 [CURRENTISSUANCEBLINDING] =
    { .tag = JET
    , .jet = currentIssuanceBlinding
    , .sourceIx = one
    , .targetIx = sWord256
    },
 [CURRENTISSUANCECONTRACT] =
    { .tag = JET
    , .jet = currentIssuanceContract
    , .sourceIx = one
    , .targetIx = sWord256
    },
 [CURRENTISSUANCEENTROPY] =
    { .tag = JET
    , .jet = currentIssuanceEntropy
    , .sourceIx = one
    , .targetIx = sWord256
    },
 [CURRENTISSUANCEASSETAMT] =
    { .tag = JET
    , .jet = currentIssuanceAssetAmt
    , .sourceIx = one
    , .targetIx = sConfWord64
    },
 [CURRENTISSUANCETOKENAMT] =
    { .tag = JET
    , .jet = currentIssuanceTokenAmt
    , .sourceIx = one
    , .targetIx = sConfWord64
    },
 [INPUTSHASH] =
    { .tag = JET
    , .jet = inputsHash
    , .sourceIx = one
    , .targetIx = word256
    },
 [OUTPUTSHASH] =
    { .tag = JET
    , .jet = outputsHash
    , .sourceIx = one
    , .targetIx = word256
    },
 [NUMINPUTS] =
    { .tag = JET
    , .jet = numInputs
    , .sourceIx = one
    , .targetIx = word32
    },
 [NUMOUTPUTS] =
    { .tag = JET
    , .jet = numOutputs
    , .sourceIx = one
    , .targetIx = word32
    },
 [FEE] =
    { .tag = JET
    , .jet = NULL /* :TODO: FEE not yet implemented. */
    , .sourceIx = word256
    , .targetIx = word64
    }
 };
static void static_initialize(void) {
  {
    sha256_midstate jet_iv;
    MK_TAG(&jet_iv, JET_TAG);

#define MK_JET(name, h0, h1, h2, h3, h4, h5, h6, h7) \
  do { \
    jet_node[name].cmr = jet_iv; \
    sha256_compression(jet_node[name].cmr.s, (uint32_t[16]){ [8] = h0, h1, h2, h3, h4, h5, h6, h7 }); \
  } while(0)

    /* Jets are identified by their specification's identity Merkle roots. */
    MK_JET(ADD_32,                 0xe40466a7u, 0xecf71ce8u, 0x62fb3c15u, 0x4c1e8f84u, 0x5d7e5707u, 0x463a8945u, 0x37a32fc7u, 0x214900adu);
    MK_JET(FULL_ADD_32,            0x4727361eu, 0xa003c1a4u, 0x83e57505u, 0xcf5b405au, 0x8227da1au, 0xddc47e2bu, 0x016c2d09u, 0xbe047fe8u);
    MK_JET(SUBTRACT_32,            0xf76ecad1u, 0xfda50f13u, 0x5bdfe3e5u, 0x33a15009u, 0x8f406261u, 0xc76f6dbfu, 0x6725f1e3u, 0x883c2ae2u);
    MK_JET(FULL_SUBTRACT_32,       0x6d96f68au, 0x945c22e7u, 0x62115c09u, 0x4297b194u, 0xbedc0ce5u, 0xa0c92db6u, 0x4b830a18u, 0xb44df0d0u);
    MK_JET(MULTIPLY_32,            0x161fd03au, 0x92c621b3u, 0x289849ffu, 0x29ad8134u, 0x99d63ed9u, 0x73db0e97u, 0x51785421u, 0xf568d18fu);
    MK_JET(FULL_MULTIPLY_32,       0xaac25361u, 0xe598e354u, 0x38b918b5u, 0x8fd2cef4u, 0xdb3c5d8cu, 0x5e63aa4fu, 0x25e9cec0u, 0xcfd9dfb1u);
    MK_JET(SHA_256_BLOCK,          0xdfc927d3u, 0x9bf7147au, 0x8b0a7f43u, 0x79466870u, 0x824db102u, 0x090a0036u, 0x2923a377u, 0xa91af681u);
    MK_JET(FE_NORMALIZE,           0xc070adbau, 0xab2c7be6u, 0xff577a75u, 0x07aff0e7u, 0x7657f309u, 0xe65d05fau, 0x23c19276u, 0xf73852ebu);
    MK_JET(FE_NEGATE,              0x8766585du, 0x27d18863u, 0x42714443u, 0x2ba483b3u, 0x6cd2dd1fu, 0x36181410u, 0xacc71493u, 0x9c0cb56au);
    MK_JET(FE_ADD,                 0xc09d58e3u, 0x8dc4ce1au, 0xcc09dae8u, 0xa5881908u, 0xfe1ebc7fu, 0x1fc742c6u, 0x1cdc8493u, 0xf233b94au);
    MK_JET(FE_SQUARE,              0x8e77cc8cu, 0x63693a2au, 0xcd9a6526u, 0x6a028906u, 0xf864214au, 0xf66ba54cu, 0xce11acb0u, 0x37c94393u);
    MK_JET(FE_MULTIPLY,            0xac5a3626u, 0xb5fc2b5au, 0x206ac18fu, 0x1b0f9ecau, 0xcb5c6314u, 0xc4efda59u, 0xe0fad3a1u, 0xb599a1bdu);
    MK_JET(FE_MULTIPLY_BETA,       0xe7a698e2u, 0x5ebbf70fu, 0x8ced3130u, 0xac04d674u, 0xa9da39e0u, 0x61761bfdu, 0x9d87d794u, 0x898f8a7au);
    MK_JET(FE_INVERT,              0xb6b11bd6u, 0x0258d326u, 0xb19b6f78u, 0x387ff3aau, 0xbf6a4c41u, 0x9d0c5a8du, 0xda6b4405u, 0x0bc6e9d5u);
    MK_JET(FE_SQUARE_ROOT,         0xf7718103u, 0x304cb436u, 0x96bdf92fu, 0x614c838du, 0x24d7dd7bu, 0xa8dc01abu, 0x5c6a7726u, 0x3c15f729u);
    MK_JET(FE_IS_ZERO,             0x52359f07u, 0xed7a7c97u, 0x0e947dc8u, 0xc4994056u, 0x6c1a1e09u, 0x5d03604au, 0xfdb4433du, 0xa13a87ecu);
    MK_JET(FE_IS_ODD,              0x4d21e4b5u, 0x476fcf56u, 0xa369e5a1u, 0x89c486e0u, 0x987f9332u, 0xaaf4c0a7u, 0x5ac3af09u, 0xf81b1709u);
    MK_JET(SCALAR_NORMALIZE,       0x90e02578u, 0x96990ba6u, 0xf0b07654u, 0x2919cd06u, 0x4ac08b27u, 0x7fae3479u, 0xe40918ebu, 0x6f5b07d8u);
    MK_JET(SCALAR_NEGATE,          0x6a976a67u, 0x68bd728fu, 0xe2105185u, 0x1c60eb25u, 0x72e5d06cu, 0x95566dfau, 0xe92820c8u, 0x424aaa4eu);
    MK_JET(SCALAR_ADD,             0x67e41fadu, 0x704500ceu, 0x97509132u, 0xd4f69734u, 0x2e8583edu, 0x7e9f7bedu, 0xb995d36cu, 0xf65ff32eu);
    MK_JET(SCALAR_SQUARE,          0xd636b49du, 0xc6b2266cu, 0xcecb7bc0u, 0x4168823bu, 0x2a5d7a1du, 0x2ac343dau, 0x605419d3u, 0x8dfdfde0u);
    MK_JET(SCALAR_MULTIPLY,        0x14513cf4u, 0x41179e62u, 0xfb4293bbu, 0x353ee5bfu, 0x01eddf8du, 0x81ce0310u, 0x062f09a8u, 0x1d2fbca8u);
    MK_JET(SCALAR_MULTIPLY_LAMBDA, 0xf62400f5u, 0xbe7400a7u, 0x12e74a1du, 0xc1a841e6u, 0x024a9618u, 0x551c3364u, 0xc4e8156du, 0x1cdded83u);
    MK_JET(SCALAR_INVERT,          0xc0e2ad1bu, 0xa6bfd910u, 0x4424f594u, 0xd0073ea1u, 0x99405e5cu, 0xa5b71283u, 0x94b613b9u, 0xe1bd36fcu);
    MK_JET(SCALAR_IS_ZERO,         0x38a457cau, 0xb1c30c51u, 0x4e20e241u, 0xd5846540u, 0x75ec4d05u, 0x496c7e0bu, 0x1ce2de5eu, 0x2fc19916u);
    MK_JET(GEJ_INFINITY,           0x2d9d36b4u, 0x6ead02dbu, 0x63b585dcu, 0xa67e5e4du, 0xcb940589u, 0xbb133c99u, 0x100d617cu, 0x27126e96u);
    MK_JET(GEJ_NORMALIZE,          0x1db135d0u, 0xe05b9976u, 0x87ac853cu, 0xf78b95cfu, 0x07418f5fu, 0xc9164ed8u, 0xd6a7f3edu, 0x70efabe5u);
    MK_JET(GEJ_NEGATE,             0x71eeffb5u, 0xb637af51u, 0xc4978002u, 0xc212cdafu, 0x396cf8efu, 0xca33aab0u, 0xf833f81au, 0x9fb6a989u);
    MK_JET(GE_NEGATE,              0xa497e71cu, 0x403c4ce2u, 0xb781893cu, 0xd69a5285u, 0xea02d7b7u, 0xfe8edfacu, 0xe78a205au, 0xad2ec033u);
    MK_JET(GEJ_DOUBLE,             0x80d0825du, 0x57ce424cu, 0xc8b89dc2u, 0x510d7e65u, 0x858a994eu, 0x8e987623u, 0xd10e3483u, 0xde26df9eu);
    MK_JET(GEJ_ADD,                0x8075b590u, 0x28649087u, 0xded0e766u, 0x6e1a0051u, 0x4509d0c9u, 0x87d88d18u, 0x681ac89bu, 0xc960eb25u);
    MK_JET(GEJ_GE_ADD_EX,          0x4a8902b1u, 0x1d739b4fu, 0xb848d185u, 0x28736ab1u, 0xd668be2eu, 0xab1fed8du, 0x068365b5u, 0x3bd77d88u);
    MK_JET(GEJ_GE_ADD,             0xddc12bb2u, 0x89175ff5u, 0x87a570b3u, 0x02af6108u, 0xfa565bcau, 0xce9c374au, 0x10b78363u, 0x951daa64u);
    MK_JET(GEJ_RESCALE,            0xfa70aa15u, 0x3dab6bc9u, 0x9355c10cu, 0x61e5bfcfu, 0xa397b381u, 0xf7ef5915u, 0x9d83791au, 0x2a6a5824u);
    MK_JET(GEJ_IS_INFINITY,        0xe186f9bdu, 0xbe4916c7u, 0x2f6c3bc2u, 0xadf3e047u, 0x22ef4cecu, 0x297253e3u, 0xecaa4e4cu, 0xc551ef2cu);
    MK_JET(GEJ_X_EQUIV,            0x65a860fau, 0x7e74601cu, 0xb6d83755u, 0x3ba19d60u, 0xc4773c1cu, 0x12b4b0f0u, 0x278b45fbu, 0x23fce967u);
    MK_JET(GEJ_Y_IS_ODD,           0xadbcf2d2u, 0xe9155854u, 0x54bc7262u, 0x0f1e66f5u, 0x9ca726e8u, 0x24860e1eu, 0x04bbe2bcu, 0xa2a49a11u);
    MK_JET(GEJ_IS_ON_CURVE,        0xa8c82e8bu, 0x3a6199dau, 0x25b2b19cu, 0xd149f9ffu, 0x4c3fdc0bu, 0x00b26480u, 0xc0006553u, 0xd43c1f6eu);
    MK_JET(GE_IS_ON_CURVE,         0xd9aa6606u, 0x5cb0ed2cu, 0x7168609du, 0xfd62ab64u, 0x3aa87c27u, 0xe0dbbf96u, 0xf2914528u, 0xfeef52c5u);
    MK_JET(GENERATE,               0x5136b9e1u, 0x4b280ab4u, 0x43ef8013u, 0x0e6acf63u, 0xc7b0066cu, 0x880ea699u, 0x1f4971f9u, 0xeb9e250cu);
    MK_JET(SCALE,                  0xa89f2191u, 0xec6ad8ebu, 0xd292adf0u, 0x623d0fb5u, 0x233ea1b1u, 0x038a1354u, 0x300fe58cu, 0x4a365972u);
    MK_JET(LINEAR_COMBINATION_1,   0x3fa1c2d8u, 0xc971e239u, 0x85fd9591u, 0x201206d4u, 0x6abdc087u, 0x9107e2b9u, 0x760438b6u, 0x093a09a5u);
    MK_JET(LINEAR_VERIFY_1,        0x2a69879au, 0xce3c7debu, 0xa2fdc206u, 0x69b85441u, 0x5ee0b550u, 0x617c37f6u, 0xede4ca57u, 0x37045b94u);
    MK_JET(POINT_VERIFY_1,         0x7ca92d09u, 0x2b44eb81u, 0xcce82137u, 0x37120369u, 0x3088bfb0u, 0x8122d0d6u, 0xa977d00bu, 0xe17cf4f4u);
    MK_JET(DECOMPRESS,             0xab5a2dbcu, 0x0f2c8208u, 0x6d2d46bbu, 0xa5691f13u, 0x12bacc94u, 0x6b08effbu, 0xe7f85151u, 0x141f7dcfu);
    MK_JET(BIP0340_VERIFY,         0x67619fe7u, 0x77a22a0fu, 0xb6d227a6u, 0x922a843bu, 0xf832286bu, 0xd5c621c1u, 0xc52f1d64u, 0x689beae5u);
#undef MK_JET

  }
  MK_TAG(&jet_node[VERSION].cmr, PRIMITIVE_TAG("version"));
  MK_TAG(&jet_node[LOCKTIME].cmr, PRIMITIVE_TAG("lockTime"));
  MK_TAG(&jet_node[INPUTISPEGIN].cmr, PRIMITIVE_TAG("inputIsPegin"));
  MK_TAG(&jet_node[INPUTPREVOUTPOINT].cmr, PRIMITIVE_TAG("inputPrevOutpoint"));
  MK_TAG(&jet_node[INPUTASSET].cmr, PRIMITIVE_TAG("inputAsset"));
  MK_TAG(&jet_node[INPUTAMOUNT].cmr, PRIMITIVE_TAG("inputAmount"));
  MK_TAG(&jet_node[INPUTSCRIPTHASH].cmr, PRIMITIVE_TAG("inputScriptHash"));
  MK_TAG(&jet_node[INPUTSEQUENCE].cmr, PRIMITIVE_TAG("inputSequence"));
  MK_TAG(&jet_node[INPUTISSUANCEBLINDING].cmr, PRIMITIVE_TAG("inputIssuanceBlinding"));
  MK_TAG(&jet_node[INPUTISSUANCECONTRACT].cmr, PRIMITIVE_TAG("inputIssuanceContract"));
  MK_TAG(&jet_node[INPUTISSUANCEENTROPY].cmr, PRIMITIVE_TAG("inputIssuanceEntropy"));
  MK_TAG(&jet_node[INPUTISSUANCEASSETAMT].cmr, PRIMITIVE_TAG("inputIssuanceAssetAmt"));
  MK_TAG(&jet_node[INPUTISSUANCETOKENAMT].cmr, PRIMITIVE_TAG("inputIssuanceTokenAmt"));
  MK_TAG(&jet_node[OUTPUTASSET].cmr, PRIMITIVE_TAG("outputAsset"));
  MK_TAG(&jet_node[OUTPUTAMOUNT].cmr, PRIMITIVE_TAG("outputAmount"));
  MK_TAG(&jet_node[OUTPUTNONCE].cmr, PRIMITIVE_TAG("outputNonce"));
  MK_TAG(&jet_node[OUTPUTSCRIPTHASH].cmr, PRIMITIVE_TAG("outputScriptHash"));
  MK_TAG(&jet_node[OUTPUTNULLDATUM].cmr, PRIMITIVE_TAG("outputNullDatum"));
  MK_TAG(&jet_node[SCRIPTCMR].cmr, PRIMITIVE_TAG("scriptCMR"));
  MK_TAG(&jet_node[CURRENTINDEX].cmr, PRIMITIVE_TAG("currentIndex"));
  MK_TAG(&jet_node[CURRENTISPEGIN].cmr, PRIMITIVE_TAG("currentIsPegin"));
  MK_TAG(&jet_node[CURRENTPREVOUTPOINT].cmr, PRIMITIVE_TAG("currentPrevOutpoint"));
  MK_TAG(&jet_node[CURRENTASSET].cmr, PRIMITIVE_TAG("currentAsset"));
  MK_TAG(&jet_node[CURRENTAMOUNT].cmr, PRIMITIVE_TAG("currentAmount"));
  MK_TAG(&jet_node[CURRENTSCRIPTHASH].cmr, PRIMITIVE_TAG("currentScriptHash"));
  MK_TAG(&jet_node[CURRENTSEQUENCE].cmr, PRIMITIVE_TAG("currentSequence"));
  MK_TAG(&jet_node[CURRENTISSUANCEBLINDING].cmr, PRIMITIVE_TAG("currentIssuanceBlinding"));
  MK_TAG(&jet_node[CURRENTISSUANCECONTRACT].cmr, PRIMITIVE_TAG("currentIssuanceContract"));
  MK_TAG(&jet_node[CURRENTISSUANCEENTROPY].cmr, PRIMITIVE_TAG("currentIssuanceEntropy"));
  MK_TAG(&jet_node[CURRENTISSUANCEASSETAMT].cmr, PRIMITIVE_TAG("currentIssuanceAssetAmt"));
  MK_TAG(&jet_node[CURRENTISSUANCETOKENAMT].cmr, PRIMITIVE_TAG("currentIssuanceTokenAmt"));
  MK_TAG(&jet_node[INPUTSHASH].cmr, PRIMITIVE_TAG("inputsHash"));
  MK_TAG(&jet_node[OUTPUTSHASH].cmr, PRIMITIVE_TAG("outputsHash"));
  MK_TAG(&jet_node[NUMINPUTS].cmr, PRIMITIVE_TAG("numInputs"));
  MK_TAG(&jet_node[NUMOUTPUTS].cmr, PRIMITIVE_TAG("numOutputs"));
  MK_TAG(&jet_node[FEE].cmr, PRIMITIVE_TAG("fee"));
}

/* Return a copy of the Simplicity node corresponding to the given Elements specific jet 'name'.
 */
static dag_node jetNode(jetName name) {
  call_once(&static_initialized, &static_initialize);

  return jet_node[name];
}

/* Decode an Elements specific jet from 'stream' into 'node'.
 * All jets begin with a bit prefix of '1' which needs to have already been consumed from the 'stream'.
 * Returns 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' if the stream's prefix doesn't match any valid code for a jet.
 * Returns 'SIMPLICITY_ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * Returns 'SIMPLICITY_ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
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
