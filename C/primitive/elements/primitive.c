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
  word512,
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
  word2TimesWord256,
  twoPlusWord4,
  word2TimesWord256PlusTwoPlusWord4,
  sWord2TimesWord256PlusTwoPlusWord4,
  sSWord2TimesWord256PlusTwoPlusWord4,
  twoTimesWord32,
  word64TimesTwo,
  word256TimesWord512,
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
  (*bound_var)[word64TimesTwo] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word64], &(*bound_var)[two] } } };
  (*bound_var)[word256TimesWord512] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word256], &(*bound_var)[word512] } } };

  *word256_ix = word256;
  *extra_var_start = NumberOfTypeNames;

  /* 'one' is a trivial binding, so we made 'NumberOfTypeNames - 1' non-trivial bindings. */
  return NumberOfTypeNames - 1;
};

/* An enumeration of the names of Elements specific jets and primitives. */
typedef enum jetName
{ ADDER32
, SUBTRACTOR32
, MULTIPLIER32
, FULLADDER32
, FULLSUBTRACTOR32
, FULLMULTIPLIER32
, SHA256_HASHBLOCK
, SCHNORRASSERT
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
 * Returns 'ERR_DATA_OUT_OF_RANGE' if the stream's prefix doesn't match any valid code for a jet.
 * Returns 'ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * Returns 'ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
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
      *result = FEE; return ERR_DATA_OUT_OF_RANGE;
    }
    assert(false);
    UNREACHABLE;
  } else {
    bit = getBit(stream);
    if (bit < 0) return bit;
    if (!bit) {
      int32_t code = getNBits(2, stream);
      if (code < 0) return code;

      switch (code) {
        case 0x0: return either(result, ADDER32, SUBTRACTOR32, stream);
        case 0x1: *result = MULTIPLIER32; return 0;
        case 0x2: return either(result, FULLADDER32, FULLSUBTRACTOR32, stream);
        case 0x3: *result = FULLMULTIPLIER32; return 0;
      }

      assert(false);
      UNREACHABLE;
    } else {
      return either(result, SHA256_HASHBLOCK, SCHNORRASSERT, stream);
    }
  }
}

/* Cached copy of each node for all the Elements specific jets.
 * Only to be accessed through 'jetNode'.
 */
static once_flag static_initialized = ONCE_FLAG_INIT;
static dag_node jet_node[] = {
 [ADDER32] =
    { .tag = JET
    , .jet = adder32
    , .sourceIx = word64
    , .targetIx = twoTimesWord32
    },
 [SUBTRACTOR32] =
    { .tag = JET
    , .jet = subtractor32
    , .sourceIx = word64
    , .targetIx = twoTimesWord32
    },
 [MULTIPLIER32] =
    { .tag = JET
    , .jet = multiplier32
    , .sourceIx = word64
    , .targetIx = word64
    },
 [FULLADDER32] =
    { .tag = JET
    , .jet = fullAdder32
    , .sourceIx = word64TimesTwo
    , .targetIx = twoTimesWord32
    },
 [FULLSUBTRACTOR32] =
    { .tag = JET
    , .jet = fullSubtractor32
    , .sourceIx = word64TimesTwo
    , .targetIx = twoTimesWord32
    },
 [FULLMULTIPLIER32] =
    { .tag = JET
    , .jet = fullMultiplier32
    , .sourceIx = word128
    , .targetIx = word64
    },
 [SHA256_HASHBLOCK] =
    { .tag = JET
    , .jet = sha256_hashBlock
    , .sourceIx = word256TimesWord512
    , .targetIx = word256
    },
 [SCHNORRASSERT] =
    { .tag = JET
    , .jet = schnorrAssert
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
    MK_JET(ADDER32,          0x6cd61593u, 0xe8e243e5u, 0xb7544d2au, 0x129315a0u, 0x192dc566u, 0xb2d80926u, 0x333b7edau, 0x5c377978u);
    MK_JET(FULLADDER32,      0x154f440cu, 0x3bb4663cu, 0xfbf795dcu, 0xde410b09u, 0x22528582u, 0x5f3b3e6fu, 0xab364569u, 0x643f50ebu);
    MK_JET(SUBTRACTOR32,     0x90dd6022u, 0xe86bf2e9u, 0x679d6316u, 0x786d5e97u, 0x4a42be02u, 0xda96354cu, 0x0ba1ae6bu, 0x762b2e65u);
    MK_JET(FULLSUBTRACTOR32, 0x5244cbdau, 0xe2dcbd1au, 0x9ccf93adu, 0x9df902ceu, 0x00de3ec5u, 0xfe163be4u, 0x1e1fd5bcu, 0xe4db6d9bu);
    MK_JET(MULTIPLIER32,     0x2383d301u, 0x3c15f748u, 0xd8aaa8b6u, 0xcb4bff29u, 0xfe4645c8u, 0x5a34e27bu, 0xa85c52d5u, 0xc88e5ec3u);
    MK_JET(FULLMULTIPLIER32, 0x40d2d461u, 0x8b844ffcu, 0x562fbef6u, 0x9e01bd91u, 0x471be4d9u, 0x8638c6b5u, 0xe2deea23u, 0xd583e2f5u);
    MK_JET(SHA256_HASHBLOCK, 0x593b9df9u, 0x727fe298u, 0x66da104cu, 0x93322616u, 0x72c095e6u, 0x77d00001u, 0x99785674u, 0x04476dd8u);
    MK_JET(SCHNORRASSERT,    0xe9d872e5u, 0xb3f86b18u, 0x50db3826u, 0x3d782076u, 0x2b40e80fu, 0x0f1bd1d6u, 0x5014436fu, 0xbc2dfa8cu);
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
 * Returns 'ERR_DATA_OUT_OF_RANGE' if the stream's prefix doesn't match any valid code for a jet.
 * Returns 'ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * Returns 'ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
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
