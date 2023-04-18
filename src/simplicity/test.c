#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include <simplicity/elements/exec.h>
#include "dag.h"
#include "deserialize.h"
#include "eval.h"
#include "hashBlock.h"
#include "rsort.h"
#include "sha256.h"
#include "schnorr0.h"
#include "schnorr6.h"
#include "typeInference.h"
#include "primitive/elements/checkSigHashAllTx1.h"

_Static_assert(CHAR_BIT == 8, "Buffers passed to fmemopen presume 8 bit chars");

static int successes = 0;
static int failures = 0;

static void test_decodeUptoMaxInt(void) {
  printf("Test decodeUptoMaxInt\n");
  const unsigned char buf[] =
  { 0x4b, 0x86, 0x39, 0xe8, 0xdf, 0xc0, 0x38, 0x0f, 0x7f, 0xff, 0xff, 0x00
  , 0x00, 0x00, 0xf0, 0xe0, 0x00, 0x00, 0x00, 0x3c, 0x3b, 0xff, 0xff, 0xff
  , 0xff, 0x0f, 0x00, 0x00, 0x00, 0x00
  };
  const int32_t expected[] =
  { 1, 2, 3, 4, 5, 7, 8, 15, 16, 17
  , 0xffff, 0x10000, 0x40000000, 0x7fffffff, SIMPLICITY_ERR_DATA_OUT_OF_RANGE
  };

  bitstream stream = initializeBitstream(buf, sizeof(buf));
  for (size_t i = 0; i < sizeof(expected)/sizeof(expected[0]); ++i) {
    int32_t result = decodeUptoMaxInt(&stream);
    if (expected[i] == result) {
      successes++;
    } else {
      failures++;
      printf("Unexpected result during parsing.  Expected %d and received %d\n", expected[i], result);
    }
  }
}

static void test_hashBlock(void) {
  printf("Test hashBlock\n");
  dag_node* dag;
  combinator_counters census;
  int32_t len, err = 0;
  bitstring witness;
  {
    bitstream stream = initializeBitstream(hashBlock, sizeof_hashBlock);
    len = decodeMallocDag(&dag, &census, &stream);
    if (!dag) {
      failures++;
      printf("Error parsing dag: %d\n", len);
    } else {
      err = decodeWitnessData(&witness, &stream);
      if (err < 0) {
        failures++;
        printf("Error parsing witness: %d\n", err);
      }
    }
  }
  if (dag && 0 <= err) {
    successes++;

    if (0 == memcmp(hashBlock_cmr, dag[len-1].cmr.s, sizeof(uint32_t[8]))) {
      successes++;
    } else {
      failures++;
      printf("Unexpected CMR of hashblock\n");
    }

    type* type_dag;
    if (!mallocTypeInference(&type_dag, dag, (size_t)len, &census) || !type_dag ||
        type_dag[dag[len-1].sourceType].bitSize != 768 || type_dag[dag[len-1].targetType].bitSize != 256) {
      failures++;
      printf("Unexpected failure of type inference for hashblock\n");
    } else if (!fillWitnessData(dag, type_dag, (size_t)len, witness)) {
      failures++;
      printf("Unexpected failure of fillWitnessData for hashblock\n");
    } else {
      {
        analyses analysis[len];
        computeAnnotatedMerkleRoot(analysis, dag, type_dag, (size_t)len);
        if (0 == memcmp(hashBlock_amr, analysis[len-1].annotatedMerkleRoot.s, sizeof(uint32_t[8]))) {
          successes++;
        } else {
          failures++;
          printf("Unexpected AMR of hashblock\n");
        }
      }
      {
        sha256_midstate imr[len];
        bool noDups;
        if (verifyNoDuplicateIdentityRoots(&noDups, imr, dag, type_dag, (size_t)len) && noDups
            && 0 == memcmp(hashBlock_imr, imr[len-1].s, sizeof(uint32_t[8]))) {
          successes++;
        } else {
          failures++;
          printf("Unexpected IMR of hashblock\n");
        }
      }

      _Static_assert(UWORD_BIT - 1 <= SIZE_MAX - (256+512), "UWORD_BIT is far too large.");
      UWORD output[ROUND_UWORD(256)];
      UWORD input[ROUND_UWORD(256+512)];
      { frameItem frame = initWriteFrame(256+512, &input[ROUND_UWORD(256+512)]);
        /* Set SHA-256's initial value. */
        write32s(&frame, (uint32_t[8])
            { 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 }
          , 8);
        /* Set the block to be compressed to "abc" with padding. */
        write32s(&frame, (uint32_t[16]){ [0] = 0x61626380, [15] = 0x18 }, 16);
      }
      bool evalSuccess;
      if (evalTCOExpression(&evalSuccess, CHECK_NONE, output, 256, input, 256+512, dag, type_dag, (size_t)len, 29100, NULL) && evalSuccess) {
        /* The expected result is the value 'SHA256("abc")'. */
        const uint32_t expectedHash[8] = { 0xba7816bful, 0x8f01cfeaul, 0x414140deul, 0x5dae2223ul
                                         , 0xb00361a3ul, 0x96177a9cul, 0xb410ff61ul, 0xf20015adul };
        frameItem frame = initReadFrame(256, &output[0]);
        uint32_t result[8];
        read32s(result, 8, &frame);
        if (0 == memcmp(expectedHash, result, sizeof(uint32_t[8]))) {
          successes++;
        } else {
          failures++;
          printf("Unexpected output of hashblock computation.\n");
        }
      } else {
        failures++;
        printf("Unexpected failure of hashblock evaluation\n");
      }
    }
    free(type_dag);
  }
  free(dag);
}

static void test_program(char* name, const unsigned char* program, size_t program_len, bool expectedResult, const uint32_t* expectedCMR,
                         const uint32_t* expectedIMR, const uint32_t* expectedAMR) {
  printf("Test %s\n", name);
  dag_node* dag;
  combinator_counters census;
  int32_t len, err = 0;
  bitstring witness;
  {
    bitstream stream = initializeBitstream(program, program_len);
    len = decodeMallocDag(&dag, &census, &stream);
    if (!dag) {
      failures++;
      printf("Error parsing dag: %d\n", len);
    } else {
      err = decodeWitnessData(&witness, &stream);
      if (err < 0) {
        failures++;
        printf("Error parsing witness: %d\n", err);
      }
    }
  }
  if (dag && 0 <= err) {
    successes++;

    if (expectedCMR) {
      if (0 == memcmp(expectedCMR, dag[len-1].cmr.s, sizeof(uint32_t[8]))) {
        successes++;
      } else {
        failures++;
        printf("Unexpected CMR.\n");
      }
    }
    type* type_dag;
    if (!mallocTypeInference(&type_dag, dag, (size_t)len, &census) || !type_dag ||
        dag[len-1].sourceType != 0 || dag[len-1].targetType != 0) {
      failures++;
      printf("Unexpected failure of type inference.\n");
    } else if (!fillWitnessData(dag, type_dag, (size_t)len, witness)) {
      failures++;
      printf("Unexpected failure of fillWitnessData.\n");
    } else {
      {
        analyses analysis[len];
        computeAnnotatedMerkleRoot(analysis, dag, type_dag, (size_t)len);
        if (expectedAMR) {
          if (0 == memcmp(expectedAMR, analysis[len-1].annotatedMerkleRoot.s, sizeof(uint32_t[8]))) {
            successes++;
          } else {
            failures++;
            printf("Unexpected AMR.\n");
          }
        }
      }
      {
        sha256_midstate imr[len];
        bool noDups;
        if (verifyNoDuplicateIdentityRoots(&noDups, imr, dag, type_dag, (size_t)len) && noDups
            && 0 == memcmp(expectedIMR, imr[len-1].s, sizeof(uint32_t[8]))) {
          successes++;
        } else {
          failures++;
          printf("Unexpected IMR.\n");
        }
      }
      bool evalSuccess;
      if (evalTCOProgram(&evalSuccess, dag, type_dag, (size_t)len, BUDGET_MAX, NULL) && expectedResult == evalSuccess) {
        successes++;
      } else {
        failures++;
        printf(expectedResult ? "Unexpected failure of evaluation.\n" : "Unexpected success of evaluation.\n");
      }
    }
    free(type_dag);
  }
  free(dag);
}

static void test_occursCheck(void) {
  printf("Test occursCheck\n");
  /* The untyped Simplicity term (case (drop iden) iden) ought to cause an occurs check failure. */
  const unsigned char buf[] = { 0xc1, 0x07, 0x20, 0x30 };
  dag_node* dag;
  combinator_counters census;
  int32_t len;
  {
    bitstream stream = initializeBitstream(buf, sizeof(buf));
    len = decodeMallocDag(&dag, &census, &stream);
  }
  if (!dag) {
    printf("Error parsing dag: %d\n", len);
  } else {
    type* type_dag;
    if (mallocTypeInference(&type_dag, dag, (size_t)len, &census) && !type_dag) {
      successes++;
    } else {
      printf("Unexpected occurs check success\n");
      failures++;
    }
    free(type_dag);
  }
  free(dag);
}

static void test_elements(void) {
  unsigned char cmr[32], amr[32];
  sha256_fromMidstate(cmr, elementsCheckSigHashAllTx1_cmr);
  sha256_fromMidstate(amr, elementsCheckSigHashAllTx1_amr);

  unsigned char genesisHash[32] = "\x0f\x91\x88\xf1\x3c\xb7\xb2\xc7\x1f\x2a\x33\x5e\x3a\x4f\xc3\x28\xbf\x5b\xeb\x43\x60\x12\xaf\xca\x59\x0b\x1a\x11\x46\x6e\x22\x06";
  rawTapEnv rawTaproot = (rawTapEnv)
    { .controlBlock = (unsigned char [33]){"\xbe\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x3b\x78\xce\x56\x3f\x89\xa0\xed\x94\x14\xf5\xaa\x28\xad\x0d\x96\xd6\x79\x5f\x9c\x63"}
    , .branchLen = 0
    , .scriptCMR = cmr
    };
  tapEnv* taproot = elements_simplicity_mallocTapEnv(&rawTaproot);

  printf("Test elements\n");
  {
    rawTransaction testTx1 = (rawTransaction)
      { .input = (rawInput[])
                 { { .annex = NULL
                   , .prevTxid = (unsigned char[32]){"\xeb\x04\xb6\x8e\x9a\x26\xd1\x16\x04\x6c\x76\xe8\xff\x47\x33\x2f\xb7\x1d\xda\x90\xff\x4b\xef\x53\x70\xf2\x52\x26\xd3\xbc\x09\xfc"}
                   , .prevIx = 0
                   , .sequence = 0xfffffffe
                   , .issuance = {0}
                   , .scriptSig = {0}
                   , .txo = { .asset = (unsigned char[33]){"\x01\x23\x0f\x4f\x5d\x4b\x7c\x6f\xa8\x45\x80\x6e\xe4\xf6\x77\x13\x45\x9e\x1b\x69\xe8\xe6\x0f\xce\xe2\xe4\x94\x0c\x7a\x0d\x5d\xe1\xb2"}
                            , .value = (unsigned char[9]){"\x01\x00\x00\x00\x02\x54\x0b\xe4\x00"}
                            , .scriptPubKey = {0}
                 } }        }
      , .output = (rawOutput[])
                  { { .asset = (unsigned char[33]){"\x01\x23\x0f\x4f\x5d\x4b\x7c\x6f\xa8\x45\x80\x6e\xe4\xf6\x77\x13\x45\x9e\x1b\x69\xe8\xe6\x0f\xce\xe2\xe4\x94\x0c\x7a\x0d\x5d\xe1\xb2"}
                    , .value = (unsigned char[9]){"\x01\x00\x00\x00\x02\x54\x0b\xd7\x1c"}
                    , .nonce = NULL
                    , .scriptPubKey = { .buf = (unsigned char [26]){"\x19\x76\xa9\x14\x48\x63\x3e\x2c\x0e\xe9\x49\x5d\xd3\xf9\xc4\x37\x32\xc4\x7f\x47\x02\xa3\x62\xc8\x88\xac"}
                                      , .len = 26
                                      }
                    }
                  , { .asset = (unsigned char[33]){"\x01\x23\x0f\x4f\x5d\x4b\x7c\x6f\xa8\x45\x80\x6e\xe4\xf6\x77\x13\x45\x9e\x1b\x69\xe8\xe6\x0f\xce\xe2\xe4\x94\x0c\x7a\x0d\x5d\xe1\xb2"}
                    , .value = (unsigned char[9]){"\x01\x00\x00\x00\x00\x00\x00\x0c\xe4"}
                    , .nonce = NULL
                    , .scriptPubKey = {0}
                  } }
      , .numInputs = 1
      , .numOutputs = 2
      , .version = 0x00000002
      , .lockTime = 0x00000000
      };
    transaction* tx1 = elements_simplicity_mallocTransaction(&testTx1);
    if (tx1) {
      successes++;
      bool execResult;
      {
        unsigned char imrResult[32];
        if (elements_simplicity_execSimplicity(&execResult, imrResult, tx1, 0, taproot, genesisHash, BUDGET_MAX, amr, elementsCheckSigHashAllTx1, sizeof_elementsCheckSigHashAllTx1) && execResult) {
          sha256_midstate imr;
          sha256_toMidstate(imr.s, imrResult);
          if (0 == memcmp(imr.s, elementsCheckSigHashAllTx1_imr, sizeof(uint32_t[8]))) {
            successes++;
          } else {
            failures++;
            printf("Unexpected IMR of elementsCheckSigHashAllTx1\n");
          }
        } else {
          failures++;
          printf("execSimplicity of elementsCheckSigHashAllTx1 on tx1 failed\n");
        }
      }
      {
        /* test the same transaction with a erroneous signature. */
        unsigned char brokenSig[sizeof_elementsCheckSigHashAllTx1];
        memcpy(brokenSig, elementsCheckSigHashAllTx1, sizeof_elementsCheckSigHashAllTx1);
        brokenSig[sizeof_elementsCheckSigHashAllTx1 - 1] ^= 0x80;
        if (elements_simplicity_execSimplicity(&execResult, NULL, tx1, 0, taproot, genesisHash, BUDGET_MAX, NULL, brokenSig, sizeof_elementsCheckSigHashAllTx1) && !execResult) {
          successes++;
        } else {
          failures++;
          printf("execSimplicity of brokenSig on tx1 unexpectedly succeeded\n");
        }
      }
    } else {
      printf("mallocTransaction(&rawTx1) failed\n");
      failures++;
    }
    free(tx1);
  }
  /* test a modified transaction with the same signature. */
  {
    rawTransaction testTx2 = (rawTransaction)
      { .input = (rawInput[])
                 { { .prevTxid = (unsigned char[32]){"\xeb\x04\xb6\x8e\x9a\x26\xd1\x16\x04\x6c\x76\xe8\xff\x47\x33\x2f\xb7\x1d\xda\x90\xff\x4b\xef\x53\x70\xf2\x52\x26\xd3\xbc\x09\xfc"}
                   , .prevIx = 0
                   , .sequence = 0xffffffff /* Here is the modification. */
                   , .issuance = {0}
                   , .txo = { .asset = (unsigned char[33]){"\x01\x23\x0f\x4f\x5d\x4b\x7c\x6f\xa8\x45\x80\x6e\xe4\xf6\x77\x13\x45\x9e\x1b\x69\xe8\xe6\x0f\xce\xe2\xe4\x94\x0c\x7a\x0d\x5d\xe1\xb2"}
                            , .value = (unsigned char[9]){"\x01\x00\x00\x00\x02\x54\x0b\xe4\x00"}
                            , .scriptPubKey = {0}
                 } }        }
      , .output = (rawOutput[])
                  { { .asset = (unsigned char[33]){"\x01\x23\x0f\x4f\x5d\x4b\x7c\x6f\xa8\x45\x80\x6e\xe4\xf6\x77\x13\x45\x9e\x1b\x69\xe8\xe6\x0f\xce\xe2\xe4\x94\x0c\x7a\x0d\x5d\xe1\xb2"}
                    , .value = (unsigned char[9]){"\x01\x00\x00\x00\x02\x54\x0b\xd7\x1c"}
                    , .nonce = NULL
                    , .scriptPubKey = { .buf = (unsigned char [26]){"\x19\x76\xa9\x14\x48\x63\x3e\x2c\x0e\xe9\x49\x5d\xd3\xf9\xc4\x37\x32\xc4\x7f\x47\x02\xa3\x62\xc8\x88\xac"}
                                      , .len = 26
                                      }
                    }
                  , { .asset = (unsigned char[33]){"\x01\x23\x0f\x4f\x5d\x4b\x7c\x6f\xa8\x45\x80\x6e\xe4\xf6\x77\x13\x45\x9e\x1b\x69\xe8\xe6\x0f\xce\xe2\xe4\x94\x0c\x7a\x0d\x5d\xe1\xb2"}
                    , .value = (unsigned char[9]){"\x01\x00\x00\x00\x00\x00\x00\x0c\xe4"}
                    , .nonce = NULL
                    , .scriptPubKey = {0}
                  } }
      , .numInputs = 1
      , .numOutputs = 2
      , .version = 0x00000002
      , .lockTime = 0x00000000
      };
    transaction* tx2 = elements_simplicity_mallocTransaction(&testTx2);
    if (tx2) {
      successes++;
      bool execResult;
      {
        if (elements_simplicity_execSimplicity(&execResult, NULL, tx2, 0, taproot, genesisHash, BUDGET_MAX, NULL, elementsCheckSigHashAllTx1, sizeof_elementsCheckSigHashAllTx1) && !execResult) {
          successes++;
        } else {
          failures++;
          printf("execSimplicity of elementsCheckSigHashAllTx1 on tx2 unexpectedly succeeded\n");
        }
      }
    } else {
      printf("mallocTransaction(&testTx2) failed\n");
      failures++;
    }
    free(tx2);
  }
  free(taproot);
}

static sha256_midstate hashint(uint_fast32_t n) {
  sha256_midstate result;
  sha256_context ctx = sha256_init(result.s);
  sha256_u32le(&ctx, n);
  sha256_finalize(&ctx);

  return result;
}

static uint_fast32_t rsort_no_duplicates(size_t i) {
  return i;
}

static uint_fast32_t rsort_all_duplicates(size_t i) {
  (void)i;
  return 0;
}

static uint_fast32_t rsort_one_duplicate(size_t i) {
  return i ? i : 1;
}

static void test_hasDuplicates(const char* name, bool expected, uint_fast32_t (*f)(size_t), size_t n) {
  sha256_midstate hashes[n];

  printf("Test %s\n", name);
  for(size_t i = 0; i < n; ++i) {
    hashes[i] = hashint(f(i));
  }

  bool duplicates;
  if (!hasDuplicates(&duplicates, hashes, n)) {
    failures++;
    printf("Unexpected failure of hasDuplicates\n");
  } else if (expected == duplicates) {
    successes++;
  } else if (expected) {
    failures++;
    printf("Expected duplicates but found none.\n");
  } else {
    failures++;
    printf("Expected no duplicate but found some.\n");
  }
}

int main(void) {
  test_decodeUptoMaxInt();
  test_hashBlock();
  test_occursCheck();

  test_hasDuplicates("hasDuplicates no duplicates testcase", false, rsort_no_duplicates, 10000);
  test_hasDuplicates("hasDuplicates all duplicates testcase", true, rsort_all_duplicates, 10000);
  test_hasDuplicates("hasDuplicates one duplicate testcase", true, rsort_one_duplicate, 10000);

  test_program("schnorr0", schnorr0, sizeof_schnorr0, true, schnorr0_cmr, schnorr0_imr, schnorr0_amr);
  test_program("schnorr6", schnorr6, sizeof_schnorr6, false, schnorr6_cmr, schnorr6_imr, schnorr6_amr);
  test_elements();

  printf("Successes: %d\n", successes);
  printf("Failures: %d\n", failures);
  return (0 == failures) ? EXIT_SUCCESS : EXIT_FAILURE;
}
