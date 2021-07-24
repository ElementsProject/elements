#include <simplicity/elements.h>

#include <stdlib.h>
#include <stdalign.h>
#include <string.h>
#include "elements/primitive.h"
#include "../deserialize.h"
#include "../eval.h"
#include "../sha256.h"
#include "../typeInference.h"

#define PADDING(alignType, allocated) ((alignof(alignType) - (allocated) % alignof(alignType)) % alignof(alignType))

/* Add a 256-bit hash to be consumed by an ongoing SHA-256 evaluation.
 *
 * Precondition: NULL != ctx;
 *               NULL != h;
 */
static void sha256_hash(sha256_context* ctx, const sha256_midstate* h) {
  unsigned char buf[32];
  sha256_fromMidstate(buf, h->s);
  sha256_uchars(ctx, buf, sizeof(buf));
}

/* Add an 'outpoint' to be consumed by an ongoing SHA-256 evaluation.
 * The 'txid' is consumed first in big endian order.
 * The 'ix' is consumed next in little endian byte-order.
 *
 * Precondition: NULL != ctx;
 *               NULL != op;
 */
static void sha256_outpoint(sha256_context* ctx, const outpoint* op) {
  sha256_hash(ctx, &op->txid);
  sha256_u32le(ctx,op->ix);
}

/* Add an 'confidential' value to be consumed by an ongoing SHA-256 evaluation.
 * If the 'confidential' value is blinded, then the 'evenPrefix' used if the y coordinate is even,
 * and the 'oddPrefix' is used if the y coordinate is odd.
 * If the 'confidential' value is explicit, then '0x01' is used as the prefix.
 * If the 'confidential' value is "NULL" then only '0x00' added.
 *
 * Precondition: NULL != ctx;
 *               NULL != conf;
 */
static void sha256_confidential(unsigned char evenPrefix, unsigned char oddPrefix, sha256_context* ctx, const confidential* conf) {
  switch (conf->prefix) {
   case NONE: sha256_uchar(ctx, 0x00); return;
   case EXPLICIT: sha256_uchar(ctx, 0x01); break;
   case EVEN_Y: sha256_uchar(ctx, evenPrefix); break;
   case ODD_Y: sha256_uchar(ctx, oddPrefix); break;
  }
  sha256_hash(ctx, &conf->data);
}

/* Add an 'confidential' asset to be consumed by an ongoing SHA-256 evaluation.
 *
 * Precondition: NULL != ctx;
 *               NULL != asset;
 */
static void sha256_confAsset(sha256_context* ctx, const confidential* asset) {
  sha256_confidential(0x0a, 0x0b, ctx, asset);
}

/* Add an 'confidential' nonce to be consumed by an ongoing SHA-256 evaluation.
 *
 * Precondition: NULL != ctx;
 *               NULL != nonce;
 */
static void sha256_confNonce(sha256_context* ctx, const confidential* nonce) {
  sha256_confidential(0x02, 0x03, ctx, nonce);
}

/* Add an 'confidential' amount to be consumed by an ongoing SHA-256 evaluation.
 *
 * Precondition: NULL != ctx;
 *               NULL != amt;
 */
static void sha256_confAmt(sha256_context* ctx, const confAmount* amt) {
  switch (amt->prefix) {
   case NONE:
    sha256_uchar(ctx, 0x00);
    return;
   case EXPLICIT:
    sha256_uchar(ctx, 0x01);
    sha256_u64be(ctx, amt->explicit);
    return;
   case EVEN_Y:
   case ODD_Y:
    sha256_uchar(ctx, EVEN_Y == amt->prefix ? 0x08 : 0x09);
    sha256_hash(ctx, &amt->confidential);
    return;
  }
}

/* Add an 'assetIssuance' to be consumed by an ongoing SHA-256 evaluation.
 *
 * Precondition: NULL != ctx;
 *               NULL != issuance;
 */
static void sha256_issuance(sha256_context* ctx, const assetIssuance* issuance) {
  switch (issuance->type) {
   case NO_ISSUANCE:
    sha256_confAmt(ctx, &(confAmount){0});
    sha256_confAmt(ctx, &(confAmount){0});
    break;
   case NEW_ISSUANCE:
    sha256_confAmt(ctx, &issuance->assetAmt);
    sha256_confAmt(ctx, &issuance->tokenAmt);
    sha256_hash(ctx, &(sha256_midstate){0});
    sha256_hash(ctx, &issuance->contractHash);
    break;
   case REISSUANCE:
    sha256_confAmt(ctx, &issuance->assetAmt);
    sha256_confAmt(ctx, &(confAmount){0});
    sha256_hash(ctx, &issuance->blindingNonce);
    sha256_hash(ctx, &issuance->entropy);
    break;
  }
}

/* Compute the SHA-256 hash of a scriptPubKey and write it into 'result'.
 *
 * Precondition: NULL != result;
 *               NULL != scriptPubKey;
 */
static void hashScriptPubKey(sha256_midstate* result, const rawScript* scriptPubKey) {
  sha256_context ctx = sha256_init(result->s);
  sha256_uchars(&ctx, scriptPubKey->code, scriptPubKey->len);
  sha256_finalize(&ctx);
}

/* Initialize a 'confidential' asset or 'confidential' nonce from an unsigned char array from a 'rawTransaction'.
 *
 * Precondition: NULL != conf;
 *               unsigned char rawConf[33] or rawConf == NULL;
 */
static void copyRawConfidential(confidential* conf, const unsigned char* rawConf) {
  if (rawConf) {
    *conf = (confidential){ .prefix = 0x01 == rawConf[0] ? EXPLICIT
                                    : 0x01 == (0x01 & rawConf[0]) ? ODD_Y
                                    : EVEN_Y
                          };
    sha256_toMidstate(conf->data.s, &rawConf[1]);
  } else {
    *conf = (confidential){0};
  }
}

/* Initialize a 'confAmount' from an unsigned char array from a 'rawTransaction'.
 *
 * Precondition: NULL != amt;
 *               unsigned char rawAmt[rawAmt[0] == 0x01 ? 9 : 33] or rawAmt == NULL
 */
static void copyRawAmt(confAmount* amt, const unsigned char* rawAmt) {
  if (rawAmt) {
    if (0x01 == rawAmt[0]) {
      amt->prefix = EXPLICIT;
      amt->explicit = ReadBE64(&rawAmt[1]);
    } else {
      amt->prefix = 0x01 == (0x01 & rawAmt[0]) ? ODD_Y : EVEN_Y;
      sha256_toMidstate(amt->confidential.s, &rawAmt[1]);
    }
  } else {
    amt->prefix = NONE;
  }
}

/* Initialize a 'sigInput' from a 'rawInput', copying or hashing the data as needed.
 *
 * Precondition: NULL != result;
 *               NULL != input;
 */
static void copyInput(sigInput* result, const rawInput* input) {
  *result = (sigInput){ .prevOutpoint = { .ix = input->prevIx }
                      , .sequence = input->sequence
                      , .isPegin = input->isPegin
                      };
  sha256_toMidstate(result->prevOutpoint.txid.s, input->prevTxid);
  hashScriptPubKey(&result->txo.scriptPubKey, &input->txo.scriptPubKey);
  copyRawConfidential(&result->txo.asset, input->txo.asset);
  copyRawAmt(&result->txo.amt, input->txo.value);
  if (input->issuance.amount || input->issuance.inflationKeys) {
    sha256_toMidstate(result->issuance.blindingNonce.s, input->issuance.blindingNonce);
    if (0 == result->issuance.blindingNonce.s[0] && 0 == result->issuance.blindingNonce.s[1] &&
        0 == result->issuance.blindingNonce.s[2] && 0 == result->issuance.blindingNonce.s[3] &&
        0 == result->issuance.blindingNonce.s[4] && 0 == result->issuance.blindingNonce.s[5] &&
        0 == result->issuance.blindingNonce.s[6] && 0 == result->issuance.blindingNonce.s[7]) {
      sha256_toMidstate(result->issuance.contractHash.s, input->issuance.assetEntropy);
      copyRawAmt(&result->issuance.assetAmt, input->issuance.amount);
      copyRawAmt(&result->issuance.tokenAmt, input->issuance.inflationKeys);
      result->issuance.type = NEW_ISSUANCE;
    } else {
      sha256_toMidstate(result->issuance.entropy.s, input->issuance.assetEntropy);
      copyRawAmt(&result->issuance.assetAmt, input->issuance.amount);
      result->issuance.type = REISSUANCE;
    }
  }
}

/* If the 'scriptPubKey' is a TX_NULL_DATA, return a count of the number of "push only" operations (this excludes the OP_RETURN).
 * Otherwise return 0.
 *
 * Note: that a TX_NULL_DATA could have zero "push only" operations,
 * in which case 0 is returned even though it is a TX_NULL_DATA scriptPubKey.
 *
 * Precondition: NULL != scriptPubKey
 */
static uint_fast32_t countNullDataCodes(const rawScript* scriptPubKey) {
  if (0 == scriptPubKey->len || 0x6a != scriptPubKey->code[0] ) return 0;

  uint_fast32_t result = 0;
  for (uint_fast32_t i = 1; i < scriptPubKey->len;) {
    uint_fast32_t skip = 0;
    unsigned char code = scriptPubKey->code[i++];
    if (0x60 < code) return 0;
    if (code < 0x4c) {
      skip = code;
    } else if (code < 0x4f) {
      if (scriptPubKey->len == i) return 0;
      skip = scriptPubKey->code[i++];
      if (0x4d <= code) {
        if (scriptPubKey->len == i) return 0;
        skip += (uint_fast32_t)(scriptPubKey->code[i++]) << 8;
        if (0x4e <= code) {
          if (scriptPubKey->len == i) return 0;
          skip += (uint_fast32_t)(scriptPubKey->code[i++]) << 16;
          if (scriptPubKey->len == i) return 0;
          skip += (uint_fast32_t)(scriptPubKey->code[i++]) << 24;
        }
      }
    }
    if (scriptPubKey->len - i < skip) return 0;
    i += skip;
    result++;
  }
  return result;
}

/* Return a count of the total number of "push only" operations in all output scriptPubKey's that are TX_NULL_DATA.
 *
 * Precondition: NULL != rawTx
 */
static uint_fast64_t countTotalNullDataCodes(const rawTransaction* rawTx) {
  uint_fast64_t result = 0;
  for (uint_fast32_t i = 0; i < rawTx->numOutputs; ++i) {
    result += countNullDataCodes(&rawTx->output[i].scriptPubKey);
  }
  return result;
}

/* Determine if 'scriptPubKey' is a TX_NULL_DATA script, and fill 'result' with (digests of) the push data opcodes.
 * If 'scriptPubKey' isn't a TX_NULL_DATA, then 'result->op' is set to NULL.
 * Otherwise '*result' is set to '(parsedNullData){ .op = *allocation, .len = countNullDataCodes(scriptPubKey) }.
 * and then the 'opcode result->op[result->len]' array is filled in with (digests of) the pus data opcode.
 *      and '*allocation' is incremented by 'result->len'
 *      and '*allocationLen' is decremented by 'result->len'.
 * Values in the '*allocation' array may be modified.
 *
 * Note: even if '*allocationLen == 0' we require that '*allocation != NULL' as a precondition
 * in order for 'result' to distinguish between non-NULL_TX_DATA and empty NULL_TX_data
 *
 * Precondition: NULL != result;
 *               NULL != *allocation;
 *               opcode (*allocation)[*allocationLen];
 *               NULL != scriptPubKey;
 *               countNullDataCodes(scriptPubKey) <= *allocationLen
 */
static void parseNullData(parsedNullData* result, opcode** allocation, size_t* allocationLen, const rawScript* scriptPubKey) {
  *result = (parsedNullData){ .op = *allocation };

  if (0 == scriptPubKey->len || 0x6a != scriptPubKey->code[0] ) { result->op = NULL; return; }

  for (uint_fast32_t i = 1; i < scriptPubKey->len; ++result->len) {
    unsigned char code = scriptPubKey->code[i++];
    if (*allocationLen <= result->len || 0x60 < code) { result->op = NULL; return; }
    if (0x4f <= code) {
      (*allocation)[result->len].code = OP_1NEGATE + (code - 0x4f);
    } else {
      uint_fast32_t skip = 0;
      if (code < 0x4c) {
        skip = code;
        (*allocation)[result->len].code = OP_IMMEDIATE;
      } else {
        if (scriptPubKey->len == i) { result->op = NULL; return; }
        skip = scriptPubKey->code[i++];
        if (code < 0x4d) {
          (*allocation)[result->len].code = OP_PUSHDATA;
        } else {
          if (scriptPubKey->len == i) { result->op = NULL; return; }
          skip += (uint_fast32_t)(scriptPubKey->code[i++]) << 8;
          if (code < 0x4e) {
            (*allocation)[result->len].code = OP_PUSHDATA2;
          } else {
            if (scriptPubKey->len == i) { result->op = NULL; return; }
            skip += (uint_fast32_t)(scriptPubKey->code[i++]) << 16;
            if (scriptPubKey->len == i) { result->op = NULL; return; }
            skip += (uint_fast32_t)(scriptPubKey->code[i++]) << 24;
            (*allocation)[result->len].code = OP_PUSHDATA4;
          }
        }
      }
      if (scriptPubKey->len - i < skip) { result->op = NULL; return; }
      {
        sha256_context ctx = sha256_init((*allocation)[result->len].dataHash.s);
        sha256_uchars(&ctx, &scriptPubKey->code[i], skip);
        sha256_finalize(&ctx);
      }
      i += skip;
    }
  }
  *allocation += result->len; /* C requires '*allocation != NULL', even when 'result->len == 0'. */
  *allocationLen -= result->len;
}

/* Initialize a 'sigOutput' from a 'rawOuput', copying or hashing the data as needed.
 *
 * '*allocation' is incremented by 'countNullDataCodes(&output->scriptPubKey)'
 * '*allocationLen' is decremented by 'countNullDataCodes(&output->scriptPubKey)'.
 * Values in the '*allocation' array may be modified.
 *
 * Precondition: NULL != result;
 *               NULL != *allocation;
 *               opcode (*allocation)[*allocationLen];
 *               NULL != output;
 *               countNullDataCodes(&output->scriptPubKey) <= *allocationLen
 */
static void copyOutput(sigOutput* result, opcode** allocation, size_t* allocationLen, const rawOutput* output) {
  hashScriptPubKey(&result->scriptPubKey, &output->scriptPubKey);
  copyRawConfidential(&result->asset, output->asset);
  copyRawAmt(&result->amt, output->value);
  copyRawConfidential(&result->nonce, output->nonce);
  parseNullData(&result->pnd, allocation, allocationLen, &output->scriptPubKey);
  result->isNullData = NULL != result->pnd.op;
}

/* Allocate and initialize a 'transaction' from a 'rawOuput', copying or hashing the data as needed.
 * Returns NULL if malloc fails (or if malloc cannot be called because we require an allocation larger than SIZE_MAX).
 *
 * Precondition: NULL != rawTx
 */
extern transaction* elements_simplicity_mallocTransaction(const rawTransaction* rawTx) {
  if (!rawTx) return NULL;

  size_t allocationSize = sizeof(transaction);

  const size_t pad1 = PADDING(sigInput, allocationSize);
  if (SIZE_MAX - allocationSize < pad1) return NULL;
  allocationSize += pad1;

  /* Multiply by (size_t)1 to disable type-limits warning. */
  if (SIZE_MAX / sizeof(sigInput) < (size_t)1 * rawTx->numInputs) return NULL;
  if (SIZE_MAX - allocationSize < rawTx->numInputs * sizeof(sigInput)) return NULL;
  allocationSize += rawTx->numInputs * sizeof(sigInput);

  const size_t pad2 = PADDING(sigOutput, allocationSize);
  if (SIZE_MAX - allocationSize < pad2) return NULL;
  allocationSize += pad2;

  /* Multiply by (size_t)1 to disable type-limits warning. */
  if (SIZE_MAX / sizeof(sigOutput) < (size_t)1 * rawTx->numOutputs) return NULL;
  if (SIZE_MAX - allocationSize < rawTx->numOutputs * sizeof(sigOutput)) return NULL;
  allocationSize += rawTx->numOutputs * sizeof(sigOutput);

  const size_t pad3 = PADDING(opcode, allocationSize);
  if (SIZE_MAX - allocationSize < pad3) return NULL;
  allocationSize += pad3;

  const uint_fast64_t totalNullDataCodes = countTotalNullDataCodes(rawTx);
  /* Multiply by (size_t)1 to disable type-limits warning. */
  if (SIZE_MAX / sizeof(opcode) < (size_t)1 * totalNullDataCodes) return NULL;
  if (SIZE_MAX - allocationSize < totalNullDataCodes * sizeof(opcode)) return NULL;
  allocationSize += totalNullDataCodes * sizeof(opcode);

  char *allocation = malloc(allocationSize);
  if (!allocation) return NULL;

  transaction* const tx = (transaction*)allocation;
  allocation += sizeof(transaction) + pad1;

  sigInput* const input = (sigInput*)allocation;
  allocation += rawTx->numInputs * sizeof(sigInput) + pad2;

  sigOutput* const output = (sigOutput*)allocation;
  allocation += rawTx->numOutputs * sizeof(sigOutput) + pad3;

  opcode* ops = (opcode*)allocation;
  size_t opsLen = (size_t)totalNullDataCodes;

  *tx = (transaction){ .input = input
                     , .output = output
                     , .numInputs = rawTx->numInputs
                     , .numOutputs = rawTx->numOutputs
                     , .version = rawTx->version
                     , .lockTime = rawTx->lockTime
                     };

  {
    sha256_context ctx = sha256_init(tx->inputsHash.s);
    for (uint_fast32_t i = 0; i < tx->numInputs; ++i) {
      copyInput(&input[i], &rawTx->input[i]);
      sha256_outpoint(&ctx, &input[i].prevOutpoint);
      sha256_u32le(&ctx, input[i].sequence);
      sha256_issuance(&ctx, &input[i].issuance);
    }
    sha256_finalize(&ctx);
  }

  {
    sha256_context ctx = sha256_init(tx->outputsHash.s);
    for (uint_fast32_t i = 0; i < tx->numOutputs; ++i) {
      copyOutput(&output[i], &ops, &opsLen, &rawTx->output[i]);
      sha256_confAsset(&ctx, &output[i].asset);
      sha256_confAmt(&ctx, &output[i].amt);
      sha256_confNonce(&ctx, &output[i].nonce);
      sha256_hash(&ctx, &output[i].scriptPubKey);
    }
    sha256_finalize(&ctx);
  }

  return tx;
}

/* Deserialize a Simplicity program from 'file' and execute it in the environment of the 'ix'th input of 'tx'.
 * If the file isn't a proper encoding of a Simplicity program, '*success' is set to false.
 * If EOF isn't encountered at the end of decoding, '*success' is set to false.
 * If 'cmr != NULL' and the commitment Merkle root of the decoded expression doesn't match 'cmr' then '*success' is set to false.
 * If 'amr != NULL' and the annotated Merkle root of the decoded expression doesn't match 'amr' then '*success' is set to false.
 * Otherwise evaluation proceeds and '*success' is set to the result of evaluation.
 * If 'imr != NULL' and '*success' is set to true, then the identity Merkle root of the decoded expression is written to 'imr'.
 * Otherwise if 'imr != NULL' then 'imr' may or may not be written to.
 *
 * If at any time there is a transient error, such as malloc failing or an I/O error reading from 'file'
 * then 'false' is returned, and 'success' and 'file' may be modified.
 * Otherwise, 'true' is returned.
 *
 * Precondition: NULL != success;
 *               NULL != imr implies unsigned char imr[32]
 *               NULL != tx;
 *               NULL != cmr implies unsigned char cmr[32]
 *               NULL != amr implies unsigned char amr[32]
 *               NULL != file;
 */
extern bool elements_simplicity_execSimplicity(bool* success, unsigned char* imr, const transaction* tx, uint_fast32_t ix,
                                               const unsigned char* cmr, const unsigned char* amr, FILE* file) {
  if (!success || !tx || !file) return false;

  bool result;
  combinator_counters census;
  dag_node* dag;
  void* witnessAlloc = NULL;
  bitstring witness;
  int32_t len;
  sha256_midstate cmr_hash, amr_hash;

  if (cmr) sha256_toMidstate(cmr_hash.s, cmr);
  if (amr) sha256_toMidstate(amr_hash.s, amr);

  {
    bitstream stream = initializeBitstream(file);
    len = decodeMallocDag(&dag, &census, &stream);
    if (len < 0) {
      *success = false;
      return PERMANENT_FAILURE(len);
    }

    int32_t err = decodeMallocWitnessData(&witnessAlloc, &witness, &stream);
    if (err < 0) {
      *success = false;
      result = PERMANENT_FAILURE(err);
    } else if (EOF != getc(file)) { /* Check that we hit the end of 'file' */
      *success = false;
      result = !ferror(file);
    } else {
      *success = result = !ferror(file);
    }
  }

  if (*success) {
    *success = !cmr || 0 == memcmp(cmr_hash.s, dag[len-1].cmr.s, sizeof(uint32_t[8]));
    if (*success) {
      type* type_dag;
      result = mallocTypeInference(&type_dag, dag, (size_t)len, &census);
      *success = result && type_dag && 0 == dag[len-1].sourceType && 0 == dag[len-1].targetType
              && fillWitnessData(dag, type_dag, (size_t)len, witness);
      if (*success) {
        sha256_midstate* imr_buf = (size_t)len <= SIZE_MAX / sizeof(sha256_midstate)
                                 ? malloc((size_t)len * sizeof(sha256_midstate))
                                 : NULL;
        bool noDupsCheck;
        result = imr_buf && verifyNoDuplicateIdentityRoots(&noDupsCheck, imr_buf, dag, type_dag, (size_t)len);
        *success = result && noDupsCheck;
        if (*success && imr) sha256_fromMidstate(imr, imr_buf[len-1].s);
        free(imr_buf);
      }
      if (*success && amr) {
        analyses *analysis = (size_t)len <= SIZE_MAX / sizeof(analyses)
                           ? malloc((size_t)len * sizeof(analyses))
                           : NULL;
        if (analysis) {
          computeAnnotatedMerkleRoot(analysis, dag, type_dag, (size_t)len);
          *success = 0 == memcmp(amr_hash.s, analysis[len-1].annotatedMerkleRoot.s, sizeof(uint32_t[8]));
        } else {
          /* malloc failed which counts as a transient error. */
          *success = result = false;
        }
        free(analysis);
      }
      if (*success) {
        result = evalTCOProgram(success, dag, type_dag, (size_t)len, &(txEnv){.tx = tx, .scriptCMR = cmr_hash.s, .ix = ix});
      }
      free(type_dag);
    }
  }

  free(dag);
  free(witnessAlloc);
  return result;
}
