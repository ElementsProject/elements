#include <simplicity/elements/exec.h>

#include <stdalign.h>
#include <string.h>
#include "primitive.h"
#include "../../deserialize.h"
#include "../../eval.h"
#include "../../limitations.h"
#include "../../simplicity_alloc.h"
#include "../../simplicity_assert.h"
#include "../../typeInference.h"

/* Deserialize a Simplicity 'program' with its 'witness' data and execute it in the environment of the 'ix'th input of 'tx' with `taproot`.
 *
 * If at any time malloc fails then '*error' is set to 'SIMPLICITY_ERR_MALLOC' and 'false' is returned,
 * meaning we were unable to determine the result of the simplicity program.
 * Otherwise, 'true' is returned indicating that the result was successfully computed and returned in the '*error' value.
 *
 * If deserialization, analysis, or execution fails, then '*error' is set to some simplicity_err.
 *
 * If 'amr != NULL' and the annotated Merkle root of the decoded expression doesn't match 'amr' then '*error' is set to 'SIMPLICITY_ERR_AMR'.
 *
 * Otherwise '*error' is set to 'SIMPLICITY_NO_ERROR'.
 *
 * If 'imr != NULL' and '*error' is set to 'SIMPLICITY_NO_ERROR', then the identity Merkle root of the decoded expression is written to 'imr'.
 * Otherwise if 'imr != NULL'  and '*error' is not set to 'SIMPLCITY_NO_ERROR', then 'imr' may or may not be written to.
 *
 * Precondition: NULL != error;
 *               NULL != imr implies unsigned char imr[32]
 *               NULL != tx;
 *               NULL != taproot;
 *               unsigned char genesisBlockHash[32]
 *               0 <= budget;
 *               NULL != amr implies unsigned char amr[32]
 *               unsigned char program[program_len]
 *               unsigned char witness[witness_len]
 */
extern bool simplicity_elements_execSimplicity( simplicity_err* error, unsigned char* imr
                                              , const transaction* tx, uint_fast32_t ix, const tapEnv* taproot
                                              , const unsigned char* genesisBlockHash
                                              , int64_t budget
                                              , const unsigned char* amr
                                              , const unsigned char* program, size_t program_len
                                              , const unsigned char* witness, size_t witness_len) {
  simplicity_assert(NULL != error);
  simplicity_assert(NULL != tx);
  simplicity_assert(NULL != taproot);
  simplicity_assert(NULL != genesisBlockHash);
  simplicity_assert(0 <= budget);
  simplicity_assert(NULL != program || 0 == program_len);
  simplicity_assert(NULL != witness || 0 == witness_len);

  combinator_counters census;
  dag_node* dag = NULL;
  int_fast32_t dag_len;
  sha256_midstate amr_hash, genesis_hash;

  if (amr) sha256_toMidstate(amr_hash.s, amr);
  sha256_toMidstate(genesis_hash.s, genesisBlockHash);

  {
    bitstream stream = initializeBitstream(program, program_len);
    dag_len = simplicity_decodeMallocDag(&dag, &census, &stream);
    if (dag_len <= 0) {
      simplicity_assert(dag_len < 0);
      *error = (simplicity_err)dag_len;
      return IS_PERMANENT(*error);
    }
    simplicity_assert(NULL != dag);
    simplicity_assert((uint_fast32_t)dag_len <= DAG_LEN_MAX);
    *error = simplicity_closeBitstream(&stream);
  }

  if (IS_OK(*error)) {
    if (0 != memcmp(taproot->scriptCMR.s, dag[dag_len-1].cmr.s, sizeof(uint32_t[8]))) {
      *error = SIMPLICITY_ERR_CMR;
    }
  }

  if (IS_OK(*error)) {
    type* type_dag = NULL;
    *error = simplicity_mallocTypeInference(&type_dag, dag, (uint_fast32_t)dag_len, &census);
    if (IS_OK(*error)) {
      simplicity_assert(NULL != type_dag);
      if (0 != dag[dag_len-1].sourceType || 0 != dag[dag_len-1].targetType) {
        *error = SIMPLICITY_ERR_TYPE_INFERENCE_NOT_PROGRAM;
      }
    }
    if (IS_OK(*error)) {
      bitstream witness_stream = initializeBitstream(witness, witness_len);
      *error = simplicity_fillWitnessData(dag, type_dag, (uint_fast32_t)dag_len, &witness_stream);
      if (IS_OK(*error)) {
        *error = simplicity_closeBitstream(&witness_stream);
        if (SIMPLICITY_ERR_BITSTREAM_TRAILING_BYTES == *error) *error = SIMPLICITY_ERR_WITNESS_TRAILING_BYTES;
        if (SIMPLICITY_ERR_BITSTREAM_ILLEGAL_PADDING == *error) *error = SIMPLICITY_ERR_WITNESS_ILLEGAL_PADDING;
      }
    }
    if (IS_OK(*error)) {
      sha256_midstate imr_buf;
      static_assert(DAG_LEN_MAX <= SIZE_MAX / sizeof(sha256_midstate), "imr_buf array too large.");
      static_assert(1 <= DAG_LEN_MAX, "DAG_LEN_MAX is zero.");
      static_assert(DAG_LEN_MAX - 1 <= UINT32_MAX, "imr_buf array index does nto fit in uint32_t.");
      *error = simplicity_verifyNoDuplicateIdentityRoots(&imr_buf, dag, type_dag, (uint_fast32_t)dag_len);
      if (IS_OK(*error) && imr) sha256_fromMidstate(imr, imr_buf.s);
    }
    if (IS_OK(*error) && amr) {
      static_assert(DAG_LEN_MAX <= SIZE_MAX / sizeof(analyses), "analysis array too large.");
      static_assert(1 <= DAG_LEN_MAX, "DAG_LEN_MAX is zero.");
      static_assert(DAG_LEN_MAX - 1 <= UINT32_MAX, "analysis array index does nto fit in uint32_t.");
      analyses *analysis = simplicity_malloc((size_t)dag_len * sizeof(analyses));
      if (analysis) {
        simplicity_computeAnnotatedMerkleRoot(analysis, dag, type_dag, (uint_fast32_t)dag_len);
        if (0 != memcmp(amr_hash.s, analysis[dag_len-1].annotatedMerkleRoot.s, sizeof(uint32_t[8]))) {
          *error = SIMPLICITY_ERR_AMR;
        }
      } else {
        /* malloc failed which counts as a transient error. */
        *error = SIMPLICITY_ERR_MALLOC;
      }
      simplicity_free(analysis);
    }
    if (IS_OK(*error)) {
      txEnv env = simplicity_build_txEnv(tx, taproot, &genesis_hash, ix);
      static_assert(BUDGET_MAX <= UBOUNDED_MAX, "BUDGET_MAX doesn't fit in ubounded.");
      *error = evalTCOProgram(dag, type_dag, (size_t)dag_len, &(ubounded){budget <= BUDGET_MAX ? (ubounded)budget : BUDGET_MAX}, &env);
    }
    simplicity_free(type_dag);
  }

  simplicity_free(dag);
  return IS_PERMANENT(*error);
}
