#include <simplicity/elements/exec.h>

#include <stdlib.h>
#include <stdalign.h>
#include <string.h>
#include "primitive.h"
#include "../../deserialize.h"
#include "../../eval.h"
#include "../../limitations.h"
#include "../../simplicity_assert.h"
#include "../../typeInference.h"

/* Deserialize a Simplicity 'program' and execute it in the environment of the 'ix'th input of 'tx' with `taproot`.
 *
 * If at any time malloc fails then '*error' is set to 'SIMPLICITY_ERR_MALLOC' and 'false' is returned,
 * meaning we were unable to determine the result of the simplicity program.
 * Otherwise, 'true' is returned indicating that the result was successfully computed and returned in the '*error' value.
 *
 * If deserialization, analysis, or execution fails, then '*error' is set to some SIMPLICITY_ERR.
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
 *               NULL != amr implies unsigned char amr[32]
 *               unsigned char program[program_len]
 */
extern bool elements_simplicity_execSimplicity( simplicity_err* error, unsigned char* imr
                                              , const transaction* tx, uint_fast32_t ix, const tapEnv* taproot
                                              , const unsigned char* genesisBlockHash
                                              , int64_t budget
                                              , const unsigned char* amr
                                              , const unsigned char* program, size_t program_len) {
  if (!error || !tx || !taproot) return false;
  simplicity_assert(NULL != program || 0 == program_len);

  combinator_counters census;
  dag_node* dag = NULL;
  bitstring witness;
  int32_t dag_len;
  sha256_midstate amr_hash, genesis_hash;

  if (amr) sha256_toMidstate(amr_hash.s, amr);
  sha256_toMidstate(genesis_hash.s, genesisBlockHash);

  {
    bitstream stream = initializeBitstream(program, program_len);
    dag_len = decodeMallocDag(&dag, &census, &stream);
    if (dag_len <= 0) {
      simplicity_assert(dag_len < 0);
      *error = dag_len;
      return IS_PERMANENT(*error);
    }
    simplicity_assert(NULL != dag);
    simplicity_assert((size_t)dag_len <= DAG_LEN_MAX);

    *error = decodeWitnessData(&witness, &stream);
    if (IS_OK(*error)) {
      *error = closeBitstream(&stream);
    }
  }

  if (IS_OK(*error)) {
    if (0 != memcmp(taproot->scriptCMR.s, dag[dag_len-1].cmr.s, sizeof(uint32_t[8]))) {
      *error = SIMPLICITY_ERR_CMR;
    }
  }

  if (IS_OK(*error)) {
    type* type_dag = NULL;
    *error = mallocTypeInference(&type_dag, dag, (size_t)dag_len, &census);
    if (IS_OK(*error)) {
      simplicity_assert(NULL != type_dag);
      if (0 != dag[dag_len-1].sourceType || 0 != dag[dag_len-1].targetType) {
        *error = SIMPLICITY_ERR_TYPE_INFERENCE_NOT_PROGRAM;
      }
    }
    if (IS_OK(*error)) {
      *error = fillWitnessData(dag, type_dag, (size_t)dag_len, witness);
    }
      if (IS_OK(*error)) {
      sha256_midstate imr_buf;
      static_assert(DAG_LEN_MAX <= SIZE_MAX / sizeof(sha256_midstate), "imr_buf array too large.");
      static_assert(1 <= DAG_LEN_MAX, "DAG_LEN_MAX is zero.");
      static_assert(DAG_LEN_MAX - 1 <= UINT32_MAX, "imr_buf array index does nto fit in uint32_t.");
      *error = verifyNoDuplicateIdentityRoots(&imr_buf, dag, type_dag, (size_t)dag_len);
      if (IS_OK(*error) && imr) sha256_fromMidstate(imr, imr_buf.s);
    }
    if (IS_OK(*error) && amr) {
      static_assert(DAG_LEN_MAX <= SIZE_MAX / sizeof(analyses), "analysis array too large.");
      static_assert(1 <= DAG_LEN_MAX, "DAG_LEN_MAX is zero.");
      static_assert(DAG_LEN_MAX - 1 <= UINT32_MAX, "analysis array index does nto fit in uint32_t.");
      analyses *analysis = malloc((size_t)dag_len * sizeof(analyses));
      if (analysis) {
        computeAnnotatedMerkleRoot(analysis, dag, type_dag, (size_t)dag_len);
        if (0 != memcmp(amr_hash.s, analysis[dag_len-1].annotatedMerkleRoot.s, sizeof(uint32_t[8]))) {
          *error = SIMPLICITY_ERR_AMR;
        }
      } else {
        /* malloc failed which counts as a transient error. */
        *error = SIMPLICITY_ERR_MALLOC;
      }
      free(analysis);
    }
    if (IS_OK(*error)) {
      txEnv env = build_txEnv(tx, taproot, &genesis_hash, ix);
      static_assert(BUDGET_MAX <= UBOUNDED_MAX, "BUDGET_MAX doesn't fit in ubounded.");
      *error = evalTCOProgram(dag, type_dag, (size_t)dag_len, &(ubounded){budget <= BUDGET_MAX ? (ubounded)budget : BUDGET_MAX}, &env);
    }
    free(type_dag);
  }

  free(dag);
  return IS_PERMANENT(*error);
}
