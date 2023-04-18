#include <simplicity/elements/exec.h>

#include <stdlib.h>
#include <stdalign.h>
#include <string.h>
#include "primitive.h"
#include "../../deserialize.h"
#include "../../eval.h"
#include "../../limitations.h"
#include "../../typeInference.h"

/* Deserialize a Simplicity 'program' and execute it in the environment of the 'ix'th input of 'tx' with `taproot`.
 * If program isn't a proper encoding of a Simplicity program, including its 'program_len', then '*success' is set to false.
 * If the static analysis of the memory use of the Simplicity program exceeds 'CELL_MAX', then '*success' is set to false.
 * If the static analysis of CPU use of the Simplicity program exceeds the 'budget' (or exceeds 'BUDGET_MAX') measured in weight units, then '*success' is set to false.
 * If 'amr != NULL' and the annotated Merkle root of the decoded expression doesn't match 'amr' then '*success' is set to false.
 * Otherwise evaluation proceeds and '*success' is set to the result of evaluation.
 * If 'imr != NULL' and '*success' is set to true, then the identity Merkle root of the decoded expression is written to 'imr'.
 * Otherwise if 'imr != NULL' then 'imr' may or may not be written to.
 *
 * If at any time there is a transient error, such as malloc failing then 'false' is returned, and 'success' may be modified.
 * Otherwise, 'true' is returned.
 *
 * Precondition: NULL != success;
 *               NULL != imr implies unsigned char imr[32]
 *               NULL != tx;
 *               NULL != taproot;
 *               unsigned char genesisBlockHash[32]
 *               NULL != amr implies unsigned char amr[32]
 *               unsigned char program[program_len]
 */
extern bool elements_simplicity_execSimplicity( bool* success, unsigned char* imr
                                              , const transaction* tx, uint_fast32_t ix, const tapEnv* taproot
                                              , const unsigned char* genesisBlockHash
                                              , int64_t budget
                                              , const unsigned char* amr
                                              , const unsigned char* program, size_t program_len) {
  if (!success || !tx || !taproot) return false;
  assert(NULL != program || 0 == program_len);

  bool result;
  combinator_counters census;
  dag_node* dag;
  bitstring witness;
  int32_t dag_len;
  sha256_midstate amr_hash, genesis_hash;

  if (amr) sha256_toMidstate(amr_hash.s, amr);
  sha256_toMidstate(genesis_hash.s, genesisBlockHash);

  {
    bitstream stream = initializeBitstream(program, program_len);
    dag_len = decodeMallocDag(&dag, &census, &stream);
    if (dag_len <= 0) {
      *success = false;
      assert(dag_len < 0);
      return PERMANENT_FAILURE(dag_len);
    }
    assert((size_t)dag_len <= DAG_LEN_MAX);

    int32_t err = decodeWitnessData(&witness, &stream);
    if (err < 0) {
      *success = false;
      result = PERMANENT_FAILURE(err);
    } else {
      *success = closeBitstream(&stream);
      result = true;
    }
  }

  if (*success) {
    *success = 0 == memcmp(taproot->scriptCMR.s, dag[dag_len-1].cmr.s, sizeof(uint32_t[8]));
    if (*success) {
      type* type_dag;
      result = mallocTypeInference(&type_dag, dag, (size_t)dag_len, &census);
      *success = result && type_dag && 0 == dag[dag_len-1].sourceType && 0 == dag[dag_len-1].targetType
              && fillWitnessData(dag, type_dag, (size_t)dag_len, witness);
      if (*success) {
        static_assert(DAG_LEN_MAX <= SIZE_MAX / sizeof(sha256_midstate), "imr_buf array too large.");
        static_assert(1 <= DAG_LEN_MAX, "DAG_LEN_MAX is zero.");
        static_assert(DAG_LEN_MAX - 1 <= UINT32_MAX, "imr_buf array index does nto fit in uint32_t.");
        sha256_midstate* imr_buf = malloc((size_t)dag_len * sizeof(sha256_midstate));
        bool noDupsCheck;
        result = imr_buf && verifyNoDuplicateIdentityRoots(&noDupsCheck, imr_buf, dag, type_dag, (size_t)dag_len);
        *success = result && noDupsCheck;
        if (*success && imr) sha256_fromMidstate(imr, imr_buf[dag_len-1].s);
        free(imr_buf);
      }
      if (*success && amr) {
        static_assert(DAG_LEN_MAX <= SIZE_MAX / sizeof(analyses), "analysis array too large.");
        static_assert(1 <= DAG_LEN_MAX, "DAG_LEN_MAX is zero.");
        static_assert(DAG_LEN_MAX - 1 <= UINT32_MAX, "analysis array index does nto fit in uint32_t.");
        analyses *analysis = malloc((size_t)dag_len * sizeof(analyses));
        if (analysis) {
          computeAnnotatedMerkleRoot(analysis, dag, type_dag, (size_t)dag_len);
          *success = 0 == memcmp(amr_hash.s, analysis[dag_len-1].annotatedMerkleRoot.s, sizeof(uint32_t[8]));
        } else {
          /* malloc failed which counts as a transient error. */
          *success = result = false;
        }
        free(analysis);
      }
      if (*success) {
        txEnv env = build_txEnv(tx, taproot, &genesis_hash, ix);
        static_assert(BUDGET_MAX <= BOUNDED_MAX, "BUDGET_MAX doesn't fit in ubounded.");
        result = evalTCOProgram(success, dag, type_dag, (size_t)dag_len, budget <= BUDGET_MAX ? (ubounded)budget : BUDGET_MAX, &env);
      }
      free(type_dag);
    }
  }

  free(dag);
  return result;
}
