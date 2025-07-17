// Copyright (c) 2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <simplicity/elements/cmr.h>
#include <simplicity/dag.h>
#include <simplicity/deserialize.h> // simplicity_decodeMallocDag
#include <simplicity/limitations.h> // DAG_LEN_MAX
#include <simplicity/simplicity_alloc.h> // simplicity_free
#include <simplicity/typeInference.h> // simplicity_mallocTypeInference
#include <simplicity/elements/env.h>
#include <simplicity/elements/exec.h>
#include <simplicity/elements/primitive.h>

// Copy of computeCmr used for AMR
bool simplicity_elements_computeAmr( simplicity_err* error, unsigned char* amr
                                   , const unsigned char* program, size_t program_len
                                   , const unsigned char* witness, size_t witness_len) {
    simplicity_assert(NULL != error);
    simplicity_assert(NULL != amr);
    simplicity_assert(NULL != program || 0 == program_len);
    simplicity_assert(NULL != witness || 0 == witness_len);

    bitstream stream = initializeBitstream(program, program_len);
    dag_node* dag = NULL;
    combinator_counters census;
    int_fast32_t dag_len = simplicity_decodeMallocDag(&dag, simplicity_elements_decodeJet, &census, &stream);
    if (dag_len <= 0) {
        simplicity_assert(dag_len < 0);
        *error = (simplicity_err)dag_len;
    } else {
        simplicity_assert(NULL != dag);
        simplicity_assert((uint_fast32_t)dag_len <= DAG_LEN_MAX);
        *error = simplicity_closeBitstream(&stream);

        type* type_dag = NULL;
        if (IS_OK(*error)) {
            *error = simplicity_mallocTypeInference(&type_dag, simplicity_elements_mallocBoundVars, dag, (uint_fast32_t)dag_len, &census);
        }
        bitstream witness_stream;
        if (IS_OK(*error)) {
            witness_stream = initializeBitstream(witness, witness_len);
            *error = simplicity_fillWitnessData(dag, type_dag, (uint_fast32_t)dag_len, &witness_stream);
        }
        if (IS_OK(*error)) {
            *error = simplicity_closeBitstream(&witness_stream);
            if (SIMPLICITY_ERR_BITSTREAM_TRAILING_BYTES == *error) *error = SIMPLICITY_ERR_WITNESS_TRAILING_BYTES;
            if (SIMPLICITY_ERR_BITSTREAM_ILLEGAL_PADDING == *error) *error = SIMPLICITY_ERR_WITNESS_ILLEGAL_PADDING;
        }
        if (IS_OK(*error)) {
            analyses *analysis = (analyses*) simplicity_malloc((size_t)dag_len * sizeof(analyses));
            simplicity_assert(NULL != analysis);
            simplicity_computeAnnotatedMerkleRoot(analysis, dag, type_dag, (uint_fast32_t)dag_len);
            sha256_fromMidstate(amr, analysis[dag_len-1].annotatedMerkleRoot.s);
            simplicity_free(analysis);
        }
        simplicity_free(type_dag);
    }

    simplicity_free(dag);
    return IS_PERMANENT(*error);
}
