/* This module provides functions for evaluating Simplicity programs and expressions.
 */
#ifndef SIMPLICITY_EVAL_H
#define SIMPLICITY_EVAL_H

#include "bounded.h"
#include "dag.h"

typedef unsigned char flags_type;
#define CHECK_NONE 0
#define CHECK_EXEC 0x10
#define CHECK_CASE 0x60
#define CHECK_ALL ((flags_type)(-1))

/* Run the Bit Machine on the well-typed Simplicity expression 'dag[len]'.
 * If 'NULL != input', initialize the active read frame's data with 'input[ROUND_UWORD(inputSize)]'.
 *
 * If malloc fails, returns 'SIMPLICITY_ERR_MALLOC'.
 * If static analysis results determines the bound on cpu requirements exceed the allowed budget, returns 'SIMPLICITY_ERR_EXEC_BUDGET'
 * If static analysis results determines the bound on memory allocation requirements exceed the allowed limits, returns 'SIMPLICITY_ERR_EXEC_MEMORY'
 * If during execution some jet execution fails, returns 'SIMPLICITY_ERR_EXEC_JET'.
 * If during execution some 'assertr' or 'assertl' combinator fails, returns 'SIMPLICITY_ERR_EXEC_ASESRT'.
 *
 * If none of the above conditions fail and 'NULL != output', then a copy the final active write frame's data is written to 'output[roundWord(outputSize)]'.
 *
 * If 'anti_dos_checks' includes the 'CHECK_EXEC' flag, and not every non-HIDDEN dag node is executed, returns 'SIMPLICITY_ERR_ANTIDOS'
 * If 'anti_dos_checks' includes the 'CHECK_CASE' flag, and not every case node has both branches executed, returns 'SIMPLICITY_ERR_ANTIDOS'
 *
 * Otherwise 'SIMPLICITY_NO_ERROR' is returned.
 *
 * Precondition: dag_node dag[len] and 'dag' is well-typed with 'type_dag' of type A |- B;
 *               inputSize == bitSize(A);
 *               outputSize == bitSize(B);
 *               output == NULL or UWORD output[ROUND_UWORD(outputSize)];
 *               input == NULL or UWORD input[ROUND_UWORD(inputSize)];
 *               budget <= BUDGET_MAX
 *               if 'dag[len]' represents a Simplicity expression with primitives then 'NULL != env';
 */
simplicity_err evalTCOExpression( flags_type anti_dos_checks, UWORD* output, ubounded outputSize, const UWORD* input, ubounded inputSize
                                , const dag_node* dag, type* type_dag, size_t len, ubounded budget, const txEnv* env
                                );

/* Run the Bit Machine on the well-typed Simplicity program 'dag[len]'.
 *
 * If malloc fails, returns 'SIMPLICITY_ERR_MALLOC'.
 * If static analysis results determines the bound on cpu requirements exceed the allowed budget, returns 'SIMPLICITY_ERR_EXEC_BUDGET'
 * If static analysis results determines the bound on memory allocation requirements exceed the allowed limits, returns 'SIMPLICITY_ERR_EXEC_MEMORY'
 * If during execution some jet execution fails, returns 'SIMPLICITY_ERR_EXEC_JET'.
 * If during execution some 'assertr' or 'assertl' combinator fails, returns 'SIMPLICITY_ERR_EXEC_ASESRT'.
 * If not every non-HIDDEN dag node is executed, returns 'SIMPLICITY_ERR_ANTIDOS'
 * If not every case node has both branches executed, returns 'SIMPLICITY_ERR_ANTIDOS'
 *
 * Otherwise 'SIMPLICITY_NO_ERROR' is returned.
 *
 * Precondition: dag_node dag[len] and 'dag' is well-typed with 'type_dag' of type 1 |- 1;
 *               budget <= BUDGET_MAX
 *               if 'dag[len]' represents a Simplicity expression with primitives then 'NULL != env';
 */
static inline simplicity_err evalTCOProgram(const dag_node* dag, type* type_dag, size_t len, ubounded budget, const txEnv* env) {
  return evalTCOExpression(CHECK_ALL, NULL, 0, NULL, 0, dag, type_dag, len, budget, env);
}
#endif
