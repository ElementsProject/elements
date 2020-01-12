/* This module provides functions for evaluating Simplicity programs and expressions.
 */
#ifndef EVAL_H
#define EVAL_H

#include "dag.h"

/* Run the Bit Machine on the well-typed Simplicity expression 'dag[len]'.
 * If 'NULL != input', initialize the active read frame's data with 'input[roundUWord(inputSize)]'.
 *
 * If malloc fails, return 'false', otherwise return 'true'.
 * If static analysis results determines the bound on memory allocation requirements exceed the allowed limits,
 * '*evalSuccess' is set to 'false'.
 * If during execution an 'assertr' or 'assertl' combinator fails, '*evalSuccess' is set to 'false'
 * Otherwise '*evalSuccess' is set to 'true'.
 *
 * If the function returns 'true' and '*evalSuccess' and 'NULL != output',
 * copy the final active write frame's data to 'output[roundWord(outputSize)]'.
 *
 * Precondition: NULL != evalSuccess
 *               dag_node dag[len] and 'dag' is well-typed with 'type_dag' of type A |- B;
 *               inputSize == bitSize(A);
 *               outputSize == bitSize(B);
 *               outputSize + UWORD_BIT - 1 <= SIZE_MAX;
 *               inputSize + UWORD_BIT - 1 <= SIZE_MAX;
 *               output == NULL or UWORD output[roundUWord(outputSize)];
 *               input == NULL or UWORD input[roundUWord(inputSize)];
 *               if 'dag[len]' represents a Simplicity expression with primitives then 'NULL != env';
 */
bool evalTCOExpression( bool *evalSuccess, UWORD* output, size_t outputSize, const UWORD* input, size_t inputSize
                      , const dag_node* dag, type* type_dag, size_t len, const txEnv* env
                      );

/* Run the Bit Machine on the well-typed Simplicity program 'dag[len]'.
 *
 * If static analysis results determines the bound on memory allocation requirements exceed the allowed limits,
 * set '*evalSuccess' to 'false' and return 'true'.
 * If malloc fails, return 'false', otherwise return 'true'.
 * If during execution an 'assertr' or 'assertl' combinator fails, '*evalSuccess' is set to 'false'
 * Otherwise '*evalSuccess' is set to 'true'.
 *
 * Precondition: NULL != evalSuccess
 *               dag_node dag[len] and 'dag' is well-typed with 'type_dag' of type 1 |- 1;
 *               if 'dag[len]' represents a Simplicity expression with primitives then 'NULL != env';
 */
static inline bool evalTCOProgram(bool *evalSuccess, const dag_node* dag, type* type_dag, size_t len, const txEnv* env) {
  return evalTCOExpression(evalSuccess, NULL, 0, NULL, 0, dag, type_dag, len, env);
}
#endif
