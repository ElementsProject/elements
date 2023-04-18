#ifndef SIMPLICITY_ELEMENTS_EXEC_H
#define SIMPLICITY_ELEMENTS_EXEC_H

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include "env.h"

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
                                              , const unsigned char* program, size_t program_len);
#endif
