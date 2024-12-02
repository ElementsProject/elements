#ifndef SIMPLICITY_ELEMENTS_EXEC_H
#define SIMPLICITY_ELEMENTS_EXEC_H

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <simplicity/errorCodes.h>
#include <simplicity/elements/env.h>

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
                                              , const unsigned char* witness, size_t witness_len);
#endif
