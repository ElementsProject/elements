/* This module defines jets that simulate various Simplicity expressions.
 * Their specifications are given by the specific Simplicity expressions they are simulating.
 * The witness Merkle roots for each jet's corresponding Simplicity expression is given in 'jetTable.gperf'.
 * See also 'jetTable.h'.
 */
#ifndef JETS_H
#define JETS_H

#include "frame.h"

/* Forward declaration of the structure holding the environment in which a Simplicity expression is evaluated within. */
typedef struct txEnv txEnv;

/* A jet simulates the execution of some Simplicity expression (without witnesses or delegation) of A |- B.
 * It reads data from a read frame 'src', and writes its output to a write frame 'dst'.
 * If successful then 'true' is returned.
 * If the expression being simulated would fail an 'ASSERTL' or 'ASSERTR' combinator, then 'false' is returned.
 * Cells in front of 'dst's cursor's final position may be overwritten.
 *
 * Precondition: 'src' is a valid read frame for 'bitSize(A)' more cells;
 *               '*dst' is a valid write frame for 'bitSize(B)' more cells;
 *               if the jet simulates a Simplicity expression with primitives then 'NULL != env';
 */
typedef bool (*jet_ptr)(frameItem* dst, frameItem src, const txEnv* env);

bool adder32(frameItem* dst, frameItem src, const txEnv* env);
bool fullAdder32(frameItem* dst, frameItem src, const txEnv* env);
bool subtractor32(frameItem* dst, frameItem src, const txEnv* env);
bool fullSubtractor32(frameItem* dst, frameItem src, const txEnv* env);
bool multiplier32(frameItem* dst, frameItem src, const txEnv* env);
bool fullMultiplier32(frameItem* dst, frameItem src, const txEnv* env);
bool sha256_hashBlock(frameItem* dst, frameItem src, const txEnv* env);

bool fe_sqrt(frameItem* dst, frameItem src, const txEnv* env);
bool offsetPoint(frameItem* dst, frameItem src, const txEnv* env);
bool ecmult(frameItem* dst, frameItem src, const txEnv* env);
bool schnorrAssert(frameItem* dst, frameItem src, const txEnv* env);

#endif
