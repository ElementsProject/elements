/* This module defines jets that simulate various Simplicity expressions.
 * Their specifications are given by the specific Simplicity expressions they are simulating.
 */
#ifndef SIMPLICITY_JETS_H
#define SIMPLICITY_JETS_H

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

bool add_32(frameItem* dst, frameItem src, const txEnv* env);
bool full_add_32(frameItem* dst, frameItem src, const txEnv* env);
bool subtract_32(frameItem* dst, frameItem src, const txEnv* env);
bool full_subtract_32(frameItem* dst, frameItem src, const txEnv* env);
bool multiply_32(frameItem* dst, frameItem src, const txEnv* env);
bool full_multiply_32(frameItem* dst, frameItem src, const txEnv* env);

bool sha_256_block(frameItem* dst, frameItem src, const txEnv* env);

bool fe_normalize(frameItem* dst, frameItem src, const txEnv* env);
bool fe_negate(frameItem* dst, frameItem src, const txEnv* env);
bool fe_add(frameItem* dst, frameItem src, const txEnv* env);
bool fe_square(frameItem* dst, frameItem src, const txEnv* env);
bool fe_multiply(frameItem* dst, frameItem src, const txEnv* env);
bool fe_multiply_beta(frameItem* dst, frameItem src, const txEnv* env);
bool fe_invert(frameItem* dst, frameItem src, const txEnv* env);
bool fe_square_root(frameItem* dst, frameItem src, const txEnv* env);
bool fe_is_zero(frameItem* dst, frameItem src, const txEnv* env);
bool fe_is_odd(frameItem* dst, frameItem src, const txEnv* env);
bool scalar_normalize(frameItem* dst, frameItem src, const txEnv* env);
bool scalar_negate(frameItem* dst, frameItem src, const txEnv* env);
bool scalar_add(frameItem* dst, frameItem src, const txEnv* env);
bool scalar_square(frameItem* dst, frameItem src, const txEnv* env);
bool scalar_multiply(frameItem* dst, frameItem src, const txEnv* env);
bool scalar_multiply_lambda(frameItem* dst, frameItem src, const txEnv* env);
bool scalar_invert(frameItem* dst, frameItem src, const txEnv* env);
bool scalar_is_zero(frameItem* dst, frameItem src, const txEnv* env);
bool gej_infinity(frameItem* dst, frameItem src, const txEnv* env);
bool gej_rescale(frameItem* dst, frameItem src, const txEnv* env);
bool gej_normalize(frameItem* dst, frameItem src, const txEnv* env);
bool gej_negate(frameItem* dst, frameItem src, const txEnv* env);
bool ge_negate(frameItem* dst, frameItem src, const txEnv* env);
bool gej_double(frameItem* dst, frameItem src, const txEnv* env);
bool gej_add(frameItem* dst, frameItem src, const txEnv* env);
bool gej_ge_add_ex(frameItem* dst, frameItem src, const txEnv* env);
bool gej_ge_add(frameItem* dst, frameItem src, const txEnv* env);
bool gej_is_infinity(frameItem* dst, frameItem src, const txEnv* env);
bool gej_x_equiv(frameItem* dst, frameItem src, const txEnv* env);
bool gej_y_is_odd(frameItem* dst, frameItem src, const txEnv* env);
bool gej_is_on_curve(frameItem* dst, frameItem src, const txEnv* env);
bool ge_is_on_curve(frameItem* dst, frameItem src, const txEnv* env);
bool scale(frameItem* dst, frameItem src, const txEnv* env);
bool generate(frameItem* dst, frameItem src, const txEnv* env);
bool linear_combination_1(frameItem* dst, frameItem src, const txEnv* env);
bool linear_verify_1(frameItem* dst, frameItem src, const txEnv* env);
bool decompress(frameItem* dst, frameItem src, const txEnv* env);
bool point_verify_1(frameItem* dst, frameItem src, const txEnv* env);
bool bip0340_verify(frameItem* dst, frameItem src, const txEnv* env);

#endif
