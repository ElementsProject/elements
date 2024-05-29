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

bool verify(frameItem* dst, frameItem src, const txEnv* env);
bool low_8(frameItem* dst, frameItem src, const txEnv* env);
bool low_16(frameItem* dst, frameItem src, const txEnv* env);
bool low_32(frameItem* dst, frameItem src, const txEnv* env);
bool low_64(frameItem* dst, frameItem src, const txEnv* env);
bool high_8(frameItem* dst, frameItem src, const txEnv* env);
bool high_16(frameItem* dst, frameItem src, const txEnv* env);
bool high_32(frameItem* dst, frameItem src, const txEnv* env);
bool high_64(frameItem* dst, frameItem src, const txEnv* env);
bool complement_8(frameItem* dst, frameItem src, const txEnv* env);
bool complement_16(frameItem* dst, frameItem src, const txEnv* env);
bool complement_32(frameItem* dst, frameItem src, const txEnv* env);
bool complement_64(frameItem* dst, frameItem src, const txEnv* env);
bool and_8(frameItem* dst, frameItem src, const txEnv* env);
bool and_16(frameItem* dst, frameItem src, const txEnv* env);
bool and_32(frameItem* dst, frameItem src, const txEnv* env);
bool and_64(frameItem* dst, frameItem src, const txEnv* env);
bool or_8(frameItem* dst, frameItem src, const txEnv* env);
bool or_16(frameItem* dst, frameItem src, const txEnv* env);
bool or_32(frameItem* dst, frameItem src, const txEnv* env);
bool or_64(frameItem* dst, frameItem src, const txEnv* env);
bool xor_8(frameItem* dst, frameItem src, const txEnv* env);
bool xor_16(frameItem* dst, frameItem src, const txEnv* env);
bool xor_32(frameItem* dst, frameItem src, const txEnv* env);
bool xor_64(frameItem* dst, frameItem src, const txEnv* env);
bool maj_8(frameItem* dst, frameItem src, const txEnv* env);
bool maj_16(frameItem* dst, frameItem src, const txEnv* env);
bool maj_32(frameItem* dst, frameItem src, const txEnv* env);
bool maj_64(frameItem* dst, frameItem src, const txEnv* env);
bool xor_xor_8(frameItem* dst, frameItem src, const txEnv* env);
bool xor_xor_16(frameItem* dst, frameItem src, const txEnv* env);
bool xor_xor_32(frameItem* dst, frameItem src, const txEnv* env);
bool xor_xor_64(frameItem* dst, frameItem src, const txEnv* env);
bool ch_8(frameItem* dst, frameItem src, const txEnv* env);
bool ch_16(frameItem* dst, frameItem src, const txEnv* env);
bool ch_32(frameItem* dst, frameItem src, const txEnv* env);
bool ch_64(frameItem* dst, frameItem src, const txEnv* env);
bool some_8(frameItem* dst, frameItem src, const txEnv* env);
bool some_16(frameItem* dst, frameItem src, const txEnv* env);
bool some_32(frameItem* dst, frameItem src, const txEnv* env);
bool some_64(frameItem* dst, frameItem src, const txEnv* env);
bool all_8(frameItem* dst, frameItem src, const txEnv* env);
bool all_16(frameItem* dst, frameItem src, const txEnv* env);
bool all_32(frameItem* dst, frameItem src, const txEnv* env);
bool all_64(frameItem* dst, frameItem src, const txEnv* env);
bool one_8(frameItem* dst, frameItem src, const txEnv* env);
bool one_16(frameItem* dst, frameItem src, const txEnv* env);
bool one_32(frameItem* dst, frameItem src, const txEnv* env);
bool one_64(frameItem* dst, frameItem src, const txEnv* env);
bool eq_8(frameItem* dst, frameItem src, const txEnv* env);
bool eq_16(frameItem* dst, frameItem src, const txEnv* env);
bool eq_32(frameItem* dst, frameItem src, const txEnv* env);
bool eq_64(frameItem* dst, frameItem src, const txEnv* env);
bool eq_256(frameItem* dst, frameItem src, const txEnv* env);
bool add_8(frameItem* dst, frameItem src, const txEnv* env);
bool add_16(frameItem* dst, frameItem src, const txEnv* env);
bool add_32(frameItem* dst, frameItem src, const txEnv* env);
bool add_64(frameItem* dst, frameItem src, const txEnv* env);
bool full_add_8(frameItem* dst, frameItem src, const txEnv* env);
bool full_add_16(frameItem* dst, frameItem src, const txEnv* env);
bool full_add_32(frameItem* dst, frameItem src, const txEnv* env);
bool full_add_64(frameItem* dst, frameItem src, const txEnv* env);
bool full_increment_8(frameItem* dst, frameItem src, const txEnv* env);
bool full_increment_16(frameItem* dst, frameItem src, const txEnv* env);
bool full_increment_32(frameItem* dst, frameItem src, const txEnv* env);
bool full_increment_64(frameItem* dst, frameItem src, const txEnv* env);
bool increment_8(frameItem* dst, frameItem src, const txEnv* env);
bool increment_16(frameItem* dst, frameItem src, const txEnv* env);
bool increment_32(frameItem* dst, frameItem src, const txEnv* env);
bool increment_64(frameItem* dst, frameItem src, const txEnv* env);
bool subtract_8(frameItem* dst, frameItem src, const txEnv* env);
bool subtract_16(frameItem* dst, frameItem src, const txEnv* env);
bool subtract_32(frameItem* dst, frameItem src, const txEnv* env);
bool subtract_64(frameItem* dst, frameItem src, const txEnv* env);
bool negate_8(frameItem* dst, frameItem src, const txEnv* env);
bool negate_16(frameItem* dst, frameItem src, const txEnv* env);
bool negate_32(frameItem* dst, frameItem src, const txEnv* env);
bool negate_64(frameItem* dst, frameItem src, const txEnv* env);
bool full_decrement_8(frameItem* dst, frameItem src, const txEnv* env);
bool full_decrement_16(frameItem* dst, frameItem src, const txEnv* env);
bool full_decrement_32(frameItem* dst, frameItem src, const txEnv* env);
bool full_decrement_64(frameItem* dst, frameItem src, const txEnv* env);
bool decrement_8(frameItem* dst, frameItem src, const txEnv* env);
bool decrement_16(frameItem* dst, frameItem src, const txEnv* env);
bool decrement_32(frameItem* dst, frameItem src, const txEnv* env);
bool decrement_64(frameItem* dst, frameItem src, const txEnv* env);
bool full_subtract_8(frameItem* dst, frameItem src, const txEnv* env);
bool full_subtract_16(frameItem* dst, frameItem src, const txEnv* env);
bool full_subtract_32(frameItem* dst, frameItem src, const txEnv* env);
bool full_subtract_64(frameItem* dst, frameItem src, const txEnv* env);
bool multiply_8(frameItem* dst, frameItem src, const txEnv* env);
bool multiply_16(frameItem* dst, frameItem src, const txEnv* env);
bool multiply_32(frameItem* dst, frameItem src, const txEnv* env);
bool multiply_64(frameItem* dst, frameItem src, const txEnv* env);
bool full_multiply_8(frameItem* dst, frameItem src, const txEnv* env);
bool full_multiply_16(frameItem* dst, frameItem src, const txEnv* env);
bool full_multiply_32(frameItem* dst, frameItem src, const txEnv* env);
bool full_multiply_64(frameItem* dst, frameItem src, const txEnv* env);
bool is_zero_8(frameItem* dst, frameItem src, const txEnv* env);
bool is_zero_16(frameItem* dst, frameItem src, const txEnv* env);
bool is_zero_32(frameItem* dst, frameItem src, const txEnv* env);
bool is_zero_64(frameItem* dst, frameItem src, const txEnv* env);
bool is_one_8(frameItem* dst, frameItem src, const txEnv* env);
bool is_one_16(frameItem* dst, frameItem src, const txEnv* env);
bool is_one_32(frameItem* dst, frameItem src, const txEnv* env);
bool is_one_64(frameItem* dst, frameItem src, const txEnv* env);
bool le_8(frameItem* dst, frameItem src, const txEnv* env);
bool le_16(frameItem* dst, frameItem src, const txEnv* env);
bool le_32(frameItem* dst, frameItem src, const txEnv* env);
bool le_64(frameItem* dst, frameItem src, const txEnv* env);
bool lt_8(frameItem* dst, frameItem src, const txEnv* env);
bool lt_16(frameItem* dst, frameItem src, const txEnv* env);
bool lt_32(frameItem* dst, frameItem src, const txEnv* env);
bool lt_64(frameItem* dst, frameItem src, const txEnv* env);
bool min_8(frameItem* dst, frameItem src, const txEnv* env);
bool min_16(frameItem* dst, frameItem src, const txEnv* env);
bool min_32(frameItem* dst, frameItem src, const txEnv* env);
bool min_64(frameItem* dst, frameItem src, const txEnv* env);
bool max_8(frameItem* dst, frameItem src, const txEnv* env);
bool max_16(frameItem* dst, frameItem src, const txEnv* env);
bool max_32(frameItem* dst, frameItem src, const txEnv* env);
bool max_64(frameItem* dst, frameItem src, const txEnv* env);
bool median_8(frameItem* dst, frameItem src, const txEnv* env);
bool median_16(frameItem* dst, frameItem src, const txEnv* env);
bool median_32(frameItem* dst, frameItem src, const txEnv* env);
bool median_64(frameItem* dst, frameItem src, const txEnv* env);
bool div_mod_8(frameItem* dst, frameItem src, const txEnv* env);
bool div_mod_16(frameItem* dst, frameItem src, const txEnv* env);
bool div_mod_32(frameItem* dst, frameItem src, const txEnv* env);
bool div_mod_64(frameItem* dst, frameItem src, const txEnv* env);
bool divide_8(frameItem* dst, frameItem src, const txEnv* env);
bool divide_16(frameItem* dst, frameItem src, const txEnv* env);
bool divide_32(frameItem* dst, frameItem src, const txEnv* env);
bool divide_64(frameItem* dst, frameItem src, const txEnv* env);
bool modulo_8(frameItem* dst, frameItem src, const txEnv* env);
bool modulo_16(frameItem* dst, frameItem src, const txEnv* env);
bool modulo_32(frameItem* dst, frameItem src, const txEnv* env);
bool modulo_64(frameItem* dst, frameItem src, const txEnv* env);
bool divides_8(frameItem* dst, frameItem src, const txEnv* env);
bool divides_16(frameItem* dst, frameItem src, const txEnv* env);
bool divides_32(frameItem* dst, frameItem src, const txEnv* env);
bool divides_64(frameItem* dst, frameItem src, const txEnv* env);

bool sha_256_iv(frameItem* dst, frameItem src, const txEnv* env);
bool sha_256_block(frameItem* dst, frameItem src, const txEnv* env);
bool sha_256_ctx_8_init(frameItem* dst, frameItem src, const txEnv* env);
bool sha_256_ctx_8_add_1(frameItem* dst, frameItem src, const txEnv* env);
bool sha_256_ctx_8_add_2(frameItem* dst, frameItem src, const txEnv* env);
bool sha_256_ctx_8_add_4(frameItem* dst, frameItem src, const txEnv* env);
bool sha_256_ctx_8_add_8(frameItem* dst, frameItem src, const txEnv* env);
bool sha_256_ctx_8_add_16(frameItem* dst, frameItem src, const txEnv* env);
bool sha_256_ctx_8_add_32(frameItem* dst, frameItem src, const txEnv* env);
bool sha_256_ctx_8_add_64(frameItem* dst, frameItem src, const txEnv* env);
bool sha_256_ctx_8_add_128(frameItem* dst, frameItem src, const txEnv* env);
bool sha_256_ctx_8_add_256(frameItem* dst, frameItem src, const txEnv* env);
bool sha_256_ctx_8_add_512(frameItem* dst, frameItem src, const txEnv* env);
bool sha_256_ctx_8_add_buffer_511(frameItem* dst, frameItem src, const txEnv* env);
bool sha_256_ctx_8_finalize(frameItem* dst, frameItem src, const txEnv* env);

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

bool check_sig_verify(frameItem* dst, frameItem src, const txEnv* env);
bool bip_0340_verify(frameItem* dst, frameItem src, const txEnv* env);

bool parse_lock(frameItem* dst, frameItem src, const txEnv* env);
bool parse_sequence(frameItem* dst, frameItem src, const txEnv* env);

#endif
