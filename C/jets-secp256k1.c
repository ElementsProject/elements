#include "jets.h"

#include "sha256.h"
#include "secp256k1/secp256k1_impl.h"

static inline void read8s(unsigned char* x, size_t n, frameItem* frame) {
  for(; n; --n) *(x++) = (unsigned char)read8(frame);
}

static inline void write8s(frameItem* frame, const unsigned char* x, size_t n) {
  for(; n; --n) write8(frame, *(x++));
}

/* Read a secp256k1 field element value from the 'src' frame, advancing the cursor 256 cells.
 *
 * Precondition: '*src' is a valid read frame for 256 more cells;
 *               NULL != r;
 */
static inline void read_fe(secp256k1_fe* r, frameItem* src) {
  unsigned char buf[32];

  read8s(buf, 32, src);
  if (!secp256k1_fe_set_b32(r, buf)) secp256k1_fe_normalize(r);
}

/* Write a secp256k1 field element value to the 'dst' frame, advancing the cursor 256 cells.
 * The field value 'r' is normalized as a side-effect.
 *
 * Precondition: '*dst' is a valid write frame for 256 more cells;
 *               NULL != r;
 */
static inline void write_fe(frameItem* dst, secp256k1_fe* r) {
  unsigned char buf[32];

  secp256k1_fe_normalize(r);
  secp256k1_fe_get_b32(buf, r);
  write8s(dst, buf, 32);
}

/* Skip 256 cells, the size of a secp256k1 field element value, in the 'dst' frame.
 *
 * Precondition: '*dst' is a valid write frame for 256 more cells;
 */
static inline void skip_fe(frameItem* dst) {
  skipBits(dst, 256);
}

/* Read a (non-infinity) secp256k1 affine group element value from the 'src' frame, advancing the cursor 512 cells.
 *
 * Precondition: '*src' is a valid read frame for 512 more cells;
 *               NULL != r;
 */
static inline void read_ge(secp256k1_ge* r, frameItem* src) {
  read_fe(&r->x, src);
  read_fe(&r->y, src);
  r->infinity = 0;
}

/* Write a secp256k1 affine group element value to the 'dst' frame, advancing the cursor 512 cells.
 *
 * Precondition: '*dst' is a valid write frame for 512 more cells;
 *               NULL != r;
 */
static inline void write_ge(frameItem* dst, secp256k1_ge* r) {
  if (r->infinity) {
    write32s(dst, (uint32_t[16]){0}, 16);
  } else {
    write_fe(dst, &r->x);
    write_fe(dst, &r->y);
  }
}

/* Skip 512 cells, the size of a secp256k1 affine group element value, in the 'dst' frame.
 *
 * Precondition: '*dst' is a valid write frame for 512 more cells;
 */
static inline void skip_ge(frameItem* dst) {
  skip_fe(dst);
  skip_fe(dst);
}

/* Read a secp256k1 jacobian group element value from the 'src' frame, advancing the cursor 768 cells.
 *
 * Precondition: '*src' is a valid read frame for 768 more cells;
 *               NULL != r;
 */
static inline void read_gej(secp256k1_gej* r, frameItem* src) {
  read_fe(&r->x, src);
  read_fe(&r->y, src);
  read_fe(&r->z, src);
  r->infinity = secp256k1_fe_is_zero(&r->z);
}

/* Write a secp256k1 jacobian group element value to the 'dst' frame, advancing the cursor 786 cells.
 * If 'r->infinity' then an fe_zero value to all coordinates in the 'dst' frame.
 * The components of 'r' may be normalized as a side-effect.
 *
 * Precondition: '*dst' is a valid write frame for 768 more cells;
 *               NULL != r;
 */
static inline void write_gej(frameItem* dst, secp256k1_gej* r) {
  write_fe(dst, &r->x);
  write_fe(dst, &r->y);
  write_fe(dst, &r->z);
}

/* Read a secp256k1 scalar element value from the 'src' frame, advancing the cursor 256 cells.
 *
 * Precondition: '*src' is a valid read frame for 256 more cells;
 *               NULL != r;
 */
static inline void read_scalar(secp256k1_scalar* r, frameItem* src) {
  unsigned char buf[32];

  read8s(buf, 32, src);
  secp256k1_scalar_set_b32(r, buf, NULL);
}

/* Write a secp256k1 scalar element value to the 'dst' frame, advancing the cursor 256 cells.
 *
 * Precondition: '*dst' is a valid write frame for 256 more cells;
 *               NULL != r;
 */
static inline void write_scalar(frameItem* dst, const secp256k1_scalar* r) {
  unsigned char buf[32];

  secp256k1_scalar_get_b32(buf, r);
  write8s(dst, buf, 32);
}

bool fe_normalize(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_fe a;
  read_fe(&a, &src);
  write_fe(dst, &a);
  return true;
}

bool fe_negate(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_fe a;
  read_fe(&a, &src);
  secp256k1_fe_negate(&a, &a, 1);
  write_fe(dst, &a);
  return true;
}

bool fe_add(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_fe a, b;
  read_fe(&a, &src);
  read_fe(&b, &src);
  secp256k1_fe_add(&a, &b);
  write_fe(dst, &a);
  return true;
}

bool fe_square(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_fe a;
  read_fe(&a, &src);
  secp256k1_fe_sqr(&a, &a);
  write_fe(dst, &a);
  return true;
}

bool fe_multiply(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_fe a, b;
  read_fe(&a, &src);
  read_fe(&b, &src);
  secp256k1_fe_mul(&a, &a, &b);
  write_fe(dst, &a);
  return true;
}

bool fe_multiply_beta(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  static const secp256k1_fe beta = SECP256K1_FE_CONST(
      0x7ae96a2bul, 0x657c0710ul, 0x6e64479eul, 0xac3434e9ul,
      0x9cf04975ul, 0x12f58995ul, 0xc1396c28ul, 0x719501eeul
  );
  secp256k1_fe a;
  read_fe(&a, &src);
  secp256k1_fe_mul(&a, &a, &beta);
  write_fe(dst, &a);
  return true;
}

bool fe_invert(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_fe a;
  read_fe(&a, &src);
  secp256k1_fe_inv_var(&a, &a);
  write_fe(dst, &a);
  return true;
}

bool fe_square_root(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_fe r, a;
  read_fe(&a, &src);
  int result = secp256k1_fe_sqrt_var(&r, &a);
  if (writeBit(dst, result)) {
    write_fe(dst, &r);
  } else {
    skip_fe(dst);
  }
  return true;
}

bool fe_is_zero(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_fe a;
  read_fe(&a, &src);
  writeBit(dst, secp256k1_fe_is_zero(&a));
  return true;
}

bool fe_is_odd(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_fe a;
  read_fe(&a, &src);
  writeBit(dst, secp256k1_fe_is_odd(&a));
  return true;
}

bool scalar_normalize(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_scalar a;
  read_scalar(&a, &src);
  write_scalar(dst, &a);
  return true;
}

bool scalar_negate(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_scalar a;
  read_scalar(&a, &src);
  secp256k1_scalar_negate(&a, &a);
  write_scalar(dst, &a);
  return true;
}

bool scalar_add(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_scalar a, b;
  read_scalar(&a, &src);
  read_scalar(&b, &src);
  secp256k1_scalar_add(&a, &a, &b);
  write_scalar(dst, &a);
  return true;
}

bool scalar_square(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_scalar a;
  read_scalar(&a, &src);
  secp256k1_scalar_mul(&a, &a, &a);
  write_scalar(dst, &a);
  return true;
}

bool scalar_multiply(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_scalar a, b;
  read_scalar(&a, &src);
  read_scalar(&b, &src);
  secp256k1_scalar_mul(&a, &a, &b);
  write_scalar(dst, &a);
  return true;
}

bool scalar_multiply_lambda(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_scalar a;
  read_scalar(&a, &src);
  secp256k1_scalar_mul(&a, &a, &secp256k1_const_lambda);
  write_scalar(dst, &a);
  return true;
}

bool scalar_invert(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_scalar a;
  read_scalar(&a, &src);
  secp256k1_scalar_inverse_var(&a, &a);
  write_scalar(dst, &a);
  return true;
}

bool scalar_is_zero(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_scalar a;
  read_scalar(&a, &src);
  writeBit(dst, secp256k1_scalar_is_zero(&a));
  return true;
}

bool gej_infinity(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  (void) env; // env is unused;

  secp256k1_gej a;
  secp256k1_gej_set_infinity(&a);
  write_gej(dst, &a);
  return true;
}

bool gej_rescale(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_gej a;
  secp256k1_fe c;
  read_gej(&a, &src);
  read_fe(&c, &src);
  secp256k1_gej_rescale(&a, &c);
  write_gej(dst, &a);
  return true;
}

bool gej_normalize(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_gej a;
  secp256k1_ge r;
  read_gej(&a, &src);
  secp256k1_ge_set_gej_var(&r, &a);
  write_ge(dst, &r);
  return true;
}

bool gej_negate(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_gej a;
  read_gej(&a, &src);
  secp256k1_gej_neg(&a, &a);
  write_gej(dst, &a);
  return true;
}

bool ge_negate(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_ge a;
  read_ge(&a, &src);
  secp256k1_ge_neg(&a, &a);
  write_ge(dst, &a);
  return true;
}

bool gej_double(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  // This r variable can be eliminated once secp256k1_gej_double_var calls set_infinity.
  secp256k1_gej r, a;
  read_gej(&a, &src);
  secp256k1_gej_clear(&r);
  secp256k1_gej_double_var(&r, &a, NULL);
  write_gej(dst, &r);
  return true;
}

bool gej_add(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_gej a, b;
  read_gej(&a, &src);
  read_gej(&b, &src);
  secp256k1_gej_add_var(&a, &a, &b, NULL);
  write_gej(dst, &a);
  return true;
}

bool gej_ge_add_ex(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_gej a;
  secp256k1_ge b;
  secp256k1_fe rzr;
  secp256k1_fe_clear(&rzr);
  read_gej(&a, &src);
  read_ge(&b, &src);
  secp256k1_gej_add_ge_var(&a, &a, &b, &rzr);
  write_fe(dst, &rzr);
  write_gej(dst, &a);
  return true;
}

bool gej_ge_add(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_gej a;
  secp256k1_ge b;
  read_gej(&a, &src);
  read_ge(&b, &src);
  secp256k1_gej_add_ge_var(&a, &a, &b, NULL);
  write_gej(dst, &a);
  return true;
}

bool gej_is_infinity(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_gej a;
  read_gej(&a, &src);
  writeBit(dst, secp256k1_gej_is_infinity(&a));
  return true;
}

bool gej_x_equiv(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_fe x;
  secp256k1_gej a;
  read_fe(&x, &src);
  read_gej(&a, &src);
  writeBit(dst, (!secp256k1_gej_is_infinity(&a)) && secp256k1_gej_eq_x_var(&x, &a));
  return true;
}

bool gej_y_is_odd(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_gej a;
  secp256k1_ge b;
  read_gej(&a, &src);
  if (secp256k1_gej_is_infinity(&a)) {
     writeBit(dst, false);
  } else {
    secp256k1_ge_set_gej_var(&b, &a);
    secp256k1_fe_normalize(&b.y);
    writeBit(dst, secp256k1_fe_is_odd(&b.y));
  }
  return true;
}

bool gej_is_on_curve(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_gej a;
  secp256k1_fe x3, y2, z6;
  read_gej(&a, &src);
  secp256k1_fe_sqr(&y2, &a.y);
  secp256k1_fe_sqr(&x3, &a.x); secp256k1_fe_mul(&x3, &x3, &a.x);
  secp256k1_fe_sqr(&z6, &a.z); secp256k1_fe_mul(&z6, &z6, &a.z); secp256k1_fe_sqr(&z6, &z6);
  secp256k1_fe_mul_int(&z6, 7);
  secp256k1_fe_add(&x3, &z6);
  writeBit(dst, secp256k1_fe_equal_var(&y2, &x3));
  return true;
}

bool ge_is_on_curve(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_ge a;
  read_ge(&a, &src);
  writeBit(dst, secp256k1_ge_is_valid_var(&a));
  return true;
}

bool scale(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_gej r, a;
  secp256k1_scalar na, ng;

  read_scalar(&na, &src);
  read_gej(&a, &src);
  secp256k1_scalar_clear(&ng);
  secp256k1_ecmult(&r, &a, &na, &ng);
  write_gej(dst, &r);
  return true;
}

bool generate(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_gej r, a;
  secp256k1_scalar na, ng;

  secp256k1_scalar_clear(&na);
  secp256k1_gej_set_infinity(&a);
  read_scalar(&ng, &src);
  secp256k1_ecmult(&r, &a, &na, &ng);
  write_gej(dst, &r);
  return true;
}

bool linear_combination_1(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_gej r, a;
  secp256k1_scalar na, ng;

  read_scalar(&na, &src);
  read_gej(&a, &src);
  read_scalar(&ng, &src);
  secp256k1_ecmult(&r, &a, &na, &ng);
  write_gej(dst, &r);
  return true;
}

bool linear_verify_1(frameItem* dst, frameItem src, const txEnv* env) {
  (void) dst; // dst is unused;
  (void) env; // env is unused;

  secp256k1_ge a, b;
  secp256k1_scalar na, ng;

  read_scalar(&na, &src);
  read_ge(&a, &src);
  read_scalar(&ng, &src);
  read_ge(&b, &src);
  if (secp256k1_ge_is_valid_var(&a) &&
      secp256k1_ge_is_valid_var(&b)) {
    secp256k1_gej r, a0;
    secp256k1_gej_set_ge(&a0, &a);
    secp256k1_ge_neg(&b, &b);
    secp256k1_ecmult(&r, &a0, &na, &ng);
    secp256k1_gej_add_ge_var(&r, &r, &b, NULL);
    return secp256k1_gej_is_infinity(&r);
  } else {
    return false;
  }
}

bool decompress(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_fe x;
  secp256k1_ge r;
  bool y = readBit(&src);
  read_fe(&x, &src);
  if (writeBit(dst, secp256k1_ge_set_xo_var(&r, &x, y))) {
    write_ge(dst, &r);
  } else {
    skip_ge(dst);
  }

  return true;
}

bool point_verify_1(frameItem* dst, frameItem src, const txEnv* env) {
  (void) dst; // dst is unused;
  (void) env; // env is unused;

  bool ay, by;
  secp256k1_fe ax, bx;
  secp256k1_ge a, b;
  secp256k1_scalar na, ng;

  read_scalar(&na, &src);
  ay = readBit(&src);
  read_fe(&ax, &src);
  read_scalar(&ng, &src);
  by = readBit(&src);
  read_fe(&bx, &src);
  if (secp256k1_ge_set_xo_var(&a, &ax, ay) &&
      secp256k1_ge_set_xo_var(&b, &bx, by)) {
    secp256k1_gej r, a0;
    secp256k1_gej_set_ge(&a0, &a);
    secp256k1_ge_neg(&b, &b);
    secp256k1_ecmult(&r, &a0, &na, &ng);
    secp256k1_gej_add_ge_var(&r, &r, &b, NULL);
    return secp256k1_gej_is_infinity(&r);
  } else {
    return false;
  }
}

bool bip0340_verify(frameItem* dst, frameItem src, const txEnv* env) {
  (void) dst; // dst is unused;
  (void) env; // env is unused;

  unsigned char buf[64];
  secp256k1_xonly_pubkey pubkey;
  unsigned char msg[32];
  unsigned char sig[64];

  read8s(buf, 32, &src);
  if (!secp256k1_xonly_pubkey_parse(&pubkey, buf)) return false;

  read8s(msg, 32, &src);
  read8s(sig, 64, &src);

  return secp256k1_schnorrsig_verify(sig, msg, &pubkey);
}
