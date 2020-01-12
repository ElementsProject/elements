#include "jets.h"

#include "sha256.h"
#include "secp256k1/secp256k1_impl.h"

/* Copy an array of 'uint32_t's into an array of 'unsigned char' by transforming each 32 bit values into four 8-bit values
 * written in big endian order.
 *
 * Precondition: unsigned char out[4*len];
 *               uint32_t in[len]
 */
static inline void unpack32s(unsigned char* out, const uint32_t* in, size_t len) {
  while (len) {
    WriteBE32(out, *in);
    out += 4;
    ++in;
    --len;
  }
}

/* Read a secp256k1 10x32 field element value from the 'src' frame, advancing the cursor 320 cells.
 *
 * Precondition: '*src' is a valid read frame for 320 more cells;
 *               NULL != r;
 */
static inline void read_fe(secp256k1_fe* r, frameItem* src) {
  read32s(r->n, 10, src);
}

/* Write a secp256k1 10x32 field element value to the 'dst' frame, advancing the cursor 320 cells.
 *
 * Precondition: '*dst' is a valid write frame for 320 more cells;
 *               NULL != r;
 */
static inline void write_fe(frameItem* dst, const secp256k1_fe* r) {
  write32s(dst, r->n, 10);
}

/* Skip 320 cells, the size of a secp256k1 10x32 field element value, in the 'dst' frame.
 *
 * Precondition: '*dst' is a valid write frame for 320 more cells;
 */
static inline void skip_fe(frameItem* dst) {
  skipBits(dst, 32*10);
}

/* Read a (non-infinity) secp256k1 affine group element value from the 'src' frame, advancing the cursor 640 cells.
 *
 * Precondition: '*src' is a valid read frame for 640 more cells;
 *               NULL != r;
 */
static inline void read_ge(secp256k1_ge* r, frameItem* src) {
  read_fe(&r->x, src);
  read_fe(&r->y, src);
  r->infinity = 0;
}

/* Read a secp256k1 jacobian group element value from the 'src' frame, advancing the cursor 960 cells.
 *
 * Precondition: '*src' is a valid read frame for 960 more cells;
 *               NULL != r;
 */
static inline void read_gej(secp256k1_gej* r, frameItem* src) {
  read_fe(&r->x, src);
  read_fe(&r->y, src);
  read_fe(&r->z, src);
  r->infinity = secp256k1_fe_is_zero(&r->z);
}

/* Write a secp256k1 jacobian group element value to the 'dst' frame, advancing the cursor 960 cells.
 * If 'r->infinity' then we write an fe_zero value to the 'z' coordinate in the 'dst' frame instead of 'r->z'.
 *
 * Precondition: '*dst' is a valid write frame for 960 more cells;
 *               NULL != r;
 */
static inline void write_gej(frameItem* dst, const secp256k1_gej* r) {
  write_fe(dst, &r->x);
  write_fe(dst, &r->y);
  if (r->infinity) {
    write32s(dst, (uint32_t[10]){0}, 10);
  } else {
    write_fe(dst, &r->z);
  }
}

/* Read a secp256k1 scalar element value from the 'src' frame, advancing the cursor 256 cells.
 * The secp256k1 8x32 scalar representation puts the 32 least significant bytes into the first array element;
 * However Simplicity uses a standard big-endian 256-bit word to represent scalar values.
 * Thus it is necessary to fill the secp256k1 scalar array in reverse order.
 *
 * Precondition: '*src' is a valid read frame for 256 more cells;
 *               NULL != r;
 */
static inline void read_scalar(secp256k1_scalar* r, frameItem* src) {
  r->d[7] = (uint32_t)read32(src);
  r->d[6] = (uint32_t)read32(src);
  r->d[5] = (uint32_t)read32(src);
  r->d[4] = (uint32_t)read32(src);
  r->d[3] = (uint32_t)read32(src);
  r->d[2] = (uint32_t)read32(src);
  r->d[1] = (uint32_t)read32(src);
  r->d[0] = (uint32_t)read32(src);
}

/* Write a secp256k1 scalar element value to the 'dst' frame, advancing the cursor 256 cells.
 * The secp256k1 8x32 scalar representation puts the 32 least significant bytes into the first array element;
 * However Simplicity uses a standard big-endian 256-bit word to represent scalar values.
 * Thus it is necessary to read from the secp256k1 scalar array in reverse order.
 *
 * Precondition: '*dst' is a valid write frame for 256 more cells;
 *               NULL != r;
 */
static inline void write_scalar(frameItem* dst, const secp256k1_scalar* r) {
  write32(dst, r->d[7]);
  write32(dst, r->d[6]);
  write32(dst, r->d[5]);
  write32(dst, r->d[4]);
  write32(dst, r->d[3]);
  write32(dst, r->d[2]);
  write32(dst, r->d[1]);
  write32(dst, r->d[0]);
}

bool fe_sqrt(frameItem* dst, frameItem src, const txEnv* env) {
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

bool offsetPoint(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_gej r, a;
  secp256k1_ge b;
  secp256k1_fe rzr;
  read_gej(&a, &src);
  read_ge(&b, &src);
  secp256k1_gej_add_ge_var(&r, &a, &b, &rzr);
  write_fe(dst, &rzr);
  write_gej(dst, &r);
  return true;
}

static struct {
   secp256k1_ecmult_context ctx;
   char alloc[SECP256K1_ECMULT_CONTEXT_PREALLOCATED_SIZE];
   bool initialized;
} ecmult_static;

/* This function will initialize the 'ecmult_static' global variable if it hasn't already been initialized. */
static void ensure_ecmult_static(void) {
  if (!ecmult_static.initialized) {
    void *prealloc = ecmult_static.alloc;
    secp256k1_ecmult_context_init(&ecmult_static.ctx);
    secp256k1_ecmult_context_build(&ecmult_static.ctx, &prealloc);
    ecmult_static.initialized = secp256k1_ecmult_context_is_built(&ecmult_static.ctx);
  }
  assert(ecmult_static.initialized);
}

bool ecmult(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;

  secp256k1_gej r, a;
  secp256k1_scalar na, ng;

  ensure_ecmult_static();
  read_gej(&a, &src);
  read_scalar(&na, &src);
  read_scalar(&ng, &src);
  secp256k1_ecmult(&ecmult_static.ctx, &r, &a, &na, &ng);

  /* This jet's implementation of ecmult is defined to always outputs the jacobian coordinate (1, 1, 0)
   * if the result is the point at infinity.
   */
  if (r.infinity) {
    secp256k1_fe_set_int(&r.x, 1);
    secp256k1_fe_set_int(&r.y, 1);
  }
  write_gej(dst, &r);
  return true;
}

bool schnorrAssert(frameItem* dst, frameItem src, const txEnv* env) {
  (void) dst; // dst is unused;
  (void) env; // env is unused;

  uint32_t buf[16];
  unsigned char buf_char[64];
  secp256k1_xonly_pubkey pubkey;
  unsigned char msg[32];
  secp256k1_schnorrsig sig;

  ensure_ecmult_static();
  read32s(buf, 8, &src);
  unpack32s(buf_char, buf, 8);
  if (!secp256k1_xonly_pubkey_parse(&pubkey, buf_char)) return false;

  read32s(buf, 8, &src);
  unpack32s(msg, buf, 8);

  read32s(buf, 16, &src);
  unpack32s(buf_char, buf, 16);
  secp256k1_schnorrsig_parse(&sig, buf_char);

  return secp256k1_schnorrsig_verify(&ecmult_static.ctx, &sig, msg, &pubkey);
}
