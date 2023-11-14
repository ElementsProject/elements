#include "jets.h"
#include "secp256k1/secp256k1.h"
#include "secp256k1/util.h"
#ifdef SECP256K1_WIDEMUL_INT128
# include "secp256k1/int128.h"
# include "secp256k1/int128_impl.h"
#else
# include "secp256k1/int128_struct.h"
# include "secp256k1/int128_struct_impl.h"
#endif

static void write128(frameItem* frame, const secp256k1_uint128* x) {
  write64(frame, secp256k1_u128_hi_u64(x));
  write64(frame, secp256k1_u128_to_u64(x));
}

/* verify : TWO |- ONE */
bool verify(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  (void) dst; /* dst is unused. */
  return readBit(&src);
}

#define LOW_(bits)                                                 \
/* low_n : ONE |- TWO^n */                                         \
bool low_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                 \
  (void) src; /* src is unused. */                                 \
  write##bits(dst, 0);                                             \
  return true;                                                     \
}
LOW_(8)
LOW_(16)
LOW_(32)
LOW_(64)

#define HIGH_(bits)                                                 \
/* high_n : ONE |- TWO^n */                                         \
bool high_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                  \
  (void) src; /* src is unused. */                                  \
  write##bits(dst, UINT##bits##_MAX);                               \
  return true;                                                      \
}
HIGH_(8)
HIGH_(16)
HIGH_(32)
HIGH_(64)

#define COMPLEMENT_(bits)                                                 \
/* complement_n : TWO^n |- TWO^n */                                       \
bool complement_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                        \
  uint_fast##bits##_t x = read##bits(&src);                               \
  write##bits(dst, ~(1U*x));                                              \
  return true;                                                            \
}
COMPLEMENT_(8)
COMPLEMENT_(16)
COMPLEMENT_(32)
COMPLEMENT_(64)

#define AND_(bits)                                                 \
/* and_n : TWO^n * TWO^n |- TWO^n */                               \
bool and_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                 \
  uint_fast##bits##_t x = read##bits(&src);                        \
  uint_fast##bits##_t y = read##bits(&src);                        \
  write##bits(dst, x & y);                                         \
  return true;                                                     \
}
AND_(8)
AND_(16)
AND_(32)
AND_(64)

#define OR_(bits)                                                 \
/* or_n : TWO^n * TWO^n |- TWO^n */                               \
bool or_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                \
  uint_fast##bits##_t x = read##bits(&src);                       \
  uint_fast##bits##_t y = read##bits(&src);                       \
  write##bits(dst, x | y);                                        \
  return true;                                                    \
}
OR_(8)
OR_(16)
OR_(32)
OR_(64)

#define XOR_(bits)                                                 \
/* xor_n : TWO^n * TWO^n |- TWO^n */                               \
bool xor_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                 \
  uint_fast##bits##_t x = read##bits(&src);                        \
  uint_fast##bits##_t y = read##bits(&src);                        \
  write##bits(dst, x ^ y);                                         \
  return true;                                                     \
}
XOR_(8)
XOR_(16)
XOR_(32)
XOR_(64)

#define MAJ_(bits)                                                 \
/* maj_n : TWO^n * TWO^n * TWO^n |- TWO^n */                       \
bool maj_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                 \
  uint_fast##bits##_t x = read##bits(&src);                        \
  uint_fast##bits##_t y = read##bits(&src);                        \
  uint_fast##bits##_t z = read##bits(&src);                        \
  write##bits(dst, (x&y) | (y&z) | (z&x));                         \
  return true;                                                     \
}
MAJ_(8)
MAJ_(16)
MAJ_(32)
MAJ_(64)

#define XOR_XOR_(bits)                                                 \
/* xor_xor_n : TWO^n * TWO^n * TWO^n |- TWO^n */                       \
bool xor_xor_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                     \
  uint_fast##bits##_t x = read##bits(&src);                            \
  uint_fast##bits##_t y = read##bits(&src);                            \
  uint_fast##bits##_t z = read##bits(&src);                            \
  write##bits(dst, x ^ y ^ z);                                         \
  return true;                                                         \
}
XOR_XOR_(8)
XOR_XOR_(16)
XOR_XOR_(32)
XOR_XOR_(64)

#define CH_(bits)                                                 \
/* ch_n : TWO^n * TWO^n * TWO^n |- TWO^n */                       \
bool ch_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                \
  uint_fast##bits##_t x = read##bits(&src);                       \
  uint_fast##bits##_t y = read##bits(&src);                       \
  uint_fast##bits##_t z = read##bits(&src);                       \
  write##bits(dst, ((x&y) | ((~(1U*x))&z)));                      \
  return true;                                                    \
}
CH_(8)
CH_(16)
CH_(32)
CH_(64)

#define SOME_(bits)                                                 \
/* some_n : TWO^n |- TWO */                                         \
bool some_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                  \
  uint_fast##bits##_t x = read##bits(&src);                         \
  writeBit(dst, x != 0);                                            \
  return true;                                                      \
}
SOME_(8)
SOME_(16)
SOME_(32)
SOME_(64)

#define ALL_(bits)                                                 \
/* all_n : TWO^n |- TWO */                                         \
bool all_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                 \
  uint_fast##bits##_t x = read##bits(&src);                        \
  writeBit(dst, x == UINT##bits##_MAX);                            \
  return true;                                                     \
}
ALL_(8)
ALL_(16)
ALL_(32)
ALL_(64)

#define ONE_(bits)                                                 \
/* one_n : ONE |- TWO^n */                                         \
bool one_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                 \
  (void) src; /* src is unused. */                                 \
  write##bits(dst, 1);                                             \
  return true;                                                     \
}
ONE_(8)
ONE_(16)
ONE_(32)
ONE_(64)

#define EQ_(bits)                                                 \
/* eq_n : TWO^n * TWO^n |- TWO */                                 \
bool eq_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                \
  uint_fast##bits##_t x = read##bits(&src);                       \
  uint_fast##bits##_t y = read##bits(&src);                       \
  writeBit(dst, x == y);                                          \
  return true;                                                    \
}
EQ_(8)
EQ_(16)
EQ_(32)
EQ_(64)

/* eq_256 : TWO^256 * TWO^256 |- TWO */
bool eq_256(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  uint32_t arr[16];
  read32s(arr, 16, &src);
  for (int i = 0; i < 8; ++i) {
    if (arr[i] != arr[i+8]) {
      writeBit(dst, false);
      return true;
    }
  }
  writeBit(dst, true);
  return true;
}

#define ADD_(bits)                                                 \
/* add_n : TWO^n * TWO^n |- TWO * TWO^n */                         \
bool add_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                 \
  uint_fast##bits##_t x = read##bits(&src);                        \
  uint_fast##bits##_t y = read##bits(&src);                        \
  writeBit(dst, 1U * UINT##bits##_MAX - y < x);                    \
  write##bits(dst, (uint_fast##bits##_t)(1U * x + y));             \
  return true;                                                     \
}
ADD_(8)
ADD_(16)
ADD_(32)
ADD_(64)

#define FULL_ADD_(bits)                                                                   \
/* full_add_n : TWO * TWO^n * TWO^n |- TWO * TWO^n */                                     \
bool full_add_##bits(frameItem* dst, frameItem src, const txEnv* env) {                   \
  (void) env; /* env is unused. */                                                        \
  bool z = readBit(&src);                                                                 \
  uint_fast##bits##_t x = read##bits(&src);                                               \
  uint_fast##bits##_t y = read##bits(&src);                                               \
  writeBit(dst, 1U * UINT##bits##_MAX - y < x || 1U * UINT##bits##_MAX - z < 1U * x + y); \
  write##bits(dst, (uint_fast##bits##_t)(1U * x + y + z));                                \
  return true;                                                                            \
}
FULL_ADD_(8)
FULL_ADD_(16)
FULL_ADD_(32)
FULL_ADD_(64)

#define FULL_INCREMENT_(bits)                                                 \
/* full_increment_n : TWO * TWO^n |- TWO * TWO^n */                           \
bool full_increment_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                            \
  bool z = readBit(&src);                                                     \
  uint_fast##bits##_t x = read##bits(&src);                                   \
  writeBit(dst, 1U * UINT##bits##_MAX - z < x);                               \
  write##bits(dst, (uint_fast##bits##_t)(1U * x + z));                        \
  return true;                                                                \
}
FULL_INCREMENT_(8)
FULL_INCREMENT_(16)
FULL_INCREMENT_(32)
FULL_INCREMENT_(64)

#define INCREMENT_(bits)                                                 \
/* increment_n : TWO^n |- TWO * TWO^n */                                 \
bool increment_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                       \
  uint_fast##bits##_t x = read##bits(&src);                              \
  writeBit(dst, 1U * UINT##bits##_MAX - 1 < x);                          \
  write##bits(dst, (uint_fast##bits##_t)(1U * x + 1));                   \
  return true;                                                           \
}
INCREMENT_(8)
INCREMENT_(16)
INCREMENT_(32)
INCREMENT_(64)

#define SUBTRACT_(bits)                                                 \
/* subtract_n : TWO^n * TWO^n |- TWO * TWO^n */                         \
bool subtract_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                      \
  uint_fast##bits##_t x = read##bits(&src);                             \
  uint_fast##bits##_t y = read##bits(&src);                             \
  writeBit(dst, x < y);                                                 \
  write##bits(dst, (uint_fast##bits##_t)(1U * x - y));                  \
  return true;                                                          \
}
SUBTRACT_(8)
SUBTRACT_(16)
SUBTRACT_(32)
SUBTRACT_(64)

#define NEGATE_(bits)                                                 \
/* negate_n : TWO^n |- TWO * TWO^n */                                 \
bool negate_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                    \
  uint_fast##bits##_t x = read##bits(&src);                           \
  writeBit(dst, x != 0);                                              \
  write##bits(dst, (uint_fast##bits##_t)(- (1U * x)));                \
  return true;                                                        \
}
NEGATE_(8)
NEGATE_(16)
NEGATE_(32)
NEGATE_(64)

#define FULL_DECREMENT_(bits)                                                 \
/* full_decrement_n : TWO * TWO^n |- TWO * TWO^n */                           \
bool full_decrement_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                            \
  bool z = readBit(&src);                                                     \
  uint_fast##bits##_t x = read##bits(&src);                                   \
  writeBit(dst, x < z);                                                       \
  write##bits(dst, (uint_fast##bits##_t)(1U * x - z));                        \
  return true;                                                                \
}
FULL_DECREMENT_(8)
FULL_DECREMENT_(16)
FULL_DECREMENT_(32)
FULL_DECREMENT_(64)

#define DECREMENT_(bits)                                                 \
/* decrement_n : TWO^n |- TWO * TWO^n */                                 \
bool decrement_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                       \
  uint_fast##bits##_t x = read##bits(&src);                              \
  writeBit(dst, x < 1);                                                  \
  write##bits(dst, (uint_fast##bits##_t)(1U * x - 1));                   \
  return true;                                                           \
}
DECREMENT_(8)
DECREMENT_(16)
DECREMENT_(32)
DECREMENT_(64)

#define FULL_SUBTRACT_(bits)                                                 \
/* full_subtract_n : TWO * TWO^n * TWO^n |- TWO * TWO^n */                   \
bool full_subtract_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                           \
  bool z = readBit(&src);                                                    \
  uint_fast##bits##_t x = read##bits(&src);                                  \
  uint_fast##bits##_t y = read##bits(&src);                                  \
  writeBit(dst, x < y || 1U * x - y < z);                                    \
  write##bits(dst, (uint_fast##bits##_t)(1U * x - y - z));                   \
  return true;                                                               \
}
FULL_SUBTRACT_(8)
FULL_SUBTRACT_(16)
FULL_SUBTRACT_(32)
FULL_SUBTRACT_(64)

#define MULTIPLY_(bits,bitsx2)                                          \
bool multiply_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                      \
  uint_fast##bitsx2##_t x = read##bits(&src);                           \
  uint_fast##bitsx2##_t y = read##bits(&src);                           \
  write##bitsx2(dst, x * y);                                            \
  return true;                                                          \
}
MULTIPLY_(8, 16)
MULTIPLY_(16, 32)
MULTIPLY_(32, 64)

bool multiply_64(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  uint_fast64_t x = read64(&src);
  uint_fast64_t y = read64(&src);
  secp256k1_uint128 r;
  secp256k1_u128_mul(&r, x, y);
  write128(dst, &r);
  return true;
}

#define FULL_MULTIPLY_(bits,bitsx2)                                          \
bool full_multiply_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                           \
  uint_fast##bitsx2##_t x = read##bits(&src);                                \
  uint_fast##bitsx2##_t y = read##bits(&src);                                \
  uint_fast##bitsx2##_t z = read##bits(&src);                                \
  uint_fast##bitsx2##_t w = read##bits(&src);                                \
  write##bitsx2(dst, x * y + z + w);                                         \
  return true;                                                               \
}
FULL_MULTIPLY_(8, 16)
FULL_MULTIPLY_(16, 32)
FULL_MULTIPLY_(32, 64)

bool full_multiply_64(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  uint_fast64_t x = read64(&src);
  uint_fast64_t y = read64(&src);
  uint_fast64_t z = read64(&src);
  uint_fast64_t w = read64(&src);
  secp256k1_uint128 r;
  secp256k1_u128_mul(&r, x, y);
  secp256k1_u128_accum_u64(&r, z);
  secp256k1_u128_accum_u64(&r, w);
  write128(dst, &r);
  return true;
}

#define IS_ZERO_(bits)                                                 \
/* is_zero_n : TWO^n |- TWO */                                         \
bool is_zero_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                     \
  uint_fast##bits##_t x = read##bits(&src);                            \
  writeBit(dst, x == 0);                                               \
  return true;                                                         \
}
IS_ZERO_(8)
IS_ZERO_(16)
IS_ZERO_(32)
IS_ZERO_(64)

#define IS_ONE_(bits)                                                 \
/* is_one_n : TWO^n |- TWO */                                         \
bool is_one_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                    \
  uint_fast##bits##_t x = read##bits(&src);                           \
  writeBit(dst, x == 1);                                              \
  return true;                                                        \
}
IS_ONE_(8)
IS_ONE_(16)
IS_ONE_(32)
IS_ONE_(64)

#define LE_(bits)                                                 \
/* le_n : TWO^n * TWO^n |- TWO */                                 \
bool le_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                \
  uint_fast##bits##_t x = read##bits(&src);                       \
  uint_fast##bits##_t y = read##bits(&src);                       \
  writeBit(dst, x <= y);                                          \
  return true;                                                    \
}
LE_(8)
LE_(16)
LE_(32)
LE_(64)

#define LT_(bits)                                                     \
/* lt_n : TWO^n * TWO^n |- TWO */                                     \
bool lt_##bits(frameItem* dst, frameItem src, const txEnv* env) {     \
  (void) env; /* env is unused. */                                    \
  uint_fast##bits##_t x = read##bits(&src);                           \
  uint_fast##bits##_t y = read##bits(&src);                           \
  writeBit(dst, x < y);                                               \
  return true;                                                        \
}
LT_(8)
LT_(16)
LT_(32)
LT_(64)

#define MIN_(bits)                                                    \
/* min_n : TWO^n * TWO^n |- TWO^n */                                  \
bool min_##bits(frameItem* dst, frameItem src, const txEnv* env) {    \
  (void) env; /* env is unused. */                                    \
  uint_fast##bits##_t x = read##bits(&src);                           \
  uint_fast##bits##_t y = read##bits(&src);                           \
  write##bits(dst, x < y ? x : y);                                    \
  return true;                                                        \
}
MIN_(8)
MIN_(16)
MIN_(32)
MIN_(64)

#define MAX_(bits)                                                    \
/* max_n : TWO^n * TWO^n |- TWO^n */                                  \
bool max_##bits(frameItem* dst, frameItem src, const txEnv* env) {    \
  (void) env; /* env is unused. */                                    \
  uint_fast##bits##_t x = read##bits(&src);                           \
  uint_fast##bits##_t y = read##bits(&src);                           \
  write##bits(dst, x < y ? y : x);                                    \
  return true;                                                        \
}
MAX_(8)
MAX_(16)
MAX_(32)
MAX_(64)

#define MEDIAN_(bits)                                                 \
/* median_n : TWO^n * TWO^n * TWO^n |- TWO^n */                       \
bool median_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
  (void) env; /* env is unused. */                                    \
  uint_fast##bits##_t x = read##bits(&src);                           \
  uint_fast##bits##_t y = read##bits(&src);                           \
  uint_fast##bits##_t z = read##bits(&src);                           \
  write##bits(dst, x < y                                              \
                 ? (y < z ? y : (z < x ? x : z))                      \
                 : (x < z ? x : (z < y ? y : z)));                    \
  return true;                                                        \
}
MEDIAN_(8)
MEDIAN_(16)
MEDIAN_(32)
MEDIAN_(64)

#define DIV_MOD_(bits)                                                  \
  /* div_mod_n : TWO^n * TWO^n |- TWO^n * TWO^n */                      \
  bool div_mod_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
    (void) env; /* env is unused. */                                    \
    uint_fast##bits##_t x = read##bits(&src);                           \
    uint_fast##bits##_t y = read##bits(&src);                           \
    write##bits(dst, 0 == y ? 0 : x / y);                               \
    write##bits(dst, 0 == y ? x : x % y);                               \
    return true;                                                        \
  }
DIV_MOD_(8)
DIV_MOD_(16)
DIV_MOD_(32)
DIV_MOD_(64)

#define DIVIDE_(bits)                                                  \
  /* divide_n : TWO^n * TWO^n |- TWO^n */                      \
  bool divide_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
    (void) env; /* env is unused. */                                    \
    uint_fast##bits##_t x = read##bits(&src);                           \
    uint_fast##bits##_t y = read##bits(&src);                           \
    write##bits(dst, 0 == y ? 0 : x / y);                               \
    return true;                                                        \
  }
DIVIDE_(8)
DIVIDE_(16)
DIVIDE_(32)
DIVIDE_(64)

#define MODULO_(bits)                                                   \
  /* modulo_n : TWO^n * TWO^n |- TWO^n */                               \
  bool modulo_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
    (void) env; /* env is unused. */                                    \
    uint_fast##bits##_t x = read##bits(&src);                           \
    uint_fast##bits##_t y = read##bits(&src);                           \
    write##bits(dst, 0 == y ? x : x % y);                               \
    return true;                                                        \
  }
MODULO_(8)
MODULO_(16)
MODULO_(32)
MODULO_(64)

#define DIVIDES_(bits)                                                   \
  /* divides_n : TWO^n * TWO^n |- TWO */                                 \
  bool divides_##bits(frameItem* dst, frameItem src, const txEnv* env) { \
    (void) env; /* env is unused. */                                     \
    uint_fast##bits##_t x = read##bits(&src);                            \
    uint_fast##bits##_t y = read##bits(&src);                            \
    writeBit(dst, 0 == (0 == x ? y : y % x));                            \
    return true;                                                         \
  }
DIVIDES_(8)
DIVIDES_(16)
DIVIDES_(32)
DIVIDES_(64)

/* sha_256_iv : ONE |- TWO^256 */
bool sha_256_iv(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  (void) src; /* env is unused. */

  uint32_t iv[8];
  sha256_iv(iv);

  write32s(dst, iv, 8);
  return true;
}

/* sha_256_block : TWO^256 * TWO^512 |- TWO^256 */
bool sha_256_block(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  uint32_t h[8];
  uint32_t block[16];
  read32s(h, 8, &src);
  read32s(block, 16, &src);
  sha256_compression(h, block);
  write32s(dst, h, 8);
  return true;
}

/* sha_256_ctx_8_init : ONE |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_init(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  (void) src; /* env is unused. */

  uint32_t iv[8];
  sha256_context ctx = sha256_init(iv);

  return write_sha256_context(dst, &ctx);
}

/* sha_256_ctx_8_add_n : CTX8 * (TWO^8)^n |- CTX8
 * where
 * n is a power of 2 less than or equal to 512
 * and
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
static bool sha_256_ctx_8_add_n(frameItem* dst, frameItem *src, size_t n) {
  simplicity_debug_assert(0 < n && n <= 512 && (n & (n - 1)) == 0);
  sha256_midstate midstate;
  unsigned char buf[512];
  sha256_context ctx = {.output = midstate.s};

  if (!read_sha256_context(&ctx, src)) return false;
  read8s(buf, n, src);
  sha256_uchars(&ctx, buf, n);
  return write_sha256_context(dst, &ctx);
}

/* sha_256_ctx_8_add_1 : CTX8 * TWO^8 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_1(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  return sha_256_ctx_8_add_n(dst, &src, 1);
}

/* sha_256_ctx_8_add_2 : CTX8 * (TWO^8)^2 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_2(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  return sha_256_ctx_8_add_n(dst, &src, 2);
}

/* sha_256_ctx_8_add_4 : CTX8 * (TWO^8)^4 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_4(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  return sha_256_ctx_8_add_n(dst, &src, 4);
}

/* sha_256_ctx_8_add_8 : CTX8 * (TWO^8)^8 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_8(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  return sha_256_ctx_8_add_n(dst, &src, 8);
}

/* sha_256_ctx_8_add_16 : CTX8 * (TWO^8)^16 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_16(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  return sha_256_ctx_8_add_n(dst, &src, 16);
}

/* sha_256_ctx_8_add_32 : CTX8 * (TWO^8)^32 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  return sha_256_ctx_8_add_n(dst, &src, 32);
}

/* sha_256_ctx_8_add_64 : CTX8 * (TWO^8)^64 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_64(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  return sha_256_ctx_8_add_n(dst, &src, 64);
}

/* sha_256_ctx_8_add_128 : CTX8 * (TWO^8)^128 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_128(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  return sha_256_ctx_8_add_n(dst, &src, 128);
}

/* sha_256_ctx_8_add_256 : CTX8 * (TWO^8)^256 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_256(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  return sha_256_ctx_8_add_n(dst, &src, 256);
}

/* sha_256_ctx_8_add_512 : CTX8 * (TWO^8)^512 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_512(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  return sha_256_ctx_8_add_n(dst, &src, 512);
}

/* sha_256_ctx_8_add_buffer_511 : CTX8 * (TWO^8)^<512 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_buffer_511(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  sha256_midstate midstate;
  unsigned char buf[511];
  size_t buf_len;
  sha256_context ctx = {.output = midstate.s};

  if (!read_sha256_context(&ctx, &src)) return false;

  read_buffer8(buf, &buf_len, &src, 8);
  sha256_uchars(&ctx, buf, buf_len);
  return write_sha256_context(dst, &ctx);
}

/* sha_256_ctx_8_finalize : CTX8 |- TWO^256
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_finalize(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  sha256_midstate midstate;
  sha256_context ctx = {.output = midstate.s};

  if (!read_sha256_context(&ctx, &src)) return false;

  sha256_finalize(&ctx);
  write32s(dst, midstate.s, 8);
  return true;
}

/* parse_sequence : TWO^32 |- TWO^32 + TWO^32 */
bool parse_lock(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  uint_fast32_t nLockTime = read32(&src);
  writeBit(dst, 500000000U <= nLockTime);
  write32(dst, nLockTime);
  return true;
}

/* parse_sequence : TWO^32 |- S (TWO^16 + TWO^16) */
bool parse_sequence(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; /* env is unused. */
  uint_fast32_t nSequence = read32(&src);
  if (writeBit(dst, nSequence < ((uint_fast32_t)1 << 31))) {
    writeBit(dst, nSequence & ((uint_fast32_t)1 << 22));
    write16(dst, nSequence & 0xffff);
  } else {
    skipBits(dst, 17);
  }
  return true;
}
