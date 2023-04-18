#include "jets.h"

/* verify : TWO |- ONE */
bool verify(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  (void) dst; // dst is unused;
  return readBit(&src);
}

/* low_32 : ONE |- TWO^32 */
bool low_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  (void) src; // src is unused;
  write32(dst, 0);
  return true;
}

/* one_32 : ONE |- TWO^32 */
bool one_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  (void) src; // src is unused;
  write32(dst, 1);
  return true;
}

/* eq_32 : TWO^32 * TWO^32 |- TWO */
bool eq_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint_fast32_t x = read32(&src);
  uint_fast32_t y = read32(&src);
  writeBit(dst, x == y);
  return true;
}

/* eq_256 : TWO^256 * TWO^256 |- TWO */
bool eq_256(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
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

bool add_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint_fast32_t x = read32(&src);
  uint_fast32_t y = read32(&src);
  writeBit(dst, 0xFFFFFFFF - y < x);
  /* <pedantic>
   * Multiplying a uint32_t by 1U promotes a value's type to the wider of unsigned int and uint32_t,
   * avoiding any possible issues with signed integer promotions causing havoc with unsigned modular arithmetic
   * if int happens to be 33 bits wide.
   * </pedantic>
   */
  write32(dst, 1U * x + y);
  return true;
}

bool full_add_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  bool z = readBit(&src);
  uint_fast32_t x = read32(&src);
  uint_fast32_t y = read32(&src);
  writeBit(dst, 0xFFFFFFFF - y < x || 0xFFFFFFFF - z < x + y);
  /* <pedantic>
   * Multiplying a uint32_t by 1U promotes a value's type to the wider of unsigned int and uint32_t,
   * avoiding any possible issues with signed integer promotions causing havoc with unsigned modular arithmetic
   * if int happens to be 33 bits wide.
   * </pedantic>
   */
  write32(dst, 1U * x + y + z);
  return true;
}

bool subtract_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint_fast32_t x = read32(&src);
  uint_fast32_t y = read32(&src);
  writeBit(dst, x < y);
  write32(dst, x - y);
  return true;
}

bool full_subtract_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  bool z = readBit(&src);
  uint_fast32_t x = read32(&src);
  uint_fast32_t y = read32(&src);
  writeBit(dst, x < y || x - y < z);
  write32(dst, x - y - z);
  return true;
}

bool multiply_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint_fast64_t x = read32(&src);
  uint_fast64_t y = read32(&src);
  write64(dst, x * y);
  return true;
}

bool full_multiply_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint_fast64_t x = read32(&src);
  uint_fast64_t y = read32(&src);
  uint_fast64_t z = read32(&src);
  uint_fast64_t w = read32(&src);
  write64(dst, x * y + z + w);
  return true;
}

/* le_32 : TWO^32 * TWO^32 |- TWO */
bool le_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint_fast32_t x = read32(&src);
  uint_fast32_t y = read32(&src);
  writeBit(dst, x <= y);
  return true;
}

/* sha_256_iv : ONE |- TWO^256 */
bool sha_256_iv(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  (void) src; // env is unused;

  uint32_t iv[8];
  sha256_iv(iv);

  write32s(dst, iv, 8);
  return true;
}

/* sha_256_block : TWO^256 * TWO^512 |- TWO^256 */
bool sha_256_block(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
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
  (void) env; // env is unused;
  (void) src; // env is unused;

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
  assert(0 < n && n <= 512 && (n & (n - 1)) == 0);
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
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 1);
}

/* sha_256_ctx_8_add_2 : CTX8 * (TWO^8)^2 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_2(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 2);
}

/* sha_256_ctx_8_add_4 : CTX8 * (TWO^8)^4 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_4(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 4);
}

/* sha_256_ctx_8_add_8 : CTX8 * (TWO^8)^8 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_8(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 8);
}

/* sha_256_ctx_8_add_16 : CTX8 * (TWO^8)^16 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_16(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 16);
}

/* sha_256_ctx_8_add_32 : CTX8 * (TWO^8)^32 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 32);
}

/* sha_256_ctx_8_add_64 : CTX8 * (TWO^8)^64 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_64(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 64);
}

/* sha_256_ctx_8_add_128 : CTX8 * (TWO^8)^128 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_128(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 128);
}

/* sha_256_ctx_8_add_256 : CTX8 * (TWO^8)^256 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_256(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 256);
}

/* sha_256_ctx_8_add_512 : CTX8 * (TWO^8)^512 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_512(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 512);
}

/* sha_256_ctx_8_add_buffer_511 : CTX8 * (TWO^8)^<512 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_buffer_511(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
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
  (void) env; // env is unused;
  sha256_midstate midstate;
  sha256_context ctx = {.output = midstate.s};

  if (!read_sha256_context(&ctx, &src)) return false;

  sha256_finalize(&ctx);
  write32s(dst, midstate.s, 8);
  return true;
}

/* parse_sequence : TWO^32 |- TWO^32 + TWO^32 */
bool parse_lock(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint_fast32_t nLockTime = read32(&src);
  writeBit(dst, 500000000U <= nLockTime);
  write32(dst, nLockTime);
  return true;
}

/* parse_sequence : TWO^32 |- S (TWO^16 + TWO^16) */
bool parse_sequence(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint_fast32_t nSequence = read32(&src);
  if (writeBit(dst, nSequence < ((uint_fast32_t)1 << 31))) {
    writeBit(dst, nSequence & ((uint_fast32_t)1 << 22));
    write16(dst, nSequence & 0xffff);
  } else {
    skipBits(dst, 17);
  }
  return true;
}
