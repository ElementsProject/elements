#include "jets.h"

#include "sha256/compression.h"

bool adder32(frameItem* dst, frameItem src, const txEnv* env) {
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

bool fullAdder32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  /* :TODO: rewrite full adder so the carry bit comes first for better bit allignment */
  uint_fast32_t x = read32(&src);
  uint_fast32_t y = read32(&src);
  bool z = readBit(&src);
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

bool subtractor32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint_fast32_t x = read32(&src);
  uint_fast32_t y = read32(&src);
  writeBit(dst, x < y);
  write32(dst, x - y);
  return true;
}

bool fullSubtractor32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  /* :TODO: rewrite full subtractor so the borrow bit comes first for better bit allignment */
  uint_fast32_t x = read32(&src);
  uint_fast32_t y = read32(&src);
  bool z = readBit(&src);
  writeBit(dst, x < y || x - y < z);
  write32(dst, x - y - z);
  return true;
}

bool multiplier32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint_fast64_t x = read32(&src);
  uint_fast64_t y = read32(&src);
  write64(dst, x * y);
  return true;
}

bool fullMultiplier32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint_fast64_t x = read32(&src);
  uint_fast64_t y = read32(&src);
  uint_fast64_t z = read32(&src);
  uint_fast64_t w = read32(&src);
  write64(dst, x * y + z + w);
  return true;
}

bool sha256_hashBlock(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint32_t h[8];
  uint32_t block[16];
  read32s(h, 8, &src);
  read32s(block, 16, &src);
  sha256_compression(h, block);
  write32s(dst, h, 8);
  return true;
}
