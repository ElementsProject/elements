#include "ops.h"

/* Compute an Element's entropy value from a prevoutpoint and a contract hash.
 * A reimplementation of GenerateAssetEntropy from Element's 'issuance.cpp'.
 *
 * Precondition: NULL != op;
 *               NULL != contract;
 */
sha256_midstate generateIssuanceEntropy(const outpoint* op, const sha256_midstate* contract) {
  uint32_t block[16];
  unsigned char buf[32];
  sha256_midstate result;

  /* First hash the outpoint data. */
  {
    sha256_context ctx = sha256_init(result.s);
    sha256_fromMidstate(buf, op->txid.s);
    sha256_uchars(&ctx, buf, 32);
    sha256_u32le(&ctx, op->ix);
    sha256_finalize(&ctx);
  }
  /* Fill in the first half of the block with the double hashed outpoint data. */
  {
    sha256_context ctx = sha256_init(&block[0]);
    sha256_fromMidstate(buf, result.s);
    sha256_uchars(&ctx, buf, 32);
    sha256_finalize(&ctx);
  }

  memcpy(&block[8], contract->s, sizeof(contract->s));
  sha256_iv(result.s);
  sha256_compression(result.s, block);

  return result;
}

/* Compute an Element's issuance Asset ID value from an entropy value.
 * A reimplementation of CalculateAsset from Element's 'issuance.cpp'.
 *
 * Precondition: NULL != entropy;
 */
sha256_midstate calculateAsset(const sha256_midstate* entropy) {
  uint32_t block[16] = {0};
  sha256_midstate result;

  memcpy(&block[0], entropy->s, sizeof(entropy->s));
  sha256_iv(result.s);
  sha256_compression(result.s, block);

  return result;
}

/* Compute an Element's issuance Token ID value from an entropy value and an amount prefix.
 * A reimplementation of CalculateReissuanceToken from Element's 'issuance.cpp'.
 *
 * Precondition: NULL != entropy;
 */
sha256_midstate calculateToken(const sha256_midstate* entropy, confPrefix prefix) {
  uint32_t block[16] = {0};
  sha256_midstate result;

  memcpy(&block[0], entropy->s, sizeof(entropy->s));
  block[8] = is_confidential(prefix) ? 0x02000000 : 0x01000000;
  sha256_iv(result.s);
  sha256_compression(result.s, block);

  return result;
}

/* Compute an Element's tapleaf hash from a tapleaf version and a 256-bit script value.
 * A reimplementation of ComputeTapleafHash from Element's 'interpreter.cpp'.
 * Only 256-bit script values are supported as that is the size used for Simplicity CMRs.
 *
 * Precondition: NULL != cmr;
 */
sha256_midstate make_tapleaf(unsigned char version, const sha256_midstate* cmr) {
  sha256_midstate result;
  sha256_midstate tapleafTag;
  {
    static unsigned char tagName[] = "TapLeaf/elements";
    sha256_context ctx = sha256_init(tapleafTag.s);
    sha256_uchars(&ctx, tagName, sizeof(tagName) - 1);
    sha256_finalize(&ctx);
  }
  sha256_context ctx = sha256_init(result.s);
  sha256_hash(&ctx, &tapleafTag);
  sha256_hash(&ctx, &tapleafTag);
  sha256_uchar(&ctx, version);
  sha256_uchar(&ctx, 32);
  sha256_hash(&ctx, cmr);
  sha256_finalize(&ctx);

  return result;
}

/* Compute an Element's tapbrach hash from two branches.
 *
 * Precondition: NULL != a;
 *               NULL != b;
 */
sha256_midstate make_tapbranch(const sha256_midstate* a, const sha256_midstate* b) {
  sha256_midstate result;
  sha256_midstate tapbranchTag;
  {
    static unsigned char tagName[] = "TapBranch/elements";
    sha256_context ctx = sha256_init(tapbranchTag.s);
    sha256_uchars(&ctx, tagName, sizeof(tagName) - 1);
    sha256_finalize(&ctx);
  }
  sha256_context ctx = sha256_init(result.s);
  sha256_hash(&ctx, &tapbranchTag);
  sha256_hash(&ctx, &tapbranchTag);
  if (sha256_cmp_be(a, b) < 0) {
    sha256_hash(&ctx, a);
    sha256_hash(&ctx, b);
  } else {
    sha256_hash(&ctx, b);
    sha256_hash(&ctx, a);
  }
  sha256_finalize(&ctx);

  return result;
}
