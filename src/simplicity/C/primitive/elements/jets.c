#include "jets.h"

#include "primitive.h"
#include "../../unreachable.h"

/* Write a 256-bit hash value to the 'dst' frame, advancing the cursor 256 cells.
 *
 * Precondition: '*dst' is a valid write frame for 256 more cells;
 *               NULL != h;
 */
static void writeHash(frameItem* dst, const sha256_midstate* h) {
fprintf(stderr, "%x%x%x%x%x%x%x%x\n",
h->s[0],
h->s[1],
h->s[2],
h->s[3],
h->s[4],
h->s[5],
h->s[6],
h->s[7]
);
  write32s(dst, h->s, 8);
}

/* Write an outpoint value to the 'dst' frame, advancing the cursor 288 cells.
 *
 * Precondition: '*dst' is a valid write frame for 288 more cells;
 *               NULL != op;
 */
static void prevOutpoint(frameItem* dst, const outpoint* op) {
fprintf(stderr, "prevOutpoint: ");
  writeHash(dst, &op->txid);
fprintf(stderr, "prevOutpoint ix: %ld", op->ix);
  write32(dst, op->ix);
}

/* Write an confidential asset to the 'dst' frame, advancing the cursor 258 cells, unless 'asset->prefix == NONE'.
 * Returns 'asset->prefix != NONE'.
 *
 * Precondition: '*dst' is a valid write frame for 258 more cells;
 *               NULL != asset;
 */
static bool asset(frameItem* dst, const confidential* asset) {
  if (NONE == asset->prefix) return false;

  if (writeBit(dst, EXPLICIT == asset->prefix)) {
    skipBits(dst, 1);
  } else {
    writeBit(dst, ODD_Y == asset->prefix);
  }
fprintf(stderr, "asset: ");
  writeHash(dst, &asset->data);
  return true;
}

/* Write an confidential amount to the 'dst' frame, advancing the cursor 258 cells, unless 'amt->prefix == NONE'.
 * Returns 'amt->prefix != NONE'.
 *
 * Precondition: '*dst' is a valid write frame for 258 more cells;
 *               NULL != amt;
 */
static bool amt(frameItem* dst, const confAmount* amt) {
fprintf(stderr, "am: \n");
  if (NONE == amt->prefix) return false;

  if (writeBit(dst, EXPLICIT == amt->prefix)) {
    skipBits(dst, 1 + 256 - 64);
    write64(dst, amt->explicit);
fprintf(stderr, "explicit: %ld\n", amt->explicit);
  } else {
    writeBit(dst, ODD_Y == amt->prefix);
    writeHash(dst, &amt->confidential);
  }
  return true;
}

/* Write an optional confidential nonce to the 'dst' frame, advancing the cursor 259 cells.
 *
 * Precondition: '*dst' is a valid write frame for 259 more cells;
 *               NULL != nonce;
 */
static void nonce(frameItem* dst, const confidential* nonce) {
  if (writeBit(dst, NONE != nonce->prefix)) {
    if (writeBit(dst, EXPLICIT == nonce->prefix)) {
      skipBits(dst, 1);
    } else {
      writeBit(dst, ODD_Y == nonce->prefix);
    }
fprintf(stderr, "nonce: ");
    writeHash(dst, &nonce->data);
  } else {
    skipBits(dst, 1+1+256);
  }
}

/* Write an optional 'blindingNonce' from an 'assetIssuance' to the 'dst' frame, advancing the cursor 257 cells.
 *
 * Precondition: '*dst' is a valid write frame for 257 more cells;
 *               NULL != issuance;
 */
static void issuanceBlinding(frameItem* dst, const assetIssuance* issuance) {
  if (writeBit(dst, REISSUANCE == issuance->type)) {
    writeHash(dst, &issuance->blindingNonce);
  } else {
    skipBits(dst, 256);
  }
}

/* Write an optional 'contractHash' from an 'assetIssuance' to the 'dst' frame, advancing the cursor 257 cells.
 *
 * Precondition: '*dst' is a valid write frame for 257 more cells;
 *               NULL != issuance;
 */
static void issuanceContract(frameItem* dst, const assetIssuance* issuance) {
  if (writeBit(dst, NEW_ISSUANCE == issuance->type)) {
    writeHash(dst, &issuance->contractHash);
  } else {
    skipBits(dst, 256);
  }
}

/* Write an optional 'entropy' from an 'assetIssuance' to the 'dst' frame, advancing the cursor 257 cells.
 *
 * Precondition: '*dst' is a valid write frame for 257 more cells;
 *               NULL != issuance;
 */
static void issuanceEntropy(frameItem* dst, const assetIssuance* issuance) {
  if (writeBit(dst, REISSUANCE == issuance->type)) {
    writeHash(dst, &issuance->entropy);
  } else {
    skipBits(dst, 256);
  }
}

/* Write an optional confidential asset amount from an 'assetIssuance' to the 'dst' frame, advancing the cursor 259 cells.
 *
 * Precondition: '*dst' is a valid write frame for 259 more cells;
 *               NULL != issuance;
 */
static void issuanceAssetAmt(frameItem* dst, const assetIssuance* issuance) {
  if (writeBit(dst, NO_ISSUANCE != issuance->type && NONE != issuance->assetAmt.prefix)) {
    if (!amt(dst, &issuance->assetAmt)) {
      /* The 'amt' function has side-effects so we cannot simply 'assert(amt(..))' as it would be removed in non-debug builds. */
      assert(false);
    }
  } else {
    skipBits(dst, 258);
  }
}

/* Write an optional confidential issued/reissued asset amount from an 'assetIssuance' to the 'dst' frame, advancing the cursor.
 *
 * Precondition: '*dst' is a valid write frame for 259 more cells;
 *               NULL != issuance;
 */
static void issuanceTokenAmt(frameItem* dst, const assetIssuance* issuance) {
  if (writeBit(dst, NEW_ISSUANCE == issuance->type) && NONE != issuance->tokenAmt.prefix) {
    if (!amt(dst, &issuance->tokenAmt)) {
      /* The 'amt' function has side-effects so we cannot simply 'assert(amt(..))' as it would be removed in non-debug builds. */
      assert(false);
    }
  } else {
    skipBits(dst, 258);
  }
}

/* version : ONE |- TWO^32 */
bool version(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  write32(dst, env->tx->version);
  return true;
}

/* lockTime : ONE |- TWO^32 */
bool lockTime(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  write32(dst, env->tx->lockTime);
  return true;
}

/* inputIsPegin : TWO^32 |- S TWO */
bool inputIsPegin(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    writeBit(dst, env->tx->input[i].isPegin);
  } else {
    skipBits(dst, 1);
  }
  return true;
}

/* inputIsPegin : TWO^32 |- S (TWO^256 * TWO^32) */
bool inputPrevOutpoint(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    prevOutpoint(dst, &env->tx->input[i].prevOutpoint);
  } else {
    skipBits(dst, 288);
  }
  return true;
}

/* inputAsset : TWO^32 |- S (Conf TWO^256) */
bool inputAsset(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    return asset(dst, &env->tx->input[i].txo.asset);
  } else {
    skipBits(dst, 258);
    return true;
  }
}

/* inputAmount : TWO^32 |- S (Conf TWO^64) */
bool inputAmount(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    return amt(dst, &env->tx->input[i].txo.amt);
  } else {
    skipBits(dst, 258);
    return true;
  }
}

/* inputScriptHash : TWO^32 |- S TWO^256 */
bool inputScriptHash(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
fprintf(stderr, "input script hash: ");
    writeHash(dst, &env->tx->input[i].txo.scriptPubKey);
  } else {
    skipBits(dst, 256);
  }
  return true;
}

/* inputSequence : TWO^32 |- S TWO^32 */
bool inputSequence(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    write32(dst, env->tx->input[i].sequence);
  } else {
    skipBits(dst, 32);
  }
  return true;
}

/* inputIssuanceBlinding : TWO^32 |- S (S TWO^256) */
bool inputIssuanceBlinding(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    issuanceBlinding(dst, &env->tx->input[i].issuance);
  } else {
    skipBits(dst, 257);
  }
  return true;
}

/* inputIssuanceContract : TWO^32 |- S (S TWO^256) */
bool inputIssuanceContract(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    issuanceContract(dst, &env->tx->input[i].issuance);
  } else {
    skipBits(dst, 257);
  }
  return true;
}

/* inputIssuanceEntropy : TWO^32 |- S (S TWO^256) */
bool inputIssuanceEntropy(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    issuanceEntropy(dst, &env->tx->input[i].issuance);
  } else {
    skipBits(dst, 257);
  }
  return true;
}

/* inputIssuanceAssetAmt : TWO^32 |- S (S (Conf TWO^64)) */
bool inputIssuanceAssetAmt(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    issuanceAssetAmt(dst, &env->tx->input[i].issuance);
  } else {
    skipBits(dst, 259);
  }
  return true;
}

/* inputIssuanceTokenAmt : TWO^32 |- S (S (Conf TWO^64)) */
bool inputIssuanceTokenAmt(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numInputs)) {
    issuanceTokenAmt(dst, &env->tx->input[i].issuance);
  } else {
    skipBits(dst, 259);
  }
  return true;
}

/* outputAsset : TWO^32 |- S (Conf TWO^256) */
bool outputAsset(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numOutputs)) {
    return asset(dst, &env->tx->output[i].asset);
  } else {
    skipBits(dst, 258);
    return true;
  }
}

/* outputAmount : TWO^32 |- S (Conf TWO^64) */
bool outputAmount(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numOutputs)) {
    return amt(dst, &env->tx->output[i].amt);
  } else {
    skipBits(dst, 258);
    return true;
  }
}

/* outputNonce : TWO^32 |- S (S (Conf TWO^256)) */
bool outputNonce(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numOutputs)) {
    nonce(dst, &env->tx->output[i].nonce);
  } else {
    skipBits(dst, 259);
  }
  return true;
}

/* outputScriptHash : TWO^32 |- S TWO^256 */
bool outputScriptHash(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numOutputs)) {
fprintf(stderr, "output script hash: ");
    writeHash(dst, &env->tx->output[i].scriptPubKey);
  } else {
    skipBits(dst, 256);
  }
  return true;
}

/* outputNullDatum : TWO^32 * TWO^32 |- S (S (TWO^2 * TWO^256 + (TWO + TWO^4)))  */
bool outputNullDatum(frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = read32(&src);
  if (writeBit(dst, i < env->tx->numOutputs && env->tx->output[i].isNullData)) {
    uint_fast32_t j = read32(&src);
    if (writeBit(dst, j < env->tx->output[i].pnd.len)) {
      if (writeBit(dst, OP_PUSHDATA4 < env->tx->output[i].pnd.op[j].code)) {
        skipBits(dst, 2 + 256 - 5);
        if (writeBit(dst, OP_1 <= env->tx->output[i].pnd.op[j].code)) {
          switch (env->tx->output[i].pnd.op[j].code) {
            case OP_1 : writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 0); break;
            case OP_2 : writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 1); break;
            case OP_3 : writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 0); break;
            case OP_4 : writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 1); break;
            case OP_5 : writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 0); break;
            case OP_6 : writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 1); break;
            case OP_7 : writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 0); break;
            case OP_8 : writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 1); break;
            case OP_9 : writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 0); break;
            case OP_10: writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 1); break;
            case OP_11: writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 0); break;
            case OP_12: writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 1); break;
            case OP_13: writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 0); break;
            case OP_14: writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 1); break;
            case OP_15: writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 0); break;
            case OP_16: writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 1); break;
            default: break;
          }
          assert(false);
          UNREACHABLE;
        } else {
          assert(OP_RESERVED == env->tx->output[i].pnd.op[j].code ||
                 OP_1NEGATE == env->tx->output[i].pnd.op[j].code);
          skipBits(dst, 3);
          writeBit(dst, OP_RESERVED == env->tx->output[i].pnd.op[j].code);
        }
      } else {
        switch (env->tx->output[i].pnd.op[j].code) {
          case OP_IMMEDIATE: writeBit(dst, 0); writeBit(dst, 0); break;
          case OP_PUSHDATA: writeBit(dst, 0); writeBit(dst, 1); break;
          case OP_PUSHDATA2: writeBit(dst, 1); writeBit(dst, 0); break;
          case OP_PUSHDATA4: writeBit(dst, 1); writeBit(dst, 1); break;
          default: assert(false); UNREACHABLE;
        }
        writeHash(dst, &env->tx->output[i].pnd.op[j].dataHash);
      }
    } else {
      skipBits(dst, 1 + 2 + 256);
    }
  } else {
    skipBits(dst, 1 + 1 + 2 + 256);
  }
  return true;
}

/* scriptCMR : ONE |- TWO^256 */
bool scriptCMR(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  write32s(dst, env->scriptCMR, 8);
  return true;
}

/* currentIndex : ONE |- TWO^32 */
bool currentIndex(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  write32(dst, env->ix);
  return true;
}

/* currentIsPegin : ONE |- TWO */
bool currentIsPegin(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  writeBit(dst, env->tx->input[env->ix].isPegin);
  return true;
}

/* currentPrevOutpoint : ONE |- TWO^256 * TWO^32 */
bool currentPrevOutpoint(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  prevOutpoint(dst, &env->tx->input[env->ix].prevOutpoint);
  return true;
}

/* currentAsset : ONE |- Conf TWO^256 */
bool currentAsset(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  return asset(dst, &env->tx->input[env->ix].txo.asset);
}

/* currentAmount : ONE |- Conf TWO^64 */
bool currentAmount(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  return amt(dst, &env->tx->input[env->ix].txo.amt);
}

/* currentScriptHash : ONE |- TWO^256 */
bool currentScriptHash(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
fprintf(stderr, "current script hash: ");
  writeHash(dst, &env->tx->input[env->ix].txo.scriptPubKey);
  return true;
}

/* currentSequence : ONE |- TWO^32 */
bool currentSequence(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  write32(dst, env->tx->input[env->ix].sequence);
  return true;
}

/* currentIssuanceBlinding : ONE |- S (Conf TWO^256) */
bool currentIssuanceBlinding(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  issuanceBlinding(dst, &env->tx->input[env->ix].issuance);
  return true;
}

/* currentIssuanceContractHash : ONE |- S (Conf TWO^256) */
bool currentIssuanceContract(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  issuanceContract(dst, &env->tx->input[env->ix].issuance);
  return true;
}

/* currentIssuanceEntropy : ONE |- S (Conf TWO^256) */
bool currentIssuanceEntropy(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  issuanceEntropy(dst, &env->tx->input[env->ix].issuance);
  return true;
}

/* currentIssuanceAssetAmt : ONE |- S (Conf TWO^64) */
bool currentIssuanceAssetAmt(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  issuanceAssetAmt(dst, &env->tx->input[env->ix].issuance);
  return true;
}

/* currentIssuanceTokenAmt : ONE |- S (Conf TWO^64) */
bool currentIssuanceTokenAmt(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  if (env->tx->numInputs <= env->ix) return false;
  issuanceTokenAmt(dst, &env->tx->input[env->ix].issuance);
  return true;
}

/* inputsHash : ONE |- TWO^256 */
bool inputsHash(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
fprintf(stderr, "intputs hash ");
  writeHash(dst, &env->tx->inputsHash);
  return true;
}

/* outputsHash : ONE |- TWO^256 */
bool outputsHash(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
fprintf(stderr, "outputs hash ");
  writeHash(dst, &env->tx->outputsHash);
  return true;
}

/* numInputs : ONE |- TWO^32 */
bool numInputs(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  write32(dst, env->tx->numInputs);
  return true;
}

/* numOutputs : ONE |- TWO^32 */
bool numOutputs(frameItem* dst, frameItem src, const txEnv* env) {
  (void) src; // src is unused;
  write32(dst, env->tx->numOutputs);
  return true;
}
