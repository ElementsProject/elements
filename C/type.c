#include "type.h"

#include <assert.h>
#include <stdbool.h>

#include "bounded.h"
#include "callonce.h"
#include "prefix.h"
#include "tag.h"
#include "unreachable.h"

/* Prepends the Simplicity TMR tag prefix to a string literal 's'. */
#define TYPE_TAG(s) SIMPLICITY_PREFIX "\x1F" "Type\x1F" s

/* Cached initial values for all the 'typeName's.
 * Only to be accessed through 'tmrIV'.
 */
static once_flag static_initialized = ONCE_FLAG_INIT;
static sha256_midstate unitIV,
                       sumIV,
                       prodIV;
static void static_initialize(void) {
  MK_TAG(&unitIV, TYPE_TAG("unit"));
  MK_TAG(&sumIV, TYPE_TAG("sum"));
  MK_TAG(&prodIV, TYPE_TAG("prod"));
}

/* Given a the 'kind' of a Simplicity type, return the SHA-256 hash of its associated TMR tag.
 * This is the "initial value" for computing the type Merkle root for that type.
 */
static sha256_midstate tmrIV(typeName kind) {
  call_once(&static_initialized, &static_initialize);

  switch (kind) {
   case ONE: return unitIV;
   case SUM: return sumIV;
   case PRODUCT: return prodIV;
  }
  /* Impossible to reach here (unless you call with uninitialized values). */
  assert(false);
  UNREACHABLE;
}

/* Given a well-formed 'type_dag', compute the bitSizes, skips, and type Merkle roots of all subexpressions.
 * For all 'i', 0 <= 'i' < 'len',
 *   'type_dag[i].typeMerkleRoot' will be the TMR
 *   and 'type_dag[i].bitSize' will be the bitSize of the subexpression denoted by the slice
 *
 *     (type_dag[i + 1])type_dag.
 *
 *   and when 'type_dag[i]' represents a non-trivial 'PRODUCT' type, where one of the two type arguments a trivial type.
 *       then 'type_dag[i].skip' is the index of the largest subexpression of 'type_dag[i]' such that
 *        either 'type_dag[type_dag[i].skip]' is a 'SUM' type
 *            or 'type_dag[type_dag[i].skip]' is a 'PRODUCT' type of two non-trivial types.
 *
 * Precondition: type type_dag[len] and 'type_dag' is well-formed.
 */
void computeTypeAnalyses(type* type_dag, const size_t len) {
  for (size_t i = 0; i < len; ++i) {
    type_dag[i].skip = i;
    switch (type_dag[i].kind) {
     case ONE:
      type_dag[i].bitSize = 0;
      break;
     case SUM:
      type_dag[i].bitSize = max(type_dag[type_dag[i].typeArg[0]].bitSize, type_dag[type_dag[i].typeArg[1]].bitSize);
      bounded_inc(&type_dag[i].bitSize);
      break;
     case PRODUCT:
      type_dag[i].bitSize = bounded_add(type_dag[type_dag[i].typeArg[0]].bitSize, type_dag[type_dag[i].typeArg[1]].bitSize);
      if (0 == type_dag[type_dag[i].typeArg[0]].bitSize) {
        type_dag[i].skip = type_dag[type_dag[i].typeArg[1]].skip;
      } else if (0 == type_dag[type_dag[i].typeArg[1]].bitSize) {
        type_dag[i].skip = type_dag[type_dag[i].typeArg[0]].skip;
      }
    }

    type_dag[i].typeMerkleRoot = tmrIV(type_dag[i].kind);

    uint32_t block[16];
    switch (type_dag[i].kind) {
     case ONE: break;
     case SUM:
     case PRODUCT:
      memcpy(block, type_dag[type_dag[i].typeArg[0]].typeMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, type_dag[type_dag[i].typeArg[1]].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(type_dag[i].typeMerkleRoot.s, block);
    }
  }
}
