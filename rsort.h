#ifndef SIMPLICITY_RSORT_H
#define SIMPLICITY_RSORT_H

#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

#include "limitations.h"
#include "sha256.h"

_Static_assert(UCHAR_MAX < SIZE_MAX, "UCHAR_MAX >= SIZE_MAX");
#define CHAR_COUNT ((size_t)1 << CHAR_BIT)

/* Internal function used by 'hasDuplicates'.  Do not call directly. */
const sha256_midstate* rsort(size_t* scratch, const sha256_midstate** a, size_t len, size_t level);

/* Searches for duplicates in an array of 'sha256_midstate's.
 * If 'true' is returned, '*duplicates' is set according to whether duplicate 'sha256_midstate' values were found.
 * If malloc fails, false is returned and '*duplicates' is unchanged.
 *
 * Precondition: NULL != duplicates;
 *               const sha256_midstate a[len];
 *               len <= DAG_LEN_MAX;
 */
static inline bool hasDuplicates(bool* duplicates, const sha256_midstate* a, size_t len) {
  if (0 == len) {
    *duplicates = false;
    return true;
  }
  static_assert(sizeof(a->s) * CHAR_BIT == 256, "sha256_midstate.s has unnamed padding.");
  static_assert(sizeof(a->s) < SIZE_MAX / CHAR_COUNT, "CHAR_BIT is way too large.");
  static_assert((sizeof(a->s) + 1) * CHAR_COUNT <= SIZE_MAX/sizeof(size_t), "sizeof(size_t) is way too large.");
  size_t * scratch = malloc((sizeof(a->s) + 1) * CHAR_COUNT * sizeof(size_t));
  static_assert(DAG_LEN_MAX <= SIZE_MAX / sizeof(const sha256_midstate*), "perm array too large.");
  static_assert(1 <= DAG_LEN_MAX, "DAG_LEN_MAX is zero.");
  static_assert(DAG_LEN_MAX - 1 <= UINT32_MAX, "perm array index does not fit in uint32_t.");
  assert(len <= SIZE_MAX / sizeof(const sha256_midstate*));
  assert(len - 1 <= UINT32_MAX);
  const sha256_midstate **perm = malloc(len * sizeof(const sha256_midstate*));
  bool result = scratch && perm;

  if (result) {
    for (size_t i = 0; i < len; ++i) {
      perm[i] = a + i;
    }

    *duplicates = rsort(scratch, perm, len, sizeof(a->s));
  }

  free(perm);
  free(scratch);
  return result;
}

#endif
