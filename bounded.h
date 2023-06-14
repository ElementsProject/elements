#ifndef SIMPLICITY_BOUNDED_H
#define SIMPLICITY_BOUNDED_H

#include <stdbool.h>
#include <stdint.h>

typedef uint_least32_t ubounded;
#define BOUNDED_MAX UINT32_MAX

static inline ubounded max(ubounded x, ubounded y) {
  return x <= y ? y : x;
}

/* Returns min(x + y, BOUNDED_MAX) */
static inline ubounded bounded_add(ubounded x, ubounded y) {
  return BOUNDED_MAX < x ? BOUNDED_MAX
       : BOUNDED_MAX - x < y ? BOUNDED_MAX
       : x + y;
}

/* *x = min(*x + 1, BOUNDED_MAX) */
static inline void bounded_inc(ubounded* x) {
  if (*x < BOUNDED_MAX) (*x)++;
}

/* 'pad(false, a, b)' computes the PADL(a, b) function.
 * 'pad( true, a, b)' computes the PADR(a, b) function.
 */
static inline ubounded pad(bool right, ubounded a, ubounded b) {
  return max(a, b) - (right ? b : a);
}

#endif
