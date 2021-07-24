#ifndef SIMPLICITY_BOUNDED_H
#define SIMPLICITY_BOUNDED_H

#include <stdint.h>

static inline size_t max(size_t x, size_t y) {
  return x <= y ? y : x;
}

/* Returns min(x + y, SIZE_MAX) */
static inline size_t bounded_add(size_t x, size_t y) {
  return SIZE_MAX - x < y ? SIZE_MAX : x + y;
}

/* *x = min(*x + 1, SIZE_MAX) */
static inline void bounded_inc(size_t* x) {
  if (*x < SIZE_MAX) (*x)++;
}

/* 'pad(false, a, b)' computes the PADL(a, b) function.
 * 'pad( true, a, b)' computes the PADR(a, b) function.
 */
static inline size_t pad(bool right, size_t a, size_t b) {
  return max(a, b) - (right ? b : a);
}

#endif
