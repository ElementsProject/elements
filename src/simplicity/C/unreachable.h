/* This module defines an UNREACHABLE macro that calls '__builtin_unreachable' if it exists.
 * Placing UNREACHABLE after a branch can allow an optimizer to eliminate the branch.
 */
#ifndef UNREACHABLE

#ifdef __has_builtin
#if __has_builtin(__builtin_unreachable)
#define UNREACHABLE __builtin_unreachable()
#endif
#endif

#ifndef UNREACHABLE
#include <stdlib.h>
#define UNREACHABLE abort()
#endif

#endif
