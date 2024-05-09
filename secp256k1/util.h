/***********************************************************************
 * Copyright (c) 2013, 2014 Pieter Wuille                              *
 * Distributed under the MIT software license, see the accompanying    *
 * file COPYING or https://www.opensource.org/licenses/mit-license.php.*
 ***********************************************************************/

#ifndef SECP256K1_UTIL_H
#define SECP256K1_UTIL_H

#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

#ifdef DETERMINISTIC
#define TEST_FAILURE(msg) do { \
    fprintf(stderr, "%s\n", msg); \
    abort(); \
} while(0);
#else
#define TEST_FAILURE(msg) do { \
    fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, msg); \
    abort(); \
} while(0)
#endif

#if SECP256K1_GNUC_PREREQ(3, 0)
#define EXPECT(x,c) __builtin_expect((x),(c))
#else
#define EXPECT(x,c) (x)
#endif

#ifdef DETERMINISTIC
#define CHECK(cond) do { \
    if (EXPECT(!(cond), 0)) { \
        TEST_FAILURE("test condition failed"); \
    } \
} while(0)
#else
#define CHECK(cond) do { \
    if (EXPECT(!(cond), 0)) { \
        TEST_FAILURE("test condition failed: " #cond); \
    } \
} while(0)
#endif

/* Like assert(), but when VERIFY is defined, and side-effect safe. */
#if defined(COVERAGE)
#define VERIFY_CHECK(check)
#define VERIFY_SETUP(stmt)
#elif defined(VERIFY)
#define VERIFY_CHECK CHECK
#define VERIFY_SETUP(stmt) do { stmt; } while(0)
#else
#define VERIFY_CHECK(cond) do { (void)(cond); } while(0)
#define VERIFY_SETUP(stmt)
#endif

/* Macro for restrict, when available and not in a VERIFY build. */
#if defined(SECP256K1_BUILD) && defined(VERIFY)
# define SECP256K1_RESTRICT
#else
# define SECP256K1_RESTRICT restrict
#endif

#if defined(__GNUC__)
# define SECP256K1_GNUC_EXT __extension__
#else
# define SECP256K1_GNUC_EXT
#endif

/** Semantics like memcmp. Variable-time.
 *
 * We use this to avoid possible compiler bugs with memcmp, e.g.
 * https://gcc.gnu.org/bugzilla/show_bug.cgi?id=95189
 */
static SECP256K1_INLINE int secp256k1_memcmp_var(const void *s1, const void *s2, size_t n) {
    const unsigned char *p1 = s1, *p2 = s2;
    size_t i;

    for (i = 0; i < n; i++) {
        int diff = p1[i] - p2[i];
        if (diff != 0) {
            return diff;
        }
    }
    return 0;
}

#if defined(USE_FORCE_WIDEMUL_INT128_STRUCT)
/* If USE_FORCE_WIDEMUL_INT128_STRUCT is set, use int128_struct. */
# define SECP256K1_WIDEMUL_INT128 1
# define SECP256K1_INT128_STRUCT 1
#elif defined(USE_FORCE_WIDEMUL_INT128)
/* If USE_FORCE_WIDEMUL_INT128 is set, use int128. */
# define SECP256K1_WIDEMUL_INT128 1
# define SECP256K1_INT128_NATIVE 1
#elif defined(USE_FORCE_WIDEMUL_INT64)
/* If USE_FORCE_WIDEMUL_INT64 is set, use int64. */
# define SECP256K1_WIDEMUL_INT64 1
#elif defined(UINT128_MAX) || defined(__SIZEOF_INT128__)
/* If a native 128-bit integer type exists, use int128. */
# define SECP256K1_WIDEMUL_INT128 1
# define SECP256K1_INT128_NATIVE 1
#elif defined(_MSC_VER) && (defined(_M_X64) || defined(_M_ARM64))
/* On 64-bit MSVC targets (x86_64 and arm64), use int128_struct
 * (which has special logic to implement using intrinsics on those systems). */
# define SECP256K1_WIDEMUL_INT128 1
# define SECP256K1_INT128_STRUCT 1
#elif SIZE_MAX > 0xffffffff
/* Systems with 64-bit pointers (and thus registers) very likely benefit from
 * using 64-bit based arithmetic (even if we need to fall back to 32x32->64 based
 * multiplication logic). */
# define SECP256K1_WIDEMUL_INT128 1
# define SECP256K1_INT128_STRUCT 1
#else
/* Lastly, fall back to int64 based arithmetic. */
# define SECP256K1_WIDEMUL_INT64 1
#endif

#ifndef __has_builtin
#define __has_builtin(x) 0
#endif

/* Determine the number of trailing zero bits in a (non-zero) 32-bit x.
 * This function is only intended to be used as fallback for
 * secp256k1_ctz32_var, but permits it to be tested separately. */
static SECP256K1_INLINE int secp256k1_ctz32_var_debruijn(uint32_t x) {
    static const uint8_t debruijn[32] = {
        0x00, 0x01, 0x02, 0x18, 0x03, 0x13, 0x06, 0x19, 0x16, 0x04, 0x14, 0x0A,
        0x10, 0x07, 0x0C, 0x1A, 0x1F, 0x17, 0x12, 0x05, 0x15, 0x09, 0x0F, 0x0B,
        0x1E, 0x11, 0x08, 0x0E, 0x1D, 0x0D, 0x1C, 0x1B
    };
    return debruijn[(uint32_t)((x & -x) * 0x04D7651FU) >> 27];
}

/* Determine the number of trailing zero bits in a (non-zero) 64-bit x.
 * This function is only intended to be used as fallback for
 * secp256k1_ctz64_var, but permits it to be tested separately. */
static SECP256K1_INLINE int secp256k1_ctz64_var_debruijn(uint64_t x) {
    static const uint8_t debruijn[64] = {
        0, 1, 2, 53, 3, 7, 54, 27, 4, 38, 41, 8, 34, 55, 48, 28,
        62, 5, 39, 46, 44, 42, 22, 9, 24, 35, 59, 56, 49, 18, 29, 11,
        63, 52, 6, 26, 37, 40, 33, 47, 61, 45, 43, 21, 23, 58, 17, 10,
        51, 25, 36, 32, 60, 20, 57, 16, 50, 31, 19, 15, 30, 14, 13, 12
    };
    return debruijn[(uint64_t)((x & -x) * 0x022FDD63CC95386DU) >> 58];
}

/* Determine the number of trailing zero bits in a (non-zero) 32-bit x. */
static SECP256K1_INLINE int secp256k1_ctz32_var(uint32_t x) {
    VERIFY_CHECK(x != 0);
#if (__has_builtin(__builtin_ctz) || SECP256K1_GNUC_PREREQ(3,4))
    /* If the unsigned type is sufficient to represent the largest uint32_t, consider __builtin_ctz. */
    if (((unsigned)UINT32_MAX) == UINT32_MAX) {
        return __builtin_ctz(x);
    }
#endif
#if (__has_builtin(__builtin_ctzl) || SECP256K1_GNUC_PREREQ(3,4))
    /* Otherwise consider __builtin_ctzl (the unsigned long type is always at least 32 bits). */
    return __builtin_ctzl(x);
#else
    /* If no suitable CTZ builtin is available, use a (variable time) software emulation. */
    return secp256k1_ctz32_var_debruijn(x);
#endif
}

/* Determine the number of trailing zero bits in a (non-zero) 64-bit x. */
static SECP256K1_INLINE int secp256k1_ctz64_var(uint64_t x) {
    VERIFY_CHECK(x != 0);
#if (__has_builtin(__builtin_ctzl) || SECP256K1_GNUC_PREREQ(3,4))
    /* If the unsigned long type is sufficient to represent the largest uint64_t, consider __builtin_ctzl. */
    if (((unsigned long)UINT64_MAX) == UINT64_MAX) {
        return __builtin_ctzl(x);
    }
#endif
#if (__has_builtin(__builtin_ctzll) || SECP256K1_GNUC_PREREQ(3,4))
    /* Otherwise consider __builtin_ctzll (the unsigned long long type is always at least 64 bits). */
    return __builtin_ctzll(x);
#else
    /* If no suitable CTZ builtin is available, use a (variable time) software emulation. */
    return secp256k1_ctz64_var_debruijn(x);
#endif
}

#endif /* SECP256K1_UTIL_H */
