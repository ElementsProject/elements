/* Translated from Bitcoin Core's C++ project:
 * src/crypto/sha256.cpp commit eb7daf4d600eeb631427c018a984a77a34aca66e
 *
 * Copyright (c) 2014-2018 The Bitcoin Core developers
 * Distributed under the MIT software license, see the accompanying
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.
 */

#include "sha256/compression.h"

#include <limits.h>

/* Multiplying a uint32_t by 1U promotes a value's type to the wider of unsigned int and uint32_t,
 * avoiding any possible issues with signed integer promotions causing havoc with unsigned modular arithmetic.
 */
static inline uint32_t Ch(uint32_t x, uint32_t y, uint32_t z) { return z ^ (x & (y ^ z)); }
static inline uint32_t Maj(uint32_t x, uint32_t y, uint32_t z) { return (x & y) | (z & (x | y)); }
static inline uint32_t Sigma0(uint32_t x) { return (x >> 2 | 1U * x << 30) ^ (x >> 13 | 1U * x << 19) ^ (x >> 22 | 1U * x << 10); }
static inline uint32_t Sigma1(uint32_t x) { return (x >> 6 | 1U * x << 26) ^ (x >> 11 | 1U * x << 21) ^ (x >> 25 | 1U * x << 7); }
static inline uint32_t sigma0(uint32_t x) { return (x >> 7 | 1U * x << 25) ^ (x >> 18 | 1U * x << 14) ^ (x >> 3); }
static inline uint32_t sigma1(uint32_t x) { return (x >> 17 | 1U * x << 15) ^ (x >> 19 | 1U * x << 13) ^ (x >> 10); }

/* One round of SHA-256.
 *
 * Precondition: NULL != d
 *               NULL != h
 *               d != h
 */
static inline void Round(uint32_t a, uint32_t b, uint32_t c, uint32_t* d, uint32_t e, uint32_t f, uint32_t g, uint32_t* h, uint32_t k) {
    uint32_t t1 = 1U * *h + Sigma1(e) + Ch(e, f, g) + k;
    uint32_t t2 = 1U * Sigma0(a) + Maj(a, b, c);
    *d = 1U * *d + t1;
    *h = 1U * t1 + t2;
}

/* Given a 256-bit 's' and a 512-bit 'chunk', then 's' becomes the value of the SHA-256 compression function ("added" to the original 's' value).
 *
 * Precondition: uint32_t s[8];
 *               uint32_t chunk[16]
 */
extern void sha256_compression(uint32_t* s, const uint32_t* chunk) {
    uint32_t a = s[0], b = s[1], c = s[2], d = s[3], e = s[4], f = s[5], g = s[6], h = s[7];
    uint32_t w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15;

    Round(a, b, c, &d, e, f, g, &h, 0x428a2f98U + (w0 = chunk[0]));
    Round(h, a, b, &c, d, e, f, &g, 0x71374491U + (w1 = chunk[1]));
    Round(g, h, a, &b, c, d, e, &f, 0xb5c0fbcfU + (w2 = chunk[2]));
    Round(f, g, h, &a, b, c, d, &e, 0xe9b5dba5U + (w3 = chunk[3]));
    Round(e, f, g, &h, a, b, c, &d, 0x3956c25bU + (w4 = chunk[4]));
    Round(d, e, f, &g, h, a, b, &c, 0x59f111f1U + (w5 = chunk[5]));
    Round(c, d, e, &f, g, h, a, &b, 0x923f82a4U + (w6 = chunk[6]));
    Round(b, c, d, &e, f, g, h, &a, 0xab1c5ed5U + (w7 = chunk[7]));
    Round(a, b, c, &d, e, f, g, &h, 0xd807aa98U + (w8 = chunk[8]));
    Round(h, a, b, &c, d, e, f, &g, 0x12835b01U + (w9 = chunk[9]));
    Round(g, h, a, &b, c, d, e, &f, 0x243185beU + (w10 = chunk[10]));
    Round(f, g, h, &a, b, c, d, &e, 0x550c7dc3U + (w11 = chunk[11]));
    Round(e, f, g, &h, a, b, c, &d, 0x72be5d74U + (w12 = chunk[12]));
    Round(d, e, f, &g, h, a, b, &c, 0x80deb1feU + (w13 = chunk[13]));
    Round(c, d, e, &f, g, h, a, &b, 0x9bdc06a7U + (w14 = chunk[14]));
    Round(b, c, d, &e, f, g, h, &a, 0xc19bf174U + (w15 = chunk[15]));

    Round(a, b, c, &d, e, f, g, &h, 0xe49b69c1U + (w0 = 1U * w0 + sigma1(w14) + w9 + sigma0(w1)));
    Round(h, a, b, &c, d, e, f, &g, 0xefbe4786U + (w1 = 1U * w1 + sigma1(w15) + w10 + sigma0(w2)));
    Round(g, h, a, &b, c, d, e, &f, 0x0fc19dc6U + (w2 = 1U * w2 + sigma1(w0) + w11 + sigma0(w3)));
    Round(f, g, h, &a, b, c, d, &e, 0x240ca1ccU + (w3 = 1U * w3 + sigma1(w1) + w12 + sigma0(w4)));
    Round(e, f, g, &h, a, b, c, &d, 0x2de92c6fU + (w4 = 1U * w4 + sigma1(w2) + w13 + sigma0(w5)));
    Round(d, e, f, &g, h, a, b, &c, 0x4a7484aaU + (w5 = 1U * w5 + sigma1(w3) + w14 + sigma0(w6)));
    Round(c, d, e, &f, g, h, a, &b, 0x5cb0a9dcU + (w6 = 1U * w6 + sigma1(w4) + w15 + sigma0(w7)));
    Round(b, c, d, &e, f, g, h, &a, 0x76f988daU + (w7 = 1U * w7 + sigma1(w5) + w0 + sigma0(w8)));
    Round(a, b, c, &d, e, f, g, &h, 0x983e5152U + (w8 = 1U * w8 + sigma1(w6) + w1 + sigma0(w9)));
    Round(h, a, b, &c, d, e, f, &g, 0xa831c66dU + (w9 = 1U * w9 + sigma1(w7) + w2 + sigma0(w10)));
    Round(g, h, a, &b, c, d, e, &f, 0xb00327c8U + (w10 = 1U * w10 + sigma1(w8) + w3 + sigma0(w11)));
    Round(f, g, h, &a, b, c, d, &e, 0xbf597fc7U + (w11 = 1U * w11 + sigma1(w9) + w4 + sigma0(w12)));
    Round(e, f, g, &h, a, b, c, &d, 0xc6e00bf3U + (w12 = 1U * w12 + sigma1(w10) + w5 + sigma0(w13)));
    Round(d, e, f, &g, h, a, b, &c, 0xd5a79147U + (w13 = 1U * w13 + sigma1(w11) + w6 + sigma0(w14)));
    Round(c, d, e, &f, g, h, a, &b, 0x06ca6351U + (w14 = 1U * w14 + sigma1(w12) + w7 + sigma0(w15)));
    Round(b, c, d, &e, f, g, h, &a, 0x14292967U + (w15 = 1U * w15 + sigma1(w13) + w8 + sigma0(w0)));

    Round(a, b, c, &d, e, f, g, &h, 0x27b70a85U + (w0 = 1U * w0 + sigma1(w14) + w9 + sigma0(w1)));
    Round(h, a, b, &c, d, e, f, &g, 0x2e1b2138U + (w1 = 1U * w1 + sigma1(w15) + w10 + sigma0(w2)));
    Round(g, h, a, &b, c, d, e, &f, 0x4d2c6dfcU + (w2 = 1U * w2 + sigma1(w0) + w11 + sigma0(w3)));
    Round(f, g, h, &a, b, c, d, &e, 0x53380d13U + (w3 = 1U * w3 + sigma1(w1) + w12 + sigma0(w4)));
    Round(e, f, g, &h, a, b, c, &d, 0x650a7354U + (w4 = 1U * w4 + sigma1(w2) + w13 + sigma0(w5)));
    Round(d, e, f, &g, h, a, b, &c, 0x766a0abbU + (w5 = 1U * w5 + sigma1(w3) + w14 + sigma0(w6)));
    Round(c, d, e, &f, g, h, a, &b, 0x81c2c92eU + (w6 = 1U * w6 + sigma1(w4) + w15 + sigma0(w7)));
    Round(b, c, d, &e, f, g, h, &a, 0x92722c85U + (w7 = 1U * w7 + sigma1(w5) + w0 + sigma0(w8)));
    Round(a, b, c, &d, e, f, g, &h, 0xa2bfe8a1U + (w8 = 1U * w8 + sigma1(w6) + w1 + sigma0(w9)));
    Round(h, a, b, &c, d, e, f, &g, 0xa81a664bU + (w9 = 1U * w9 + sigma1(w7) + w2 + sigma0(w10)));
    Round(g, h, a, &b, c, d, e, &f, 0xc24b8b70U + (w10 = 1U * w10 + sigma1(w8) + w3 + sigma0(w11)));
    Round(f, g, h, &a, b, c, d, &e, 0xc76c51a3U + (w11 = 1U * w11 + sigma1(w9) + w4 + sigma0(w12)));
    Round(e, f, g, &h, a, b, c, &d, 0xd192e819U + (w12 = 1U * w12 + sigma1(w10) + w5 + sigma0(w13)));
    Round(d, e, f, &g, h, a, b, &c, 0xd6990624U + (w13 = 1U * w13 + sigma1(w11) + w6 + sigma0(w14)));
    Round(c, d, e, &f, g, h, a, &b, 0xf40e3585U + (w14 = 1U * w14 + sigma1(w12) + w7 + sigma0(w15)));
    Round(b, c, d, &e, f, g, h, &a, 0x106aa070U + (w15 = 1U * w15 + sigma1(w13) + w8 + sigma0(w0)));

    Round(a, b, c, &d, e, f, g, &h, 0x19a4c116U + (w0 = 1U * w0 + sigma1(w14) + w9 + sigma0(w1)));
    Round(h, a, b, &c, d, e, f, &g, 0x1e376c08U + (w1 = 1U * w1 + sigma1(w15) + w10 + sigma0(w2)));
    Round(g, h, a, &b, c, d, e, &f, 0x2748774cU + (w2 = 1U * w2 + sigma1(w0) + w11 + sigma0(w3)));
    Round(f, g, h, &a, b, c, d, &e, 0x34b0bcb5U + (w3 = 1U * w3 + sigma1(w1) + w12 + sigma0(w4)));
    Round(e, f, g, &h, a, b, c, &d, 0x391c0cb3U + (w4 = 1U * w4 + sigma1(w2) + w13 + sigma0(w5)));
    Round(d, e, f, &g, h, a, b, &c, 0x4ed8aa4aU + (w5 = 1U * w5 + sigma1(w3) + w14 + sigma0(w6)));
    Round(c, d, e, &f, g, h, a, &b, 0x5b9cca4fU + (w6 = 1U * w6 + sigma1(w4) + w15 + sigma0(w7)));
    Round(b, c, d, &e, f, g, h, &a, 0x682e6ff3U + (w7 = 1U * w7 + sigma1(w5) + w0 + sigma0(w8)));
    Round(a, b, c, &d, e, f, g, &h, 0x748f82eeU + (w8 = 1U * w8 + sigma1(w6) + w1 + sigma0(w9)));
    Round(h, a, b, &c, d, e, f, &g, 0x78a5636fU + (w9 = 1U * w9 + sigma1(w7) + w2 + sigma0(w10)));
    Round(g, h, a, &b, c, d, e, &f, 0x84c87814U + (w10 = 1U * w10 + sigma1(w8) + w3 + sigma0(w11)));
    Round(f, g, h, &a, b, c, d, &e, 0x8cc70208U + (w11 = 1U * w11 + sigma1(w9) + w4 + sigma0(w12)));
    Round(e, f, g, &h, a, b, c, &d, 0x90befffaU + (w12 = 1U * w12 + sigma1(w10) + w5 + sigma0(w13)));
    Round(d, e, f, &g, h, a, b, &c, 0xa4506cebU + (w13 = 1U * w13 + sigma1(w11) + w6 + sigma0(w14)));
    Round(c, d, e, &f, g, h, a, &b, 0xbef9a3f7U + (1U * w14 + sigma1(w12) + w7 + sigma0(w15)));
    Round(b, c, d, &e, f, g, h, &a, 0xc67178f2U + (1U * w15 + sigma1(w13) + w8 + sigma0(w0)));

    s[0] = 1U * s[0] + a;
    s[1] = 1U * s[1] + b;
    s[2] = 1U * s[2] + c;
    s[3] = 1U * s[3] + d;
    s[4] = 1U * s[4] + e;
    s[5] = 1U * s[5] + f;
    s[6] = 1U * s[6] + g;
    s[7] = 1U * s[7] + h;
}

/* Given a 256-bit 's' and a 512-bit 'chunk', then 's' becomes the value of the SHA-256 compression function ("added" to the original 's' value).
 *
 * Precondition: uint32_t s[8];
 *               unsigned char chunk[64]
 */
extern void sha256_compression_uchar(uint32_t* s, const unsigned char* chunk) {
  sha256_compression(s, (const uint32_t[16])
    { ReadBE32(chunk + 4*0)
    , ReadBE32(chunk + 4*1)
    , ReadBE32(chunk + 4*2)
    , ReadBE32(chunk + 4*3)
    , ReadBE32(chunk + 4*4)
    , ReadBE32(chunk + 4*5)
    , ReadBE32(chunk + 4*6)
    , ReadBE32(chunk + 4*7)
    , ReadBE32(chunk + 4*8)
    , ReadBE32(chunk + 4*9)
    , ReadBE32(chunk + 4*10)
    , ReadBE32(chunk + 4*11)
    , ReadBE32(chunk + 4*12)
    , ReadBE32(chunk + 4*13)
    , ReadBE32(chunk + 4*14)
    , ReadBE32(chunk + 4*15)
    });
}
