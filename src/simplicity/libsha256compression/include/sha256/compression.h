#ifndef SHA256_COMPRESSION_H
#define SHA256_COMPRESSION_H

#include <stdint.h>

/* Packs (the 8 least significant bits of) 4 'unsigned char's into a 'uint32_t' in "big endian" order.
 *
 * Precondition: unsigned char b[4]
 */
static inline uint32_t ReadBE32(const unsigned char* b) {
  return (uint32_t)(b[0]) << 24
       | (uint32_t)(b[1] & 0xff) << 16
       | (uint32_t)(b[2] & 0xff) << 8
       | (uint32_t)(b[3] & 0xff);
}

/* Unpacks 4 bytes from a 'uint32_t' into an 'unsigned char' array in "big endian" order.
 *
 * Precondition: unsigned char ptr[4]
 */
static inline void WriteBE32(unsigned char* ptr, uint32_t x) {
  ptr[0] = (unsigned char)(x >> 24);
  ptr[1] = (x >> 16) & 0xff;
  ptr[2] = (x >> 8) & 0xff;
  ptr[3] = x & 0xff;
}

/* Sets the value of 'iv' to SHA-256's initial value.
 *
 * Precondition: uint32_t iv[8]
 */
static inline void sha256_iv(uint32_t* iv) {
    iv[0] = 0x6a09e667ul;
    iv[1] = 0xbb67ae85ul;
    iv[2] = 0x3c6ef372ul;
    iv[3] = 0xa54ff53aul;
    iv[4] = 0x510e527ful;
    iv[5] = 0x9b05688cul;
    iv[6] = 0x1f83d9abul;
    iv[7] = 0x5be0cd19ul;
}

/* Coverts a given 'midstate' value to a 'hash' value as 32 bytes stored in an unsigned char array.
 *
 * Precondition: unsigned char hash[32];
 *               uint32_t midstate[8]
 */
static inline void sha256_fromMidstate(unsigned char* hash, const uint32_t* midstate) {
  WriteBE32(hash + 0*4, midstate[0]);
  WriteBE32(hash + 1*4, midstate[1]);
  WriteBE32(hash + 2*4, midstate[2]);
  WriteBE32(hash + 3*4, midstate[3]);
  WriteBE32(hash + 4*4, midstate[4]);
  WriteBE32(hash + 5*4, midstate[5]);
  WriteBE32(hash + 6*4, midstate[6]);
  WriteBE32(hash + 7*4, midstate[7]);
}

/* Coverts a given 'hash' value as 32 bytes stored in an unsigned char array to a 'midstate' value.
 *
 * Precondition: uint32_t midstate[8];
 *               unsigned char hash[32]
 */
static inline void sha256_toMidstate(uint32_t* midstate, const unsigned char* hash) {
  midstate[0] = ReadBE32(hash + 0*4);
  midstate[1] = ReadBE32(hash + 1*4);
  midstate[2] = ReadBE32(hash + 2*4);
  midstate[3] = ReadBE32(hash + 3*4);
  midstate[4] = ReadBE32(hash + 4*4);
  midstate[5] = ReadBE32(hash + 5*4);
  midstate[6] = ReadBE32(hash + 6*4);
  midstate[7] = ReadBE32(hash + 7*4);
}

/* Given a 256-bit 'midstate' and a 512-bit 'block', then 'midstate' becomes the value of the SHA-256 compression function ("added" to the original 'midstate' value).
 *
 * Precondition: uint32_t midstate[8];
 *               uint32_t block[16]
 */
extern void sha256_compression(uint32_t* midstate, const uint32_t* block);

/* Given a 256-bit 'midstate' and a 512-bit 'block', then 'midstate' becomes the value of the SHA-256 compression function ("added" to the original 'midstate' value).
 *
 * Precondition: uint32_t midstate[8];
 *               unsigned char block[64]
 */
extern void sha256_compression_uchar(uint32_t* midstate, const unsigned char* block);

#endif /* SHA256_COMPRESSION_H */
