#include "frame.h"

const size_t c_sizeof_UWORD = sizeof(UWORD);
const size_t c_sizeof_frameItem = sizeof(frameItem);

void c_initReadFrame(frameItem* frame, size_t n, UWORD* from) {
  *frame = initReadFrame(n, from);
}

void c_initWriteFrame(frameItem* frame, size_t n, UWORD* from) {
  *frame = initWriteFrame(n, from);
}

bool c_readBit(frameItem* frame) {
  return readBit(frame);
}

void c_writeBit(frameItem* frame, bool bit) {
  writeBit(frame, bit);
}

void c_skipBits(frameItem* frame, size_t n) {
  skipBits(frame, n);
}
