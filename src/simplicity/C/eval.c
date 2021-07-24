#include "eval.h"

#include <string.h>
#include "bounded.h"
#include "unreachable.h"

/* We choose an unusual representation for frames of the Bit Machine.
 *
 * An 'n'-bit frame is stored in the array of 'UWORD's of length 'l' where 'l' is the least value such that 'n <= l * UWORD_BIT'.
 * Thus there may be extra "padding" bits in the array when 'n < l * UWORD_BIT'.
 *
 * We choose to store the frames bits in a sequence with the first bits in the last element of the array and
 * the last bits in the first element of the array.
 * Within a 'UWORD' array element, the bits of the frame are stored with the first bits in the most significant positions
 * and the last bits in the least significant positions.
 * We choose to put padding bits entirely within the most significant bits of the last element of the array.
 *
 * Thus the last bit of the frame will always be the least significant bit of the first element of the array.
 * When there are no padding bits, the first bit of the frame will be the most significant bit of the last element of the array.
 * When there are padding bits, the first bit of the frame will occur at the most significant non-padding bit.
 *
 * More precisely, bit 'm' of an 'n'-bit frame (with '0 <= m < n') is the bit at position '1 << ((n-m-1) % UWORD_BIT)'
 * of the element of the array at index '(n-m-1 / UWORD_BIT)'.
 *
 * 0-bit frames are allowed, in which case the array will have length 0.
 *
 * Rationale:
 *
 * The Bit Machine's standard library of jets operates using a "big endian" representation of integers
 * from the Bit Machine's perspective.
 * It is often the case that we encounter types that are sums of various integers sizes.
 * For example, the Bitcoin primitive 'outputValue : TWO^32 |- ONE + TWO^64' has a target type
 * that is the sum of 64-bit integer (with a 0-bit integer).
 *
 * When a frame is generated from a type such as 'ONE + TWO^64' our representation places the tag for this type
 * by itself as the least significant bit of the last element of the frame's array (as long as 'UWORD_BIT' divides 64).
 * When this frame contains a value of the right-hand type, 'TWO^64', this value entirely fits perfectly within
 * the within the first elements of the array (again, as long as 'UWORD_BIT' divides 64).
 * Furthermore, if 'UWORD_BIT == 8', then this representation place this value of type 'TWO^64'
 * into the machine's memory in little endian byte order.
 *
 * All of the above means that when jets need to marshal values from the Bit Machine's representation
 * to the architecture's representation, it will often be the case that the data is already byte-aligned and
 * in the correct order for little endian processors.
 * When a jet marshals a architecture-sized word, and 'UWORD' is the architecture's native integer size, then
 * it will often be the case that the data is word-aligned (for both big and little endian processors).
 * Only the case when 'UWORD_BIT == 8' and architecture's processor is big-endian will the compiler need to emit
 * byte-swapping instructions.
 *
 * Nevertheless, our implementation is independent of architecture and will function correctly on all architectures
 * for any value of UWORD_BIT.
 *
 * Note: while we do attempt make the fast path for marshaling values for jets common, when assigning discounts to jets
 * it is important to only consider the worst case, slow path, behaviour, as good byte or bit alignment is not guaranteed in
 * presence of oddly shaped pairs of values.
 */

/* The main memory used by the Bit Machine during execution is contained in a single allocation of an array of 'UWORD's
 * named 'cells'.
 * The read and write frames used by the Bit Machine during execution are slices of this single array allocation.
 * We represent the read frame and write frame stacks within 'cells' using a [gap buffer](https://en.wikipedia.org/wiki/Gap_buffer).
 * The frames of the read frame stack are assigned to the beginning of the cell array
 * with the active read frame occurring as the last of these frames.
 * The frames of the write frame stack are assigned to the end of the cell array
 * with the active write frame occurring as the first of these frames.
 * This leaves a (possibly empty) gap of unused UWORDs between the '.edge' of the active read frame
 * and the '.edge' of the active write frame.
 * This gap will shrink / grow / move during the execution of the Bit Machine.
 * Thus whether a particular UWORD from 'cells' belongs to some read frame or write frame will vary during the execution.
 * Static analysis determines a safe size that is acceptable for the 'cells' array.
 */

/* To keep track of the individual frames of the read frame and write frame stacks we another single allocation of
 * an array of 'frameItem's called 'frames'.
 * This 'frames' array is another instance of a [gap buffer](https://en.wikipedia.org/wiki/Gap_buffer).
 * The read frames are tracked by 'frameItem's occurring at the beginning of the 'frames' array
 * with the active read frame tracked the last of these 'frameItem's.
 * The write frames are tracked by 'frameItem's occurring at the end of the 'frames' array
 * with the active write frame tracked the first of these 'frameItem's.
 * This leaves a (possibly empty) gap of unused 'frameItem's between the item that tracks active read frame
 * and the item that tracks the active write frame.
 * This gap will shrink / grow / move during the execution of the Bit Machine.
 * Thus whether a particular 'frameItem' from 'frames' tracks a read frame or write frame will vary during the execution.
 * The 'frameItem' that tracks the active read frame is located at 'state.activeReadFrame'.
 * The 'frameItem' that tracks the active write frame is located at 'state.activeWriteFrame'.
 * There is always an active read frame and an active write frame, though these frames are initially of size 0
 * when evaluating Simplicity programs.
 * Static analysis determines a safe size that is acceptable for the 'frames' array.
 */

/* When a 'frameItem' tracks a read frame, its '.edge' field points to the UWORD from 'cell' that is
 * one-past-the-end of the 'cells' slice that makes up that frame.
 * The '.offset' value indirectly tracks the position of the read frame's cursor.
 * A cursor at the beginning of a read frame is denoted by an '.offset' value equal to that frame's padding.
 * When the frame has no padding, a cursor at the beginning of a read frame is denoted by an '.offset' of 0.
 * For each subsequent cursor position within the read frame, the '.offset' increments by one.
 * When the cursor is at (one-cell past) the end of the read frame, the '.offset' value will be equal to the total number of bits
 * allocated for the frame (including padding bits), which is necessarily some multiple of (UWORD_BIT).
 * We say "a read frame is valid for /n/ more cells" when '.edge - ROUND_UWORD(.offset + n)' points to a
 * 'UWORD[ROUND_UWORD(.offset + n)]' array of initialized values.
 * We say "a read frame is valid" if it is valid for 0 more cells.
 *
 * When a 'frameItem' tracks a write frame, its '.edge' field points the UWORD from 'cell' that is
 * the first element of the 'cells' slice that makes up that frame.
 * The '.offset' value indirectly tracks the position of the write frame's cursor.
 * A cursor at the beginning of a read frame is denoted by an '.offset' value equal to
 * that frame's number of bits (excluding padding).
 * For each subsequent cursor position within the write frame, the '.offset' decrements by one.
 * When the cursor is at (one-cell past) the end of the write frame, the '.offset' value will be equal to 0.
 * We say "a write frame is valid for /n/ more cells" when '.edge' points to an 'UWORD[ROUND_UWORD(.offset)]' array of
 * initialized values and 'n <= .offset'.
 * We say "a write frame is valid" if it is valid for 0 more cells.
 *
 * Notice that the interpretation of the fields of a 'frameItem' depends on whether the 'frameItem' is tracking a read frame or
 * a write frame.
 */

/* Given a read frame, advance its cursor by 'n' cells.
 *
 * Precondition: NULL != frame.
 */
static void forward(frameItem* frame, size_t n) {
  frame->offset += n;
}

/* Given a read frame, move its cursor backwards by 'n' cells.
 *
 * Precondition: n <= frame->offset
 */
static void backward(frameItem* frame, size_t n) {
  assert(n <= frame->offset);
  frame->offset -= n;
}

/* Given a write frame, advance its cursor by 'n' cells.
 *
 * Precondition: n <= frame->offset
 */
static void skip(frameItem* frame, size_t n) {
  assert(n <= frame->offset);
  frame->offset -= n;
}

/* Given a write frame and a read frame, copy 'n' cells from after the read frame's cursor to after the write frame's cursor,
 * Cells in within the write frame beyond 'n' cells after the write frame's cursor may also be overwritten.
 *
 * Precondition: '*dst' is a valid write frame for 'n' more cells;
 *               '*src' is a valid read frame for 'n' more cells;
 *               '0 < n';
 */
static void copyBitsHelper(const frameItem* dst, const frameItem *src, size_t n) {
  /* Pointers to the UWORDs of the read and write frame that contain the frame's cursor. */
  UWORD* src_ptr = src->edge - 1 - src->offset / UWORD_BIT;
  UWORD* dst_ptr = dst->edge + (dst->offset - 1) / UWORD_BIT;
  /* The specific bit within those UWORDs that is immediately in front of their respective cursors.
   * That bit is specifically '1 << (src_shift - 1)' for the read frame,
   * and '1 << (dst_shift - 1)' for the write frame, unless 'dst_shift == 0', in which case it is '1 << (UWORD_BIT - 1)'.
   */
  size_t src_shift = UWORD_BIT - (src->offset % UWORD_BIT);
  size_t dst_shift = dst->offset % UWORD_BIT;
  if (dst_shift) {
    /* The write frame's current UWORD is partially filled.
     * Fill the rest of it without overwriting the existing data.
     */
    *dst_ptr = LSBclear(*dst_ptr, dst_shift);

    if (src_shift < dst_shift) {
      /* The read frame's current UWORD doesn't have enough data to entirely fill the rest of the write frame's current UWORD.
       * Fill as much as we can and move src_ptr to the read frame's next UWORD.
       */
      *dst_ptr |= (UWORD)(LSBkeep(*src_ptr, src_shift) << (dst_shift - src_shift));
      if (n <= src_shift) return;
      n -= src_shift;
      dst_shift -= src_shift;
      src_ptr--;
      src_shift = UWORD_BIT;
    }

    /* Fill the rest of the write frame's current UWORD and move dst_ptr to the write frame's next UWORD. */
    *dst_ptr |= LSBkeep((UWORD)(*src_ptr >> (src_shift - dst_shift)), dst_shift);
    if (n <= dst_shift) return;
    n -= dst_shift;
    src_shift -= dst_shift;
    dst_ptr--;
  }
  /* The next cell in the write frame to be filled begins at the boundary of a UWORD. */

  /* :TODO: Use static analysis to limit the total amount of copied memory. */
  if (0 == src_shift % UWORD_BIT) {
    /* The next cell in the read frame to be filled also begins at the boundary of a UWORD.
     * We can use 'memcpy' to copy data in bulk.
     */
    size_t m = ROUND_UWORD(n);
    /* If we went through the previous 'if (dst_shift)' block then 'src_shift == 0' and we need to decrement src_ptr.
     * If we did not go through the previous 'if (dst_shift)' block then 'src_shift == UWORD_BIT'
     * and we do not need to decrement src_ptr.
     * We have folded this conditional decrement into the equation applied to 'src_ptr' below.
     */
    memcpy(dst_ptr - (m - 1), src_ptr - (m - src_shift / UWORD_BIT), m * sizeof(UWORD));
  } else {
    while(1) {
      /* Fill the write frame's UWORD by copying the LSBs of the read frame's current UWORD
       * to the MSBs of the write frame's current UWORD,
       * and copy the MSBs of the read frame's next UWORD to the LSBs of the write frame's current UWORD.
       * Then move both the src_ptr and dst_ptr to their next UWORDs.
       */
      *dst_ptr = (UWORD)(LSBkeep(*src_ptr, src_shift) << (UWORD_BIT - src_shift));
      if (n <= src_shift) return;

      *dst_ptr |= (UWORD)(*(src_ptr - 1) >> src_shift);
      if (n <= UWORD_BIT) return;
      n -= UWORD_BIT;
      dst_ptr--; src_ptr--;
    }
  }
}

/* Given a write frame and a read frame, copy 'n' cells from after the read frame's cursor to after the write frame's cursor,
 * and then advance the write frame's cursor by 'n'.
 * Cells in front of the '*dst's cursor's final position may be overwritten.
 *
 * Precondition: '*dst' is a valid write frame for 'n' more cells;
 *               '*src' is a valid read frame for 'n' more cells;
 */
static void copyBits(frameItem* dst, const frameItem* src, size_t n) {
  if (0 == n) return;
  copyBitsHelper(dst, src, n);
  dst->offset -= n;
}

/* Given the contents of a 'witness v : A |- B' expression, write the value 'v' to a write frame and advance its cursor.
 * Cells in front of the '*dst's cursor's final position may be overwritten.
 *
 * Precondition: '*dst' is a valid write frame for 'bitSize(B)' more cells;
 *               'data' is a compact bitstring representation of a value 'v : B';
 *               'type_dag[typeIx]' is a type dag for the type B.
 */
static void writeWitness(frameItem* dst, const bitstring* data, size_t typeIx, type* type_dag) {
  size_t cur = typeSkip(typeIx, type_dag);
  size_t offset = data->offset;
  bool calling = true;
  type_dag[cur].back = 0;
  while (cur) {
    if (SUM == type_dag[cur].kind) {
      assert(calling);

      /* Write one bit to the write frame and then skip over any padding bits. */
      bool bit = 1 & (data->arr[offset/CHAR_BIT] >> (CHAR_BIT - 1 - offset % CHAR_BIT));
      offset++;
      writeBit(dst, bit);
      skip(dst, pad(bit, type_dag[type_dag[cur].typeArg[0]].bitSize, type_dag[type_dag[cur].typeArg[1]].bitSize));

      size_t next = typeSkip(type_dag[cur].typeArg[bit], type_dag);
      if (next) {
        type_dag[next].back = type_dag[cur].back;
        cur = next;
      } else {
        cur = type_dag[cur].back;
        calling = false;
      }
    } else {
      assert(PRODUCT == type_dag[cur].kind);
      size_t next;
      if (calling) {
        next = typeSkip(type_dag[cur].typeArg[0], type_dag);
        if (next) {
          /* Travese the first element of the product type, if it has any data. */
          type_dag[next].back = cur;
          cur = next;
          continue;
        }
      }
      next = typeSkip(type_dag[cur].typeArg[1], type_dag);
      if (next) {
        /* Travese the second element of the product type, if it has any data. */
        type_dag[next].back = type_dag[cur].back;
        cur = next;
        calling = true;
      } else {
        cur = type_dag[cur].back;
        calling = false;
      }
    }
  }
  /* Note: Above we use 'typeSkip' to skip over long chains of products against trivial types
   * This avoids a potential DOS vulnerability where a DAG of deeply nested products of unit types with sharing is traversed,
   * taking exponential time.
   * While traversing still could take exponential time in terms of the size of the type's dag,
   * at least one bit of witness data is required per PRODUCT type encountered.
   * This ought to limit the total number of times through the above loop to no more that 3 * data.len.
   */
}

/* Our representation of the Bit Machine state consists of a gap buffer of 'frameItem's.
 * The gap buffer is allocated at 'frame'
 * The read frames of the gap buffer extends from the beginning of the buffer to '.activeReadFrame'.
 * The write frames extend from the end of the buffer down to '.activeWriteFrame'.
 */
typedef struct evalState {
  frameItem* activeReadFrame;
  frameItem* activeWriteFrame;
} evalState;

/* 'call' is an item is used to track the "call stack" of the Bit Machine during evaluation.
 * Each call stack frame holds the call's TCO state and where to return to after the call.
 */
typedef struct call {
  size_t return_to;
  union {
    bool tcoOn;
    bool bit; /* Scratch space used by the 'CASE' combinator. */
  };
} call;

/* Starting from the Bit Machine 'state',
 * run the machine with the TCO (off) program generated by the well-typed Simplicity expression 'dag[len]' of type 'A |- B'.
 * If an 'assertr' or 'assertl' combinator fails, return 'false', otherwise return 'true'.
 *
 * The 'state' of the Bit Machine is whatever the state is after the last successfully executed Bit Machine instruction.
 *
 * ** No heap allocations are allowed in 'runTCO' or any of its subroutines. **
 *
 * Precondition: The gap between 'state.activeReadFrame' and 'state.activeWriteFrame' is sufficient for execution of 'dag'
 *                 and the values are initialized;
 *               The gap between 'activeReadFrame(state)->edge' and 'activeWriteFrame(state)->edge'
 *                 is sufficent for execution of 'dag';
 *               '*activeReadFrame(state)' is a valid read frame for 'bitSize(A)' more cells.
 *               '*activeWriteFrame(state)' is a valid write frame for 'bitSize(B)' more cells.
 *               call stack[len];
 *               dag_node dag[len] and 'dag' is well-typed with 'type_dag';
 *               if 'dag[len]' represents a Simplicity expression with primitives then 'NULL != env';
 */
static bool runTCO(evalState state, call* stack, const dag_node* dag, type* type_dag, size_t len, const txEnv* env) {
/* The program counter, 'pc', is the current combinator being interpreted.  */
  size_t pc = len - 1;

/* 'stack' represents the interpreter's call stack.
 * However, the stack is not directly represented as an array.
 * Instead, the bottom of the call stack is located at 'stack[len - 1]' and the top of the call stack is located at 'stack[pc]'.
 * The intermediate call stack items are somewhere between 'pc' and 'len - 1'.
 * The each call stack item references the one below it through the 'stack[i].return_to' values.
 * The bottom of the stack's '.return_to' value is set to 'len' which is an out-of-bounds index.
 *
 * During CALLs, a new 'stack[i]' value is created where 'i' is index of the combinator being called,
 * and 'stack[i].return_to' is set to the current 'pc' value.
 * During TAIL_CALLs, 'stack[i].return_to' is instead set to the 'stack[pc].return_to' value.
 * During RETURNs, the 'pc' is set to the 'stack[pc].return_to' value.
 * TAIL_CALLs allows for faster returns within the interpreter (unrelated to Simplicity's TCO),
 * skipping over intermediate combinators.
 */
  stack[pc] = (call){ .return_to = len, .tcoOn = false };

/* 'calling' lets us know if we are entering a CALL or returning from a CALL. */
  bool calling = true;

  /* :TODO: Use static analysis to limit the number of iterations through this loop. */
  while(pc < len) {
    tag_t tag = dag[pc].tag;
    assert(state.activeReadFrame < state.activeWriteFrame);
    assert(state.activeReadFrame->edge <= state.activeWriteFrame->edge);
    if (dag[pc].jet) {
      if(!dag[pc].jet(state.activeWriteFrame, *state.activeReadFrame, env)) return false;
      /* Like IDEN and WITNESS, we want to "fallthrough" to the UNIT case. */
      tag = UNIT;
    }
    switch (tag) {
     case COMP:
      if (calling) {
        /* NEW_FRAME(BITSIZE(B)) */
        *(state.activeWriteFrame - 1) = initWriteFrame(type_dag[COMP_B(dag, type_dag, pc)].bitSize, state.activeWriteFrame->edge);
        state.activeWriteFrame--;

        /* CALL(dag[pc].child[0], SAME_TCO) */
        stack[dag[pc].child[0]] = (call){ .return_to = pc, .tcoOn = stack[pc].tcoOn };
        pc = dag[pc].child[0];
      } else {
        /* MOVE_FRAME */
        assert(0 == state.activeWriteFrame->offset);
        memmove( state.activeReadFrame->edge, state.activeWriteFrame->edge
               , (size_t)((state.activeWriteFrame + 1)->edge - state.activeWriteFrame->edge) * sizeof(UWORD)
               );
        *(state.activeReadFrame + 1) = initReadFrame(type_dag[COMP_B(dag, type_dag, pc)].bitSize, state.activeReadFrame->edge);
        state.activeWriteFrame++; state.activeReadFrame++;

        /* TAIL_CALL(dag[pc].child[1], true) */
        calling = true;
        stack[dag[pc].child[1]] = (call){ .return_to = stack[pc].return_to, .tcoOn = true };
        pc = dag[pc].child[1];
      }
      break;
     case ASSERTL:
     case ASSERTR:
     case CASE:
      if (calling) {
        bool bit = peekBit(state.activeReadFrame);

        /* FWD(1 + PADL(A,B) when bit = 0; FWD(1 + PADR(A,B) when bit = 1 */
        forward(state.activeReadFrame, 1 + pad( bit
                                     , type_dag[CASE_A(dag, type_dag, pc)].bitSize
                                     , type_dag[CASE_B(dag, type_dag, pc)].bitSize));

        /* CONDITIONAL_TAIL_CALL(dag[pc].child[bit]); */
        stack[dag[pc].child[bit]] = (call)
          { .return_to = stack[pc].tcoOn ? stack[pc].return_to : pc
          , .tcoOn = stack[pc].tcoOn
          };

        /* Remember the bit we peeked at for the case when we return. */
        stack[pc].bit = bit;

        pc = dag[pc].child[bit];

      } else {
        /* BWD(1 + PADL(A,B) when bit = 0; BWD(1 + PADR(A,B) when bit = 1 */
        backward(state.activeReadFrame, 1 + pad( stack[pc].bit
                                      , type_dag[CASE_A(dag, type_dag, pc)].bitSize
                                      , type_dag[CASE_B(dag, type_dag, pc)].bitSize));

        /* RETURN; */
        pc = stack[pc].return_to;
      }
      break;
     case PAIR:
      if (calling) {
        /* CALL(dag[pc].child[0], false); */
        stack[dag[pc].child[0]] = (call){ .return_to = pc, .tcoOn = false };
        pc = dag[pc].child[0];
      } else {
        /* TAIL_CALL(dag[pc].child[1], SAME_TCO); */
        calling = true;
        stack[dag[pc].child[1]] = (call)
          { .return_to = stack[pc].return_to
          , .tcoOn = stack[pc].tcoOn
          };
        pc = dag[pc].child[1];
      }
      break;
     case DISCONNECT:
      if (calling) {
        /* NEW_FRAME(BITSIZE(WORD256 * A)) */
        *(state.activeWriteFrame - 1) = initWriteFrame(type_dag[DISCONNECT_W256A(dag, type_dag, pc)].bitSize,
                                                       state.activeWriteFrame->edge);
        state.activeWriteFrame--;

        /* WRITE_HASH(dag[dag[pc].child[1]].cmr) */
        write32s(state.activeWriteFrame, dag[dag[pc].child[1]].cmr.s, 8);

        /* COPY(BITSIZE(A)) */
        copyBits(state.activeWriteFrame, state.activeReadFrame, type_dag[DISCONNECT_A(dag, type_dag, pc)].bitSize);

        if (stack[pc].tcoOn) {
          /* DROP_FRAME */
          state.activeReadFrame--;
        }

        /* MOVE_FRAME */
        assert(0 == state.activeWriteFrame->offset);
        memmove( state.activeReadFrame->edge, state.activeWriteFrame->edge
               , (size_t)((state.activeWriteFrame + 1)->edge - state.activeWriteFrame->edge) * sizeof(UWORD)
               );
        *(state.activeReadFrame + 1) = initReadFrame(type_dag[DISCONNECT_W256A(dag, type_dag, pc)].bitSize,
                                                     state.activeReadFrame->edge);
        state.activeWriteFrame++; state.activeReadFrame++;

        /* NEW_FRAME(BITSIZE(B * C)) */
        *(state.activeWriteFrame - 1) = initWriteFrame(type_dag[DISCONNECT_BC(dag, type_dag, pc)].bitSize,
                                                       state.activeWriteFrame->edge);
        state.activeWriteFrame--;

        /* CALL(dag[pc].child[0], true) */
        stack[dag[pc].child[0]] = (call){ .return_to = pc, .tcoOn = true };
        pc = dag[pc].child[0];
      } else {
        /* MOVE_FRAME */
        assert(0 == state.activeWriteFrame->offset);
        memmove( state.activeReadFrame->edge, state.activeWriteFrame->edge
               , (size_t)((state.activeWriteFrame + 1)->edge - state.activeWriteFrame->edge) * sizeof(UWORD)
               );
        *(state.activeReadFrame + 1) = initReadFrame(type_dag[DISCONNECT_BC(dag, type_dag, pc)].bitSize,
                                                     state.activeReadFrame->edge);
        state.activeWriteFrame++; state.activeReadFrame++;

        /* COPY(BITSIZE(B)) */
        copyBits(state.activeWriteFrame, state.activeReadFrame, type_dag[DISCONNECT_B(dag, type_dag, pc)].bitSize);

        /* FWD(BITSIZE(B)) */
        forward(state.activeReadFrame, type_dag[DISCONNECT_B(dag, type_dag, pc)].bitSize);

        /* TAIL_CALL(dag[pc].child[1], true) */
        calling = true;
        stack[dag[pc].child[1]] = (call){ .return_to = stack[pc].return_to, .tcoOn = true };
        pc = dag[pc].child[1];
      }
      break;
     case INJL:
     case INJR:
      /* WRITE(0) when INJL; WRITE(1) when INJR */
      writeBit(state.activeWriteFrame, INJR == dag[pc].tag);

      /* SKIP(PADL(A,B)) when INJL; SKIP(PADR(A,B)) when INJR */
      skip(state.activeWriteFrame, pad( INJR == dag[pc].tag
                                 , type_dag[INJ_B(dag, type_dag, pc)].bitSize
                                 , type_dag[INJ_C(dag, type_dag, pc)].bitSize));
      /*@fallthrough@*/
     case TAKE:
      assert(calling);
      /* TAIL_CALL(dag[pc].child[0], SAME_TCO); */
      stack[dag[pc].child[0]] = (call)
        { .return_to = stack[pc].return_to
        , .tcoOn = stack[pc].tcoOn
        };
      pc = dag[pc].child[0];
      break;
     case DROP:
      if (calling) {
        /* FWD(BITSIZE(A)) */
        forward(state.activeReadFrame, type_dag[PROJ_A(dag, type_dag, pc)].bitSize);

        /* CONDITIONAL_TAIL_CALL(dag[pc].child[0]); */
        stack[dag[pc].child[0]] = (call)
          { .return_to = stack[pc].tcoOn ? stack[pc].return_to : pc
          , .tcoOn = stack[pc].tcoOn
          };
        pc = dag[pc].child[0];
      } else {
        /* BWD(BITSIZE(A)) */
        backward(state.activeReadFrame, type_dag[PROJ_A(dag, type_dag, pc)].bitSize);

        /* RETURN; */
        pc = stack[pc].return_to;
      }
      break;
     case IDEN:
     case WITNESS:
      if (IDEN == tag) {
        /* COPY(BITSIZE(A)) */
        copyBits(state.activeWriteFrame, state.activeReadFrame, type_dag[IDEN_A(dag, type_dag, pc)].bitSize);
      } else {
        assert(WITNESS == tag);
        writeWitness(state.activeWriteFrame, &dag[pc].witness, WITNESS_B(dag, type_dag, pc), type_dag);
      }
      /*@fallthrough@*/
     case UNIT:
      assert(calling);
      if (stack[pc].tcoOn) {
        /* DROP_FRAME */
        state.activeReadFrame--;
      }

      /* RETURN; */
      calling = false;
      pc = stack[pc].return_to;
      break;
     case HIDDEN: return false; /* We have failed an 'ASSERTL' or 'ASSERTR' combinator. */
     case JET:
      /* Jets (and primitives) should already have been processed by dag[i].jet already */
      assert(false);
      UNREACHABLE;
    }
  }
  assert(pc == len);
  return true;
}

/* This structure is used by the static analysis that computes  bounds on the working memory that suffices for
 * the Simplicity interpreter.
 */
typedef struct memBound {
  size_t extraCellsBoundTCO[2];
  size_t extraStackBound[2]; /* extraStackBound[0] is for TCO off and extraStackBound[1] is for TCO on */
} memBound;

/* :TODO: Document extraStackBoundTCO in the Tech Report (and implement it in Haskell) */
/* Given a well-typed dag representing a Simplicity expression, set '*dag_bound' to the memory requirement for evaluation.
 * For all 'i', 0 <= 'i' < 'len', compute 'bound[i].extraCellsBoundTCO' and 'bound[i].extraStackBoundTCO'
 * for the subexpression denoted by the slice
 *
 *     (dag_nodes[i + 1])dag.
 *
 * Then '*dag_bound' is set to 'bound[len-1]'.
 *
 * If 'malloc' fails, then return false.
 *
 * Precondition: NULL != dag_bound
 *               dag_node dag[len] and 'dag' is well-typed with 'type_dag'.
 * Postcondition: if the result is 'true'
 *                then 'max(dag_bound->extraCellsBoundTCO[0], dag_bound->extraCellsBoundTCO[1]) == SIZE_MAX'.
 *                       or 'dag_bound->extraCellsBoundTCO' characterizes the number of UWORDs needed
 *                         for the frames allocated during evaluation of 'dag';
 *                     'dag_bound->extraStackBoundTCO[0] == SIZE_MAX'
 *                       or 'dag_bound->extraStackBoundTCO[0]' bounds the the number of stack frames needed
 *                          during execution of 'dag';
 */
static bool computeEvalTCOBound(memBound *dag_bound, const dag_node* dag, const type* type_dag, const size_t len) {
  memBound* bound = len <= SIZE_MAX / sizeof(memBound)
                  ? malloc(len * sizeof(memBound))
                  : NULL;
  if (!bound) return false;

  for (size_t i = 0; i < len; ++i) {
    switch (dag[i].tag) {
     case ASSERTL:
     case ASSERTR:
     case CASE:
      bound[i].extraCellsBoundTCO[0] = max( bound[dag[i].child[0]].extraCellsBoundTCO[0]
                                          , bound[dag[i].child[1]].extraCellsBoundTCO[0] );
      bound[i].extraCellsBoundTCO[1] = max( bound[dag[i].child[0]].extraCellsBoundTCO[1]
                                          , bound[dag[i].child[1]].extraCellsBoundTCO[1] );

      bound[i].extraStackBound[0] = max( bound[dag[i].child[0]].extraStackBound[0]
                                       , bound[dag[i].child[1]].extraStackBound[0] );
      bound[i].extraStackBound[1] = max( bound[dag[i].child[0]].extraStackBound[1]
                                       , bound[dag[i].child[1]].extraStackBound[1] );
      break;
     case DISCONNECT:
      /* :TODO: replace this check with a consensus critical limit. */
      if (SIZE_MAX <= type_dag[DISCONNECT_W256A(dag, type_dag, i)].bitSize ||
          SIZE_MAX <= type_dag[DISCONNECT_BC(dag, type_dag, i)].bitSize) {
        /* 'BITSIZE(WORD256 * A)' or 'BITSIZE(B * C)' has exceeded our limits. */
        bound[i].extraCellsBoundTCO[0] = SIZE_MAX;
        bound[i].extraCellsBoundTCO[1] = SIZE_MAX;
      } else {
        bound[i].extraCellsBoundTCO[1] = ROUND_UWORD(type_dag[DISCONNECT_W256A(dag, type_dag, i)].bitSize);
        bound[i].extraCellsBoundTCO[0] = max(
          bounded_add(
            ROUND_UWORD(type_dag[DISCONNECT_BC(dag, type_dag, i)].bitSize),
            max( bounded_add(bound[i].extraCellsBoundTCO[1], bound[dag[i].child[0]].extraCellsBoundTCO[1])
               , max(bound[dag[i].child[0]].extraCellsBoundTCO[0], bound[dag[i].child[1]].extraCellsBoundTCO[1]))),
          bound[dag[i].child[1]].extraCellsBoundTCO[0]);
      }
      bound[i].extraStackBound[0] = bound[i].extraStackBound[1]
                                  = max( bounded_add(1, bound[dag[i].child[0]].extraStackBound[1])
                                       , bound[dag[i].child[1]].extraStackBound[1]);
      bounded_inc(&bound[i].extraStackBound[0]);
      break;
     case COMP:
      /* :TODO: replace this check with a consensus critical limit. */
      if (SIZE_MAX <= type_dag[COMP_B(dag, type_dag, i)].bitSize) {
        /* 'BITSIZE(B)' has exceeded our limits. */
        bound[i].extraCellsBoundTCO[0] = SIZE_MAX;
        bound[i].extraCellsBoundTCO[1] = SIZE_MAX;
      } else {
        size_t scratch = ROUND_UWORD(type_dag[COMP_B(dag, type_dag, i)].bitSize);
        bound[i].extraCellsBoundTCO[0] = max( bounded_add( scratch
                                                         , max( bound[dag[i].child[0]].extraCellsBoundTCO[0]
                                                              , bound[dag[i].child[1]].extraCellsBoundTCO[1] ))
                                            , bound[dag[i].child[1]].extraCellsBoundTCO[0] );
        bound[i].extraCellsBoundTCO[1] = bounded_add(scratch, bound[dag[i].child[0]].extraCellsBoundTCO[1]);
      }
      bound[i].extraStackBound[0] = max( bound[dag[i].child[0]].extraStackBound[0]
                                       , bound[dag[i].child[1]].extraStackBound[1] );
      bounded_inc(&bound[i].extraStackBound[0]);
      bound[i].extraStackBound[1] = max( bounded_add(1, bound[dag[i].child[0]].extraStackBound[1])
                                       , bound[dag[i].child[1]].extraStackBound[1] );
      break;
     case PAIR:
      bound[i].extraCellsBoundTCO[0] = bound[dag[i].child[1]].extraCellsBoundTCO[0];
      bound[i].extraCellsBoundTCO[1] = max( bound[dag[i].child[0]].extraCellsBoundTCO[0]
                                          , max( bound[dag[i].child[0]].extraCellsBoundTCO[1]
                                               , bound[dag[i].child[1]].extraCellsBoundTCO[1] ));

      bound[i].extraStackBound[0] = max( bound[dag[i].child[0]].extraStackBound[0]
                                       , bound[dag[i].child[1]].extraStackBound[0] );
      bound[i].extraStackBound[1] = max( bound[dag[i].child[0]].extraStackBound[0]
                                       , bound[dag[i].child[1]].extraStackBound[1] );
      break;
     case INJL:
     case INJR:
     case TAKE:
     case DROP:
      bound[i].extraCellsBoundTCO[0] = bound[dag[i].child[0]].extraCellsBoundTCO[0];
      bound[i].extraCellsBoundTCO[1] = bound[dag[i].child[0]].extraCellsBoundTCO[1];
      bound[i].extraStackBound[0] = bound[dag[i].child[0]].extraStackBound[0];
      bound[i].extraStackBound[1] = bound[dag[i].child[0]].extraStackBound[1];
      break;
     case IDEN:
     case UNIT:
     case HIDDEN:
     case WITNESS:
     case JET:
      bound[i].extraCellsBoundTCO[0] = bound[i].extraCellsBoundTCO[1] = 0;
      bound[i].extraStackBound[0] = bound[i].extraStackBound[1] = 0;
    }
  }

  *dag_bound = bound[len-1];
  free(bound);
  return true;
}

/* Run the Bit Machine on the well-typed Simplicity expression 'dag[len]'.
 * If 'NULL != input', initialize the active read frame's data with 'input[ROUND_UWORD(inputSize)]'.
 *
 * If malloc fails, return 'false', otherwise return 'true'.
 * If static analysis results determines the bound on memory allocation requirements exceed the allowed limits,
 * '*evalSuccess' is set to 'false'.
 * If during execution an 'assertr' or 'assertl' combinator fails, '*evalSuccess' is set to 'false'
 * Otherwise '*evalSuccess' is set to 'true'.
 *
 * If the function returns 'true' and '*evalSuccess' and 'NULL != output',
 * copy the final active write frame's data to 'output[roundWord(outputSize)]'.
 *
 * Precondition: NULL != evalSuccess
 *               dag_node dag[len] and 'dag' is well-typed with 'type_dag' of type A |- B;
 *               inputSize == bitSize(A);
 *               outputSize == bitSize(B);
 *               output == NULL or UWORD output[ROUND_UWORD(outputSize)];
 *               input == NULL or UWORD input[ROUND_UWORD(inputSize)];
 *               if 'dag[len]' represents a Simplicity expression with primitives then 'NULL != env';
 */
bool evalTCOExpression( bool *evalSuccess, UWORD* output, size_t outputSize, const UWORD* input, size_t inputSize
                      , const dag_node* dag, type* type_dag, size_t len, const txEnv* env
                      ) {
  memBound bound;
  if (!computeEvalTCOBound(&bound, dag, type_dag, len)) return false;

  size_t cellsBound = bounded_add( bounded_add(ROUND_UWORD(inputSize), ROUND_UWORD(outputSize))
                                 , max(bound.extraCellsBoundTCO[0], bound.extraCellsBoundTCO[1])
                                 );
  size_t stackBound = bounded_add(bound.extraStackBound[0], 2);

  /* :TODO: add reasonable, consensus critical limits to cells and stack bounds */
  if (SIZE_MAX <= outputSize || SIZE_MAX <= inputSize || SIZE_MAX <= cellsBound || SIZE_MAX <= stackBound) {
    *evalSuccess = false;
    return true;
  }

  /* We use calloc for 'cells' because the frame data must be initialized before we can perform bitwise operations. */
  UWORD* cells = calloc(cellsBound ? cellsBound : 1, sizeof(UWORD));
  frameItem* frames = stackBound <= SIZE_MAX / sizeof(frameItem)
                    ? malloc(stackBound * sizeof(frameItem))
                    : NULL;
  call* stack = len <= SIZE_MAX / sizeof(call)
              ? malloc(len * sizeof(call))
              : NULL;

  const bool result = cells && frames && stack;
  if (result) {
    if (input) memcpy(cells, input, ROUND_UWORD(inputSize) * sizeof(UWORD));

    evalState state =
      { .activeReadFrame = frames
      , .activeWriteFrame = frames + (stackBound - 1)
      };
    *(state.activeReadFrame) = initReadFrame(inputSize, cells);
    *(state.activeWriteFrame) = initWriteFrame(outputSize, cells + cellsBound);

    *evalSuccess = runTCO(state, stack, dag, type_dag, len, env);

    if (*evalSuccess && output) {
      memcpy(output, state.activeWriteFrame->edge, ROUND_UWORD(outputSize) * sizeof(UWORD));
    }
  }

  free(stack);
  free(frames);
  free(cells);
  return result;
}
