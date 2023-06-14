#include "eval.h"

#include <string.h>
#include <stdlib.h>
#include "bounded.h"
#include "limitations.h"
#include "simplicity_assert.h"

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
  simplicity_debug_assert(n <= frame->offset);
  frame->offset -= n;
}

/* Given a write frame, advance its cursor by 'n' cells.
 *
 * Precondition: n <= frame->offset
 */
static void skip(frameItem* frame, size_t n) {
  simplicity_debug_assert(n <= frame->offset);
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

/* Given a compact bit representation of a value 'v : B', write the value 'v' to a write frame, skipping cells as needed
 * and advance its cursor.
 * Cells in front of the '*dst's cursor's final position may be overwritten.
 *
 * :TODO: Consider writing an optimized version of this function for word type 'TWO^(2^n)' which is a very common case and
 * doesn't need any skipping of cells.
 *
 * Precondition: '*dst' is a valid write frame for 'bitSize(B)' more cells;
 *               'compactValue' is a compact bitstring representation of a value 'v : B';
 *               'type_dag[typeIx]' is a type dag for the type B.
 */
static void writeValue(frameItem* dst, const bitstring* compactValue, size_t typeIx, type* type_dag) {
  size_t cur = typeSkip(typeIx, type_dag);
  size_t offset = 0;
  bool calling = true;
  type_dag[cur].back = 0;
  while (cur) {
    if (SUM == type_dag[cur].kind) {
      simplicity_debug_assert(calling);

      /* Write one bit to the write frame and then skip over any padding bits. */
      bool bit = getBit(compactValue, offset);
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
      simplicity_debug_assert(PRODUCT == type_dag[cur].kind);
      size_t next;
      if (calling) {
        next = typeSkip(type_dag[cur].typeArg[0], type_dag);
        if (next) {
          /* Traverse the first element of the product type, if it has any data. */
          type_dag[next].back = cur;
          cur = next;
          continue;
        }
      }
      next = typeSkip(type_dag[cur].typeArg[1], type_dag);
      if (next) {
        /* Traverse the second element of the product type, if it has any data. */
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
   * This ought to limit the total number of times through the above loop to no more that 3 * compactValue->len.
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
 * Each call stack frame remembers where to return to after the call and a set of flags to hold various bits of state.
 */
typedef struct call {
  size_t return_to;
  flags_type flags;
} call;

#define FLAG_TCO        0x01 // Whether TCO is on (1) or off (0).
#define FLAG_LAST_CASE  0x02 // For case combinators, last branch executed was right (1) or left (0).
#define FLAG_EXEC       0x10 // Whether this combinator has ever been executed (1) or not (0).
#define FLAG_CASE_LEFT  0x20 // For case combinators, whether the left branch has ever been executed (1) or not (0).
#define FLAG_CASE_RIGHT 0x40 // For case combinators, whether the right branch has ever been executed (1) or not (0).

static inline bool get_tco_flag(const call *stack) {
  return FLAG_TCO == (stack->flags & FLAG_TCO);
}

static inline void set_tco_flag(call *stack, bool flag) {
  if (flag) {
     stack->flags |= FLAG_TCO;
  } else {
     stack->flags &= (flags_type)(~FLAG_TCO);
  }
}

static inline bool get_case_last_flag(const call *stack) {
  return FLAG_LAST_CASE == (stack->flags & FLAG_LAST_CASE);
}

static inline void set_case_last_flag(call *stack, bool flag) {
  if (flag) {
     stack->flags |= FLAG_LAST_CASE;
  } else {
     stack->flags &= (flags_type)(~FLAG_LAST_CASE);
  }
}

/* Starting from the Bit Machine 'state',
 * run the machine with the TCO (off) program generated by the well-typed Simplicity expression 'dag[len]' of type 'A |- B'.
 * If some jet execution fails, returns 'SIMPLICITY_ERR_EXEC_JET'.
 * If some 'assertr' or 'assertl' combinator fails, returns 'SIMPLICITY_ERR_EXEC_ASSERT'.
 * Otherwise returns 'SIMPLICITY_NO_ERROR'.
 *
 * The 'state' of the Bit Machine is whatever the state is after the last successfully executed Bit Machine instruction.
 *
 * ** No heap allocations are allowed in 'runTCO' or any of its subroutines. **
 *
 * Precondition: The gap between 'state.activeReadFrame' and 'state.activeWriteFrame' is sufficient for execution of 'dag'
 *                 and the values are initialized;
 *               The gap between 'activeReadFrame(state)->edge' and 'activeWriteFrame(state)->edge'
 *                 is sufficient for execution of 'dag';
 *               '*activeReadFrame(state)' is a valid read frame for 'bitSize(A)' more cells.
 *               '*activeWriteFrame(state)' is a valid write frame for 'bitSize(B)' more cells.
 *               call stack[len];
 *               for all i < len, stack[i].flags = 0;
 *               dag_node dag[len] and 'dag' is well-typed with 'type_dag';
 *               if 'dag[len]' represents a Simplicity expression with primitives then 'NULL != env';
 */
static simplicity_err runTCO(evalState state, call* stack, const dag_node* dag, type* type_dag, size_t len, const txEnv* env) {
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
  stack[pc].return_to = len;
  set_tco_flag(&stack[pc], false);

/* 'calling' lets us know if we are entering a CALL or returning from a CALL. */
  bool calling = true;

  /* :TODO: Use static analysis to limit the number of iterations through this loop. */
  while(pc < len) {
    stack[pc].flags |= FLAG_EXEC;
    tag_t tag = dag[pc].tag;
    simplicity_debug_assert(state.activeReadFrame < state.activeWriteFrame);
    simplicity_debug_assert(state.activeReadFrame->edge <= state.activeWriteFrame->edge);
    if (dag[pc].jet) {
      if(!dag[pc].jet(state.activeWriteFrame, *state.activeReadFrame, env)) return SIMPLICITY_ERR_EXEC_JET;
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
        stack[dag[pc].child[0]].return_to = pc;
        set_tco_flag(&stack[dag[pc].child[0]], get_tco_flag(&stack[pc]));
        pc = dag[pc].child[0];
      } else {
        /* MOVE_FRAME */
        simplicity_debug_assert(0 == state.activeWriteFrame->offset);
        memmove( state.activeReadFrame->edge, state.activeWriteFrame->edge
               , (size_t)((state.activeWriteFrame + 1)->edge - state.activeWriteFrame->edge) * sizeof(UWORD)
               );
        *(state.activeReadFrame + 1) = initReadFrame(type_dag[COMP_B(dag, type_dag, pc)].bitSize, state.activeReadFrame->edge);
        state.activeWriteFrame++; state.activeReadFrame++;

        /* TAIL_CALL(dag[pc].child[1], true) */
        calling = true;
        stack[dag[pc].child[1]].return_to = stack[pc].return_to;
        set_tco_flag(&stack[dag[pc].child[1]], true);
        pc = dag[pc].child[1];
      }
      break;
     case ASSERTL:
     case ASSERTR:
     case CASE:
      if (calling) {
        bool bit = peekBit(state.activeReadFrame);

        if (bit) {
           stack[pc].flags |= FLAG_CASE_RIGHT;
        } else {
           stack[pc].flags |= FLAG_CASE_LEFT;
        }

        /* FWD(1 + PADL(A,B) when bit = 0; FWD(1 + PADR(A,B) when bit = 1 */
        forward(state.activeReadFrame, 1 + pad( bit
                                     , type_dag[CASE_A(dag, type_dag, pc)].bitSize
                                     , type_dag[CASE_B(dag, type_dag, pc)].bitSize));

        /* CONDITIONAL_TAIL_CALL(dag[pc].child[bit]); */
        stack[dag[pc].child[bit]].return_to = get_tco_flag(&stack[pc]) ? stack[pc].return_to : pc;
        set_tco_flag(&stack[dag[pc].child[bit]], get_tco_flag(&stack[pc]));

        /* Remember the bit we peeked at for the case when we return. */
        set_case_last_flag(&stack[pc], bit);

        pc = dag[pc].child[bit];
      } else {
        /* BWD(1 + PADL(A,B) when bit = 0; BWD(1 + PADR(A,B) when bit = 1 */
        backward(state.activeReadFrame, 1 + pad( get_case_last_flag(&stack[pc])
                                      , type_dag[CASE_A(dag, type_dag, pc)].bitSize
                                      , type_dag[CASE_B(dag, type_dag, pc)].bitSize));

        /* RETURN; */
        pc = stack[pc].return_to;
      }
      break;
     case PAIR:
      if (calling) {
        /* CALL(dag[pc].child[0], false); */
        stack[dag[pc].child[0]].return_to = pc;
        set_tco_flag(&stack[dag[pc].child[0]], false);
        pc = dag[pc].child[0];
      } else {
        /* TAIL_CALL(dag[pc].child[1], SAME_TCO); */
        calling = true;
        stack[dag[pc].child[1]].return_to = stack[pc].return_to;
        set_tco_flag(&stack[dag[pc].child[1]], get_tco_flag(&stack[pc]));
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

        if (get_tco_flag(&stack[pc])) {
          /* DROP_FRAME */
          state.activeReadFrame--;
        }

        /* MOVE_FRAME */
        simplicity_debug_assert(0 == state.activeWriteFrame->offset);
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
        stack[dag[pc].child[0]].return_to = pc;
        set_tco_flag(&stack[dag[pc].child[0]], true);
        pc = dag[pc].child[0];
      } else {
        /* MOVE_FRAME */
        simplicity_debug_assert(0 == state.activeWriteFrame->offset);
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
        stack[dag[pc].child[1]].return_to = stack[pc].return_to;
        set_tco_flag(&stack[dag[pc].child[1]], true);
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
      simplicity_debug_assert(calling);
      /* TAIL_CALL(dag[pc].child[0], SAME_TCO); */
      stack[dag[pc].child[0]].return_to = stack[pc].return_to;
      set_tco_flag(&stack[dag[pc].child[0]], get_tco_flag(&stack[pc]));
      pc = dag[pc].child[0];
      break;
     case DROP:
      if (calling) {
        /* FWD(BITSIZE(A)) */
        forward(state.activeReadFrame, type_dag[PROJ_A(dag, type_dag, pc)].bitSize);

        /* CONDITIONAL_TAIL_CALL(dag[pc].child[0]); */
        stack[dag[pc].child[0]].return_to = get_tco_flag(&stack[pc]) ? stack[pc].return_to : pc;
        set_tco_flag(&stack[dag[pc].child[0]], get_tco_flag(&stack[pc]));
        pc = dag[pc].child[0];
      } else {
        /* BWD(BITSIZE(A)) */
        backward(state.activeReadFrame, type_dag[PROJ_A(dag, type_dag, pc)].bitSize);

        /* RETURN; */
        pc = stack[pc].return_to;
      }
      break;
     case IDEN:
     case WORD:
     case WITNESS:
      if (IDEN == tag) {
        /* COPY(BITSIZE(A)) */
        copyBits(state.activeWriteFrame, state.activeReadFrame, type_dag[IDEN_A(dag, type_dag, pc)].bitSize);
      } else {
        writeValue(state.activeWriteFrame, &dag[pc].compactValue, dag[pc].targetType, type_dag);
      }
      /*@fallthrough@*/
     case UNIT:
      simplicity_debug_assert(calling);
      if (get_tco_flag(&stack[pc])) {
        /* DROP_FRAME */
        state.activeReadFrame--;
      }

      /* RETURN; */
      calling = false;
      pc = stack[pc].return_to;
      break;
     case HIDDEN: return SIMPLICITY_ERR_EXEC_ASSERT; /* We have failed an 'ASSERTL' or 'ASSERTR' combinator. */
     case JET:
      /* Jets (and primitives) should already have been processed by dag[i].jet already */
      SIMPLICITY_UNREACHABLE;
    }
  }
  simplicity_assert(pc == len);

  return SIMPLICITY_NO_ERROR;
}

/* Inspects the stack contents after a successful runTCO execution to verify anti-DOS properties:
 * 1. If 'checks' includes 'CHECK_EXEC', then check that all non-HIDDEN dag nodes were executed at least once.
 * 2. If 'checks' includes 'CHECK_CASE', then check that both branches of every CASE node were executed.
 *
 * If these are violated, it means that the dag had unpruned nodes.
 *
 * Returns 'SIMPLICITY_ERR_ANTIDOS' if any of the anti-DOS checks fail.
 * Otherwise returns 'SIMPLICITY_NO_ERR'.
 *
 * Precondition: call stack[len];
 *               dag_node dag[len];
 */
static simplicity_err antiDos(flags_type checks, const call* stack, const dag_node* dag, size_t len) {
  static_assert(CHECK_EXEC == FLAG_EXEC, "CHECK_EXEC does not match FLAG_EXEC");
  static_assert(CHECK_CASE == (FLAG_CASE_LEFT | FLAG_CASE_RIGHT), "CHECK_CASE does not match FLAG_CASE");
  simplicity_assert(CHECK_CASE == (checks & CHECK_CASE) || 0 == (checks & CHECK_CASE));

  if (!checks) return SIMPLICITY_NO_ERROR;

  for(size_t i = 0; i < len; ++i) {
    /* All non-HIDDEN nodes must be executed at least once. */
    /* Both branches of every case combinator must be executed at least once. */
    flags_type test_flags = (HIDDEN != dag[i].tag ? CHECK_EXEC : 0)
                          | (CASE == dag[i].tag ? CHECK_CASE : 0);

    /* Only enable requested checks */
    test_flags &= checks;
    if (test_flags != (test_flags & stack[i].flags)) {
      return SIMPLICITY_ERR_ANTIDOS;
    }
  }

  return SIMPLICITY_NO_ERROR;
}

/* This structure is used by the static analysis that computes  bounds on the working memory that suffices for
 * the Simplicity interpreter.
 */
typedef struct memBound {
  ubounded extraCellsBound[2];
  ubounded extraUWORDBound[2];
  ubounded extraFrameBound[2]; /* extraStackBound[0] is for TCO off and extraStackBound[1] is for TCO on */
  ubounded cost;
} memBound;

/* :TODO: Document extraFrameBound in the Tech Report (and implement it in Haskell) */
/* Given a well-typed dag representing a Simplicity expression, set '*dag_bound' to the memory and CPU requirements for evaluation.
 * For all 'i', 0 <= 'i' < 'len', compute 'bound[i]' fields for the subexpression denoted by the slice
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
 *                then 'dag_bound->cost == BOUNDED_MAX' or 'dag_bound->const' bounds the dags CPU cost measured in milli weight units
 *                 and 'max(dag_bound->extraCellsBound[0], dag_bound->extraCellsBound[1]) == BOUNDED_MAX'
 *                     or 'dag_bound->extraCellsBound' characterizes the number of cells needed during evaluation of 'dag'
 *                        and 'dag_bound->extraUWORDBound' characterizes the number of UWORDs needed
 *                              for the frames allocated during evaluation of 'dag'
 *                        and 'dag_bound->extraFrameBound[0]' bounds the the number of stack frames needed during execution of 'dag'.
 *
 * :TODO: The cost calculations below are estimated and need to be replaced by experimental data.
 */
static bool computeEvalTCOBound(memBound *dag_bound, const dag_node* dag, const type* type_dag, const size_t len) {
  const ubounded overhead = 10 /* milli weight units */;
  static_assert(DAG_LEN_MAX <= SIZE_MAX / sizeof(memBound), "bound array too large.");
  static_assert(1 <= DAG_LEN_MAX, "DAG_LEN_MAX is zero.");
  static_assert(DAG_LEN_MAX - 1 <= UINT32_MAX, "bound array index does not fit in uint32_t.");
  simplicity_assert(1 <= len);
  simplicity_assert(len <= DAG_LEN_MAX);
  memBound* bound = malloc(len * sizeof(memBound));
  if (!bound) return false;

  for (size_t i = 0; i < len; ++i) {
    switch (dag[i].tag) {
     case ASSERTL:
     case ASSERTR:
     case CASE:
      bound[i].extraCellsBound[0] = max( bound[dag[i].child[0]].extraCellsBound[0]
                                       , bound[dag[i].child[1]].extraCellsBound[0] );
      bound[i].extraCellsBound[1] = max( bound[dag[i].child[0]].extraCellsBound[1]
                                       , bound[dag[i].child[1]].extraCellsBound[1] );

      bound[i].extraUWORDBound[0] = max( bound[dag[i].child[0]].extraUWORDBound[0]
                                       , bound[dag[i].child[1]].extraUWORDBound[0] );
      bound[i].extraUWORDBound[1] = max( bound[dag[i].child[0]].extraUWORDBound[1]
                                       , bound[dag[i].child[1]].extraUWORDBound[1] );

      bound[i].extraFrameBound[0] = max( bound[dag[i].child[0]].extraFrameBound[0]
                                       , bound[dag[i].child[1]].extraFrameBound[0] );
      bound[i].extraFrameBound[1] = max( bound[dag[i].child[0]].extraFrameBound[1]
                                       , bound[dag[i].child[1]].extraFrameBound[1] );
      bound[i].cost = bounded_add(overhead, max( bound[dag[i].child[0]].cost
                                               , bound[dag[i].child[1]].cost ));
      break;
     case DISCONNECT:
      if (BOUNDED_MAX <= type_dag[DISCONNECT_W256A(dag, type_dag, i)].bitSize ||
          BOUNDED_MAX <= type_dag[DISCONNECT_BC(dag, type_dag, i)].bitSize) {
        /* 'BITSIZE(WORD256 * A)' or 'BITSIZE(B * C)' has exceeded our limits. */
        bound[i].extraCellsBound[0] = BOUNDED_MAX;
        bound[i].extraCellsBound[1] = BOUNDED_MAX;
      } else {
        bound[i].extraCellsBound[1] = type_dag[DISCONNECT_W256A(dag, type_dag, i)].bitSize;
        bound[i].extraCellsBound[0] = max(
          bounded_add( type_dag[DISCONNECT_BC(dag, type_dag, i)].bitSize
                     , max( bounded_add(bound[i].extraCellsBound[1], bound[dag[i].child[0]].extraCellsBound[1])
                          , max(bound[dag[i].child[0]].extraCellsBound[0], bound[dag[i].child[1]].extraCellsBound[1]))),
          bound[dag[i].child[1]].extraCellsBound[0]);
      }
      bound[i].extraUWORDBound[1] = (ubounded)ROUND_UWORD(type_dag[DISCONNECT_W256A(dag, type_dag, i)].bitSize);
      bound[i].extraUWORDBound[0] = max(
          (ubounded)ROUND_UWORD(type_dag[DISCONNECT_BC(dag, type_dag, i)].bitSize) +
          max( bound[i].extraUWORDBound[1] + bound[dag[i].child[0]].extraUWORDBound[1]
             , max(bound[dag[i].child[0]].extraUWORDBound[0], bound[dag[i].child[1]].extraUWORDBound[1])),
        bound[dag[i].child[1]].extraUWORDBound[0]);

      bound[i].extraFrameBound[1] = max( bound[dag[i].child[0]].extraFrameBound[1] + 1
                                       , bound[dag[i].child[1]].extraFrameBound[1]);
      bound[i].extraFrameBound[0] = bound[i].extraFrameBound[1] + 1;
      bound[i].cost = bounded_add(overhead
                    , bounded_add(type_dag[DISCONNECT_W256A(dag, type_dag, i)].bitSize
                    , bounded_add(type_dag[DISCONNECT_W256A(dag, type_dag, i)].bitSize /* counted twice because the frame is both filled in and moved. */
                    , bounded_add(type_dag[DISCONNECT_BC(dag, type_dag, i)].bitSize
                    , bounded_add(bound[dag[i].child[0]].cost, bound[dag[i].child[1]].cost)))));
      break;
     case COMP:
      if (BOUNDED_MAX <= type_dag[COMP_B(dag, type_dag, i)].bitSize) {
        /* 'BITSIZE(B)' has exceeded our limits. */
        bound[i].extraCellsBound[0] = BOUNDED_MAX;
        bound[i].extraCellsBound[1] = BOUNDED_MAX;
      } else {
        bound[i].extraCellsBound[0] = max( bounded_add( type_dag[COMP_B(dag, type_dag, i)].bitSize
                                                      , max( bound[dag[i].child[0]].extraCellsBound[0]
                                                           , bound[dag[i].child[1]].extraCellsBound[1] ))
                                         , bound[dag[i].child[1]].extraCellsBound[0] );
        bound[i].extraCellsBound[1] = bounded_add( type_dag[COMP_B(dag, type_dag, i)].bitSize
                                                 , bound[dag[i].child[0]].extraCellsBound[1] );
      }
      bound[i].extraUWORDBound[0] = max( (ubounded)ROUND_UWORD(type_dag[COMP_B(dag, type_dag, i)].bitSize) +
                                         max( bound[dag[i].child[0]].extraUWORDBound[0]
                                            , bound[dag[i].child[1]].extraUWORDBound[1] )
                                       , bound[dag[i].child[1]].extraUWORDBound[0] );
      bound[i].extraUWORDBound[1] = (ubounded)ROUND_UWORD(type_dag[COMP_B(dag, type_dag, i)].bitSize)
                                  + bound[dag[i].child[0]].extraUWORDBound[1];

      bound[i].extraFrameBound[0] = max( bound[dag[i].child[0]].extraFrameBound[0]
                                       , bound[dag[i].child[1]].extraFrameBound[1] )
                                  + 1;
      bound[i].extraFrameBound[1] = max( bound[dag[i].child[0]].extraFrameBound[1] + 1
                                       , bound[dag[i].child[1]].extraFrameBound[1] );
      bound[i].cost = bounded_add(overhead
                    , bounded_add(type_dag[COMP_B(dag, type_dag, i)].bitSize
                    , bounded_add(bound[dag[i].child[0]].cost, bound[dag[i].child[1]].cost)));
      break;
     case PAIR:
      bound[i].extraCellsBound[0] = bound[dag[i].child[1]].extraCellsBound[0];
      bound[i].extraCellsBound[1] = max( bound[dag[i].child[0]].extraCellsBound[0]
                                       , max( bound[dag[i].child[0]].extraCellsBound[1]
                                            , bound[dag[i].child[1]].extraCellsBound[1] ));

      bound[i].extraUWORDBound[0] = bound[dag[i].child[1]].extraUWORDBound[0];
      bound[i].extraUWORDBound[1] = max( bound[dag[i].child[0]].extraUWORDBound[0]
                                       , max( bound[dag[i].child[0]].extraUWORDBound[1]
                                            , bound[dag[i].child[1]].extraUWORDBound[1] ));

      bound[i].extraFrameBound[0] = max( bound[dag[i].child[0]].extraFrameBound[0]
                                       , bound[dag[i].child[1]].extraFrameBound[0] );
      bound[i].extraFrameBound[1] = max( bound[dag[i].child[0]].extraFrameBound[0]
                                       , bound[dag[i].child[1]].extraFrameBound[1] );
      bound[i].cost = bounded_add(overhead, bounded_add( bound[dag[i].child[0]].cost
                                                       , bound[dag[i].child[1]].cost ));
      break;
     case INJL:
     case INJR:
     case TAKE:
     case DROP:
      bound[i].extraCellsBound[0] = bound[dag[i].child[0]].extraCellsBound[0];
      bound[i].extraCellsBound[1] = bound[dag[i].child[0]].extraCellsBound[1];

      bound[i].extraUWORDBound[0] = bound[dag[i].child[0]].extraUWORDBound[0];
      bound[i].extraUWORDBound[1] = bound[dag[i].child[0]].extraUWORDBound[1];

      bound[i].extraFrameBound[0] = bound[dag[i].child[0]].extraFrameBound[0];
      bound[i].extraFrameBound[1] = bound[dag[i].child[0]].extraFrameBound[1];
      bound[i].cost = bounded_add(overhead, bound[dag[i].child[0]].cost);
      break;
     case IDEN:
     case UNIT:
     case HIDDEN:
     case WITNESS:
     case JET:
     case WORD:
      bound[i].extraCellsBound[0] = bound[i].extraCellsBound[1] = 0;
      bound[i].extraUWORDBound[0] = bound[i].extraUWORDBound[1] = 0;
      bound[i].extraFrameBound[0] = bound[i].extraFrameBound[1] = 0;
      bound[i].cost = IDEN == dag[i].tag ? bounded_add(overhead, type_dag[IDEN_A(dag, type_dag, i)].bitSize)
                    : WITNESS == dag[i].tag || WORD == dag[i].tag ? bounded_add(overhead, type_dag[dag[i].targetType].bitSize)
                    : JET == dag[i].tag ? dag[i].cost
                    : HIDDEN == dag[i].tag ? 0
                    : overhead;
    }
  }

  *dag_bound = bound[len-1];
  free(bound);
  return true;
}

/* Run the Bit Machine on the well-typed Simplicity expression 'dag[len]'.
 * If 'NULL != input', initialize the active read frame's data with 'input[ROUND_UWORD(inputSize)]'.
 *
 * If malloc fails, returns 'SIMPLICITY_ERR_MALLOC'.
 * If static analysis results determines the bound on cpu requirements exceed the allowed budget, returns 'SIMPLICITY_ERR_EXEC_BUDGET'
 * If static analysis results determines the bound on memory allocation requirements exceed the allowed limits, returns 'SIMPLICITY_ERR_EXEC_MEMORY'
 * If during execution some jet execution fails, returns 'SIMPLICITY_ERR_EXEC_JET'.
 * If during execution some 'assertr' or 'assertl' combinator fails, returns 'SIMPLICITY_ERR_EXEC_ASESRT'.
 *
 * If none of the above conditions fail and 'NULL != output', then a copy the final active write frame's data is written to 'output[roundWord(outputSize)]'.
 *
 * If 'anti_dos_checks' includes the 'CHECK_EXEC' flag, and not every non-HIDDEN dag node is executed, returns 'SIMPLICITY_ERR_ANTIDOS'
 * If 'anti_dos_checks' includes the 'CHECK_CASE' flag, and not every case node has both branches executed, returns 'SIMPLICITY_ERR_ANTIDOS'
 *
 * Otherwise 'SIMPLICITY_NO_ERROR' is returned.
 *
 * Precondition: dag_node dag[len] and 'dag' is well-typed with 'type_dag' of type A |- B;
 *               inputSize == bitSize(A);
 *               outputSize == bitSize(B);
 *               output == NULL or UWORD output[ROUND_UWORD(outputSize)];
 *               input == NULL or UWORD input[ROUND_UWORD(inputSize)];
 *               budget <= BUDGET_MAX
 *               if 'dag[len]' represents a Simplicity expression with primitives then 'NULL != env';
 */
simplicity_err evalTCOExpression( flags_type anti_dos_checks, UWORD* output, ubounded outputSize, const UWORD* input, ubounded inputSize
                                , const dag_node* dag, type* type_dag, size_t len, ubounded budget, const txEnv* env
                                ) {
  simplicity_assert(1 <= len);
  simplicity_assert(len <= DAG_LEN_MAX);
  simplicity_assert(budget <= BUDGET_MAX);
  memBound bound;
  if (!computeEvalTCOBound(&bound, dag, type_dag, len)) return SIMPLICITY_ERR_MALLOC;

  const ubounded cellsBound = bounded_add( bounded_add(inputSize, outputSize)
                                         , max(bound.extraCellsBound[0], bound.extraCellsBound[1])
                                         );
  const ubounded UWORDBound = (ubounded)ROUND_UWORD(inputSize) + (ubounded)ROUND_UWORD(outputSize)
                          + max(bound.extraUWORDBound[0], bound.extraUWORDBound[1]);
  const ubounded frameBound = bound.extraFrameBound[0] + 2; /* add the initial input and output frames to the count. */

  static_assert(1 <= BOUNDED_MAX, "BOUNDED_MAX is zero.");
  static_assert(BUDGET_MAX <= (BOUNDED_MAX - 1) / 1000, "BUDGET_MAX is too large.");
  static_assert(CELLS_MAX < BOUNDED_MAX, "CELLS_MAX is too large.");
  if (budget * 1000 < bound.cost) return SIMPLICITY_ERR_EXEC_BUDGET;
  if (CELLS_MAX < cellsBound) return SIMPLICITY_ERR_EXEC_MEMORY;

  /* frameBound is at most 2*len. */
  static_assert(DAG_LEN_MAX <= SIZE_MAX / 2, "2*DAG_LEN_MAX does not fit in size_t.");
  simplicity_assert(frameBound <= 2*len);

  /* UWORDBound * UWORD_BIT, the number of bits actually allocacted, is at most the cellBound count plus (worse case) padding bits in each frame. */
  static_assert(1 <= UWORD_BIT, "UWORD_BIT is zero.");
  static_assert(2*DAG_LEN_MAX <= (SIZE_MAX - CELLS_MAX) / (UWORD_BIT - 1), "cellsBound + frameBound*(UWORD_BIT - 1) doesn't fit in size_t.");
  simplicity_assert(UWORDBound <= (cellsBound + frameBound*(UWORD_BIT - 1)) / UWORD_BIT);

  /* UWORDBound, is also at most the cellsBound, with an entire UWORD per cell (the rest of the UWORD being padding). */
  simplicity_assert(UWORDBound <= cellsBound);

  /* We use calloc for 'cells' because the frame data must be initialized before we can perform bitwise operations. */
  static_assert(CELLS_MAX - 1 <= UINT32_MAX, "cells array index does not fit in uint32_t.");
  UWORD* cells = calloc(UWORDBound ? UWORDBound : 1, sizeof(UWORD));
  static_assert(2*DAG_LEN_MAX <= SIZE_MAX / sizeof(frameItem), "frames array does not fit in size_t.");
  static_assert(1 <= DAG_LEN_MAX, "DAG_LEN_MAX is zero.");
  static_assert(2*DAG_LEN_MAX - 1 <= UINT32_MAX, "frames array index does not fit in uint32_t.");
  frameItem* frames = malloc(frameBound * sizeof(frameItem));
  call* stack = calloc(len, sizeof(call));

  simplicity_err result = cells && frames && stack ? SIMPLICITY_NO_ERROR : SIMPLICITY_ERR_MALLOC;
  if (IS_OK(result)) {
    if (input) memcpy(cells, input, ROUND_UWORD(inputSize) * sizeof(UWORD));

    evalState state =
      { .activeReadFrame = frames
      , .activeWriteFrame = frames + (frameBound - 1)
      };
    *(state.activeReadFrame) = initReadFrame(inputSize, cells);
    *(state.activeWriteFrame) = initWriteFrame(outputSize, cells + UWORDBound);

    result = runTCO(state, stack, dag, type_dag, len, env);

    if (IS_OK(result)) {
      if (output) memcpy(output, state.activeWriteFrame->edge, ROUND_UWORD(outputSize) * sizeof(UWORD));

      result = antiDos(anti_dos_checks, stack, dag, len);
    }
  }

  free(stack);
  free(frames);
  free(cells);
  return result;
}
