#include "dag.h"

#include <assert.h>
#include <stdbool.h>
#include "bounded.h"
#include "callonce.h"
#include "prefix.h"
#include "rsort.h"
#include "sha256.h"
#include "tag.h"
#include "uword.h"
#include "unreachable.h"

/* Prepends Simplicity tag prefixes to a string literal 's'. */
#define COMMITMENT_TAG(s) SIMPLICITY_PREFIX "\x1F" "Commitment\x1F" s
#define ANNOTATED_TAG(s) SIMPLICITY_PREFIX "\x1F" "Annotated\x1F" s
#define IDENTITY_TAG(s) SIMPLICITY_PREFIX "\x1F" "Identity\x1F" s

/* Cached initial values for all the tags.
 * Only to be accessed through 'cmrIV' or 'amrIV'.
 */
static once_flag static_initialized = ONCE_FLAG_INIT;
static sha256_midstate cmr_compIV,
                       cmr_caseIV,
                       cmr_pairIV,
                       cmr_disconnectIV,
                       cmr_injlIV,
                       cmr_injrIV,
                       cmr_takeIV,
                       cmr_dropIV,
                       cmr_idenIV,
                       cmr_unitIV,
                       cmr_witnessIV;
static sha256_midstate amr_compIV,
                       amr_assertlIV,
                       amr_assertrIV,
                       amr_caseIV,
                       amr_pairIV,
                       amr_disconnectIV,
                       amr_injlIV,
                       amr_injrIV,
                       amr_takeIV,
                       amr_dropIV,
                       amr_idenIV,
                       amr_unitIV,
                       amr_witnessIV;
static sha256_midstate imr_disconnectIV,
                       imr_witnessIV;
static sha256_midstate identityIV,
                       hiddenIV;
static void static_initialize(void) {
  MK_TAG(&cmr_compIV, COMMITMENT_TAG("comp"));
  MK_TAG(&cmr_caseIV, COMMITMENT_TAG("case"));
  MK_TAG(&cmr_pairIV, COMMITMENT_TAG("pair"));
  MK_TAG(&cmr_disconnectIV, COMMITMENT_TAG("disconnect"));
  MK_TAG(&cmr_injlIV, COMMITMENT_TAG("injl"));
  MK_TAG(&cmr_injrIV, COMMITMENT_TAG("injr"));
  MK_TAG(&cmr_takeIV, COMMITMENT_TAG("take"));
  MK_TAG(&cmr_dropIV, COMMITMENT_TAG("drop"));
  MK_TAG(&cmr_idenIV, COMMITMENT_TAG("iden"));
  MK_TAG(&cmr_unitIV, COMMITMENT_TAG("unit"));
  MK_TAG(&cmr_witnessIV, COMMITMENT_TAG("witness"));
  MK_TAG(&amr_compIV, ANNOTATED_TAG("comp"));
  MK_TAG(&amr_assertlIV, ANNOTATED_TAG("assertl"));
  MK_TAG(&amr_assertrIV, ANNOTATED_TAG("assertr"));
  MK_TAG(&amr_caseIV, ANNOTATED_TAG("case"));
  MK_TAG(&amr_pairIV, ANNOTATED_TAG("pair"));
  MK_TAG(&amr_disconnectIV, ANNOTATED_TAG("disconnect"));
  MK_TAG(&amr_injlIV, ANNOTATED_TAG("injl"));
  MK_TAG(&amr_injrIV, ANNOTATED_TAG("injr"));
  MK_TAG(&amr_takeIV, ANNOTATED_TAG("take"));
  MK_TAG(&amr_dropIV, ANNOTATED_TAG("drop"));
  MK_TAG(&amr_idenIV, ANNOTATED_TAG("iden"));
  MK_TAG(&amr_unitIV, ANNOTATED_TAG("unit"));
  MK_TAG(&amr_witnessIV, ANNOTATED_TAG("witness"));
  MK_TAG(&imr_disconnectIV, IDENTITY_TAG("disconnect"));
  MK_TAG(&imr_witnessIV, IDENTITY_TAG("witness"));
  MK_TAG(&identityIV, SIMPLICITY_PREFIX "\x1F" "Identity");
  MK_TAG(&hiddenIV, SIMPLICITY_PREFIX "\x1F" "Hidden");
}

/* Given a tag for a node, return the SHA-256 hash of its associated CMR tag.
 * This is the "initial value" for computing the commitment Merkle root for that expression.
 *
 * Precondition: 'tag' \notin {HIDDEN, JET}
 */
static sha256_midstate cmrIV(tag_t tag) {
  call_once(&static_initialized, &static_initialize);

  switch (tag) {
   case COMP: return cmr_compIV;
   case ASSERTL:
   case ASSERTR:
   case CASE: return cmr_caseIV;
   case PAIR: return cmr_pairIV;
   case DISCONNECT: return cmr_disconnectIV;
   case INJL: return cmr_injlIV;
   case INJR: return cmr_injrIV;
   case TAKE: return cmr_takeIV;
   case DROP: return cmr_dropIV;
   case IDEN: return cmr_idenIV;
   case UNIT: return cmr_unitIV;
   case WITNESS: return cmr_witnessIV;
   /* Precondition violated. */
   case HIDDEN:
   case JET:
    break;
  }
  assert(false);
  UNREACHABLE;
}

/* Given a tag for a node, return the SHA-256 hash of its associated IMR tag.
 * This is the "initial value" for computing the commitment Merkle root for that expression.
 *
 * Precondition: 'tag' \notin {HIDDEN, JET}
 */
static sha256_midstate imrIV(tag_t tag) {
  call_once(&static_initialized, &static_initialize);

  return DISCONNECT == tag ? imr_disconnectIV
       : WITNESS == tag ? imr_witnessIV
       : cmrIV(tag);
}

/* Given a tag for a node, return the SHA-256 hash of its associated AMR tag.
 * This is the "initial value" for computing the annotated Merkle root for that expression.
 *
 * Precondition: 'tag' \notin {HIDDEN, JET}
 */
static sha256_midstate amrIV(tag_t tag) {
  call_once(&static_initialized, &static_initialize);

  switch (tag) {
   case COMP: return amr_compIV;
   case ASSERTL: return amr_assertlIV;
   case ASSERTR: return amr_assertrIV;
   case CASE: return amr_caseIV;
   case PAIR: return amr_pairIV;
   case DISCONNECT: return amr_disconnectIV;
   case INJL: return amr_injlIV;
   case INJR: return amr_injrIV;
   case TAKE: return amr_takeIV;
   case DROP: return amr_dropIV;
   case IDEN: return amr_idenIV;
   case UNIT: return amr_unitIV;
   case WITNESS: return amr_witnessIV;
   /* Precondition violated. */
   case HIDDEN:
   case JET:
    break;
  }
  assert(false);
  UNREACHABLE;
}

/* Given a well-formed dag[i + 1], such that for all 'j', 0 <= 'j' < 'i',
 * 'dag[j].cmr' is the CMR of the subexpression denoted by the slice
 *
 *     (dag_nodes[j + 1])dag,
 *
 * then we set the value of 'dag[i].cmr' to be the CMR of the subexpression denoted by 'dag'.
 *
 * Precondition: dag_node dag[i + 1] and 'dag' is well-formed.
 *               dag[i].'tag' \notin {HIDDEN, JET}
 */
void computeCommitmentMerkleRoot(dag_node* dag, const size_t i) {
  uint32_t block[16] = {0};
  size_t j = 8;

  assert (HIDDEN != dag[i].tag);
  assert (JET != dag[i].tag);

  dag[i].cmr = cmrIV(dag[i].tag);

  /* Hash the child sub-expression's CMRs (if there are any children). */
  switch (dag[i].tag) {
   case COMP:
   case ASSERTL:
   case ASSERTR:
   case CASE:
   case PAIR:
    memcpy(block + j, dag[dag[i].child[1]].cmr.s, sizeof(uint32_t[8]));
    j = 0;
    /*@fallthrough@*/
   case DISCONNECT: /* Only the first child is used in the CMR. */
   case INJL:
   case INJR:
   case TAKE:
   case DROP:
    memcpy(block + j, dag[dag[i].child[0]].cmr.s, sizeof(uint32_t[8]));
    sha256_compression(dag[i].cmr.s, block);
   case IDEN:
   case UNIT:
   case WITNESS:
   case HIDDEN:
   case JET:
    break;
  }
}

/* Computes the identity Merkle roots of every subexpression in a well-typed 'dag' with witnesses.
 * 'imr[i]' is set to the identity Merkle root of the subexpression 'dag[i]'.
 * When 'HIDDEN == dag[i].tag', then 'imr[i]' is instead set to a hidden root hash for that hidden node.
 *
 * Precondition: sha256_midstate imr[len];
 *               dag_node dag[len] and 'dag' is well-typed with 'type_dag' and contains witnesses.
 */
static void computeIdentityMerkleRoot(sha256_midstate* imr, const dag_node* dag, const type* type_dag, const size_t len) {
  call_once(&static_initialized, &static_initialize);

  /* Pass 1 */
  for (size_t i = 0; i < len; ++i) {
    uint32_t block[16] = {0};
    size_t j = 8;

    /* For jets and primitives, the first pass identity Merkle root is the same as their commitment Merkle root. */
    imr[i] = HIDDEN == dag[i].tag ? dag[i].cmr
           : JET == dag[i].tag ? dag[i].cmr
           : imrIV(dag[i].tag);
    switch (dag[i].tag) {
     case WITNESS:
      sha256_bitstring(block, &dag[i].witness);
      memcpy(block + 8, type_dag[WITNESS_B(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(imr[i].s, block);
      break;
     case COMP:
     case ASSERTL:
     case ASSERTR:
     case CASE:
     case PAIR:
     case DISCONNECT:
      memcpy(block + j, imr[dag[i].child[1]].s, sizeof(uint32_t[8]));
      j = 0;
      /*@fallthrough@*/
     case INJL:
     case INJR:
     case TAKE:
     case DROP:
      memcpy(block + j, imr[dag[i].child[0]].s, sizeof(uint32_t[8]));
      sha256_compression(imr[i].s, block);
     case IDEN:
     case UNIT:
     case HIDDEN:
     case JET:
      break;
    }
  }

  /* Pass 2 */
  for (size_t i = 0; i < len; ++i) {
    uint32_t block[16] = {0};

    if (HIDDEN == dag[i].tag) {
      memcpy(block + 8, imr[i].s, sizeof(uint32_t[8]));
      imr[i] = hiddenIV;
      sha256_compression(imr[i].s, block);
    } else {
      memcpy(block + 8, imr[i].s, sizeof(uint32_t[8]));
      imr[i] = identityIV;
      sha256_compression(imr[i].s, block);
      memcpy(block, type_dag[dag[i].sourceType].typeMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, type_dag[dag[i].targetType].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(imr[i].s, block);
    }
  }
}

/* Given a well-typed dag representing a Simplicity expression, compute the annotated Merkle roots of all subexpressions.
 * For all 'i', 0 <= 'i' < 'len', 'analysis[i].annotatedMerkleRoot' will be the AMR of the subexpression denoted by the slice
 *
 *     (dag_nodes[i + 1])dag.
 *
 * The AMR of the overall expression will be 'analysis[len - 1].annotatedMerkleRoot'.
 *
 * Precondition: analyses analysis[len];
 *               dag_node dag[len] and 'dag' has witness data and is well-typed with 'type_dag'.
 * Postconditon: analyses analysis[len] contains the annotated Merkle roots of each subexpressions of 'dag'.
 */
void computeAnnotatedMerkleRoot(analyses* analysis, const dag_node* dag, const type* type_dag, const size_t len) {
  for (size_t i = 0; i < len; ++i) {
    uint32_t block[16] = {0};

    /* For jets and primitives, their annotated Merkle root is the same as their commitment Merkle root. */
    analysis[i].annotatedMerkleRoot = HIDDEN == dag[i].tag ? dag[i].cmr
                                    : JET == dag[i].tag ? dag[i].cmr
                                    : amrIV(dag[i].tag);
    switch (dag[i].tag) {
     case ASSERTL:
     case ASSERTR:
     case CASE:
      memcpy(block, type_dag[CASE_A(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8,
             type_dag[CASE_B(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      memcpy(block, type_dag[CASE_C(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, type_dag[CASE_D(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      memcpy(block, analysis[dag[i].child[0]].annotatedMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, analysis[dag[i].child[1]].annotatedMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      break;
     case DISCONNECT:
      memcpy(block, type_dag[DISCONNECT_A(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, type_dag[DISCONNECT_B(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      memcpy(block, type_dag[DISCONNECT_C(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, type_dag[DISCONNECT_D(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      memcpy(block, analysis[dag[i].child[0]].annotatedMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, analysis[dag[i].child[1]].annotatedMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      break;
     case COMP:
      memcpy(block + 8, type_dag[COMP_A(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      memcpy(block, type_dag[COMP_B(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, type_dag[COMP_C(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      memcpy(block, analysis[dag[i].child[0]].annotatedMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, analysis[dag[i].child[1]].annotatedMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      break;
     case PAIR:
      memcpy(block + 8, type_dag[PAIR_A(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      memcpy(block, type_dag[PAIR_B(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, type_dag[PAIR_C(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      memcpy(block, analysis[dag[i].child[0]].annotatedMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, analysis[dag[i].child[1]].annotatedMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      break;
     case INJL:
     case INJR:
      memcpy(block, type_dag[INJ_A(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, type_dag[INJ_B(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      memcpy(block, type_dag[INJ_C(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, analysis[dag[i].child[0]].annotatedMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      break;
     case TAKE:
     case DROP:
      memcpy(block, type_dag[PROJ_A(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, type_dag[PROJ_B(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      memcpy(block, type_dag[PROJ_C(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, analysis[dag[i].child[0]].annotatedMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      break;
     case IDEN:
      memcpy(block + 8, type_dag[IDEN_A(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      break;
     case UNIT:
      memcpy(block + 8, type_dag[UNIT_A(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      break;
     case WITNESS:
      memcpy(block + 8, type_dag[WITNESS_A(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      memcpy(block, type_dag[WITNESS_B(dag, type_dag, i)].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_bitstring(block + 8, &dag[i].witness);
      sha256_compression(analysis[i].annotatedMerkleRoot.s, block);
      break;
     case HIDDEN:
     case JET:
      break;
    }
  }
}

/* Verifies that the 'dag' is in canonical order, meaning that nodes under the left branches have lower indices than nodes under
 * right branches, with the exception that nodes under right braches may (cross-)reference identical nodes that already occur under
 * left branches.
 *
 * Returns 'true' if the 'dag' is in canonical order, and returns 'false' if it is not.
 *
 * May modify dag[i].aux values and invalidate dag[i].sourceType and dag[i].targetType.
 * This function should only be used prior to calling 'mallocTypeInference'.
 *
 * Precondition: dag_node dag[len] and 'dag' is well-formed.
 */
bool verifyCanonicalOrder(dag_node* dag, const size_t len) {
  size_t bottom = 0;
  size_t top = len-1; /* Underflow is checked below. */

  if (!len) {
    assert(false); /* A well-formed dag has non-zero length */
    return true; /* However, an empty dag is technically in canonical order */
  }

  /* We use dag[i].aux as a "stack" to manage the traversal of the DAG. */
  dag[top].aux = len; /* We will set top to 'len' to indicate we are finished. */

  /* Each time any particular 'top' value is revisted in this loop, bottom has increased to be strictly larger than the last 'child'
     value examined.  Therefore we will make further progress in the loop the next time around.
     By this reasoning any given 'top' value will be visited no more than numChildren(dag[top].tag) + 1 <= 3 times.
     Thus this loop iterates at most O('len') times.
   */
  while (top < len) {
    /* We determine cannonical order by iterating through the dag in canonical (pre-)order,
       incrementing 'bottom' each time we encounter a node that is (correctly) placed at the 'bottom' index.
       We take advantage of the precondition that the dag is well-formed to know in advance that any children
       of a node have index strictly less than the node itself.
     */

    /* Check first child. */
    size_t child = dag[top].child[0];
    switch (dag[top].tag) {
     case ASSERTL:
     case ASSERTR:
     case CASE:
     case DISCONNECT:
     case COMP:
     case PAIR:
     case INJL:
     case INJR:
     case TAKE:
     case DROP:
      if (bottom < child) {
        dag[child].aux = top;
        top = child;
        continue;
      }
      if (bottom == child) bottom++;
     case IDEN:
     case UNIT:
     case WITNESS:
     case HIDDEN:
     case JET:
      break;
    }

    /* Check second child. */
    child = dag[top].child[1];
    switch (dag[top].tag) {
     case ASSERTL:
     case ASSERTR:
     case CASE:
     case DISCONNECT:
     case COMP:
     case PAIR:
      if (bottom < child) {
        dag[child].aux = top;
        top = child;
        continue;
      }
      if (bottom == child) bottom++;
     case INJL:
     case INJR:
     case TAKE:
     case DROP:
     case IDEN:
     case UNIT:
     case WITNESS:
     case HIDDEN:
     case JET:
      break;
    }

    /* Check current node. */
    if (bottom < top) return false; /* Not in canonical order.  */
    if (bottom == top) bottom++;
    /* top < bottom */
    top = dag[top].aux; /* Return. */
  }
  assert(bottom == top && top == len);

  return true;
}

/* This function fills in the 'WITNESS' nodes of a 'dag' with the data from 'witness'.
 * For each 'WITNESS' : A |- B expression in 'dag', the bits from the 'witness' bitstring are decoded in turn
 * to construct a compact representation of a witness value of type B.
 * This function only returns 'true' when exactly 'witness.len' bits are consumed by all the 'dag's witness values.
 *
 * Note: the 'witness' value is passed by copy because the implementation manipulates a local copy of the structure.
 *
 * Precondition: dag_node dag[len] and 'dag' without witness data and is well-typed with 'type_dag';
 *               witness is a valid bitstring;
 *
 * Postcondition: dag_node dag[len] and 'dag' has witness data and is well-typed with 'type_dag'
 *                  when the result is 'true';
 */
bool fillWitnessData(dag_node* dag, type* type_dag, const size_t len, bitstring witness) {
  for (size_t i = 0; i < len; ++i) {
    if (WITNESS == dag[i].tag) {
      if (witness.len <= 0) {
        /* There is no more data left in witness. */
        dag[i].witness = (bitstring){0};
        /* This is fine as long as the witness type is trivial */
        if (type_dag[WITNESS_B(dag, type_dag, i)].bitSize) return false;
      } else {
        dag[i].witness = (bitstring)
          { .arr = &witness.arr[witness.offset/CHAR_BIT]
          , .offset = witness.offset % CHAR_BIT
          , .len = witness.len /* The value of .len will be finalized after the while loop. */
          };

        /* Traverse the witness type to parse the witness's compact representation as a bit sting. */
        size_t cur = typeSkip(WITNESS_B(dag, type_dag, i), type_dag);
        bool calling = true;
        type_dag[cur].back = 0;
        while (cur) {
          if (SUM == type_dag[cur].kind) {
            /* Parse one bit and traverse the left type or the right type depending on the value of the bit parsed. */
            assert(calling);
            if (witness.len <= 0) return false;
            bool bit = 1 & (witness.arr[witness.offset/CHAR_BIT] >> (CHAR_BIT - 1 - witness.offset % CHAR_BIT));
            witness.offset++; witness.len--;
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
        /* The length of this 'WITNESS' node's witness value is
         * the difference between the remaining witness length from before and after parsing.
         */
        dag[i].witness.len -= witness.len;

        /* Note: Above we use 'typeSkip' to skip over long chains of products against trivial types
         * This avoids a potential DOS vulnerability where a DAG of deeply nested products of unit types with sharing is traversed,
         * taking exponential time.
         * While traversing still could take exponential time in terms of the size of the type's dag,
         * at least one bit of witness data is required per PRODUCT type encountered.
         * This ought to limit the total number of times through the above loop to no more that 3 * dag[i].witness.len.
         */
        /* :TODO: build a test case that creates such a long chain of products with unit types for a witness value. */
      }
    }
  }
  return (0 == witness.len);
}

/* Computes the identity Merkle roots of every subexpression in a well-typed 'dag' with witnesses.
 * imr[i]' is set to the identity Merkle root of the subexpression 'dag[i]'.
 * When 'HIDDEN == dag[i].tag', then 'imr[i]' is instead set to a hidden root hash for that hidden node.
 *
 * If malloc fails, return 'false', otherwise return 'true'.
 * If 'true' is returned then '*success' is set to true if all the identity Merkle roots (and hidden roots) are all unique.
 *
 * Precondition: NULL != success;
 *               sha256_midstate imr[len];
 *               dag_node dag[len] and 'dag' is well-typed with 'type_dag' and contains witnesses.
 */
bool verifyNoDuplicateIdentityRoots(bool* success, sha256_midstate* imr,
                                    const dag_node* dag, const type* type_dag, const size_t len) {
  bool result, duplicates;

  computeIdentityMerkleRoot(imr, dag, type_dag, len);

  result = hasDuplicates(&duplicates, imr, len);
  *success = result && !duplicates;

  return result;
}
