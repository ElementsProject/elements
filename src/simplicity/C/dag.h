/* This module defines the structure for Simplicity DAGs, and functions for some analysis of that structure,
 * such as computing Merkle Roots.
 */
#ifndef SIMPLICITY_DAG_H
#define SIMPLICITY_DAG_H

#include <stddef.h>
#include <stdint.h>
#include "bitstring.h"
#include "jets.h"
#include "type.h"

/* An enumeration of the various kinds of Simplicity nodes. */
typedef enum tag_t
{ COMP
, CASE
, ASSERTL
, ASSERTR
, PAIR
, DISCONNECT
, INJL
, INJR
, TAKE
, DROP
, IDEN
, UNIT
, HIDDEN
, WITNESS
, JET
} tag_t;

/* This structure is use to count the different kinds of combinators in a Simplicity DAG. */
typedef struct combinator_counters {
  size_t comp_cnt, case_cnt, pair_cnt, disconnect_cnt,
         injl_cnt, injr_cnt, take_cnt, drop_cnt;
} combinator_counters;

/* Given a tag for an expression, add it to the 'census'.
 */
static inline void enumerator(combinator_counters* census, tag_t tag) {
  if (!census) return;
  switch (tag) {
   case COMP: census->comp_cnt++; return;
   case ASSERTL:
   case ASSERTR: /* Assertions are counted as CASE combinators. */
   case CASE: census->case_cnt++; return;
   case PAIR: census->pair_cnt++; return;
   case DISCONNECT: census->disconnect_cnt++; return;
   case INJL: census->injl_cnt++; return;
   case INJR: census->injr_cnt++; return;
   case TAKE: census->take_cnt++; return;
   case DROP: census->drop_cnt++; return;

   /* These tags are not accounted for in the census. */
   case IDEN:
   case UNIT:
   case HIDDEN:
   case WITNESS:
   case JET:
    return;
  }
}

/* Returns the number of children that a Simplicity combinator of the 'tag' kind has.
 */
static inline size_t numChildren(tag_t tag) {
  switch (tag) {
   case COMP:
   case ASSERTL:
   case ASSERTR:
   case CASE:
   case PAIR:
   case DISCONNECT:
    return 2;
   case INJL:
   case INJR:
   case TAKE:
   case DROP:
    return 1;
   case IDEN:
   case UNIT:
   case HIDDEN:
   case WITNESS:
   case JET:
    return 0;
  }
}

/* A node the the DAG of a Simplicity expression.
 * It consists of a 'tag' indicating the kind of expression the node represents.
 * The contents of a node depend on the kind of the expressions.
 * The node may have references to children, when it is a combinator kind of expression.
 *
 * Invariant: 'NULL != jet' when 'tag == JET';
 *            bitstring witness is be active when tag == WITNESS and the node has witness data;
 *            size_t sourceIx, targetIx are active when tag == JET;
 *            size_t child[numChildren(tag)] when tag \notin {HIDDEN, WITNESS, JET};
 */
typedef struct dag_node {
  jet_ptr jet;
  sha256_midstate cmr;
  union {
    size_t aux; /* Used as scratch space for verifyCanonicalOrder. */
    struct {
       size_t sourceType, targetType;
    };
  };
  union {
    struct {
      size_t sourceIx, targetIx;
    };
    struct {
      size_t child[2];
    };
    bitstring witness;
  };
  tag_t tag;
} dag_node;

/* Inline functions for accessing the type annotations of combinators */
static inline size_t IDEN_A(const dag_node* dag, const type* type_dag, size_t i) {
  (void)type_dag;
  assert(IDEN == dag[i].tag);
  return dag[i].sourceType;
}

static inline size_t UNIT_A(const dag_node* dag, const type* type_dag, size_t i) {
  (void)type_dag;
  assert(UNIT == dag[i].tag);
  return dag[i].sourceType;
}

static inline size_t COMP_A(const dag_node* dag, const type* type_dag, size_t i) {
  (void)type_dag;
  assert(COMP == dag[i].tag);
  return dag[i].sourceType;
}

static inline size_t COMP_B(const dag_node* dag, const type* type_dag, size_t i) {
  (void)type_dag;
  assert(COMP == dag[i].tag);
  return dag[dag[i].child[1]].sourceType;
}

static inline size_t COMP_C(const dag_node* dag, const type* type_dag, size_t i) {
  (void)type_dag;
  assert(COMP == dag[i].tag);
  return dag[i].targetType;
}

static inline size_t CASE_A(const dag_node* dag, const type* type_dag, size_t i) {
  assert(CASE == dag[i].tag || ASSERTL == dag[i].tag || ASSERTR == dag[i].tag);
  assert(PRODUCT == type_dag[dag[i].sourceType].kind);
  assert(SUM == type_dag[type_dag[dag[i].sourceType].typeArg[0]].kind);
  return type_dag[type_dag[dag[i].sourceType].typeArg[0]].typeArg[0];
}

static inline size_t CASE_B(const dag_node* dag, const type* type_dag, size_t i) {
  assert(CASE == dag[i].tag || ASSERTL == dag[i].tag || ASSERTR == dag[i].tag);
  assert(PRODUCT == type_dag[dag[i].sourceType].kind);
  assert(SUM == type_dag[type_dag[dag[i].sourceType].typeArg[0]].kind);
  return type_dag[type_dag[dag[i].sourceType].typeArg[0]].typeArg[1];
}

static inline size_t CASE_C(const dag_node* dag, const type* type_dag, size_t i) {
  assert(CASE == dag[i].tag || ASSERTL == dag[i].tag || ASSERTR == dag[i].tag);
  assert(PRODUCT == type_dag[dag[i].sourceType].kind);
  return type_dag[dag[i].sourceType].typeArg[1];
}

static inline size_t CASE_D(const dag_node* dag, const type* type_dag, size_t i) {
  (void)type_dag;
  assert(CASE == dag[i].tag || ASSERTL == dag[i].tag || ASSERTR == dag[i].tag);
  return dag[i].targetType;
}

static inline size_t PAIR_A(const dag_node* dag, const type* type_dag, size_t i) {
  (void)type_dag;
  assert(PAIR == dag[i].tag);
  return dag[i].sourceType;
}

static inline size_t PAIR_B(const dag_node* dag, const type* type_dag, size_t i) {
  assert(PAIR == dag[i].tag);
  assert(PRODUCT == type_dag[dag[i].targetType].kind);
  return type_dag[dag[i].targetType].typeArg[0];
}

static inline size_t PAIR_C(const dag_node* dag, const type* type_dag, size_t i) {
  assert(PAIR == dag[i].tag);
  assert(PRODUCT == type_dag[dag[i].targetType].kind);
  return type_dag[dag[i].targetType].typeArg[1];
}

static inline size_t DISCONNECT_A(const dag_node* dag, const type* type_dag, size_t i) {
  (void)type_dag;
  assert(DISCONNECT == dag[i].tag);
  return dag[i].sourceType;
}

static inline size_t DISCONNECT_B(const dag_node* dag, const type* type_dag, size_t i) {
  assert(DISCONNECT == dag[i].tag);
  assert(PRODUCT == type_dag[dag[i].targetType].kind);
  return type_dag[dag[i].targetType].typeArg[0];
}

static inline size_t DISCONNECT_C(const dag_node* dag, const type* type_dag, size_t i) {
  (void)type_dag;
  assert(DISCONNECT == dag[i].tag);
  return dag[dag[i].child[1]].sourceType;
}

static inline size_t DISCONNECT_D(const dag_node* dag, const type* type_dag, size_t i) {
  assert(DISCONNECT == dag[i].tag);
  assert(PRODUCT == type_dag[dag[i].targetType].kind);
  return type_dag[dag[i].targetType].typeArg[1];
}

static inline size_t DISCONNECT_W256A(const dag_node* dag, const type* type_dag, size_t i) {
  (void)type_dag;
  assert(DISCONNECT == dag[i].tag);
  return dag[dag[i].child[0]].sourceType;
}

static inline size_t DISCONNECT_BC(const dag_node* dag, const type* type_dag, size_t i) {
  (void)type_dag;
  assert(DISCONNECT == dag[i].tag);
  return dag[dag[i].child[0]].targetType;
}

static inline size_t INJ_A(const dag_node* dag, const type* type_dag, size_t i) {
  (void)type_dag;
  assert(INJL == dag[i].tag || INJR == dag[i].tag);
  return dag[i].sourceType;
}

static inline size_t INJ_B(const dag_node* dag, const type* type_dag, size_t i) {
  assert(INJL == dag[i].tag || INJR == dag[i].tag);
  assert(SUM == type_dag[dag[i].targetType].kind);
  return type_dag[dag[i].targetType].typeArg[0];
}

static inline size_t INJ_C(const dag_node* dag, const type* type_dag, size_t i) {
  assert(INJL == dag[i].tag || INJR == dag[i].tag);
  assert(SUM == type_dag[dag[i].targetType].kind);
  return type_dag[dag[i].targetType].typeArg[1];
}

static inline size_t PROJ_A(const dag_node* dag, const type* type_dag, size_t i) {
  assert(TAKE == dag[i].tag || DROP == dag[i].tag);
  assert(PRODUCT == type_dag[dag[i].sourceType].kind);
  return type_dag[dag[i].sourceType].typeArg[0];
}

static inline size_t PROJ_B(const dag_node* dag, const type* type_dag, size_t i) {
  assert(TAKE == dag[i].tag || DROP == dag[i].tag);
  assert(PRODUCT == type_dag[dag[i].sourceType].kind);
  return type_dag[dag[i].sourceType].typeArg[1];
}

static inline size_t PROJ_C(const dag_node* dag, const type* type_dag, size_t i) {
  (void)type_dag;
  assert(TAKE == dag[i].tag || DROP == dag[i].tag);
  return dag[i].targetType;
}

static inline size_t WITNESS_A(const dag_node* dag, const type* type_dag, size_t i) {
  (void)type_dag;
  assert(WITNESS == dag[i].tag);
  return dag[i].sourceType;
}

static inline size_t WITNESS_B(const dag_node* dag, const type* type_dag, size_t i) {
  (void)type_dag;
  assert(WITNESS == dag[i].tag);
  return dag[i].targetType;
}

/* A well-formed Simplicity DAG is an array of 'dag_node's,
 *
 *     dag_node dag[len],
 *
 * such that
 *
 *     0 < len
 *
 * and for all 'i', 0 <= 'i' < 'len' and for all 'j', 0 <= 'j' < 'numChildren(dag[i].tag)',
 *
 *     dag[i].child[j] < i
 *
 * and for all 'i', 0 <= 'i' < 'len',
 *
 *     if dag[dag[i].child[0]].tag == HIDDEN then dag[i].tag == ASSERTR
 *
 *     and
 *
 *     if dag[dag[i].child[1]].tag == HIDDEN then dag[i].tag == ASSERTL
 *
 * Note that a well-formed Simplicity DAG is not necessarily a well-typed Simplicity DAG.
 */

/* A structure of static analyses for a particular node of a Simplicity DAG.
 * 'annotatedMerkleRoot' is the a Merkle root to includes the type annotations of all subexpressions.
 */
typedef struct analyses {
  sha256_midstate annotatedMerkleRoot;
} analyses;

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
void computeCommitmentMerkleRoot(dag_node* dag, size_t i);

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
void computeAnnotatedMerkleRoot(analyses* analysis, const dag_node* dag, const type* type_dag, size_t len);

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
bool verifyCanonicalOrder(dag_node* dag, const size_t len);

/* This function fills in the 'WITNESS' nodes of a 'dag' with the data from 'witness'.
 * For each 'WITNESS' : A |- B expression in 'dag', the bits from the 'witness' bitstring are decoded in turn
 * to construct a compact representation of a witness value of type B.
 * This function only returns 'true' when exactly 'witness.len' bits are consumed by all the 'dag's witness values.
 *
 * Precondition: dag_node dag[len] and 'dag' without witness data and is well-typed with 'type_dag';
 *               witness is a valid bitstring;
 *
 * Postcondition: dag_node dag[len] and 'dag' has witness data and is well-typed with 'type_dag'
 *                  when the result is 'true';
 */
bool fillWitnessData(dag_node* dag, type* type_dag, const size_t len, bitstring witness);

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
                                    const dag_node* dag, const type* type_dag, const size_t len);

#endif
