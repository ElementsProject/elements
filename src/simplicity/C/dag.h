/* This module defines the structure for Simplicity DAGs, and functions for some analysis of that structure,
 * such as computing Merkle Roots.
 */
#ifndef DAG_H
#define DAG_H

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

/* The contents of a 'WITNESS' node that has witness data. */
typedef struct witnessInfo {
  size_t typeAnnotation[2]; /* A 'witness v : A |- B' expression has only 2 type annotations. */
  bitstring data;           /* A compact bitstring representation for a value 'v' of type 'B'. */
} witnessInfo;

/* A node the the DAG of a Simplicity expression.
 * It consists of a 'tag' indicating the kind of expression the node represents.
 * The contents of a node depend on the kind of the expressions.
 * The node may have references to children, when it is a combinator kind of expression.
 *
 * Invariant: 'NULL != jet' when 'tag == JET';
 *            sha256_midstate hash is active when tag == HIDDEN;
 *            witnessInfo witness is be active when tag == WITNESS and the node has witness data;
 *            sha256_midstate wmr and size_t sourceIx, targetIx are active when tag == JET;
 *            size_t child[numChildren(tag)] when tag \notin {HIDDEN, WITNESS, JET};
 */
typedef struct dag_node {
  jet_ptr jet;
  union {
    struct {
      sha256_midstate wmr;
      size_t sourceIx, targetIx;
    };
    struct {
      size_t typeAnnotation[4];
      size_t child[2];
    };
    witnessInfo witness;
    sha256_midstate hash;
  };
  tag_t tag;
} dag_node;

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
 * 'commitmentMerkleRoot' is the commitment Merkle root of the subexpressions represented by the node.
 */
typedef struct analyses {
  sha256_midstate commitmentMerkleRoot;
  sha256_midstate witnessMerkleRoot;
} analyses;

/* Given a well-formed dag representing a Simplicity expression, compute the commitment Merkle roots of all subexpressions.
 * For all 'i', 0 <= 'i' < 'len', 'analysis[i].commitmentMerkleRoot' will be the CMR of the subexpression denoted by the slice
 *
 *     (dag_nodes[i + 1])dag.
 *
 * The CMR of the overall expression will be 'analysis[len - 1].commitmentMerkleRoot'.
 *
 * Precondition: analyses analysis[len];
 *               dag_node dag[len] and 'dag' is well-formed.
 */
void computeCommitmentMerkleRoot(analyses* analysis, const dag_node* dag, size_t len);

/* Given a well-typed dag representing a Simplicity expression, compute the witness Merkle roots of all subexpressions.
 * For all 'i', 0 <= 'i' < 'len', 'analysis[i].witnessMerkleRoot' will be the WMR of the subexpression denoted by the slice
 *
 *     (dag_nodes[i + 1])dag.
 *
 * The WMR of the overall expression will be 'analysis[len - 1].witnessMerkleRoot'.
 *
 * Precondition: analyses analysis[len];
 *               dag_node dag[len] and 'dag' has witness data and is well-typed with 'type_dag'.
 * Postconditon: analyses analysis[len] contains the witness Merkle roots of each subexpressions of 'dag'.
 */
void computeWitnessMerkleRoot(analyses* analysis, const dag_node* dag, const type* type_dag, size_t len);

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

#endif
