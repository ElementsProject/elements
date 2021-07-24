#include "typeInference.h"

#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include "bounded.h"
#include "primitive.h"

/* Every subexpression in a Simplicity expression has a unification variable for its inferred source and target type. */
typedef struct unification_arrow {
  unification_var source, target;
} unification_arrow;

/* Returns the representative of this variable's equivalence class.
 * Note: the 'parent' pointers of some variables within this equivalence class may be adjusted (to point more directly to the
 * representative).
 *
 * Precondition: NULL != alpha
 *
 * Postcondition: NULL == result_value->parent
 */
static unification_var* findRoot(unification_var* alpha) {
  /* During unification, when '.rank' fields are active, the value of 'alpha->rank' strictly increases during this loop.
   * If 'alpha->rank' = 'i', then there must be at least 2^'i' unification variables referencing (indirectly) 'alpha'.
   * Therefore, this loop terminates in at most log_2('n')/2 steps where 'n' is the number of unification variables in 'alpha's
   * equivalence class.
   * This bound holds even during freezing when 'alpha->rank' may not be activated.
   *
   * Note: the total number of unification variables created for type inference is linearly bounded by the number of nodes
   * in the Simplicity expression being inferred's DAG.
   *
   * According to ``Worst-Case Analysis of Set Union Algorithms'' by Robert E. Tarjan and Jan van Leeuwen (1984)
   * the "path halving" method used in this implementation is adequate to ensure that the amortized time complexity is
   * O(InvAck('n')) and ``for all practical purposes InvAck('n') a constant no larger than four''.
   */
  while (alpha->parent != NULL) {
    if (alpha->parent->parent != NULL) alpha->parent = alpha->parent->parent;
    alpha = alpha->parent;
  }
  return alpha;
}

/* Begin attempt to add a new binding, 'bound', to a unification variable 'alpha' representing its equivalence class.
 * If 'alpha' is a free variable, it becomes a bound to a copy of 'bound' and 'true' is returned.
 * If 'alpha' is already bound to the same kind of type, new unification constraints may be added by overwriting '**cont'
 * and putting more elements into the '*cont' stack and 'true' is returned.
 * Hence, '*cont' must be a non-empty stack whose top element is scratch space available to be overwritten.
 * If 'alpha' is already bound to the same kind of non-trivial binding then '*bindings_used' is decremented
 * and 'bound->cont' may become active.
 *
 * In cases where no new unification constraints are need, the top element of '*cont' is popped off the stack,
 * removing the scratch item.
 *
 * If 'alpha' is already bound to a different kind of type, then 'false' is returned.
 *
 * If 'false' is returned, then '*alpha', '*bound', '*cont', '*bindings_used',
 * and values referenced by these structures may be modified.
 *
 * Preconditon: NULL != alpha and NULL == alpha->parent;
 *              NULL != bound;
 *              NULL != cont and '*cont' is a non-empty stack;
 *              NULL != bindings_used
 */
static bool applyBinding_cont(unification_var* alpha, binding* bound, unification_cont** cont, size_t* bindings_used) {
  if (!alpha->isBound) {
    /* alpha is currently a free variable.  Copy the provided binding. */
    alpha->isBound = true;
    alpha->bound = *bound;
    *cont = (*cont)->next;
    return true;
  }

  if (alpha->bound.kind != bound->kind) return false; /* Unification failure */
  /* Otherwise 'bound' is bound to the same kind of type as 'alpha's. */

  if (ONE == bound->kind) {
    /* 'bound' is a trivial binding. */
    *cont = (*cont)->next;
    return true;
  } else {
    /* 'bound' is a non-trivial binding.
     * Push two new pairs of the 'alpha->bound' and 'bound' type's unification variables to the stack of variables to be unified
     * by overwriting the top of the stack and slipping a new stack item underneath it.
     */

    (*cont)->alpha = alpha->bound.arg[0];
    (*cont)->beta = bound->arg[0];
    /* 'bound' will not be used further, so it is safe to activate 'bound->cont'.  */
    bound->cont = (unification_cont){ .alpha = alpha->bound.arg[1]
                                    , .beta = bound->arg[1]
                                    , .next = (*cont)->next
                                    };
    (*cont)->next = &(bound->cont);
    assert(0 < *bindings_used);
    (*bindings_used)--;
  }
  return true;
}

/* Unify a stack of pairs of unification variables.
 * If any unification fails, then NULL is returned.
 * If all unifications are successful, the representative of the equivalence class of the top pair of unified variables
 * from the stack is returned.
 * '*bindings_used' is decremented by the number of pairs of (non-trivial) bindings that are successfully unified.
 *
 * If 'NULL' is returned, then '*cont', '*bindings_used', and values referenced by these structures may be modified.
 *
 * Precondition: 'cont' is a non-empty stack;
 *               All of the 'unification_var's accessible through 'cont' have their '.rank' fields active;
 *               NULL != bindings_used
 */
static unification_var* unify_cont(unification_cont* cont, size_t* bindings_used) {
  unification_var* result = NULL;

  /* Each time we go through this loop, the stack size of 'cont' either increases by 1 or decreases by 1.
   * Whenever the stack size increases by 1, at the same time '*bindings_used' decreases by 1.
   *
   * For the above reason, the total number of times this loop iterates summed over all calls to 'unify_cont' cannot exceed
   *
   *     (2 * the total number of bindings created + the number of times 'unify_cont' is called).
   *
   * The total number of bindings created is bounded linearly in the number of nodes in the Simplicity expression's DAG.
   * The total number of calls to 'unify_cont' (via 'unify' and 'applyBinding') is bounded
   * linearly in the number of nodes in the Simplicity expression's DAG.
   * Therefore the total number of times this loop iterates summed over all calls to 'unify_cont' is bounded
   * linearly in the number of nodes in the Simplicity DAG.
   */
  while (cont) {
    unification_var* alpha = findRoot(cont->alpha);
    unification_var* beta = findRoot(cont->beta);

    if (alpha == beta) {
      /* 'cont->alpha' and 'cont->beta' are already equivalent. */
      cont = cont->next;
    } else {
      /* We will be making 'alpha' a parent of 'beta', so swap the variables to ensure that 'alpha's rank
       * is at least as large as 'beta'.
       */
      if (alpha->rank < beta->rank) {
         unification_var* tmp = beta; beta = alpha; alpha = tmp;
      }

      /* Make 'beta' equivalent to 'alpha'. */
      beta->parent = alpha;

      if (beta->isBound) {
         /* Copy/unify 'beta's binding to/with 'alpha'. */
         if (!applyBinding_cont(alpha, &beta->bound, &cont, bindings_used)) return NULL; /* Unification failure */
      } else {
        /* 'beta' used to be a free variable. */
        cont = cont->next;
      }

      /* Ensure 'alpha's rank exceeds 'beta's rank.
       * Note that if 'alpha->rank' == 'beta->rank' then the two variables equivalence classes each had at least
       * 2^'alpha->rank' variables in each of them.
       * Therefore the unified equivalence classes will now have at least 2^'alpha->rank + 1' variables,
       * which will be compatible with 'alpha's increased rank.
       */
      if (alpha->rank == beta->rank) alpha->rank++;
    }

    /* Return the representative of the unified variable of the two inputs that was on the top of the stack
     * (as long as all other unifications are successful).
     */
    if (!result) result = alpha;
  }

  return result;
}

/* Add a new binding, 'bound', to a unification variable 'alpha'.
 * If 'alpha' is already bound to a type that doesn't unify with 'bound', then 'false' is returned.
 * Otherwise variables of 'bound's bindings and 'alpha's bindings (if any) are recursively unified and 'true' is returned.
 * '*bindings_used' is decremented by the number of pairs of (non-trivial) bindings that are successfully unified.
 *
 * If 'false' is returned, then '*alpha', '*bound', '*bindings_used', and values referenced by these structures may be modified.
 *
 * Precondition: NULL != alpha;
 *               NULL != bound;
 *               All of the 'unification_var's accessible through 'alpha' and 'bound' (including 'alpha' itself)
 *                 have their '.rank' fields active;
 *               NULL != bindings_used
 */
static bool applyBinding(unification_var* alpha, binding* bound, size_t* bindings_used) {
  unification_cont scratch = {0};
  unification_cont* cont = &scratch;
  if (!applyBinding_cont(findRoot(alpha), bound, &cont, bindings_used)) return false;
  return NULL == cont || unify_cont(cont, bindings_used);
}

/* Unify a pair of unification variables.
 * If unification fails, then NULL is returned.
 * If unification is successful, the representative of the equivalence class of unified pair of variables is returned.
 * If alpha or beta is NULL, then NULL is returned.  This allows you to chain calls to 'unify'.
 *
 * '*bindings_used' is decremented by the number of pairs of (non-trivial) bindings that are successfully unified.
 *
 * If unification fails, then '*alpha', '*beta', '*bindings_used', and values referenced by these structures may be modified.
 *
 * Precondition: NULL != bindings_used;
 *               All of the 'unification_var's accessible through 'alpha' and 'beta' (including themselves if they are not NULL)
 *                 have their '.rank' fields active.
 */
static unification_var* unify(unification_var* alpha, unification_var* beta, size_t* bindings_used) {
  return alpha && beta ? unify_cont(&(unification_cont){ .alpha = alpha, .beta = beta }, bindings_used) : NULL;
}

/* Given a census containing a tally of the different tags that occurs in some Simplicity DAG,
 * return an upper bound on number of extra unification variables, 'extra_var',
 * that the 'typeInference' function will end up needing for that DAG.
 *
 * Precondition: NULL != census
 */
static size_t max_extra_vars(const combinator_counters* census) {
  return 4*(census->case_cnt)
       +   (census->disconnect_cnt)
       +   (census->injl_cnt)
       +   (census->injr_cnt)
       +   (census->take_cnt)
       +   (census->drop_cnt);
}

/* Solve the constraints of source and target types of each subexpression in a Simplicity DAG.
 *
 * If the Simplicity DAG, 'dag', has a principal type (including constraints due to sharing of subexprssions),
 * then 'arrow[i]'s and 'source' and 'target' fields are set to unification variables
 * that are bound to the principal source and target types of subexpression denoted by the slice '(dag_nodes[i + 1])dag'.
 * If the 'dag' does not have a principal type then either 'false' is returned
 * or there will be a cycle in the graph of the bindings of the unification variables accessible from the resulting 'arrows' array.
 *
 * If 'false' is returned, then '*arrow', '*extra_var', '*word256Type', '*bindings_used', and values referenced by these structures
 * may be modified.
 *
 * Precondition: unification_arrow arrow[len];
 *               dag_node dag[len] is well-formed;
 *               unification_var extra_var[max_extra_vars(&census)]
 *                 where 'census' contains a tally of the different tags that occur in 'dag';
 *               unification_var bound_var[N];
 *               forall '0 <= i < len', if 'dag[i].tag == JET'
 *                                      then 'dag[i].sourceIx < N' and 'dag[i].targetIx < N'
 *               word256_ix < N and 'bound_var[word256_ix]' is bound to the type 'TWO^256';
 *               '*bindings_used' is at least the number of unification variables that have
 *                 non-trivial bindings that are accessible from the 'bound_var' array.
 *
 * Postcondition: if 'true' is returned
 *                  then '*bindings_used' is at least the number of unification variables that have non-trivial bindings
 *                    that are accessible from the 'arrow' array and 'bound_var' array.
 *                  and 'arrow' is a graph of bindings that satisfies the typing constraints of imposed by 'dag'.
 */
static bool typeInference(unification_arrow* arrow, const dag_node* dag, const size_t len,
                          unification_var* extra_var, unification_var* bound_var, size_t word256_ix, size_t* bindings_used) {
  for (size_t i = 0; i < len; ++i) {
    switch (dag[i].tag) {
      #define UNIFY(a, b) { if (!unify((a), (b), bindings_used)) return false; }
      #define APPLY_BINDING(a, b) { if (!applyBinding((a), (b), bindings_used)) return false; }
     case COMP:
      arrow[i] = (unification_arrow){0};
      UNIFY(&(arrow[dag[i].child[0]].source), &(arrow[i].source));
      UNIFY(&(arrow[dag[i].child[1]].target), &(arrow[i].target));
      UNIFY(&(arrow[dag[i].child[0]].target), &(arrow[dag[i].child[1]].source));
      break;
     case ASSERTL:
     case ASSERTR:
     case CASE:
      *bindings_used += 2;
      extra_var[0] = extra_var[1] = extra_var[2] = (unification_var){0};
      extra_var[3] = (unification_var)
       { .isBound = true
       , .bound = { .kind = SUM
                  , .arg = { &extra_var[0], &extra_var[1] }
       }          };
      arrow[i] = (unification_arrow){ .source =
        { .isBound = true
        , .bound = { .kind = PRODUCT
                   , .arg = { &extra_var[3], &extra_var[2] }
        }          } };
      if (ASSERTR != dag[i].tag) {
        *bindings_used += 1;
        APPLY_BINDING(&(arrow[dag[i].child[0]].source), &((binding)
          { .kind = PRODUCT
          , .arg = { &extra_var[0], &extra_var[2] }
          }));
        UNIFY(&(arrow[dag[i].child[0]].target), &(arrow[i].target));
      }
      if (ASSERTL != dag[i].tag) {
        *bindings_used += 1;
        APPLY_BINDING(&(arrow[dag[i].child[1]].source), &((binding)
          { .kind = PRODUCT
          , .arg = { &extra_var[1], &extra_var[2] }
          }));
        UNIFY(&(arrow[dag[i].child[1]].target), &(arrow[i].target));
      }
      extra_var += 4;
      break;
     case PAIR:
      *bindings_used += 1;
      arrow[i] = (unification_arrow){ .target =
        { .isBound = true
        , .bound = { .kind = PRODUCT
                   , .arg = { &(arrow[dag[i].child[0]].target), &(arrow[dag[i].child[1]].target) }
        }          } };
      UNIFY(unify(&(arrow[dag[i].child[0]].source), &(arrow[dag[i].child[1]].source), bindings_used), &(arrow[i].source));
      break;
     case DISCONNECT:
      *bindings_used += 3;
      *extra_var = (unification_var){0};
      arrow[i] = (unification_arrow){ .target =
        { .isBound = true
        , .bound = { .kind = PRODUCT
                   , .arg = { extra_var, &(arrow[dag[i].child[1]].target) }
        }          } };
      APPLY_BINDING(&(arrow[dag[i].child[0]].source), &((binding)
        { .kind = PRODUCT
        , .arg = { &(bound_var[word256_ix]), &(arrow[i].source) }
        }));
      APPLY_BINDING(&(arrow[dag[i].child[0]].target), &((binding)
        { .kind = PRODUCT
        , .arg = { extra_var, &(arrow[dag[i].child[1]].source) }
        }));
      extra_var++;
      break;
     case INJL:
     case INJR:
      *bindings_used += 1;
      *extra_var = (unification_var){0};
      arrow[i] = (unification_arrow){ .target =
        { .isBound = true
        , .bound = { .kind = SUM
                   , .arg = { INJL == dag[i].tag ? &(arrow[dag[i].child[0]].target) : extra_var
                            , INJL == dag[i].tag ? extra_var : &(arrow[dag[i].child[0]].target)
        }          }        } };
      UNIFY(&(arrow[dag[i].child[0]].source), &(arrow[i].source));
      extra_var++;
      break;
     case TAKE:
     case DROP:
      *bindings_used += 1;
      *extra_var = (unification_var){0};
      arrow[i] = (unification_arrow){ .source =
        { .isBound = true
        , .bound = { .kind = PRODUCT
                   , .arg = { TAKE == dag[i].tag ? &(arrow[dag[i].child[0]].source) : extra_var
                            , TAKE == dag[i].tag ? extra_var : &(arrow[dag[i].child[0]].source)
        }          }        } };
      UNIFY(&(arrow[dag[i].child[0]].target), &(arrow[i].target));
      extra_var++;
      break;
     case IDEN:
      arrow[i] = (unification_arrow){0};
      UNIFY(&(arrow[i].source), &(arrow[i].target));
      break;
     case UNIT:
      /* UNIT only imposes trivial bindings, so we do not increment 'bindings_used'. */
      arrow[i] = (unification_arrow){ .target = { .isBound = true, .bound = { .kind = ONE } } };
      break;
     case HIDDEN:
     case WITNESS:
      arrow[i] = (unification_arrow){0};
      break;
     case JET:
      arrow[i] = (unification_arrow){0};
      UNIFY(&(bound_var[dag[i].sourceIx]),&arrow[i].source);
      UNIFY(&(bound_var[dag[i].targetIx]),&arrow[i].target);
      #undef APPLY_BINDING
      #undef UNIFY
    }
  }

  return true;
}

/* Determine if the representative of an equivalence class of unification variables already has a reference
 * to a frozen version of its bound type.
 *
 * Note that free variables and variables bound to the 'ONE' type are automatically always frozen.
 *
 * Precondition: NULL == var->parent
 */
static bool isFrozen(unification_var* var) {
  assert (!var->isBound || ONE != var->bound.kind || 0 == var->bound.frozen_ix);
  return !var->isBound || ONE == var->bound.kind || var->bound.frozen_ix;
}

/* Given the representative of an equivalence class of unification variables that already has a reference to a frozen version
 * of its bound type, return that reference.
 *
 * Precondition: NULL == var->parent;
 *               isFrozen(var)
 */
static size_t getFrozenIx(unification_var* var) {
  return var->isBound ? var->bound.frozen_ix : 0;
}

/* Set '*result' to the index within 'type_dag' that contains an instance type bound by 'var' where free variables are instantiated
 * at the ONE type, recursively adding new nodes to 'type_dag' as necessary.
 * '*type_dag_used' will be incremented by the number of new 'type_dag' nodes created.
 *
 * If it is impossible to create a required instance (due to a cycle in the bindings reachable by 'var'), then 'false' is returned,
 * otherwise 'true' is returned.
 *
 * If 'false' is returned, then '*result', '*type_dag', '*type_dag_used', and values referenced by these structures may be modified.
 *
 * Precondition: NULL != result;
 *               type type_dag[*type_dag_used + n]
 *                 where 'n' is the number of unfrozen unification variables that have non-trivial bindings
 *                   that are accessable from 'var' array;
 *               type type_dag[*type_dag_used] is well-formed;
 *               NULL != type_dag_used;
 *               NULL != var
 *
 * Postcondition: If 'true' is returned, then type type_dag[*type_dag_used] is well-formed
 */
static bool freeze(size_t* result, type* type_dag, size_t* type_dag_used, unification_var* var) {
  var = findRoot(var);

  if (isFrozen(var)) {
    *result = getFrozenIx(var);
    return true;
  }

  /* 'var' is not frozen, and therefore it must have a non-trivial binding.
   * Create a one item stack of unification variables 'var' to be frozen.
   */
  var->next = NULL;
  assert(!var->bound.occursCheck);
  var->bound.occursCheck = true;

  /* Attempt to freeze all variables on the stack, pushing new variables onto the stack to recursively freeze them if needed.
   *
   * All variables in the stack are representatives of their equivalence class and have just had their 'occursCheck' flag changed
   * from 'false' to 'true'.
   * Variables never change their 'occursCheck' flag back from 'true' to 'false'.
   * Variables are only removed from the stack after being frozen.
   * Each time we go through this loop, the stack size either increases by 1 or decreases by 1.
   * Therefore the total number of times this loop iterates summed over all calls to 'freeze' is bounded by
   * twice the number of unification variable (representatives) with non-trivial bindings.
   * ("twice" because once to add the variable to the stack and once to remove the variable from the stack).
   *
   * Note that number of unification_variables is bound linearly in the number of nodes in the Simplicity DAG.
   */
  while (var) {
    unification_var* typeArg[2] = { findRoot(var->bound.arg[0]), findRoot(var->bound.arg[1]) };
    if (!isFrozen(typeArg[0])) {
      /* The first type argument's representative isn't frozen.  Add it to the stack and immediately attempt to freeze it. */
      if (typeArg[0]->bound.occursCheck) return false; /* Occurs check failure. */
      typeArg[0]->bound.occursCheck = true;
      typeArg[0]->next = var;
      var = typeArg[0];
    } else if (!isFrozen(typeArg[1])) {
      /* The second type argument's representative isn't frozen.  Add it to the stack and immediately attempt to freeze it. */
      if (typeArg[1]->bound.occursCheck) return false; /* Occurs check failure. */
      typeArg[1]->bound.occursCheck = true;
      typeArg[1]->next = var;
      var = typeArg[1];
    } else {
      /* Both the type argument's representatives are frozen.
       * Create a new entry in the 'type_dag' for 'var's binding and freeze 'var'.
       */
      *result = var->bound.frozen_ix = (*type_dag_used)++;
      type_dag[var->bound.frozen_ix] = (type)
        { .kind = var->bound.kind
        , .typeArg = { getFrozenIx(typeArg[0]), getFrozenIx(typeArg[1]) }
        };
      var = var->next;
    }
  }

  return true;
}

/* Create a type DAG that supports all the type annotations of the Simplicity expression, 'dag',
 * and the input and output types of whole expression.
 *
 * If the Simplicity DAG, 'dag', has a principal type (including constraints due to sharing of subexpressions),
 * and 'arrow[i]'s and 'source' and 'target' field's unification variables are bound to the principal source and target types
 * of subexpression denoted by the slice '(dag_nodes[i + 1])dag', then we create a well-formed 'type_dag' (see 'type.h')
 * that includes the input and output types for every subexpression in 'dag', with all free type variables instantiated to the type
 * 'ONE' and add references to these type annotations to 'dag'
 * and return 'true'.
 *
 * The type Merkle roots of the 'type_dag' are also filled in.
 *
 * We say 'dag' is "well-typed" if it is a well-formed 'dag' with source and target types on all subexpressions,
 * referencing a well-formed 'type_dag', that satisfies all the typing constraints of Simplicity.
 * Hidden nodes are not actually typed and are instead assigned references to the type 'ONE' for their input and output types.
 *
 * If the Simplicity DAG, 'dag' does not have a principal type, yet the precondition on 'arrow' below is still satisfied,
 * then there must be a cycle in the graph of bindings accessible through the 'arrow' array, and in this case we return 'false'.
 *
 * In either case, '*arrow', and values referenced by these structures may be modified.
 *
 * If 'false' is returned, then the 'type_dag' array, and the '.sourceType', '.targetType' within the 'dag' array may be modified.
 *
 * Precondition: type type_dag[1 + n]
 *                 where 'n' is the number of unification variables that have non-trivial bindings
 *                   that are accessible from the 'arrow' array;
 *               dag_node dag[len] is well-formed;
 *               unification_arrow arrow[len] is a graph of bindings that satisfies the typing constraints of imposed by 'dag'.
 */
static bool freezeTypes(type* type_dag, dag_node* dag, unification_arrow* arrow, const size_t len) {
  /* First entry of type_dag gets assigned to the ONE type. */
  type_dag[0] = (type){ .kind = ONE };
  size_t type_dag_used = 1;

  for (size_t i = 0; i < len; ++i) {
    if (!(freeze(&(dag[i].sourceType), type_dag, &type_dag_used, &(arrow[i].source)) &&
          freeze(&(dag[i].targetType), type_dag, &type_dag_used, &(arrow[i].target)))) return false;
  }

  computeTypeAnalyses(type_dag, type_dag_used);

  return true;
}

/* If the Simplicity DAG, 'dag', has a principal type (including constraints due to sharing of subexpressions),
 * then allocate a well-formed type DAG containing all the types needed for all the subexpressions of 'dag',
 * with all free type variables instantiated at ONE, and set '*type_dag' to this allocation,
 * and update the '.sourceType' and '.targetType' fields within each node of the 'dag' 'type_dag[dag[i].sourceType]'
 * and 'type_dag[dag[i].targetType]' are the inferred types of the Simplicity subexpression at dag[i].
 *
 * If malloc fails, return 'false', otherwise return 'true'.
 * If the Simplicity DAG, 'dag', has no principal type (because it has a type error), then '*type_dag' is set to NULL.
 *
 * Precondition: NULL != type_dag;
 *               dag_node dag[len] is well-formed;
 *               '*census' contains a tally of the different tags that occur in 'dag'.
 *
 * Postcondition: if the return value is 'true'
 *                then either NULL == '*type_dag'
 *                     or 'dag' is well-typed with '*type_dag' and without witness values
 *                if the return value is 'false' then 'NULL == *type_dag'
 */
bool mallocTypeInference(type** type_dag, dag_node* dag, const size_t len, const combinator_counters* census) {
  *type_dag = NULL;
  /* :TODO: static assert that MAX_DAG size is small enough that these sizes fit within SIZE_T. */
  /* These arrays could be allocated on the stack, but they are potentially large, so we allocate them on the heap instead. */
  unification_arrow* arrow = len <= SIZE_MAX / sizeof(unification_arrow)
                           ? malloc(len * sizeof(unification_arrow))
                           : NULL;
  unification_var* bound_var;
  size_t word256_ix, extra_var_start;
  size_t bindings_used = mallocBoundVars(&bound_var, &word256_ix, &extra_var_start, max_extra_vars(census));

  bool result = arrow && bound_var;
  if (result) {
    if (typeInference(arrow, dag, len, bound_var + extra_var_start, bound_var, word256_ix, &bindings_used)) {
      /* :TODO: constrain the root of the dag to be a Simplicity program: ONE |- ONE */

      /* :TODO: static assert that MAX_DAG size is small enough that this size fits within SIZE_T. */
      *type_dag = bindings_used < SIZE_MAX / sizeof(type)
                ? malloc((1 + bindings_used) * sizeof(type))
                : NULL;
      result = *type_dag;
      if (result) {
        if (!freezeTypes(*type_dag, dag, arrow, len)) {
          free(*type_dag);
          *type_dag = NULL;
        }
      }
    }
  }

  free(arrow);
  free(bound_var);
  return result;
}
