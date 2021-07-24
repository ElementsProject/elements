{-# LANGUAGE ConstraintKinds, GADTs, RankNTypes, ScopedTypeVariables #-}
-- | This module provides the 'sortDag' function for converting a Simplicity expression into an topologically sorted, DAG representation.
module Simplicity.Dag
  ( jetDag, jetSubst
  , JetDag, NoJetDag
  -- * Type annoated, open recursive Simplicity terms
  , TermF(..), SimplicityDag
  -- * Wrapped Simplicity
  , WrappedSimplicity, unwrap
  ) where

import Prelude hiding (fail, drop, take)

import Control.Applicative (empty)
import Control.Monad.Trans.State (StateT(..), evalStateT)
import Control.Monad.Trans.Writer (Writer, execWriter, tell)
import Data.Foldable (toList)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq)
import Lens.Family2 ((&), (%~))
import Lens.Family2.State (use)
import Lens.Family2.Stock (at)

import Simplicity.Digest
import Simplicity.Inference
import Simplicity.JetType
import Simplicity.MerkleRoot
import Simplicity.Tensor
import Simplicity.Term

-- A monad used in the implementation of linearizeDag.
type LinearM j w a = StateT (Map.Map Hash256 Integer) (Writer (SimplicityDag [] () j w)) a

execLinearM :: LinearM j w a -> SimplicityDag [] () j w
execLinearM m = execWriter (evalStateT m Map.empty)

-- Emit a new node and add insert it into the state's map.
tellNode :: Hash256 -> TermF () j w Integer -> LinearM j w Integer
tellNode h iterm = StateT go
 where
  go map = do
    tell $ [f <$> iterm]
    return (sz, Map.insert h sz map)
   where
    sz = toInteger (Map.size map)
    f i = sz - i -- transform indexes to offsets

-- | A 'Simplicity' instance used with 'jetDag'.
-- This instance merges identical typed Simplicity sub-expressions to create a DAG (directed acyclic graph) structure that represents the expression.
--
-- @'JetDag' jt@ is used to create DAGs containing jets of @'JetType' jt@ by finding subexpressions that match the jet specifications of @jt@.
data JetDag jt a b = Dag { dagRoot :: IdentityRoot a b
                         , dagMap :: Map.Map Hash256 (DagMapContents jt)
                         , dagMatcher :: Maybe (MatcherInfo jt a b)
                         }

-- Each entry in the 'dagMap' contains an untyped term with references to the map index of its subexpressions, and the 'MatcherInfo' of some 'JetType'.
data DagMapContents jt = DMC { dmcTerm :: UntypedTermF (SomeArrow jt) UntypedValue Hash256, dmcMatcher :: Maybe (SomeArrow (MatcherInfo jt)) }

-- | A 'JetDag' instance that matches 'NoJets'.
type NoJetDag a b = JetDag NoJets a b

-- Topologically sort the 'Dag'.
-- The type annotations are also stripped in order to ensure the result isn't accidentally serialized before inference of principle type annotations.
-- All sharing of subexpressions remains monomorphic to ensure that types can be infered in (quasi-)linear time.
-- Any jets found are condensed into 'uJet' nodes.
linearizeDag :: (JetType jt, TyC a, TyC b) => JetDag jt a b -> SimplicityDag [] () (SomeArrow jt) UntypedValue
linearizeDag dag = execLinearM . go . identityRoot . dagRoot $ dag
 where
  someArrowMatcher (SomeArrow jm) = SomeArrow <$> matcher jm
  dmap = dagMap dag
  go h = do
    mi <- use (at h)
    case mi of
     Just i -> return i
     Nothing -> case someArrowMatcher =<< dmcMatcher contents of
                  Just jt -> tellNode h (uJet jt)
                  Nothing -> traverse go (dmcTerm contents) >>= tellNode h
   where
    contents = dmap ! h

-- | Given a Simplicity expression, return a type annotated 'SimplicityDag', with shared subexpressions and @'JetType' jt@ jets, that is suitable for serialization using "Simplicity.Serialization.BitString".
--
-- Any discounted jets marked in the original expression are discarded and replaced with their specification.
-- After the discounted jets are replaced, the Simplicity expression is scanned for jets matching the 'JetType' @jt@, which will introduce a new set of jets.
-- If a different set of jets are introduced, then the 'CommitmentRoot' of the result might also not match the 'CommitmentRoot' of the input.
-- This function invokes type inference to ensure that the type annotations are principle types (with type variables instantiated at unit types)
-- in order to ensure maximum sharing of expressions with identical 'identityRoot's.
jetDag :: forall jt a b. (JetType jt, TyC a, TyC b) => JetDag jt a b -> SimplicityDag Seq Ty (SomeArrow jt) UntypedValue
jetDag t = pass2
 where
  pass1 :: JetDag jt a b
  -- The patterns should never fail as we are running type inference on terms that are already known to be well typed.
  -- A failure of a pattern match here suggests there is an error in the type inference engine.
  -- The first pass matches jets and wraps them in a uJet combinator to ensure their types are not simplified by the type inference pass, which could possibly destroy the structure of the jets.
  pass1 = case typeCheck =<< typeInference pass1 (linearizeDag t) of
            Right pass -> pass
            Left e -> error $ "jetDag.pass1: " ++ e
  pass2 = case typeInference pass1 (linearizeDag pass1) of
            Right pass -> pass
            Left e -> error $ "jetDag.pass2: " ++ e

-- | A type isomorphic to @forall term. Simplicity term => term a b@ accessed by 'unwap'.
-- Because the type @forall term. Simplicity term => term a b@ is polymorphic, it is very difficult to memoize computations that produce such a type.
-- Internally `WrappedTerm` implements a co-yoneda transformation to provide a concrete hook for memoizing values.
type WrappedSimplicity = WrappedTerm Simplicity

data WrappedTerm simplicity a b where
  (:@:) :: (forall term. simplicity term => x -> term a b) -> x -> WrappedTerm simplicity a b

-- | Transform a @WrappedTerm simplicity@ to a @forall term. simplicity term => term a b@.
unwrap :: simplicity term => WrappedTerm simplicity a b -> term a b
unwrap (f :@: x) = f x

-- | Find all the expressions in a term that can be replaced with jets of type @jt@.
-- Because discounted jets are not transparent, this replacement will change the CMR of the term.
-- In particular the CMR values passed to 'disconnect' may be different, and thus the result of
-- evaluation could change in the presence of 'disconnect'.
jetSubst :: forall k jt a b. (JetType jt, TyC a, TyC b) => JetDag jt a b -> WrappedSimplicity a b
jetSubst t = k :@: jetDag t
 where
  k x = case typeCheck x of
                 Right pass -> pass
                 Left e -> error $ "subJets: " ++ e

-- These combinators are used in to assist making 'Dag' instances.
mkLeaf idComb jmComb uComb =
   Dag { dagRoot = root
       , dagMap = Map.singleton (identityRoot root) (DMC uComb (SomeArrow <$> jm))
       , dagMatcher = jm
       }
  where
   root = idComb
   jm = jmComb

mkUnary idComb jmComb uComb t =
   Dag { dagRoot = root
       , dagMap = Map.insert (identityRoot root) (DMC (uComb (identityRoot (dagRoot t))) (SomeArrow <$> jm))
                $ dagMap t
       , dagMatcher = jm
       }
  where
   root = idComb (dagRoot t)
   jm = jmComb <*> dagMatcher t

mkBinary idComb jmComb uComb s t =
   Dag { dagRoot = root
       , dagMap = Map.insert (identityRoot root) (DMC (uComb (identityRoot (dagRoot s)) (identityRoot (dagRoot t))) (SomeArrow <$> jm))
                $ union
       , dagMatcher = jm
       }
  where
   root = idComb (dagRoot s) (dagRoot t)
   jm = jmComb <*> dagMatcher s <*> dagMatcher t
   union = Map.union (dagMap s) (dagMap t)

-- 'Dag' instances for Simplicity expressions.
instance JetType jt => Core (JetDag jt) where
  iden = mkLeaf iden (pure iden) uIden
  comp = mkBinary comp (pure comp) uComp
  unit = mkLeaf unit (pure unit) uUnit
  injl = mkUnary injl (pure injl) uInjl
  injr = mkUnary injr (pure injr) uInjr
  match = mkBinary match (pure match) uCase
  pair = mkBinary pair (pure pair) uPair
  take = mkUnary take (pure take) uTake
  drop = mkUnary drop (pure drop) uDrop

instance JetType jt => Assert (JetDag jt) where
  assertl s h = Dag { dagRoot = root
                    , dagMap = Map.insert (identityRoot root) (DMC (uCase (identityRoot (dagRoot s)) hRoot) (SomeArrow <$> jm))
                             . Map.insert hRoot (DMC (uHidden h) Nothing)
                             $ dagMap s
                    , dagMatcher = jm
                    }
   where
    hRoot = hiddenRoot h
    root = assertl (dagRoot s) h
    jm = assertl <$> dagMatcher s <*> pure h
  assertr h t = Dag { dagRoot = root
                    , dagMap = Map.insert (identityRoot root) (DMC (uCase hRoot (identityRoot (dagRoot t))) (SomeArrow <$> jm))
                             . Map.insert hRoot (DMC (uHidden h) Nothing)
                             $ dagMap t
                    , dagMatcher = jm
                    }
   where
    hRoot = hiddenRoot h
    root = assertr h (dagRoot t)
    jm = assertr h <$> dagMatcher t
  fail b = mkLeaf (fail b) (pure (fail b)) (uFail b)

instance Witness (JetDag jt) where
  witness v = mkLeaf (witness v) empty (uWitness (untypedValue v))

instance Delegate (JetDag jt) where
  disconnect = mkBinary disconnect empty uDisconnect

instance JetType jt => Primitive (JetDag jt)  where
  primitive p = mkLeaf (primitive p) (pure (primitive p)) (Prim (SomeArrow p))

-- Exisiting jets are discarded when coverting to a dag.  They are reconstructed using a jet matcher.
instance JetType jt => Jet (JetDag jt) where
  jet t = Dag { dagRoot = root
              -- We make this identityRoot point to the same subexpression as the root of t.
              -- This lets the jet matcher match on nodes marked as jets, but otherwise the JetDag ignores marked jets.
              , dagMap = Map.insert (identityRoot root) (DMC (dmcTerm (map ! identityRoot (dagRoot dag))) (SomeArrow <$> jm))
                       $ map
              , dagMatcher = jm
              }
   where
    dag = t
    root = jet t
    jm = dagMatcher dag
    map = dagMap dag

instance JetType jt => Simplicity (JetDag jt) where
