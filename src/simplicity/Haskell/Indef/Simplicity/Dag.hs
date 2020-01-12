{-# LANGUAGE EmptyCase, RankNTypes, ScopedTypeVariables #-}
-- | This module provides the 'sortDag' function for converting a Simplicity expression into an topologically sorted, DAG representation.
module Simplicity.Dag
  ( jetDag
  , JetDag, NoJetDag
  -- * Type annoated, open recursive Simplicity terms.
  , TermF(..), SimplicityDag
  ) where

import Prelude hiding (fail, drop, take)

import Control.Applicative (empty)
import Control.Monad.Trans.State (StateT(..), evalStateT)
import Control.Monad.Trans.Writer (Writer, execWriter, tell)
import Data.Foldable (toList)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
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
type JetDag jt a b = Dag (SomeArrow jt) (MatcherInfo jt) a b

data Dag jt jm a b = Dag { dagRoot :: WitnessRoot a b
                         , dagMap :: Map.Map Hash256 (DagMapContents jt jm)
                         , dagMatcher :: Maybe (jm a b)
                         }

-- Each entry in the 'dagMap' contains an untyped term with references to the map index of its subexpressions, and the 'MatcherInfo' of some 'JetType'.
data DagMapContents jt jm = JDMC { jdmcTerm :: UntypedTermF jt UntypedValue Hash256, jdmcMatcher :: Maybe (SomeArrow jm) }

-- | A 'JetDag' instance that matches 'NoJets'.
type NoJetDag a b = JetDag NoJets a b

-- Topologically sort the 'Dag'.
-- The type annotations are also stripped in order to ensure the result isn't accidentally serialized before inference of principle type annotations.
-- All sharing of subexpressions remains monomorphic to ensure that types can be infered in (quasi-)linear time.
-- Any jets found by @jetMatcher@ are condensed into a 'uJet' node.
linearizeDag :: (SomeArrow jm -> Maybe jt) -> Dag jt jm a b -> SimplicityDag [] () jt UntypedValue
linearizeDag jetMatcher dag = execLinearM . go . witnessRoot . dagRoot $ dag
 where
  dmap = dagMap dag
  go h = do
    mi <- use (at h)
    case mi of
     Just i -> return i
     Nothing -> case jetMatcher =<< jdmcMatcher contents of
                  Just jt -> tellNode h (uJet jt)
                  Nothing -> traverse go (jdmcTerm contents) >>= tellNode h
   where
    contents = dmap ! h

-- | Given a Simplicity expression, return a type annotated 'SimplicityDag', with shared subexpressions and @'JetType' jt@ jets, that is suitable for serialization using "Simplicity.Serialization.BitString".
--
-- Any discounted jets marked in the original expression are discarded and replaced with their specification.
-- After the discounted jets are replaced, the Simpliciity expression is scanned for jets matching the 'JetType' @jt@, which will introduce a new set of jets.
-- This function invokes type inference to ensure that the type annotations are principle types (with type variables instantiated at unit types).
-- For these reasons the 'WitnessRoot' of the result may not match the 'WitnessRoot' of the input.
jetDag :: forall jt a b. (JetType jt, TyC a, TyC b) => JetDag jt a b -> SimplicityDag [] Ty (SomeArrow jt) UntypedValue
jetDag t = toList pass2
 where
  wrappedMatcher (SomeArrow jm) = SomeArrow <$> matcher jm
  pass1 :: JetDag jt a b
  -- The patterns should never fail as we are running type inference on terms that are already known to be well typed.
  -- A failure of a pattern match here suggests there is an error in the type inference engine.
  -- The first pass matches jets and wraps them in a uJet combinator to ensure their types are not simplified by the type inference pass, which could possibly destroy the structure of the jets.
  pass1 = case typeCheck =<< typeInference pass1 (linearizeDag wrappedMatcher t) of
            Right pass -> pass
            Left e -> error $ "sortDag.pass1: " ++ e
  linearize2 = linearizeDag wrappedMatcher pass1
  pass2 = case typeInference pass1 linearize2 of
            Right pass -> pass
            Left e -> error $ "sortDag.pass2: " ++ e

-- These combinators are used in to assist making 'Dag' instances.
mkLeaf wComb jmComb uComb =
   Dag { dagRoot = root
       , dagMap = Map.singleton (witnessRoot root) (JDMC uComb (SomeArrow <$> jm))
       , dagMatcher = jm
       }
  where
   root = wComb
   jm = jmComb

mkUnary wComb jmComb uComb t =
   Dag { dagRoot = root
       , dagMap = Map.insert (witnessRoot root) (JDMC (uComb (witnessRoot (dagRoot t))) (SomeArrow <$> jm))
                   $ dagMap t
       , dagMatcher = jm
       }
  where
   root = wComb (dagRoot t)
   jm = jmComb <*> dagMatcher t

mkBinary wComb jmComb uComb s t =
   Dag { dagRoot = root
       , dagMap = Map.insert (witnessRoot root) (JDMC (uComb (witnessRoot (dagRoot s)) (witnessRoot (dagRoot t))) (SomeArrow <$> jm))
                   $ union
       , dagMatcher = jm
       }
  where
   root = wComb (dagRoot s) (dagRoot t)
   jm = jmComb <*> dagMatcher s <*> dagMatcher t
   union = Map.union (dagMap s) (dagMap t)

-- 'Dag' instances for Simplicity expressions.
instance Core jm => Core (Dag jt jm) where
  iden = mkLeaf iden (pure iden) uIden
  comp = mkBinary comp (pure comp) uComp
  unit = mkLeaf unit (pure unit) uUnit
  injl = mkUnary injl (pure injl) uInjl
  injr = mkUnary injr (pure injr) uInjr
  match = mkBinary match (pure match) uCase
  pair = mkBinary pair (pure pair) uPair
  take = mkUnary take (pure take) uTake
  drop = mkUnary drop (pure drop) uDrop

instance Assert jm => Assert (Dag jt jm) where
  assertl s h = Dag { dagRoot = root
                    , dagMap = Map.insert (witnessRoot root) (JDMC (uCase (witnessRoot (dagRoot s)) hRoot) (SomeArrow <$> jm))
                             . Map.insert hRoot (JDMC (uHidden h) Nothing)
                             $ dagMap s
                    , dagMatcher = jm
                    }
   where
    hRoot = hiddenRoot h
    root = assertl (dagRoot s) h
    jm = assertl <$> dagMatcher s <*> pure h
  assertr h t = Dag { dagRoot = root
                    , dagMap = Map.insert (witnessRoot root) (JDMC (uCase hRoot (witnessRoot (dagRoot t))) (SomeArrow <$> jm))
                             . Map.insert hRoot (JDMC (uHidden h) Nothing)
                             $ dagMap t
                    , dagMatcher = jm
                    }
   where
    hRoot = hiddenRoot h
    root = assertr h (dagRoot t)
    jm = assertr h <$> dagMatcher t
  fail b = mkLeaf (fail b) (pure (fail b)) (uFail b)

instance Witness (Dag jt jm) where
  witness v = mkLeaf (witness v) empty (uWitness (untypedValue v))

instance Delegate (Dag jt jm) where
  disconnect = mkBinary disconnect empty uDisconnect

instance Primitive jm => Primitive (Dag jt jm)  where
  primitive p = mkLeaf (primitive p) (pure (primitive p)) (Prim (SomeArrow p))

-- Exisiting jets are discarded when coverting to a dag.  They are reconstructed using a jet matcher.
instance Jet jm => Jet (Dag jt jm) where
  jet t = Dag { dagRoot = root
              -- We make this witness root point to the same subexpression as the root of t.
              -- This lets the jet matcher match on nodes marked as jets, but otherwise the JetDag ignores marked jets.
              , dagMap = Map.insert (witnessRoot root) (JDMC (jdmcTerm (map ! witnessRoot (dagRoot dag))) (SomeArrow <$> jm))
                       $ map
              , dagMatcher = jm
              }
   where
    dag = t
    root = jet t
    jm = pure (jet t)
    map = dagMap dag

instance Jet jm => Simplicity (Dag jt jm) where
