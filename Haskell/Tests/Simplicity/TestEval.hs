-- | This module builds a wrapper around 'Simplicity.CoreJets.fastCoreEval' to define a 'testCoreEval' variant.
module Simplicity.TestEval
 ( TestCoreEval, testCoreEval
 ) where

import Prelude hiding (drop, fail, take)

import Control.Arrow (Kleisli(Kleisli), runKleisli)

import Simplicity.CoreJets
import Simplicity.Digest
import Simplicity.MerkleRoot
import Simplicity.Term.Core

-- | An Assert instance for 'testCoreEval'.
data TestCoreEval a b = TestCoreEval { testCoreEvalSem :: Kleisli Maybe a b
                                     , testCoreEvalFast :: FastCoreEval a b
                                     }

-- | 'testCoreEval' optimizes Simplicity with assertions evaluation using jets, similar to 'fastCoreEval',
-- but excludes the expression itself from being substituted.
-- This is used in for testing jets against their specificaitons under the assumption that jets for any subexpressions are correct.
testCoreEval = runKleisli . testCoreEvalSem

testFastKleisli = Kleisli . fastCoreEval . testCoreEvalFast

mkLeaf sComb fComb = TestCoreEval sComb fComb

mkUnary sComb fComb t = TestCoreEval (sComb (testFastKleisli t)) (fComb (testCoreEvalFast t))

mkBinary sComb fComb s t = TestCoreEval (sComb (testFastKleisli s) (testFastKleisli t))
                                        (fComb (testCoreEvalFast s) (testCoreEvalFast t))

instance Core TestCoreEval where
  iden = mkLeaf iden iden
  comp = mkBinary comp comp
  unit = mkLeaf unit unit
  injl = mkUnary injl injl
  injr = mkUnary injr injr
  match = mkBinary match match
  pair = mkBinary pair pair
  take = mkUnary take take
  drop = mkUnary drop drop

instance Assert TestCoreEval where
  assertl s h = mkUnary (flip assertl h) (flip assertl h) s
  assertr h t = mkUnary (assertr h) (assertr h) t
  fail b = mkLeaf (fail b) (fail b)
