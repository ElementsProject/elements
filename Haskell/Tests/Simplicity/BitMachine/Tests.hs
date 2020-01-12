{-# LANGUAGE RankNTypes #-}
-- This module tests the Bit Machine evaluation by comparing its results with Simplicity's denotational semantics.
module Simplicity.BitMachine.Tests (tests) where

import Simplicity.BitMachine
import Simplicity.BitMachine.Authentic
import Simplicity.BitMachine.Translate as Translate
import Simplicity.BitMachine.Translate.TCO as TCO
import Simplicity.Programs.Sha256.Lib
import Simplicity.Term.Core
import Simplicity.Programs.Word

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty)

-- Run tests comparing Bit Machine execution with Simplicity's denotational semantics using both naive and TCO translation.
tests :: TestTree
tests = testGroup "BitMachine"
      [ testCompiler "Translate" Translate.translate
      , testCompiler "TCO" TCO.translate
      ]

-- Given a translator and a Simplicity expression, test that execuing using the authentic Bit Machine is equivalent to denoational semantics of the Simplicity expression.
testUsing :: (Core trans, TyC a, TyC b) => (trans a b -> MachineCode) -> (forall term. Core term => term a b) -> a -> Bool
testUsing translator program x = executeUsing (runMachine . translator) program x == Just (program x)

-- Run the 'testUsing' test with a given translator on a small set of Simplicity expressions.
testCompiler :: Core trans => String -> (forall a b. (TyC a, TyC b) => trans a b -> MachineCode) -> TestTree
testCompiler name translator = testGroup name
                  [ testProperty "fullAdder word8" (testUsing translator (fullAdder word8))
                  , testProperty "adder word8" (testUsing translator (adder word8))
                  , testProperty "fullMultiplier word8" (testUsing translator (fullMultiplier word8))
                  , testProperty "multiplier word8" (testUsing translator (multiplier word8))
                  , testProperty "hashBlock" (testUsing translator hashBlock)
                  ]
