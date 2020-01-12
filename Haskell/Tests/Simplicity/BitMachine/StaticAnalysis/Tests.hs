{-# LANGUAGE RankNTypes #-}
-- This module tests the static analysis of computation resources used by the Bit Machine by comparing it with the results of dyanmic execution by running the Bit Machine on arbitrary inputs.
module Simplicity.BitMachine.StaticAnalysis.Tests (tests) where

import Control.Monad.Trans.Maybe (runMaybeT)
import Control.Monad.Trans.Writer (execWriter)
import Data.List (foldl')

import Simplicity.BitMachine
import Simplicity.BitMachine.Authentic
import Simplicity.BitMachine.StaticAnalysis as Analysis
import Simplicity.BitMachine.StaticAnalysis.TCO as AnalysisTCO
import Simplicity.BitMachine.Translate as Translate
import Simplicity.BitMachine.Translate.TCO as TranslateTCO
import Simplicity.Programs.Word
import Simplicity.Programs.Sha256.Lib
import Simplicity.Term.Core

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (Arbitrary, Property, Testable, property, testProperty, withMaxSuccess)
import Test.Tasty.HUnit (testCase, assert)

-- Run the static analysis tests on a small set of Simplicity expressions.
tests :: TestTree
tests = testGroup "StaticAnalysis"
      [ testGroup "memSize"
        [ testSquare "fullAdder word8" (fullAdder word8)
        , testSquare "adder word8" (adder word8)
        , testSquare "fullMultiplier word8" (fullMultiplier word8)
        , testSquare "multiplier word8" (multiplier word8)
        , testSquareAdj (withMaxSuccess 10) "hashBlock" hashBlock
        ]
      ]

-- For a given program we expect the static analysis of Cell use to bound the dynamic analysis of Cell use for both naive and TCO translation.
-- We also expect TCO translation's static and dynamic analysis to be no greater than the same analysis of naive translation.
-- Together these two pairs of tests for a square of comparisions that we expect to hold.
testSquareAdj :: (Arbitrary a, TyC a, TyC b) => (forall prop. Testable prop => prop -> Property) -> String -> (forall term. (Core term) => term a b) -> TestTree
testSquareAdj adj name program = testProperty name (adj assertion)
 where
  staticMem = Analysis.cellsBnd program
  staticMemTCO = AnalysisTCO.cellsBnd program
  dynamicMem i = memSize . fold . execWriter . runMaybeT $ executeUsing (instrumentMachine . Translate.translate) program i
  dynamicMemTCO i = memSize . fold . execWriter . runMaybeT $ executeUsing (instrumentMachine . TranslateTCO.translate) program i
  square a b c d = a <= b && a <= c && b <=d && c <= d
  assertion i = square (dynamicMemTCO i) (dynamicMem i) staticMemTCO staticMem
  fold l = foldl' mappend mempty l

testSquare :: (Arbitrary a, TyC a, TyC b) => String -> (forall term. (Core term) => term a b) -> TestTree
testSquare = testSquareAdj property
