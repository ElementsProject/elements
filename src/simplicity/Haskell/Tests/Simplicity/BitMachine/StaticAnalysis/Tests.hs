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
import Simplicity.Programs.Arith
import Simplicity.Programs.Example
import Simplicity.Programs.Sha256.Lib
import Simplicity.Term.Core
import qualified Simplicity.Word

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck ( Gen, Property, Testable
                             , arbitrary, arbitraryBoundedIntegral
                             , property, testProperty
                             , withMaxSuccess
                             )
import Test.Tasty.HUnit (testCase, assert)

-- Run the static analysis tests on a small set of Simplicity expressions.
tests :: TestTree
tests = testGroup "StaticAnalysis"
      [ testGroup "memSize"
        [ testSquare "full_add word8" (full_add word8) (arbitrary <×> gen16)
        , testSquare "add word8" (add word8) gen16
        , testSquare "full_multiply word8" (full_multiply word8) gen32
        , testSquare "multiply word8" (multiply word8) gen16
        , testSquareAdj (withMaxSuccess 10) "hashBlock" hashBlock (gen256 <×> gen512)
        , testSquareAdj (withMaxSuccess 10) "fib" fib (arbitrary <×> gen32)
        ]
      ]
 where
  gen16 = (toWord16 . fromIntegral) <$> (arbitraryBoundedIntegral :: Gen Simplicity.Word.Word16)
  gen32 = (toWord32 . fromIntegral) <$> (arbitraryBoundedIntegral :: Gen Simplicity.Word.Word32)
  gen256 = (toWord256 . fromIntegral) <$> (arbitraryBoundedIntegral :: Gen Simplicity.Word.Word256)
  gen512 =  gen256 <×> gen256
  a <×> b = (,) <$> a <*> b

-- For a given program we expect the static analysis of Cell use to bound the dynamic analysis of Cell use for both naive and TCO translation.
-- We also expect TCO translation's static and dynamic analysis to be no greater than the same analysis of naive translation.
-- Together these two pairs of tests for a square of comparisions that we expect to hold.
testSquareAdj :: (TyC a, TyC b) => (forall prop. Testable prop => prop -> Property) -> String -> (forall term. (Delegate term, Assert term) => term a b) -> Gen a -> TestTree
testSquareAdj adj name program gen = testProperty name (adj (assertion <$> gen))
 where
  staticMem = Analysis.cellsBnd program
  staticMemTCO = AnalysisTCO.cellsBnd program
  dynamicMem i = memSize . fold . execWriter . runMaybeT $ executeUsing (instrumentMachine . Translate.translate) program i
  dynamicMemTCO i = memSize . fold . execWriter . runMaybeT $ executeUsing (instrumentMachine . TranslateTCO.translate) program i
  square a b c d = a <= b && a <= c && b <=d && c <= d
  assertion i = square (dynamicMemTCO i) (dynamicMem i) staticMemTCO staticMem
  fold l = foldl' mappend mempty l

testSquare :: (TyC a, TyC b) => String -> (forall term. (Delegate term, Assert term) => term a b) -> Gen a -> TestTree
testSquare = testSquareAdj property
