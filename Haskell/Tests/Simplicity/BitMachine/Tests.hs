{-# LANGUAGE RankNTypes #-}
-- This module tests the Bit Machine evaluation by comparing its results with Simplicity's denotational semantics.
module Simplicity.BitMachine.Tests (tests) where

import Control.Arrow (runKleisli)

import Simplicity.BitMachine
import Simplicity.BitMachine.Authentic
import Simplicity.BitMachine.Translate as Translate
import Simplicity.BitMachine.Translate.TCO as TCO
import Simplicity.Delegator
import Simplicity.Programs.Sha256.Lib
import Simplicity.Term.Core
import Simplicity.Programs.Arith
import Simplicity.Programs.Example
import qualified Simplicity.Word

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (Gen, arbitrary, arbitraryBoundedIntegral, testProperty)

-- Run tests comparing Bit Machine execution with Simplicity's denotational semantics using both naive and TCO translation.
tests :: TestTree
tests = testGroup "BitMachine"
      [ testCompiler "Translate" Translate.translate
      , testCompiler "TCO" TCO.translate
      ]

-- Given a translator and a Simplicity expression, test that execuing using the authentic Bit Machine is equivalent to denoational semantics of the Simplicity expression.
testUsing :: (Delegate trans, Assert trans, TyC a, TyC b) => (trans a b -> MachineCode) -> (forall term. (Delegate term, Assert term) => term a b) -> a -> Bool
testUsing translator program x = executeUsing (runMachine . translator) program x == (runDelegatorKleisli program x `asTypeOf` Nothing)

-- Run the 'testUsing' test with a given translator on a small set of Simplicity expressions.
testCompiler :: (Delegate trans, Assert trans) => String -> (forall a b. (TyC a, TyC b) => trans a b -> MachineCode) -> TestTree
testCompiler name translator = testGroup name
                  [ testProperty "full_add word8" (testUsing translator (full_add word8) <$> (arbitrary <×> gen16))
                  , testProperty "add word8" (testUsing translator (add word8) <$> gen16)
                  , testProperty "full_multiply word8" (testUsing translator (full_multiply word8) <$> gen32)
                  , testProperty "multiply word8" (testUsing translator (multiply word8) <$> gen16)
                  , testProperty "hashBlock" (testUsing translator hashBlock <$> (gen256 <×> gen512))
                  , testProperty "fib" (testUsing translator fib <$> (arbitrary <×> gen32))
                  ]
 where
  gen16 = (toWord16 . fromIntegral) <$> (arbitraryBoundedIntegral :: Gen Simplicity.Word.Word16)
  gen32 = (toWord32 . fromIntegral) <$> (arbitraryBoundedIntegral :: Gen Simplicity.Word.Word32)
  gen256 = (toWord256 . fromIntegral) <$> (arbitraryBoundedIntegral :: Gen Simplicity.Word.Word256)
  gen512 =  gen256 <×> gen256
  a <×> b = (,) <$> a <*> b
