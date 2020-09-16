{-# LANGUAGE GADTs #-}
-- This modules tests for some operations for Simplicity types.
module Simplicity.Ty.Tests (arbTy, arbValue, arbValueR, tests) where

import Prelude hiding (sum, prod)
import Data.Functor.Compose (Compose(..))
import Data.Vector.Unboxed (fromList)

import Simplicity.Serialization
import Simplicity.Ty

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (Arbitrary(..), Gen, Property, forAll, choose, elements, oneof, sized, testProperty)

-- Choose an arbitrary Simplicity type of a given size.
arbSizeTy :: Int -> Gen Ty
arbSizeTy 0 = return one
arbSizeTy n = do
  i <- choose (0, n-1)
  elements [sum, prod] <*> arbSizeTy i <*> arbSizeTy (n-1-i)

arbTy :: Gen Ty
arbTy = sized arbSizeTy

-- Choose an arbitrary value of a given Simplicity type.
arbValueR :: TyReflect a -> Gen a
arbValueR ra = case ra of
  OneR -> arbitrary
  SumR rl rr -> oneof [Left <$> arbValueR rl, Right <$> arbValueR rr]
  ProdR r1 r2 -> (,) <$> arbValueR r1 <*> arbValueR r2

arbValue :: TyC a => Gen a
arbValue = arbValueR reify

tests :: TestTree
tests = testGroup "Ty"
        [ testProperty "get-put value of Simplicity type" prop_getPutValue
        ]

-- Verify that the serialization of arbitrary values of arbitrary Simplicity types can be deserialized.
prop_getPutValue :: Property
prop_getPutValue = forAll arbTy go
  where
   go a = case reflect a of
            SomeTy ra -> forAll (arbValueR ra) (\v -> evalExactVector (getValueR ra) (fromList (putValueR ra v)) == Just v)
