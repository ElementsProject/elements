{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
-- This modules tests Simplicity's serialization and deserialization functions.
module Simplicity.Bitcoin.Serialization.Tests (tests) where

import Control.Arrow ((|||))
import Data.Either (lefts)
import Data.Foldable (toList)
import Data.Maybe (fromMaybe)
import Data.Serialize (Get, Putter, runGetState, runPut)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import Lens.Family2 (Traversal, (&), (.~))

import Simplicity.Bitcoin.Dag
import Simplicity.Bitcoin.Inference
import Simplicity.MerkleRoot
import Simplicity.Bitcoin.Primitive
import Simplicity.Bitcoin.JetType
import Simplicity.Bitcoin.Serialization.BitString as BitString
import Simplicity.Bitcoin.Serialization.ByteString as ByteString
import Simplicity.Bitcoin.Term
import Simplicity.Digest
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Programs.Sha256.Lib
import Simplicity.Serialization
import Simplicity.Ty.Tests hiding (tests)
import Simplicity.Ty.Word

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck ( Testable, testProperty, Positive(Positive)
                             , Gen, Property, arbitrary, choose, elements, forAll, listOf1, oneof)
import Test.QuickCheck.Property (Result, failed, succeeded, reason)

-- This collects the tests for the various serialization/deserialization pairs.
tests :: TestTree
tests = testGroup "Serialization"
        [ testProperty "get-put bit-string" prop_getPutBitString
        , testProperty "get-put positive" prop_getPutPositive
        , testProperty "get-put BitString DAG" prop_getPutBitStringDag
        , testProperty "get-put ByteString DAG" prop_getPutByteStringDag
        -- This collection tests type inference on a few sample programs.
        , testGroup "Inference"
          [ testInference "full_add word8" (Arith.full_add word8)
          , testInference "add word8" (Arith.add word8)
          , testInference "full_multiply word8" (Arith.full_multiply word8)
          , testInference "multiply word8" (Arith.multiply word8)
          , testInference "hashBlock" hashBlock
        ] ]

-- Check that deserialization of serialization of bit-strings returns the original input.
prop_getPutBitString :: [Bool] -> Bool
prop_getPutBitString l = evalExactVector getBitString (UV.fromList (putBitString l [])) == Just l

-- Check that deserialization of serialization of positive numbers returns the original input.
prop_getPutPositive :: Positive Integer -> Bool
prop_getPutPositive (Positive n) = evalExactVector getPositive (UV.fromList (putPositive n [])) == Just n

-- Test a 'SimplicityDag' predicate over suitable Arbitrary inputs.
forallSimplicityDag :: Testable prop => (SimplicityDag [] Ty (SomeArrow NoJets) UntypedValue -> prop) -> Property
forallSimplicityDag = forAll gen_UntypedTermF_list
 where
  gen_UntypedTermF_list = do
    l <- traverse f =<< (zip [1..] <$> listOf1 gen_UntypedTermF)
    case l of
     [] -> return []
     nl -> (:nl) <$> elements [Iden one, Unit one]
   where
    f (i, term) = traverse (const (choose (1,i))) term
  -- We are subverting putDag's type annotation requirement.  It is for purpose of testing the 'putDag' function, so maybe it is okay to do.
  -- :TODO: replace this with a proper generator for well-typed Simplicity terms.
  gen_UntypedTermF :: Gen (TermF Ty j UntypedValue ())
  gen_UntypedTermF = oneof
    [ pure $ Iden one
    , pure $ Unit one
    , pure $ Injl one one one ()
    , pure $ Injr one one one ()
    , pure $ Take one one one ()
    , pure $ Drop one one one ()
    , pure $ Comp one one one () ()
    , pure $ Case one one one one () ()
    , pure $ Pair one one one () ()
    , pure $ Disconnect one one one one () ()
    , Hidden <$> get256Bits arbitrary
    , wit
    , Prim <$> elements allPrim
    ]
   where
    -- Here we are careful to place a correct type annotation for witness values.
    wit = do
      b <- arbTy
      v <- case reflect b of SomeTy rb -> untypedValue <$> arbValueR rb
      return (Witness one b v)
    allPrim = getPrimBit [False,True]

-- Compare 'SimplicityDag' disregarding most type annotations.
-- Witness nodes are compared using the 'compareWitness' function which may or may not consider type annotations.
compareDag :: (Eq a, Eq j) => (ty0 -> w0 -> ty1 -> w1 -> Bool) -> [TermF ty0 j w0 a] -> [TermF ty1 j w1 a] -> Bool
compareDag compareWitness v1 v2 = (and $ zipWith compareNode v1 v2) && (length v1 == length v2)
 where
  compareNode (Iden _) (Iden _) = True
  compareNode (Unit _) (Unit _) = True
  compareNode (Injl _ _ _ x0) (Injl _ _ _ x1) = x0 == x1
  compareNode (Injr _ _ _ x0) (Injr _ _ _ x1) = x0 == x1
  compareNode (Take _ _ _ x0) (Take _ _ _ x1) = x0 == x1
  compareNode (Drop _ _ _ x0) (Drop _ _ _ x1) = x0 == x1
  compareNode (Comp _ _ _ x0 y0) (Comp _ _ _ x1 y1) = [x0,y0] == [x1,y1]
  compareNode (Case _ _ _ _ x0 y0) (Case _ _ _ _ x1 y1) = [x0,y0] == [x1,y1]
  compareNode (Pair _ _ _ x0 y0) (Pair _ _ _ x1 y1) = [x0,y0] == [x1,y1]
  compareNode (Disconnect _ _ _ _ x0 y0) (Disconnect _ _ _ _ x1 y1) = [x0,y0] == [x1,y1]
  compareNode (Hidden h0) (Hidden h1) = h0 == h1
  compareNode (Witness _ b0 w0) (Witness _ b1 w1) = compareWitness b0 w0 b1 w1
  compareNode (Prim p0) (Prim p1) = p0 == p1
  compareNode (Jet j0) (Jet j1) = j0 == j1
  compareNode _ _ = False

-- Check that 'BitString.putDag's serialization of 'SimplicityDag's works can be deserialized by a combination of 'BitString.getDagNoWitness' and 'BitString.getWitnessData'.
-- Note: Because we do not yet have a generator for arbitrary well-typed Simplicity expressions we cannot easily test 'BitString.putTerm' with 'BitString.getTerm'.
-- Instead we perform an akward combinator of 'BitString.getDagNoWitness' and 'BitString.getWitnessData' on mostly untyped Simplicity DAGs for now.
prop_getPutBitStringDag :: Bool -> Property
prop_getPutBitStringDag stopCode = forallSimplicityDag prop
 where
  compareWitness _ w0 _ w1 = w0 == w1
  prop :: SimplicityDag [] Ty (SomeArrow NoJets) UntypedValue -> Result
  prop v = case eval of
    Left msg -> failed { reason = show msg }
    Right (pdag, wdag) | not (compareDag (\_ _ _ _ -> True) v (toList pdag)) -> failed { reason = "Bitstring.getDagNoWiness returned bad value" }
                       | not (compareDag compareWitness v (toList wdag)) -> failed { reason = "Bitstring.getWitnessData returend bad value" }
                       | otherwise -> succeeded
   where
    Just bs = (if stopCode then BitString.putDagStopCode else BitString.putDagLengthCode) v -- generation is designed to create terms that always succeed at serializaiton.
    eval = flip evalStreamWithError bs $ \abort next -> do
     pdag <- (if stopCode then BitString.getDagNoWitnessStopCode else BitString.getDagNoWitnessLengthCode) abort next
     wdag <- BitString.getWitnessData vStripped abort next
     return (pdag, wdag)
    vStripped = v & traverse . witness_ .~ ()
     where
      witness_ :: Traversal (TermF ty j w0 a) (TermF ty j w1 a) w0 w1
      witness_ = witnessData . const

-- Check that deserialization of serialization of 'SimplicityDag's works for the byte-string serialization.
prop_getPutByteStringDag :: Property
prop_getPutByteStringDag = forallSimplicityDag prop
 where
  compareWitness b w0 _ w1 = case reflect b of
                               SomeTy rb -> fromMaybe False $ (==) <$> castUntypedValueR rb w0 <*> evalExactVector (getValueR rb) w1
  prop v = case runGetState (toList <$> ByteString.getDag) bs 0 of
            Left _ -> False
            Right (v', rest) -> rest == mempty && compareDag compareWitness v (v' :: SimplicityDag [] () (SomeArrow NoJets) (UV.Vector Bool))
   where
    Just bs = runPut <$> ByteString.putDag v -- generation is designed to create terms that always succeed at serializaiton.

-- Check that type inference on Simplicity expressions produce correct terms by testing their Merkle roots.
testInference :: forall a b. (TyC a, TyC b) => String -> (forall term. (Core term) => term a b) -> TestTree
testInference name program = testGroup name [testProperty "CommitmentRoot" assertion1, testProperty "AnnotatedRoot" assertion2]
 where
  dag :: NoJetDag a b
  dag = program
  -- type inference on first pass is not necessarily equal to the orginal program because the Haskell type of internal nodes in the original program might not have the term's principle type.
  pass1 :: forall term. Simplicity term => Either String (term a b)
  pass1 = typeCheck =<< typeInference dag (jetDag dag)
  -- Type inference on the second pass ought to always be equal to the first pass.
  pass2 :: forall term. Simplicity term => Either String (term a b)
  pass2 = typeCheck =<< (typeInference dag . jetDag) =<< (pass1 :: Either String (NoJetDag a b))
  assertion1 = pass1 == Right (program :: CommitmentRoot a b)
  assertion2 = pass2 == (pass1 :: Either String (AnnotatedRoot a b))
