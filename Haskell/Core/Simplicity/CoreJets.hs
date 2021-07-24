-- | This modules provides a GADT for a type of "core" Simplicity jets, i.e. those jets that don't use applicaiton specific primitives.
--
-- While the 'CoreJet' data type could be made an instance of 'Simplicity.JetType.JetType', we instead generally expect it to be used as a substructure of all jets used in each specific Simplicity application.
-- The other exports of this library aid in building an instance of 'Simplicity.JetType.JetType' for those that make use of 'CoreJet' as a substructure.
{-# LANGUAGE GADTs, StandaloneDeriving, TypeFamilies #-}
module Simplicity.CoreJets
 ( CoreJet
 , specification, coreJetMap, coreJetLookup
 , implementation
 , fastCoreEval
 , putJetBit, getJetBit
 , FastCoreEval
 ) where

import Prelude hiding (fail, drop, take, subtract)

import Control.Arrow (Kleisli(Kleisli), runKleisli)
import qualified Data.Map as Map
import Data.Type.Equality ((:~:)(Refl))
import Data.Void (Void, vacuous)

import Simplicity.Digest
import Simplicity.FFI.Jets as FFI
import Simplicity.MerkleRoot
import Simplicity.Serialization
import Simplicity.Programs.Arith
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp256k1
import qualified Simplicity.Programs.Sha256.Lib as Sha256
import Simplicity.Term.Core

-- | A data type of (typed) tokens representing known "core" jets.
--
-- A core jet is a jet that doesn't use primitives.
data CoreJet a b where
  WordJet :: WordJet a b -> CoreJet a b
  ArithJet :: ArithJet a b -> CoreJet a b
  HashJet :: HashJet a b -> CoreJet a b
  Secp256k1Jet :: Secp256k1Jet a b -> CoreJet a b
  SignatureJet :: SignatureJet a b -> CoreJet a b
deriving instance Eq (CoreJet a b)
deriving instance Show (CoreJet a b)

data WordJet a b where
deriving instance Eq (WordJet a b)
deriving instance Show (WordJet a b)

data ArithJet a b where
  Add32 :: ArithJet (Word32, Word32) (Bit, Word32)
  FullAdd32 :: ArithJet (Bit, (Word32, Word32)) (Bit, Word32)
  Subtract32 :: ArithJet (Word32, Word32) (Bit, Word32)
  FullSubtract32 :: ArithJet (Bit, (Word32, Word32)) (Bit, Word32)
  Multiply32 :: ArithJet (Word32, Word32) Word64
  FullMultiply32 :: ArithJet ((Word32, Word32), (Word32, Word32)) Word64
deriving instance Eq (ArithJet a b)
deriving instance Show (ArithJet a b)

data HashJet a b where
  Sha256Block :: HashJet (Sha256.Hash, Sha256.Block) Sha256.Hash
deriving instance Eq (HashJet a b)
deriving instance Show (HashJet a b)

data Secp256k1Jet a b where
  FeNormalize :: Secp256k1Jet Secp256k1.FE Secp256k1.FE
  FeNegate :: Secp256k1Jet Secp256k1.FE Secp256k1.FE
  FeAdd :: Secp256k1Jet (Secp256k1.FE, Secp256k1.FE) Secp256k1.FE
  FeSquare :: Secp256k1Jet Secp256k1.FE Secp256k1.FE
  FeMultiply :: Secp256k1Jet (Secp256k1.FE, Secp256k1.FE) Secp256k1.FE
  FeMultiplyBeta :: Secp256k1Jet Secp256k1.FE Secp256k1.FE
  FeInvert :: Secp256k1Jet Secp256k1.FE Secp256k1.FE
  FeSquareRoot :: Secp256k1Jet Secp256k1.FE (Either () Secp256k1.FE)
  FeIsZero :: Secp256k1Jet Secp256k1.FE Bit
  FeIsOdd :: Secp256k1Jet Secp256k1.FE Bit
  ScalarNormalize :: Secp256k1Jet Secp256k1.Scalar Secp256k1.Scalar
  ScalarNegate :: Secp256k1Jet Secp256k1.Scalar Secp256k1.Scalar
  ScalarAdd :: Secp256k1Jet (Secp256k1.Scalar, Secp256k1.Scalar) Secp256k1.Scalar
  ScalarSquare :: Secp256k1Jet Secp256k1.Scalar Secp256k1.Scalar
  ScalarMultiply :: Secp256k1Jet (Secp256k1.Scalar, Secp256k1.Scalar) Secp256k1.Scalar
  ScalarMultiplyLambda :: Secp256k1Jet Secp256k1.Scalar Secp256k1.Scalar
  ScalarInvert :: Secp256k1Jet Secp256k1.Scalar Secp256k1.Scalar
  ScalarIsZero :: Secp256k1Jet Secp256k1.Scalar Bit
  GejInfinity :: Secp256k1Jet () Secp256k1.GEJ
  GejNormalize :: Secp256k1Jet Secp256k1.GEJ Secp256k1.GE
  GejNegate :: Secp256k1Jet Secp256k1.GEJ Secp256k1.GEJ
  GeNegate :: Secp256k1Jet Secp256k1.GE Secp256k1.GE
  GejDouble :: Secp256k1Jet Secp256k1.GEJ Secp256k1.GEJ
  GejAdd :: Secp256k1Jet (Secp256k1.GEJ,Secp256k1.GEJ) Secp256k1.GEJ
  GejGeAddEx :: Secp256k1Jet (Secp256k1.GEJ,Secp256k1.GE) (Secp256k1.FE, Secp256k1.GEJ)
  GejGeAdd :: Secp256k1Jet (Secp256k1.GEJ,Secp256k1.GE) Secp256k1.GEJ
  GejRescale :: Secp256k1Jet (Secp256k1.GEJ,Secp256k1.FE) Secp256k1.GEJ
  GejIsInfinity :: Secp256k1Jet Secp256k1.GEJ Bit
  GejXEquiv :: Secp256k1Jet (Secp256k1.FE, Secp256k1.GEJ) Bit
  GejYIsOdd :: Secp256k1Jet Secp256k1.GEJ Bit
  GejIsOnCurve :: Secp256k1Jet Secp256k1.GEJ Bit
  GeIsOnCurve :: Secp256k1Jet Secp256k1.GE Bit
  Generate :: Secp256k1Jet Secp256k1.Scalar Secp256k1.GEJ
  Scale :: Secp256k1Jet (Secp256k1.Scalar,Secp256k1.GEJ) Secp256k1.GEJ
  LinearCombination1 :: Secp256k1Jet ((Secp256k1.Scalar,Secp256k1.GEJ),Secp256k1.Scalar) Secp256k1.GEJ
  LinearVerify1 :: Secp256k1Jet (((Secp256k1.Scalar,Secp256k1.GE),Secp256k1.Scalar),Secp256k1.GE) ()
  PointVerify1 :: Secp256k1Jet (((Secp256k1.Scalar,Secp256k1.Point),Secp256k1.Scalar),Secp256k1.Point) ()
  Decompress :: Secp256k1Jet Secp256k1.Point (Either () Secp256k1.GE)
deriving instance Eq (Secp256k1Jet a b)
deriving instance Show (Secp256k1Jet a b)

data SignatureJet a b where
  Bip0340Verify :: SignatureJet ((Secp256k1.PubKey, Word256),Secp256k1.Sig) ()
deriving instance Eq (SignatureJet a b)
deriving instance Show (SignatureJet a b)


-- | The specification of "core" jets.  This can be used to help instantiate the 'Simplicity.JetType.specification' method.
specification :: Assert term => CoreJet a b -> term a b
specification (ArithJet x) = specificationArith x
specification (HashJet x) = specificationHash x
specification (Secp256k1Jet x) = specificationSecp256k1 x
specification (SignatureJet x) = specificationSignature x

specificationArith :: Assert term => ArithJet a b -> term a b
specificationArith Add32 = add word32
specificationArith FullAdd32 = full_add word32
specificationArith Subtract32 = subtract word32
specificationArith FullSubtract32 = full_subtract word32
specificationArith Multiply32 = multiply word32
specificationArith FullMultiply32 = full_multiply word32

specificationHash :: Assert term => HashJet a b -> term a b
specificationHash Sha256Block = Sha256.hashBlock

specificationSecp256k1 :: Assert term => Secp256k1Jet a b -> term a b
specificationSecp256k1 FeNormalize = Secp256k1.fe_normalize
specificationSecp256k1 FeNegate = Secp256k1.fe_negate
specificationSecp256k1 FeAdd = Secp256k1.fe_add
specificationSecp256k1 FeSquare = Secp256k1.fe_square
specificationSecp256k1 FeMultiply = Secp256k1.fe_multiply
specificationSecp256k1 FeMultiplyBeta = Secp256k1.fe_multiply_beta
specificationSecp256k1 FeInvert = Secp256k1.fe_invert
specificationSecp256k1 FeSquareRoot = Secp256k1.fe_square_root
specificationSecp256k1 FeIsZero = Secp256k1.fe_is_zero
specificationSecp256k1 FeIsOdd = Secp256k1.fe_is_odd
specificationSecp256k1 ScalarNormalize = Secp256k1.scalar_normalize
specificationSecp256k1 ScalarNegate = Secp256k1.scalar_negate
specificationSecp256k1 ScalarAdd = Secp256k1.scalar_add
specificationSecp256k1 ScalarSquare = Secp256k1.scalar_square
specificationSecp256k1 ScalarMultiply = Secp256k1.scalar_multiply
specificationSecp256k1 ScalarMultiplyLambda = Secp256k1.scalar_multiply_lambda
specificationSecp256k1 ScalarInvert = Secp256k1.scalar_invert
specificationSecp256k1 ScalarIsZero = Secp256k1.scalar_is_zero
specificationSecp256k1 GejInfinity = Secp256k1.gej_infinity
specificationSecp256k1 GejNormalize = Secp256k1.gej_normalize
specificationSecp256k1 GejNegate = Secp256k1.gej_negate
specificationSecp256k1 GeNegate = Secp256k1.ge_negate
specificationSecp256k1 GejDouble = Secp256k1.gej_double
specificationSecp256k1 GejAdd = Secp256k1.gej_add
specificationSecp256k1 GejGeAddEx = Secp256k1.gej_ge_add_ex
specificationSecp256k1 GejGeAdd = Secp256k1.gej_ge_add
specificationSecp256k1 GejRescale = Secp256k1.gej_rescale
specificationSecp256k1 GejIsInfinity = Secp256k1.gej_is_infinity
specificationSecp256k1 GejXEquiv = Secp256k1.gej_x_equiv
specificationSecp256k1 GejYIsOdd = Secp256k1.gej_y_is_odd
specificationSecp256k1 GejIsOnCurve = Secp256k1.gej_is_on_curve
specificationSecp256k1 GeIsOnCurve = Secp256k1.ge_is_on_curve
specificationSecp256k1 Generate = Secp256k1.generate
specificationSecp256k1 Scale = Secp256k1.scale
specificationSecp256k1 LinearCombination1 = Secp256k1.linear_combination_1
specificationSecp256k1 LinearVerify1 = Secp256k1.linear_verify_1
specificationSecp256k1 PointVerify1 = Secp256k1.point_verify_1
specificationSecp256k1 Decompress = Secp256k1.decompress

specificationSignature :: Assert term => SignatureJet a b -> term a b
specificationSignature Bip0340Verify = Secp256k1.bip0340_verify

-- | A jetted implementaiton for "core" jets.
--
-- @
-- 'implementation' x === 'runKleisli' ('specification' x)
-- @
implementation :: CoreJet a b -> a -> Maybe b
implementation (ArithJet x) = implementationArith x
implementation (HashJet x) = implementationHash x
implementation (Secp256k1Jet x) = implementationSecp256k1 x
implementation (SignatureJet x) = implementationSignature x

implementationArith :: ArithJet a b -> a -> Maybe b
implementationArith Add32 = \(x, y) -> do
  let z = fromWord32 x + fromWord32 y
  return (toBit (z >= 2 ^ 32), toWord32 z)
implementationArith FullAdd32 = \(c, (x, y)) -> do
  let z = fromWord32 x + fromWord32 y + fromWord1 c
  return (toBit (z >= 2 ^ 32), toWord32 z)
implementationArith Subtract32 = \(x, y) -> do
  let z = fromWord32 x - fromWord32 y
  return (toBit (z < 0), toWord32 z)
implementationArith FullSubtract32 = \(b, (x, y)) -> do
  let z = fromWord32 x - fromWord32 y - fromWord1 b
  return (toBit (z < 0), toWord32 z)
implementationArith Multiply32 = \(x, y) -> do
  let z = fromWord32 x * fromWord32 y
  return (toWord64 z)
implementationArith FullMultiply32 = \((x, y), (a, b)) -> do
  let z = fromWord32 x * fromWord32 y + fromWord32 a + fromWord32 b
  return (toWord64 z)

implementationHash :: HashJet a b -> a -> Maybe b
implementationHash Sha256Block = FFI.sha_256_block

implementationSecp256k1 :: Secp256k1Jet a b -> a -> Maybe b
implementationSecp256k1 FeNormalize = FFI.fe_normalize
implementationSecp256k1 FeNegate = FFI.fe_negate
implementationSecp256k1 FeAdd = FFI.fe_add
implementationSecp256k1 FeSquare = FFI.fe_square
implementationSecp256k1 FeMultiply = FFI.fe_multiply
implementationSecp256k1 FeMultiplyBeta = FFI.fe_multiply_beta
implementationSecp256k1 FeInvert = FFI.fe_invert
implementationSecp256k1 FeSquareRoot = FFI.fe_square_root
implementationSecp256k1 FeIsZero = FFI.fe_is_zero
implementationSecp256k1 FeIsOdd = FFI.fe_is_odd
implementationSecp256k1 ScalarNormalize = FFI.scalar_normalize
implementationSecp256k1 ScalarNegate = FFI.scalar_negate
implementationSecp256k1 ScalarAdd = FFI.scalar_add
implementationSecp256k1 ScalarSquare = FFI.scalar_square
implementationSecp256k1 ScalarMultiply = FFI.scalar_multiply
implementationSecp256k1 ScalarMultiplyLambda = FFI.scalar_multiply_lambda
implementationSecp256k1 ScalarInvert = FFI.scalar_invert
implementationSecp256k1 ScalarIsZero = FFI.scalar_is_zero
implementationSecp256k1 GejInfinity = FFI.gej_infinity
implementationSecp256k1 GejNormalize = FFI.gej_normalize
implementationSecp256k1 GejNegate = FFI.gej_negate
implementationSecp256k1 GeNegate = FFI.ge_negate
implementationSecp256k1 GejDouble = FFI.gej_double
implementationSecp256k1 GejAdd = FFI.gej_add
implementationSecp256k1 GejGeAddEx = FFI.gej_ge_add_ex
implementationSecp256k1 GejGeAdd = FFI.gej_ge_add
implementationSecp256k1 GejRescale = FFI.gej_rescale
implementationSecp256k1 GejIsInfinity = FFI.gej_is_infinity
implementationSecp256k1 GejXEquiv = FFI.gej_x_equiv
implementationSecp256k1 GejYIsOdd = FFI.gej_y_is_odd
implementationSecp256k1 GejIsOnCurve = FFI.gej_is_on_curve
implementationSecp256k1 GeIsOnCurve = FFI.ge_is_on_curve
implementationSecp256k1 Generate = FFI.generate
implementationSecp256k1 Scale = FFI.scale
implementationSecp256k1 LinearCombination1 = FFI.linear_combination_1
implementationSecp256k1 LinearVerify1 = FFI.linear_verify_1
implementationSecp256k1 PointVerify1 = FFI.point_verify_1
implementationSecp256k1 Decompress = FFI.decompress

implementationSignature :: SignatureJet a b -> a -> Maybe b
implementationSignature Bip0340Verify = FFI.bip0340_verify

-- | A canonical deserialization operation for "core" jets.  This can be used to help instantiate the 'Simplicity.JetType.getJetBit' method.
getJetBit :: (Monad m) => m Void -> m Bool -> m (SomeArrow CoreJet)
getJetBit abort next =  getPositive next >>= match
 where
  makeArrow p = return (SomeArrow p)
  match 2 = (someArrowMap ArithJet) <$> getJetBitArith abort next
  match 3 = (someArrowMap HashJet) <$> getJetBitHash abort next
  match 4 = (someArrowMap Secp256k1Jet) <$> getJetBitSecp256k1 abort next
  match 5 = (someArrowMap SignatureJet) <$> getJetBitSignature abort next
  getJetBitArith :: (Monad m) => m Void -> m Bool -> m (SomeArrow ArithJet)
  getJetBitArith abort next = getPositive next >>= matchArith
   where
    matchArith 2 = getPositive next >>= matchFullAdd
    matchArith 3 = getPositive next >>= matchAdd
    matchArith 7 = getPositive next >>= matchFullSubtract
    matchArith 8 = getPositive next >>= matchSubtract
    matchArith 12 = getPositive next >>= matchFullMultiply
    matchArith 13 = getPositive next >>= matchMultiply
    matchArth _ = vacuous abort
    matchAdd 5 = makeArrow Add32
    matchAdd _ = vacuous abort
    matchFullAdd 5 = makeArrow FullAdd32
    matchFullAdd _ = vacuous abort
    matchSubtract 5 = makeArrow Subtract32
    matchSubtract _ = vacuous abort
    matchFullSubtract 5 = makeArrow FullSubtract32
    matchFullSubtract _ = vacuous abort
    matchMultiply 5 = makeArrow Multiply32
    matchMultiply _ = vacuous abort
    matchFullMultiply 5 = makeArrow FullMultiply32
    matchFullMultiply _ = vacuous abort
  getJetBitHash :: (Monad m) => m Void -> m Bool -> m (SomeArrow HashJet)
  getJetBitHash abort next = getPositive next >>= matchHash
   where
    matchHash 1 = getPositive next >>= matchSha2
    matchHash _ = vacuous abort
    matchSha2 1 = makeArrow Sha256Block
    matchSha2 _ = vacuous abort
  getJetBitSecp256k1 :: (Monad m) => m Void -> m Bool -> m (SomeArrow Secp256k1Jet)
  getJetBitSecp256k1 abort next = getPositive next >>= matchSecp256k1
   where
    matchSecp256k1 35 = makeArrow FeNormalize
    matchSecp256k1 36 = makeArrow FeNegate
    matchSecp256k1 37 = makeArrow FeAdd
    matchSecp256k1 38 = makeArrow FeSquare
    matchSecp256k1 39 = makeArrow FeMultiply
    matchSecp256k1 40 = makeArrow FeMultiplyBeta
    matchSecp256k1 41 = makeArrow FeInvert
    matchSecp256k1 42 = makeArrow FeSquareRoot
    matchSecp256k1 43 = makeArrow FeIsZero
    matchSecp256k1 44 = makeArrow FeIsOdd
    matchSecp256k1 23 = makeArrow ScalarNormalize
    matchSecp256k1 24 = makeArrow ScalarNegate
    matchSecp256k1 25 = makeArrow ScalarAdd
    matchSecp256k1 26 = makeArrow ScalarSquare
    matchSecp256k1 27 = makeArrow ScalarMultiply
    matchSecp256k1 28 = makeArrow ScalarMultiplyLambda
    matchSecp256k1 29 = makeArrow ScalarInvert
    matchSecp256k1 30 = makeArrow ScalarIsZero
    matchSecp256k1 7  = makeArrow GejInfinity
    matchSecp256k1 8  = makeArrow GejNormalize
    matchSecp256k1 9  = makeArrow GejNegate
    matchSecp256k1 10 = makeArrow GeNegate
    matchSecp256k1 11 = makeArrow GejDouble
    matchSecp256k1 12 = makeArrow GejAdd
    matchSecp256k1 13 = makeArrow GejGeAddEx
    matchSecp256k1 14 = makeArrow GejGeAdd
    matchSecp256k1 15 = makeArrow GejRescale
    matchSecp256k1 16 = makeArrow GejIsInfinity
    matchSecp256k1 19 = makeArrow GejXEquiv
    matchSecp256k1 20 = makeArrow GejYIsOdd
    matchSecp256k1 21 = makeArrow GejIsOnCurve
    matchSecp256k1 22 = makeArrow GeIsOnCurve
    matchSecp256k1 6  = makeArrow Generate
    matchSecp256k1 5  = makeArrow Scale
    matchSecp256k1 4  = getPositive next >>= matchLinearCombination
    matchSecp256k1 3  = getPositive next >>= matchLinearVerify
    matchSecp256k1 1  = getPositive next >>= matchPointVerify
    matchSecp256k1 2  = makeArrow Decompress
    matchLinearCombination 1 = makeArrow LinearCombination1
    matchLinearCombination _ = vacuous abort
    matchLinearVerify 1 = makeArrow LinearVerify1
    matchLinearVerify _ = vacuous abort
    matchPointVerify 1 = makeArrow PointVerify1
    matchPointVerify _ = vacuous abort
  getJetBitSignature :: (Monad m) => m Void -> m Bool -> m (SomeArrow SignatureJet)
  getJetBitSignature abort next = getPositive next >>= matchSignature
   where
    matchSignature 1 = makeArrow Bip0340Verify
    matchSignature _ = vacuous abort

-- | A canonical serialization operation for "core" jets.  This can be used to help instantiate the 'Simplicity.JetType.putJetBit' method.
putJetBit :: CoreJet a b -> DList Bool
putJetBit (ArithJet x) = putPositive 2 . putJetBitArith x
putJetBit (HashJet x) = putPositive 3 . putJetBitHash x
putJetBit (Secp256k1Jet x) = putPositive 4 . putJetBitSecp256k1 x
putJetBit (SignatureJet x) = putPositive 5 . putJetBitSignature x

putJetBitArith :: ArithJet a b -> DList Bool
putJetBitArith FullAdd32      = putPositive 2 . putPositive 5
putJetBitArith Add32          = putPositive 3 . putPositive 5
putJetBitArith FullSubtract32 = putPositive 7 . putPositive 5
putJetBitArith Subtract32     = putPositive 8 . putPositive 5
putJetBitArith FullMultiply32 = putPositive 12 . putPositive 5
putJetBitArith Multiply32     = putPositive 13 . putPositive 5

putJetBitHash :: HashJet a b -> DList Bool
putJetBitHash Sha256Block = putPositive 1 . putPositive 1

putJetBitSecp256k1 :: Secp256k1Jet a b -> DList Bool
putJetBitSecp256k1 FeNormalize = putPositive 35
putJetBitSecp256k1 FeNegate = putPositive 36
putJetBitSecp256k1 FeAdd = putPositive 37
putJetBitSecp256k1 FeSquare = putPositive 38
putJetBitSecp256k1 FeMultiply = putPositive 39
putJetBitSecp256k1 FeMultiplyBeta = putPositive 40
putJetBitSecp256k1 FeInvert = putPositive 41
putJetBitSecp256k1 FeSquareRoot = putPositive 42
putJetBitSecp256k1 FeIsZero = putPositive 43
putJetBitSecp256k1 FeIsOdd = putPositive 44
putJetBitSecp256k1 ScalarNormalize = putPositive 23
putJetBitSecp256k1 ScalarNegate = putPositive 24
putJetBitSecp256k1 ScalarAdd = putPositive 25
putJetBitSecp256k1 ScalarSquare = putPositive 26
putJetBitSecp256k1 ScalarMultiply = putPositive 27
putJetBitSecp256k1 ScalarMultiplyLambda = putPositive 28
putJetBitSecp256k1 ScalarInvert = putPositive 29
putJetBitSecp256k1 ScalarIsZero = putPositive 30
putJetBitSecp256k1 GejInfinity = putPositive 7
putJetBitSecp256k1 GejNormalize = putPositive 8
putJetBitSecp256k1 GejNegate = putPositive 9
putJetBitSecp256k1 GeNegate = putPositive 10
putJetBitSecp256k1 GejDouble = putPositive 11
putJetBitSecp256k1 GejAdd = putPositive 12
putJetBitSecp256k1 GejGeAddEx = putPositive 13
putJetBitSecp256k1 GejGeAdd = putPositive 14
putJetBitSecp256k1 GejRescale = putPositive 15
putJetBitSecp256k1 GejIsInfinity = putPositive 16
putJetBitSecp256k1 GejXEquiv = putPositive 19
putJetBitSecp256k1 GejYIsOdd = putPositive 20
putJetBitSecp256k1 GejIsOnCurve = putPositive 21
putJetBitSecp256k1 GeIsOnCurve = putPositive 22
putJetBitSecp256k1 Generate = putPositive 6
putJetBitSecp256k1 Scale = putPositive 5
putJetBitSecp256k1 LinearCombination1 = putPositive 4 . putPositive 1
putJetBitSecp256k1 LinearVerify1 = putPositive 3 . putPositive 1
putJetBitSecp256k1 PointVerify1 = putPositive 1 . putPositive 1
putJetBitSecp256k1 Decompress = putPositive 2

putJetBitSignature :: SignatureJet a b -> DList Bool
putJetBitSignature Bip0340Verify  = putPositive 1

-- | A 'Map.Map' from the identity roots of the "core" jet specification to their corresponding token.
-- This can be used to help instantiate the 'Simplicity.JetType.matcher' method.
coreJetMap :: Map.Map Hash256 (SomeArrow CoreJet)
coreJetMap = Map.fromList
  [ -- ArithJet
    mkAssoc (ArithJet Add32)
  , mkAssoc (ArithJet Subtract32)
  , mkAssoc (ArithJet Multiply32)
  , mkAssoc (ArithJet FullAdd32)
  , mkAssoc (ArithJet FullSubtract32)
  , mkAssoc (ArithJet FullMultiply32)
    -- HashJet
  , mkAssoc (HashJet Sha256Block)
    -- Secp256k1Jet
  , mkAssoc (Secp256k1Jet FeNormalize)
  , mkAssoc (Secp256k1Jet FeNegate)
  , mkAssoc (Secp256k1Jet FeAdd)
  , mkAssoc (Secp256k1Jet FeSquare)
  , mkAssoc (Secp256k1Jet FeMultiply)
  , mkAssoc (Secp256k1Jet FeMultiplyBeta)
  , mkAssoc (Secp256k1Jet FeInvert)
  , mkAssoc (Secp256k1Jet FeSquareRoot)
  , mkAssoc (Secp256k1Jet FeIsZero)
  , mkAssoc (Secp256k1Jet FeIsOdd)
  , mkAssoc (Secp256k1Jet ScalarNormalize)
  , mkAssoc (Secp256k1Jet ScalarNegate)
  , mkAssoc (Secp256k1Jet ScalarAdd)
  , mkAssoc (Secp256k1Jet ScalarSquare)
  , mkAssoc (Secp256k1Jet ScalarMultiply)
  , mkAssoc (Secp256k1Jet ScalarMultiplyLambda)
  , mkAssoc (Secp256k1Jet ScalarInvert)
  , mkAssoc (Secp256k1Jet ScalarIsZero)
  , mkAssoc (Secp256k1Jet GejInfinity)
  , mkAssoc (Secp256k1Jet GejNormalize)
  , mkAssoc (Secp256k1Jet GejNegate)
  , mkAssoc (Secp256k1Jet GeNegate)
  , mkAssoc (Secp256k1Jet GejDouble)
  , mkAssoc (Secp256k1Jet GejAdd)
  , mkAssoc (Secp256k1Jet GejGeAddEx)
  , mkAssoc (Secp256k1Jet GejGeAdd)
  , mkAssoc (Secp256k1Jet GejIsInfinity)
  , mkAssoc (Secp256k1Jet GejXEquiv)
  , mkAssoc (Secp256k1Jet GejYIsOdd)
  , mkAssoc (Secp256k1Jet GejIsOnCurve)
  , mkAssoc (Secp256k1Jet GeIsOnCurve)
  , mkAssoc (Secp256k1Jet Generate)
  , mkAssoc (Secp256k1Jet Scale)
  , mkAssoc (Secp256k1Jet LinearCombination1)
  , mkAssoc (Secp256k1Jet LinearVerify1)
  , mkAssoc (Secp256k1Jet PointVerify1)
  , mkAssoc (Secp256k1Jet Decompress)
    -- SignatureJet
  , mkAssoc (SignatureJet Bip0340Verify)
  ]
 where
  mkAssoc :: (TyC a, TyC b) => CoreJet a b -> (Hash256, (SomeArrow CoreJet))
  mkAssoc jt = (identityRoot (specification jt), SomeArrow jt)

-- | Performs a lookup from `coreJetMap` from an `IdentityRoot`.
-- This operation preserves the Simplicity types.
coreJetLookup :: (TyC a, TyC b) => IdentityRoot a b -> Maybe (CoreJet a b)
coreJetLookup ir = do
  SomeArrow jt <- Map.lookup (identityRoot ir) coreJetMap
  let (ira, irb) = reifyArrow ir
  let (jta, jtb) = reifyArrow jt
  case (equalTyReflect ira jta, equalTyReflect irb jtb) of
    (Just Refl, Just Refl) -> return jt
    otherwise -> error "Simplicity.CoreJets.coreJetLookup: type match error"

-- | An Assert instance for 'fastCoreEval'.
data FastCoreEval a b = FastCoreEval { fastCoreEvalSem :: Kleisli Maybe a b
                                     , fastCoreEvalMatcher :: IdentityRoot a b
                                     }

-- | 'fastCoreEval' optimizes Simplicity with assertions evaluation using jets.
--
-- @
-- 'fastCoreEval' t === 'sem' t
-- @
fastCoreEval = runKleisli . fastCoreEvalSem

withJets :: (TyC a, TyC b) => FastCoreEval a b -> FastCoreEval a b
withJets ~(FastCoreEval _ ir) | Just cj <- coreJetLookup ir =
  FastCoreEval { fastCoreEvalSem = Kleisli $ implementation cj
               , fastCoreEvalMatcher = ir
               }
withJets fe | otherwise = fe

mkLeaf sComb jmComb = withJets $
  FastCoreEval { fastCoreEvalSem = sComb
               , fastCoreEvalMatcher = jmComb
               }

mkUnary sComb jmComb t = withJets $
  FastCoreEval { fastCoreEvalSem = sComb (fastCoreEvalSem t)
               , fastCoreEvalMatcher = jmComb (fastCoreEvalMatcher t)
               }
mkBinary sComb jmComb s t = withJets $
  FastCoreEval { fastCoreEvalSem = sComb (fastCoreEvalSem s) (fastCoreEvalSem t)
               , fastCoreEvalMatcher = jmComb (fastCoreEvalMatcher s) (fastCoreEvalMatcher t)
               }

instance Core FastCoreEval where
  iden = mkLeaf iden iden
  comp = mkBinary comp comp
  unit = mkLeaf unit unit
  injl = mkUnary injl injl
  injr = mkUnary injr injr
  match = mkBinary match match
  pair = mkBinary pair pair
  take = mkUnary take take
  drop = mkUnary drop drop

instance Assert FastCoreEval where
  assertl s h = mkUnary (flip assertl h) (flip assertl h) s
  assertr h t = mkUnary (assertr h) (assertr h) t
  fail b = mkLeaf (fail b) (fail b)
