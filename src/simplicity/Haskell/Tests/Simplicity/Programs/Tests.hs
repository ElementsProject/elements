-- This module tests the Simplicity programs on arbitrary inputs.
module Simplicity.Programs.Tests (tests) where

import Prelude hiding (sqrt, all)
import Control.Arrow ((***), right)
import Data.Bits ((.|.))
import qualified Data.Bits as W
import Data.ByteString (pack)
import Data.ByteString.Short (toShort)
import qualified Data.List as L
import Lens.Family2 ((^..), allOf, zipWithOf)
import Lens.Family2.Stock (backwards, both_)

import Simplicity.Bip0340
import Simplicity.Digest
import Simplicity.LibSecp256k1.Spec ((.+.), (.*.), (.^.))
import qualified Simplicity.LibSecp256k1.Spec as Spec
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Programs.Bit
import Simplicity.Programs.LibSecp256k1.Lib
import Simplicity.Programs.Sha256.Lib
import Simplicity.Programs.Word
import Simplicity.Term.Core
import Simplicity.TestEval
import Simplicity.Ty.Arbitrary
import Simplicity.Ty.Word as Ty
import qualified Simplicity.Word as W

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit ((@=?), Assertion, testCase)
import Test.Tasty.QuickCheck (Arbitrary(..), Gen, Property
                             , arbitraryBoundedIntegral, choose, elements, forAll, resize, sized, testProperty
                             , withMaxSuccess
                             )

-- This collects the tests for the various Simplicity programs.
tests :: TestTree
tests = testGroup "Programs"
      [ testGroup "Word"
        [ testCase "low word8" assert_low8
        , testCase "high word8" assert_high8
        , testProperty "compelment word8" prop_complement8
        , testProperty "and word8" prop_and8
        , testProperty "or word8" prop_or8
        , testProperty "xor word8" prop_xor8
        , testProperty "xor3 word8" prop_xor3_8
        , testProperty "maj word8" prop_maj8
        , testProperty "ch word8" prop_ch8
        , testProperty "some word4" prop_some4
        , testProperty "all word4" prop_all4
        , testProperty "shift_const_by false word8" prop_shift_const_by_false8
        , testProperty "rotate_const word8" prop_rotate_const8
        , testProperty "transpose zv2 zv8" prop_transpose_2x8
        , testProperty "transpose zv8 zv8" prop_transpose_8x8
        ]
      , testGroup "Arith"
        [ testCase "zero word8" assert_zero8
        , testCase "one word8" assert_one8
        , testProperty "full_add word8" prop_full_add8
        , testProperty "add word8" prop_fe_add8
        , testProperty "full_increment word8" prop_full_increment8
        , testProperty "increment word8" prop_increment8
        , testProperty "full_subtract word8" prop_full_subtract8
        , testProperty "subtract word8" prop_subtract8
        , testProperty "negate word8" prop_negateate8
        , testProperty "full_decrement word8" prop_full_decrement8
        , testProperty "decrement word8" prop_decrement8
        , testProperty "fullMultiply word8" prop_full_multiply8
        , testProperty "multiply word8" prop_fe_multiplytiply8
        , testProperty "is_zero word4" prop_is_zero4
        , testProperty "is_one word4" prop_is_one4
        , testProperty "lt word8" prop_lt8
        , testProperty "le word8" prop_le8
        , testProperty "min word8" prop_min8
        , testProperty "max word8" prop_max8
        , testProperty "median word8" prop_median8
        , testProperty "lsb word8" prop_lsb8
        , testProperty "msb word8" prop_msb8
        , testProperty "div_mod word8" prop_div_mod8
        , testProperty "divide word8" prop_divide8
        , testProperty "modulo word8" prop_modulo8
        , testProperty "divides word8" prop_divides8
        , testProperty "bezout word8" prop_bezout8
        , testProperty "cofactors word8" prop_cofactors8
        , testProperty "gcd word8" prop_gcd8
        , testProperty "lcm word8" prop_lcm8
        , testProperty "absolute_value word4" prop_absolute_value4
        , testProperty "sign word4" prop_sign4
        ]
      , testProperty "sha256" prop_sha256
      , testGroup "ellipticCurve"
        [ testProperty "fe_normalize" prop_fe_normalize
        , testProperty "fe_add" prop_fe_add
        , testProperty "fe_multiply" prop_fe_multiply
        , testProperty "fe_square" prop_fe_square
        , testProperty "fe_negate" prop_fe_negate
        , testProperty "fe_invert" (withMaxSuccess 10 prop_fe_invert)
        , testProperty "fe_square_root" (withMaxSuccess 10 prop_fe_square_root)
        , testProperty "gej_rescale" prop_gej_rescale
        , testProperty "gej_rescale_inf" prop_gej_rescale_inf
        , testProperty "gej_double" prop_gej_double
        , testProperty "gej_double_inf" prop_gej_double_inf
        , testProperty "gej_add_ex" prop_gej_add_ex
        , testProperty "gej_add_ex_double" prop_gej_add_ex_double
        , testProperty "gej_add_ex_opp" prop_gej_add_ex_opp
        , testProperty "gej_add_ex_infl" prop_gej_add_ex_infl
        , testProperty "gej_add_ex_infr" prop_gej_add_ex_infr
        , testProperty "gej_add" prop_gej_add
        , testProperty "gej_add_double" prop_gej_add_double
        , testProperty "gej_add_opp" prop_gej_add_opp
        , testProperty "gej_add_infl" prop_gej_add_infl
        , testProperty "gej_add_infr" prop_gej_add_infr
        , testProperty "gej_ge_add_ex" prop_gej_ge_add_ex
        , testProperty "gej_ge_add_ex_double" prop_gej_ge_add_ex_double
        , testProperty "gej_ge_add_ex_opp" prop_gej_ge_add_ex_opp
        , testProperty "gej_ge_add_ex_inf" prop_gej_ge_add_ex_inf
        , testProperty "gej_x_equiv" prop_gej_x_equiv
        , testProperty "gej_x_equiv_inf" prop_gej_x_equiv_inf
        , testProperty "gej_x_equiv_true" prop_gej_x_equiv_true
        , testProperty "gej_x_equiv_inf_zero" prop_gej_x_equiv_inf_zero
        , testProperty "gej_is_on_curve" prop_gej_is_on_curve
        , testProperty "gej_is_on_curve_half" prop_gej_is_on_curve_half
        , testProperty "gej_is_on_curve_inf" prop_gej_is_on_curve_inf
        , testProperty "gej_is_on_curve_inf_half" prop_gej_is_on_curve_inf_half
        , testProperty "ge_is_on_curve" prop_ge_is_on_curve
        , testProperty "ge_is_on_curve_half" prop_ge_is_on_curve_half
        , testProperty "scalar_normalize" prop_scalar_normalize
        , testProperty "scalar_add" prop_scalar_add
        , testProperty "scalar_square" prop_scalar_square
        , testProperty "scalar_multiply" prop_scalar_multiply
        , testProperty "scalar_negate" prop_scalar_negate
        , testProperty "scalar_invert" prop_scalar_invert
        , testProperty "scalar_split_lambda" prop_scalar_split_lambda
        , testProperty "wnaf5" prop_wnaf5
        , testProperty "wnaf15" prop_wnaf15
        , testProperty "decompress" prop_decompress
        , testProperty "linear_combination_1" prop_linear_combination_1
        , testProperty "linear_combination_1_0" prop_linear_combination_1_0
        , testProperty "linear_combination_1_inf" prop_linear_combination_1_inf
        , testProperty "linear_check_1" prop_linear_check_1
        , testProperty "point_check_1" prop_point_check_1
        ]
      , testGroup "bip0340"
        [ testProperty "pubkey_unpack" prop_pubkey_unpack
        , testProperty "pubkey_unpack_neg" prop_pubkey_unpack_neg
        , testProperty "signature_unpack" prop_signature_unpack
        ]
      , group_bip0340_check
      ]

assert_low8 :: Assertion
assert_low8 = 0 @=? fromWord8 (low word8 ())

assert_high8 :: Assertion
assert_high8 = 0xff @=? fromWord8 (high word8 ())

prop_complement8 :: Word8 -> Bool
prop_complement8 x = W.complement (fromInteger . fromWord8 $ x) == (fromInteger . fromWord8 $ complement word8 x :: W.Word8)

prop_and8 :: Word8 -> Word8 -> Bool
prop_and8 x y = (fromInteger $ fromWord8 x) W..&. (fromInteger $ fromWord8 y)
             == (fromInteger . fromWord8 $ bitwise_and word8 (x, y) :: W.Word8)

prop_or8 :: Word8 -> Word8 -> Bool
prop_or8 x y = (fromInteger $ fromWord8 x) W..|. (fromInteger $ fromWord8 y)
            == (fromInteger . fromWord8 $ bitwise_or word8 (x, y) :: W.Word8)

prop_xor8 :: Word8 -> Word8 -> Bool
prop_xor8 x y = (fromInteger $ fromWord8 x) `W.xor` (fromInteger $ fromWord8 y)
             == (fromInteger . fromWord8 $ bitwise_xor word8 (x, y) :: W.Word8)

prop_xor3_8 :: Word8 -> Word8 -> Word8 -> Bool
prop_xor3_8 x y z = (fromInteger $ fromWord8 x) `W.xor` (fromInteger $ fromWord8 y) `W.xor` (fromInteger $ fromWord8 z)
                 == (fromInteger . fromWord8 $ bitwise_xor3 word8 (x, (y, z)) :: W.Word8)

prop_maj8 :: Word8 -> Word8 -> Word8 -> Bool
prop_maj8 x y z = zipWith3 maj (x^..bits8) (y^..bits8) (z^..bits8)
               == (fromBit <$> bitwise_maj word8 (x, (y, z))^..bits8)
 where
  maj a b c = 2 <= fromWord1 a + fromWord1 b + fromWord1 c
  bits8 x = (both_.both_.both_) x

prop_ch8 :: Word8 -> Word8 -> Word8 -> Bool
prop_ch8 x y z = zipWith3 ch (x^..bits8) (y^..bits8) (z^..bits8)
              == (fromBit <$> bitwise_ch word8 (x, (y, z))^..bits8)
 where
  ch a b c = if fromBit a then fromBit b else fromBit c
  bits8 x = (both_.both_.both_) x

prop_some4 :: Word4 -> Bool
prop_some4 x = (0 /= fromWord4 x)
            == fromBit (some word4 x)

prop_all4 :: Word4 -> Bool
prop_all4 x = (0xf == fromWord4 x)
           == fromBit (all word4 x)

prop_shift_const_by_false8 :: Word8 -> Property
prop_shift_const_by_false8 x = forAll (choose (-8,16)) $ \c ->
                               W.shift (conv x) c == conv (shift_const_by false word8 c x)
 where
  conv :: Word8 -> W.Word8
  conv = fromInteger . fromWord8

prop_rotate_const8 :: Word8 -> Property
prop_rotate_const8 x = forAll (choose (-8,16)) $ \c ->
                       W.rotate (conv x) c == conv (rotate_const word8 c x)
 where
  conv :: Word8 -> W.Word8
  conv = fromInteger . fromWord8

prop_transpose_2x8 :: Word16 -> Bool
prop_transpose_2x8 x = L.transpose (map (^..both_) (x^..both_.both_.both_))
                    == map (^..both_.both_.both_) (transpose zv2 zv8 x^..both_)
 where
  zv2 = DoubleZV SingleZV
  zv8 = DoubleZV . DoubleZV . DoubleZV $ SingleZV

prop_transpose_8x8 :: Word64 -> Bool
prop_transpose_8x8 x = L.transpose (map (^..both_.both_.both_) (x^..both_.both_.both_))
                    == map (^..both_.both_.both_) (transpose zv8 zv8' x^..both_.both_.both_)
 where
  zv8 = DoubleZV . DoubleZV . DoubleZV $ SingleZV
  zv8' = DoubleZV . DoubleZV . DoubleZV $ SingleZV -- monomorhpism restriction

assert_zero8 :: Assertion
assert_zero8 = 0 @=? fromWord8 (Arith.zero word8 ())

assert_one8 :: Assertion
assert_one8 = 0x1 @=? fromWord8 (Arith.one word8 ())

-- The specification for full adder on Word8
prop_full_add8 :: Bit -> Word8 -> Word8 -> Bool
prop_full_add8 z x y = (if fromBit carry then 2^8 else 0) + fromWord8 result8 == fromWord8 x + fromWord8 y + if fromBit z then 1 else 0
 where
  (carry, result8) = Arith.full_add word8 (z, (x, y))

-- The specification for adder on Word8
prop_fe_add8 :: Word8 -> Word8 -> Bool
prop_fe_add8 x y = (if fromBit carry then 2^8 else 0) + fromWord8 result8 == fromWord8 x + fromWord8 y
 where
  (carry, result8) = Arith.add word8 (x, y)

prop_full_increment8 :: Bit -> Word8 -> Bool
prop_full_increment8 z x = (if fromBit carry then 2^8 else 0) + fromWord8 result8 == fromWord8 x + if fromBit z then 1 else 0
 where
  (carry, result8) = Arith.full_increment word8 (z, x)

prop_increment8 :: Word8 -> Bool
prop_increment8 x = (if fromBit carry then 2^8 else 0) + fromWord8 result8 == fromWord8 x + 1
 where
  (carry, result8) = Arith.increment word8 x

-- The specification for full subtractor on Word8
prop_full_subtract8 :: Bit -> Word8 -> Word8 -> Bool
prop_full_subtract8 z x y = fromWord8 result8 == (if fromBit borrow then 2^8 else 0) + fromWord8 x - fromWord8 y - if fromBit z then 1 else 0
 where
  (borrow, result8) = Arith.full_subtract word8 (z, (x, y))

-- The specification for subtractor on Word8
prop_subtract8 :: Word8 -> Word8 -> Bool
prop_subtract8 x y = fromWord8 result8 == (if fromBit borrow then 2^8 else 0) + fromWord8 x - fromWord8 y
 where
  (borrow, result8) = Arith.subtract word8 (x, y)

prop_negateate8 :: Word8 -> Word8 -> Bool
prop_negateate8 x y = fromWord8 result8 == (if fromBit borrow then 2^8 else 0) - fromWord8 x
 where
  (borrow, result8) = Arith.negate word8 x

prop_full_decrement8 :: Bit -> Word8 -> Bool
prop_full_decrement8 z x = fromWord8 result8 == (if fromBit borrow then 2^8 else 0) + fromWord8 x - if fromBit z then 1 else 0
 where
  (borrow, result8) = Arith.full_decrement word8 (z, x)

prop_decrement8 :: Word8 -> Bool
prop_decrement8 x = fromWord8 result8 == (if fromBit borrow then 2^8 else 0) + fromWord8 x - 1
 where
  (borrow, result8) = Arith.decrement word8 x

-- The specification for full multiplier on Word8
prop_full_multiply8 :: Word8 -> Word8 -> Word8 -> Word8 -> Bool
prop_full_multiply8 w x y z = fromWord16 (Arith.full_multiply word8 ((x, y), (w, z))) == fromWord8 x * fromWord8 y + fromWord8 w + fromWord8 z

-- The specification for multiplier on Word8
prop_fe_multiplytiply8 :: Word8 -> Word8 -> Bool
prop_fe_multiplytiply8 x y = fromWord16 (Arith.multiply word8 (x, y)) == fromWord8 x * fromWord8 y

prop_is_zero4 :: Word4 -> Bool
prop_is_zero4 x = (0 == fromWord4 x) == fromBit (Arith.is_zero word4 x)

prop_is_one4 :: Word4 -> Bool
prop_is_one4 x = (1 == fromWord4 x) == fromBit (Arith.is_one word4 x)

prop_lt8 :: Word8 -> Word8 -> Bool
prop_lt8 x y = (fromWord8 x < fromWord8 y) == fromBit (Arith.lt word8 (x,y))

prop_le8 :: Word8 -> Word8 -> Bool
prop_le8 x y = (fromWord8 x <= fromWord8 y) == fromBit (Arith.le word8 (x,y))

prop_min8 :: Word8 -> Word8 -> Bool
prop_min8 x y = (fromWord8 x `min` fromWord8 y) == fromWord8 (Arith.min word8 (x,y))

prop_max8 :: Word8 -> Word8 -> Bool
prop_max8 x y = (fromWord8 x `max` fromWord8 y) == fromWord8 (Arith.max word8 (x,y))

prop_median8 :: Word8 -> Word8 -> Word8 -> Bool
prop_median8 x y z = median (fromWord8 x) (fromWord8 y) (fromWord8 z) == fromWord8 (Arith.median word8 (x,(y,z)))
 where
  median a b c = head . tail . L.sort $ [a,b,c]

prop_lsb8 :: Word8 -> Bool
prop_lsb8 x = W.testBit (fromWord8 x) 0 == fromBit (Arith.lsb word8 x)

prop_msb8 :: Word8 -> Bool
prop_msb8 x = W.testBit (fromWord8 x) 7 == fromBit (Arith.msb word8 x)

prop_div_mod8 :: Word8 -> Word8 -> Bool
prop_div_mod8 x y = div_mod_spec (fromWord8 x) (fromWord8 y) == (fromWord8 a, fromWord8 b)
 where
  div_mod_spec x 0 = (0, x)
  div_mod_spec x y = divMod x y
  (a, b) = Arith.div_mod word8 (x, y)

prop_divide8 :: Word8 -> Word8 -> Bool
prop_divide8 x y = div_spec (fromWord8 x) (fromWord8 y) == fromWord8 (Arith.divide word8 (x, y))
 where
  div_spec x 0 = 0
  div_spec x y = div x y

prop_modulo8 :: Word8 -> Word8 -> Bool
prop_modulo8 x y = mod_spec (fromWord8 x) (fromWord8 y) == fromWord8 (Arith.modulo word8 (x, y))
 where
  mod_spec x 0 = x
  mod_spec x y = mod x y

prop_divides8 :: Word8 -> Word8 -> Bool
prop_divides8 x y = divides_spec (fromWord8 x) (fromWord8 y) == fromBit (Arith.divides word8 (x, y))
 where
  divides_spec 0 y = y == 0
  divides_spec x y = y `mod` x == 0

prop_bezout8 :: Word8 -> Word8 -> Bool
prop_bezout8 x y = a * x' + b * y' == d
                && if x' == y' then (a == 1 && b == 0)
                   else if y' == 0 then (a == 1 && b == 0)
                   else if x' == 0 then (a == 0 && b == 1)
                   else (if d == y' then a == 0 else abs a * 2 * d <= y')
                     && (if d == x' then b == 0 else abs b * 2 * d <= x')
 where
  x' = fromWord8 x
  y' = fromWord8 y
  d = x' `gcd` y'
  (a, b) = either f g $ Arith.bezout word8 (x, y)
  f (a, b) = (fromWord8 a, - fromWord8 b)
  g (a, b) = (- fromWord8 a, fromWord8 b)

prop_cofactors8 :: Word8 -> Word8 -> Bool
prop_cofactors8 x y = fromWord8 x == d * fromWord8 a
                   && fromWord8 y == d * fromWord8 b
 where
  d = fromWord8 x `gcd` fromWord8 y
  (a, b) = Arith.cofactors word8 (x, y)

prop_gcd8 :: Word8 -> Word8 -> Bool
prop_gcd8 x y = (fromWord8 x `gcd` fromWord8 y) == fromWord8 (Arith.gcd word8 (x,y))

prop_lcm8 :: Word8 -> Word8 -> Bool
prop_lcm8 x y = (fromWord8 x `lcm` fromWord8 y) == fromWord16 (Arith.lcm word8 (x,y))

prop_absolute_value4 :: Word4 -> Bool
prop_absolute_value4 x = abs (fromInt4 x) == fromWord4 (Arith.absolute_value word4 x)
 where
  fromInt4 x = if 2^3 <= w4 then w4 - 2^4 else w4
   where
    w4 = fromWord4 x

prop_sign4 :: Word4 -> Bool
prop_sign4 x = signum (fromInt4 x) == fromInt2 (Arith.sign word4 x)
 where
  fromInt4 x = if 2^3 <= w4 then w4 - 2^4 else w4
   where
    w4 = fromWord4 x
  fromInt2 x = if 2^1 <= w2 then w2 - 2^2 else w2
   where
    w2 = fromWord2 x

-- The specification for SHA-256's block compression function.
prop_sha256 :: [W.Word8] -> Bool
prop_sha256 x0 = integerHash256 (bsHash (pack x)) == fromWord256 ((iv &&& iden >>> hashBlock) (toWord512 paddedInteger))
 where
  x = L.take 55 x0
  len = length x
  mkInteger l = go l 0
   where
    go [] n     = n
    go (w:ws) n = go ws (W.shiftL n 8 .|. toInteger w)
  paddedInteger = W.shiftL (mkInteger (x ++ [0x80])) (8*(64 - (len + 1))) .|. toInteger len*8

prop_fe_normalize :: FieldElement -> Bool
prop_fe_normalize a = fe_normalize (feAsTy a) == toFE (feAsSpec a)

fe_unary_prop f g = \a -> fastF (feAsTy a) == Just (toFE (g (feAsSpec a)))
 where
  fastF = testCoreEval f

fe_binary_prop f g = \a b -> fastF (feAsTy a, feAsTy b) == Just (toFE (g (feAsSpec a) (feAsSpec b)))
 where
  fastF = testCoreEval f

prop_fe_add :: FieldElement -> FieldElement -> Bool
prop_fe_add = fe_binary_prop fe_add Spec.fe_add

prop_fe_multiply :: FieldElement -> FieldElement -> Bool
prop_fe_multiply = fe_binary_prop fe_multiply Spec.fe_multiply

prop_fe_square :: FieldElement -> Bool
prop_fe_square = fe_unary_prop fe_square Spec.fe_square

prop_fe_negate :: FieldElement -> Bool
prop_fe_negate = fe_unary_prop fe_negate Spec.fe_negate

prop_fe_invert :: FieldElement -> Bool
prop_fe_invert = fe_unary_prop fe_invert Spec.fe_invert

prop_fe_square_root :: FieldElement -> Bool
prop_fe_square_root = \a -> fastSqrt (feAsTy a) == Just ((fmap toFE . maybeToTy) (Spec.fe_square_root (feAsSpec a)))
 where
  fastSqrt = testCoreEval fe_square_root

prop_gej_rescale :: GroupElementJacobian -> FieldElement -> Bool
prop_gej_rescale = \a c -> fast_gej_rescale (gejAsTy a, feAsTy c) == Just (toGEJ (Spec.gej_rescale (gejAsSpec a) (feAsSpec c)))
 where
  fast_gej_rescale = testCoreEval gej_rescale

prop_gej_rescale_inf :: FieldElement -> Property
prop_gej_rescale_inf c = forAll gen_inf $ flip prop_gej_rescale c

prop_gej_double :: GroupElementJacobian -> Bool
prop_gej_double = \a -> fast_gej_double (gejAsTy a) == Just (toGEJ (Spec.gej_double (gejAsSpec a)))
 where
  fast_gej_double = testCoreEval gej_double

prop_gej_double_inf :: Property
prop_gej_double_inf = forAll gen_inf $ prop_gej_double

prop_gej_add_ex :: GroupElementJacobian -> GroupElementJacobian -> Bool
prop_gej_add_ex = \a b ->
  let rzc = fast_gej_add_ex (gejAsTy a, gejAsTy b)
      (rz', c') = Spec.gej_add_ex (gejAsSpec a) (gejAsSpec b)
  in (fst <$> rzc) == Just (toFE rz') && (snd <$> rzc) == Just (toGEJ c')
 where
  fast_gej_add_ex = testCoreEval gej_add_ex

prop_gej_add_ex_double :: FieldElement -> GroupElementJacobian -> Bool
prop_gej_add_ex_double z b@(GroupElementJacobian bx by bz) = prop_gej_add_ex a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  bz' = feAsSpec bz
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack $ by' .*. z' .^. 3)
                           (FieldElement . Spec.fe_pack $ bz' .*. z')

prop_gej_add_ex_opp :: FieldElement -> GroupElementJacobian -> Bool
prop_gej_add_ex_opp z b@(GroupElementJacobian bx by bz) = prop_gej_add_ex a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  bz' = feAsSpec bz
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack . Spec.fe_negate $ by' .*. z' .^. 3)
                           (FieldElement . Spec.fe_pack $ bz' .*. z')

prop_gej_add_ex_infl b = forAll gen_inf $ \a -> prop_gej_add_ex a b
prop_gej_add_ex_infr a = forAll gen_inf $ \b -> prop_gej_add_ex a b

prop_gej_add :: GroupElementJacobian -> GroupElementJacobian -> Bool
prop_gej_add = \a b -> fast_gej_add (gejAsTy a, gejAsTy b) == Just (toGEJ (gejAsSpec a <> gejAsSpec b))
 where
  fast_gej_add = testCoreEval gej_add

prop_gej_add_double :: FieldElement -> GroupElementJacobian -> Bool
prop_gej_add_double z b@(GroupElementJacobian bx by bz) = prop_gej_add a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  bz' = feAsSpec bz
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack $ by' .*. z' .^. 3)
                           (FieldElement . Spec.fe_pack $ bz' .*. z')

prop_gej_add_opp :: FieldElement -> GroupElementJacobian -> Bool
prop_gej_add_opp z b@(GroupElementJacobian bx by bz) = prop_gej_add a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  bz' = feAsSpec bz
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack . Spec.fe_negate $ by' .*. z' .^. 3)
                           (FieldElement . Spec.fe_pack $ bz' .*. z')

prop_gej_add_infl b = forAll gen_inf $ \a -> prop_gej_add a b
prop_gej_add_infr a = forAll gen_inf $ \b -> prop_gej_add a b

prop_gej_ge_add_ex :: GroupElementJacobian -> GroupElement -> Bool
prop_gej_ge_add_ex = \a b ->
  let rzc = fast_gej_ge_add_ex (gejAsTy a, geAsTy b)
      (rz', c') = Spec.gej_ge_add_ex (gejAsSpec a) (geAsSpec b)
  in (fst <$> rzc) == Just (toFE rz') && (snd <$> rzc) == Just (toGEJ c')
 where
  fast_gej_ge_add_ex = testCoreEval gej_ge_add_ex

prop_gej_ge_add_ex_double :: FieldElement -> GroupElement -> Bool
prop_gej_ge_add_ex_double z b@(GroupElement bx by) = prop_gej_ge_add_ex a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack $ by' .*. z' .^. 3)
                           z

prop_gej_ge_add_ex_opp :: FieldElement -> GroupElement -> Bool
prop_gej_ge_add_ex_opp z b@(GroupElement bx by) = prop_gej_ge_add_ex a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack . Spec.fe_negate $ by' .*. z' .^. 3)
                           z

prop_gej_ge_add_ex_inf b = forAll gen_inf $ \a -> prop_gej_ge_add_ex a b

prop_gej_x_equiv :: FieldElement -> GroupElementJacobian -> Bool -- gej_x_equiv will essentially always be false on random inputs.
prop_gej_x_equiv = \x0 a -> fast_gej_x_equiv (feAsTy x0, gejAsTy a) == Just (toBit (Spec.gej_x_equiv (feAsSpec x0) (gejAsSpec a) ))
 where
  fast_gej_x_equiv = testCoreEval gej_x_equiv

prop_gej_x_equiv_inf x0 = forAll gen_inf $ prop_gej_x_equiv x0
prop_gej_x_equiv_true y z x0 = prop_gej_x_equiv x0 a
  where
   z' = feAsSpec z
   x0' = feAsSpec x0
   a = GroupElementJacobian (FieldElement . Spec.fe_pack $ x0' .*. z' .^. 2) y z

prop_gej_x_equiv_inf_zero = prop_gej_x_equiv_inf (FieldElement 0)

prop_ge_is_on_curve :: GroupElement -> Bool
prop_ge_is_on_curve = \a -> fast_ge_is_on_curve (geAsTy a) == Just (toBit (Spec.ge_is_on_curve (geAsSpec a)))
 where
  fast_ge_is_on_curve = testCoreEval ge_is_on_curve

prop_ge_is_on_curve_half = forAll gen_half_curve prop_ge_is_on_curve

prop_gej_is_on_curve :: GroupElementJacobian -> Bool
prop_gej_is_on_curve = \a -> fast_gej_is_on_curve (gejAsTy a) == Just (toBit (Spec.gej_is_on_curve (gejAsSpec a)))
 where
  fast_gej_is_on_curve = testCoreEval gej_is_on_curve

prop_gej_is_on_curve_inf = forAll gen_inf prop_gej_is_on_curve
prop_gej_is_on_curve_inf_half = forAll gen_half_curve_inf prop_gej_is_on_curve
prop_gej_is_on_curve_half = forAll gen_half_curve_jacobian prop_gej_is_on_curve

scalar_unary_prop f g = \a -> fastF (scalarAsTy a) == Just (toScalar (g (scalarAsSpec a)))
 where
  fastF = testCoreEval f

scalar_binary_prop f g = \a b -> fastF (scalarAsTy a, scalarAsTy b) == Just (toScalar (g (scalarAsSpec a) (scalarAsSpec b)))
 where
  fastF = testCoreEval f

prop_scalar_normalize :: ScalarElement -> Bool
prop_scalar_normalize a@(ScalarElement w) = scalar_normalize (scalarAsTy a) == toScalar (Spec.scalar (toInteger w))

prop_scalar_add :: ScalarElement -> ScalarElement -> Bool
prop_scalar_add = scalar_binary_prop scalar_add Spec.scalar_add

prop_scalar_square :: ScalarElement -> Bool
prop_scalar_square = scalar_unary_prop scalar_square Spec.scalar_square

prop_scalar_multiply :: ScalarElement -> ScalarElement -> Bool
prop_scalar_multiply = scalar_binary_prop scalar_multiply Spec.scalar_multiply

prop_scalar_negate :: ScalarElement -> Bool
prop_scalar_negate = scalar_unary_prop scalar_negate Spec.scalar_negate

prop_scalar_invert :: ScalarElement -> Bool
prop_scalar_invert = scalar_unary_prop scalar_invert Spec.scalar_invert

prop_scalar_split_lambda :: ScalarElement -> Bool
prop_scalar_split_lambda = \a -> ((interp *** interp) <$> fast_scalar_split_lambda (scalarAsTy a))
                            == Just (Spec.scalar_split_lambda (scalarAsSpec a))
 where
  interp (b,x) = fromWord128 x - if fromBit b then 2^128 else 0
  fast_scalar_split_lambda = testCoreEval scalar_split_lambda

prop_wnaf5 :: WnafElement -> Bool
prop_wnaf5 n = L.and $ zipWith (==) lhs (fmap (maybeToTy . fmap (unsign . toInteger)) (Spec.wnaf 5 (wnafAsSpec n) ++ repeat Nothing))
 where
  lhs = fmap fromWord4 <$> wnaf5 (wnafAsTy n)^..(backwards traverseWnaf)
  unsign x | x < 0 = 2^4 + x
           | otherwise = x

prop_wnaf15 :: WnafElement -> Bool
prop_wnaf15 n = L.and $ zipWith (==) lhs (fmap (maybeToTy . fmap (unsign . toInteger)) (Spec.wnaf 15 (wnafAsSpec n) ++ repeat Nothing))
 where
  lhs = fmap (fromWord16) <$> wnaf15 (wnafAsTy n)^..(backwards traverseWnaf)
  unsign x | x < 0 = 2^16 + 2*x+1
           | otherwise = 2*x+1

prop_linear_combination_1 :: ScalarElement -> GroupElementJacobian -> ScalarElement -> Bool
prop_linear_combination_1 = \na a ng -> fast_linear_combination_1 ((scalarAsTy na, gejAsTy a), scalarAsTy ng)
             == Just (toGEJ (Spec.linear_combination_1 (scalarAsSpec na) (gejAsSpec a) (scalarAsSpec ng)))
 where
  fast_linear_combination_1 = testCoreEval linear_combination_1

prop_linear_combination_1_0 :: GroupElementJacobian -> ScalarElement -> Bool
prop_linear_combination_1_0 a ng = prop_linear_combination_1 na a ng
 where
  na = ScalarElement 0

prop_linear_combination_1_inf :: ScalarElement -> ScalarElement -> Property
prop_linear_combination_1_inf na ng = forAll gen_inf $ \a -> prop_linear_combination_1 na a ng

prop_linear_check_1 :: ScalarElement -> GroupElement -> ScalarElement -> GroupElement -> Bool
prop_linear_check_1 = \na a ng r -> fast_linear_check_1 (((scalarAsTy na, geAsTy a), scalarAsTy ng), geAsTy r)
             == Just (toBit (Spec.linear_check [(scalarAsSpec na, geAsSpec a)] (scalarAsSpec ng) (geAsSpec r)))
 where
  fast_linear_check_1 = testCoreEval linear_check_1

prop_decompress :: PointElement -> Bool
prop_decompress = \a -> fast_decompress (pointAsTy a)
             == Just ((fmap toGE . maybeToTy) (Spec.decompress (pointAsSpec a)))
 where
  fast_decompress = testCoreEval decompress

prop_point_check_1 :: ScalarElement -> PointElement -> ScalarElement -> PointElement -> Bool
prop_point_check_1 = \na a ng r -> fast_point_check_1 (((scalarAsTy na, pointAsTy a), scalarAsTy ng), pointAsTy r)
             == Just (toBit (Spec.point_check [(scalarAsSpec na, pointAsSpec a)] (scalarAsSpec ng) (pointAsSpec r)))
 where
  fast_point_check_1 = testCoreEval point_check_1

prop_pubkey_unpack :: FieldElement -> Bool
prop_pubkey_unpack a@(FieldElement w) = fast_pubkey_unpack (feAsTy a)
                                     == Just ((fmap toPoint . maybeToTy) (Spec.pubkey_unpack (Spec.PubKey w)))
 where
  fast_pubkey_unpack = testCoreEval pubkey_unpack

prop_pubkey_unpack_neg :: FieldElement -> Bool
prop_pubkey_unpack_neg a@(FieldElement w) = fast_pubkey_unpack_neg (feAsTy a)
                                         == Just ((fmap toPoint . maybeToTy) (Spec.pubkey_unpack_neg (Spec.PubKey w)))
 where
  fast_pubkey_unpack_neg = testCoreEval pubkey_unpack_neg

prop_signature_unpack :: FieldElement -> ScalarElement -> Bool
prop_signature_unpack r@(FieldElement wr) s@(ScalarElement ws) =
  fast_signature_unpack (feAsTy r, scalarAsTy s) ==
  Just ((fmap (toFE *** toScalar) . maybeToTy) (Spec.signature_unpack (Spec.Sig wr ws)))
 where
  fast_signature_unpack = testCoreEval signature_unpack

fast_bip0340_check = fromJust . testCoreEval bip0340_check
 where
  fromJust (Just a) = fromBit a
  fromJust Nothing = False

group_bip0340_check = testGroup "bip0340_check" (zipWith case_bip0340_check_vector [0..] bip0340Vectors)
 where
  assert_bip0340_check_vector tv = bip0340TestResult tv @=? fast_bip0340_check (bip0340TestAsTy tv)
  case_bip0340_check_vector n tv = testCase name (assert_bip0340_check_vector tv)
   where
    name = "bip0340_vector_" ++ show n
