module Simplicity.LibSecp256k1.FFI.Tests
 ( tests
 , main
 ) where

import Lens.Family2 ((^.), (^..), over, allOf, review, zipWithOf)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.QuickCheck ( Arbitrary(..), arbitrarySizedBoundedIntegral, shrinkIntegral
                             , choose, forAll, testProperty
                             )
import Test.Tasty.HUnit (assertBool, assertEqual, testCase)

import Simplicity.Digest
import Simplicity.LibSecp256k1.FFI as C
import Simplicity.LibSecp256k1.Spec as Spec
import Simplicity.Word

main = defaultMain tests

tests :: TestTree
tests = testGroup "C / SPEC"
      [ testGroup "field"
        [ hunit_feIsZero_true "C" C.feIsZero
        , hunit_feIsZero_true "Spec" Spec.feIsZero
        , testProperty "normalizeWeak" prop_normalizeWeak
        , testProperty "normalize" prop_normalize
        , testProperty "normalize_over_low" prop_normalize_over_low
        , testProperty "normalize_over_high" prop_normalize_over_high
        , testProperty "fePack" prop_fePack
        , testProperty "fePack_over_low" prop_fePack_over_low
        , testProperty "fePack_over_high" prop_fePack_over_high
        , testProperty "feUnpack" prop_feUnpack
        , testProperty "feIsZero" prop_feIsZero
        , testProperty "neg" prop_neg
        , testProperty "mulInt" prop_mulInt
        , testProperty "add" prop_add
        , testProperty "mul" prop_mul
        , testProperty "sqr" prop_sqr
        , testProperty "inv" prop_inv
        , testProperty "sqrt" prop_sqrt
        ]
      , testGroup "group"
        [ testProperty "double_inf" prop_double_inf
        , testProperty "double" prop_double
        , testProperty "addPoint" prop_addPoint
        , testProperty "addPoint_double" prop_addPoint_double
        , testProperty "addPoint_opp" prop_addPoint_opp
        , testProperty "addPoint_inf" prop_addPoint_inf
        , testProperty "addPoint_inf_l" prop_addPoint_inf_l
        , testProperty "addPoint_inf_r" prop_addPoint_inf_r
        , testProperty "offsetPoint_all" prop_offsetPoint_all
        , testProperty "offsetPoint_double" prop_offsetPoint_double
        , testProperty "offsetPoint_opp" prop_offsetPoint_opp
        , testProperty "offsetPoint_inf" prop_offsetPoint_inf
        , testProperty "offsetPointZinv_all" prop_offsetPointZinv_all
        , testProperty "offsetPointZinv_double" prop_offsetPointZinv_double
        , testProperty "offsetPointZinv_opp" prop_offsetPointZinv_opp
        , testProperty "offsetPointZinv_inf" prop_offsetPointZinv_inf
        , testProperty "eqXCoord" prop_eqXCoord
        , testProperty "eqXCoord_true" prop_eqXCoord_true
        , testProperty "hasQuadY" prop_hasQuadY
        , testProperty "hasQuadY_inf" prop_hasQuadY_inf
        ]
      , testGroup "scalar"
        [ hunit_scalarNegate_zero
        , testProperty "scalarNegate" prop_scalarNegate
        , testProperty "scalarNegate_high" prop_scalarNegate_high
        ]
      , testGroup "ecMult"
        [ testProperty "wnaf 5" (prop_wnaf 5)
        , testProperty "wnaf_high 5" (prop_wnaf_high 5)
        , testProperty "wnaf 16" (prop_wnaf 16)
        , testProperty "wnaf_high 16" (prop_wnaf_high 16)
        , testProperty "ecMult0" prop_ecMult0
        , testProperty "ecMult" prop_ecMult
        ]
      , testGroup "ecMult"
        [ testProperty "schnorr_almost_always_false" schnorr_almost_always_false
        , hunit_schnorr
      ] ]

instance Arbitrary FE where
  arbitrary = review fe arbitrary

instance Arbitrary GEJ where
  arbitrary = review gej arbitrary

instance Arbitrary Word256 where
  arbitrary = arbitrarySizedBoundedIntegral
  shrink = shrinkIntegral

instance Arbitrary Scalar where
  arbitrary = Scalar <$> arbitrary

eq_fe = zipWithOf (allOf fe) (==)
eq_gej = zipWithOf (allOf (gej.fe)) (==)
eq_fe_gej (a0,a1) (b0,b1) = (eq_fe a0 b0) && (eq_gej a1 b1)

hunit_feIsZero_true name isZero = testGroup ("feIsZero_true: " ++ name)
                           $ [ testCase (show i ++ " * bigZero1") (assertBool "feIsZero" $ isZero (C.mulInt i bigZero1)) | i <- [0..64]]
                          ++ [ testCase (show i ++ " * bigZero2") (assertBool "feIsZero" $ isZero (C.mulInt i bigZero2)) | i <- [1..16]]
                          ++ [ testCase (show (2^i) ++ " * bigZero3 + " ++ show (2^i-1) ++ " * R")
                                        (assertBool "feIsZero" $ isZero (C.mulInt (2^i) bigZero3 .+. C.mulInt (2^i-1) r)) | i <- [0..6]]
                          ++ [ testCase ("zeroIsALie "++show i) (assertBool "feIsZero" $ isZero z) | (i,z) <- zip [1..] zeroIsALie]
 where
  bigZero1 = bigZero
  bigZero2 = FE 0x3FF0BC0 0x3FFEFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0xFFFFFFF
  bigZero3 = FE 0x3F0BC00 0x3FEFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0xFFFFFFFF
  r = FE 0xF4400 0x10000 0 0 0 0 0 0 0 0
  zeroIsALie = [ FE 0xFFF0BFD1 0XFFFF0040 0 0 0 0 0 0 0 0xFFC00000
               , FE 0x3F0BFD1 0XFFFF003F 0 0 0 0 0 0 0 0xFFC00000
               , FE 0x4000000 0XFFFFFFFF 0 0 0 0 0 0 0 0
               , FE 0x7F0BFD1 0XFFFF003E 0 0 0 0 0 0 0 0xFFC00000
               ]

prop_normalizeWeak a = C.normalizeWeak a `eq_fe` Spec.normalizeWeak a
prop_normalize a = C.normalize a `eq_fe` Spec.normalize a
over_low x y = FE (0x3FFFFFF-x) (0x3FFFFFF-y) 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x03FFFFF
over_high x y = FE (0x3FFFFFF-x) (0x3FFFFFF-y) 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x07FFFFF
prop_normalize_over_low x y = prop_normalize (over_low x y)
prop_normalize_over_high x y = prop_normalize (over_high x y)
prop_fePack a = C.fePack a == Spec.fePack a
prop_fePack_over_low x y = prop_fePack (over_low x y)
prop_fePack_over_high x y = prop_fePack (over_high x y)
prop_feUnpack w = C.feUnpack w `eq_fe` Spec.feUnpack w
prop_feIsZero a = C.feIsZero a == Spec.feIsZero a -- feIsZero will essentially always be false on random inputs.
prop_neg a = forAll (choose (0, 32)) (\m -> C.neg (fromIntegral m) a `eq_fe` Spec.neg m a)
prop_mulInt a = forAll (choose (0, 32)) (\m -> C.mulInt (fromIntegral m) a `eq_fe` Spec.mulInt m a)
prop_add a b = C.add a b `eq_fe` Spec.add a b
prop_mul a b = C.mul a b `eq_fe` Spec.mul a b
prop_sqr a = C.sqr a `eq_fe` Spec.sqr a
prop_inv a = C.inv a `eq_fe` Spec.inv a
prop_sqrt a = C.sqrt a^..(traverse._fe) == Spec.sqrt a^..(traverse._fe)

gen_inf = GEJ <$> arbitrary <*> arbitrary <*> pure feZero

prop_double_inf = forAll gen_inf prop_double
prop_double a = C.double a `eq_gej` Spec.double a
prop_addPoint a b = C.addPoint a b `eq_gej` mappend a b
prop_addPoint_double z a = prop_addPoint a b
 where
  z2 = C.sqr z
  z3 = z .*. z2
  b = GEJ (a^._x .*. z2) (a^._y .*. z3) (a^._z .*. z)
prop_addPoint_opp z a = prop_addPoint a b
 where
  z2 = C.sqr z
  z3 = z .*. z2
  b = GEJ (a^._x .*. z2) (C.neg 1 (a^._y .*. z3)) (a^._z .*. z)
prop_addPoint_inf = forAll gen_inf $ \a -> forAll gen_inf $ \b -> prop_addPoint a b
prop_addPoint_inf_l b = forAll gen_inf $ \a -> prop_addPoint a b
prop_addPoint_inf_r a = forAll gen_inf $ \b -> prop_addPoint a b
prop_offsetPoint a b = C.offsetPoint a b `eq_fe_gej` Spec.offsetPoint a b
prop_offsetPoint_all a bx by = prop_offsetPoint a b
 where
  b = GE bx by
prop_offsetPoint_double z bx by = prop_offsetPoint a b
 where
  z2 = C.sqr z
  z3 = z .*. z2
  a = GEJ (bx .*. z2) (by .*. z3) z
  b = GE bx by
prop_offsetPoint_opp z bx by = prop_offsetPoint a b
 where
  z2 = C.sqr z
  z3 = z .*. z2
  a = GEJ (bx .*. z2) (C.neg 1 (by .*. z3)) z
  b = GE bx by
prop_offsetPoint_inf bx by = forAll gen_inf $ \a -> prop_offsetPoint a b
 where
  b = GE bx by
prop_offsetPointZinv a b bz = C.offsetPointZinv a b bz `eq_gej` Spec.offsetPointZinv a b bz
prop_offsetPointZinv_all a b = prop_offsetPointZinv a (GE bx by) bz
 where
  GEJ bx by bz = b
prop_offsetPointZinv_double z b = prop_offsetPointZinv a (GE bx by) bz
 where
  z2 = C.sqr z
  z3 = z .*. z2
  a = GEJ (bx .*. z2) (by .*. z3) (C.inv bz .*. z)
  GEJ bx by bz = b
prop_offsetPointZinv_opp z b = prop_offsetPointZinv a (GE bx by) bz
 where
  z2 = C.sqr z
  z3 = z .*. z2
  a = GEJ (bx .*. z2) (C.neg 1 (by .*. z3)) (C.inv bz .*. z)
  GEJ bx by bz = b
prop_offsetPointZinv_inf b = forAll gen_inf $ \a -> prop_offsetPointZinv a (GE bx by) bz
 where
  GEJ bx by bz = b
prop_eqXCoord x a = C.eqXCoord x a == Spec.eqXCoord x a -- eqXCoord will essentially always be false on random inputs.
prop_eqXCoord_true x y z = prop_eqXCoord x (GEJ (x .*. z2) y z)
 where
  z2 = C.sqr z
prop_hasQuadY a = C.hasQuadY a == Spec.hasQuadY a
prop_hasQuadY_inf = forAll gen_inf $ prop_hasQuadY

scalar_high :: Word64 -> Word64 -> Scalar
scalar_high a0 a1 = Scalar $ (fromIntegral a0) + (fromIntegral a1)*2^64 + (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF * 2^128)

hunit_scalarNegate_zero = testCase "scalarNegate_zero" (assertEqual "" (C.scalarNegate scalarZero) (Spec.scalarNegate scalarZero))
prop_scalarNegate a = C.scalarNegate a == Spec.scalarNegate a
prop_scalarNegate_high a0 a1 = prop_scalarNegate $ scalar_high a0 a1

prop_wnaf n a = C.wnaf n a == map f (Spec.wnaf n a)
 where
  f Nothing = 0
  f (Just x) = 2*x+1
prop_wnaf_high :: Int -> Word64 -> Word64 -> Bool
prop_wnaf_high n a0 a1 = prop_wnaf n $ scalar_high a0 a1

prop_ecMult x y z = C.ecMult x y z `eq_gej` Spec.ecMult x y z
prop_ecMult0 x z = prop_ecMult x y z
 where
  y = scalarZero

schnorr_almost_always_false py px m r s = not $ schnorr (PubKey py px) (review (over be256) m) (Sig r s)

hunit_schnorr = testGroup "schnorr"
              $ [ testCase "vector 1" (assertBool "schnorr" $ schnorr (PubKey False 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798) (conv 0) (Sig 0x787A848E71043D280C50470E8E1532B2DD5D20EE912A45DBDD2BD1DFBF187EF6 0x7031A98831859DC34DFFEEDDA86831842CCD0079E1F92AF177F7F22CC1DCED05))
                , testCase "vector 2" (assertBool "schnorr" $ schnorr (PubKey False 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659) (conv pi) (Sig 0x2A298DACAE57395A15D0795DDBFD1DCB564DA82B0F269BC70A74F8220429BA1D 0x1E51A22CCEC35599B8F266912281F8365FFC2D035A230434A1A64DC59F7013FD))
                , testCase "vector 3" (assertBool "schnorr" $ schnorr (PubKey True 0xFAC2114C2FBB091527EB7C64ECB11F8021CB45E8E7809D3C0938E4B8C0E5F84B) (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C) (Sig 0x00DA9B08172A9B6F0466A2DEFD817F2D7AB437E0D253CB5395A963866B3574BE 0x00880371D01766935B92D2AB4CD5C8A2A5837EC57FED7660773A05F0DE142380))
                , testCase "vector 4" (assertBool "schnorr" $ schnorr (PubKey True 0xDEFDEA4CDB677750A420FEE807EACF21EB9898AE79B9768766E4FAA04A2D4A34) (conv bla) (Sig 0x00000000000000000000003B78CE563F89A0ED9414F5AA28AD0D96D6795F9C63 0x02A8DC32E64E86A333F20EF56EAC9BA30B7246D6D25E22ADB8C6BE1AEB08D49D))
                , testCase "vector 5" (assertBool "not schnorr" . not $ schnorr (PubKey False 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659) (conv pi) (Sig 0x2A298DACAE57395A15D0795DDBFD1DCB564DA82B0F269BC70A74F8220429BA1D 0xFA16AEE06609280A19B67A24E1977E4697712B5FD2943914ECD5F730901B4AB7))
                , testCase "vector 6" (assertBool "not schnorr" . not $ schnorr (PubKey True 0xFAC2114C2FBB091527EB7C64ECB11F8021CB45E8E7809D3C0938E4B8C0E5F84B) (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C) (Sig 0x00DA9B08172A9B6F0466A2DEFD817F2D7AB437E0D253CB5395A963866B3574BE 0xD092F9D860F1776A1F7412AD8A1EB50DACCC222BC8C0E26B2056DF2F273EFDEC))
                , testCase "vector 7" (assertBool "not schnorr" . not $ schnorr (PubKey False 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798) (conv 0) (Sig 0x787A848E71043D280C50470E8E1532B2DD5D20EE912A45DBDD2BD1DFBF187EF6 0x8FCE5677CE7A623CB20011225797CE7A8DE1DC6CCD4F754A47DA6C600E59543C))
                , testCase "vector 8" (assertBool "not schnorr" . not $ schnorr (PubKey True 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659) (conv pi) (Sig 0x2A298DACAE57395A15D0795DDBFD1DCB564DA82B0F269BC70A74F8220429BA1D 0x1E51A22CCEC35599B8F266912281F8365FFC2D035A230434A1A64DC59F7013FD))
                ]
 where
  conv :: Word256 -> Hash256
  conv = review (over be256)
  pi = 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  bla = 0x4DF3C3F68FCC83B27E9D42C90431A72499F17875C81A599B566C9889B9696703
