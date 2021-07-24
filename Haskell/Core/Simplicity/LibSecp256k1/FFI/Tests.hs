module Simplicity.LibSecp256k1.FFI.Tests
 ( tests
 , main
 ) where

import Control.Arrow ((***))
import Lens.Family2 ((^.), (^..), over, allOf, review, zipWithOf)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.QuickCheck ( Arbitrary(..), arbitrarySizedBoundedIntegral, shrinkIntegral
                             , choose, forAll, testProperty
                             )
import Test.Tasty.HUnit ((@?=), assertBool, testCase)

import Simplicity.Digest
import Simplicity.LibSecp256k1.FFI as C
import Simplicity.LibSecp256k1.Spec as Spec
import Simplicity.Word

main = defaultMain tests

tests :: TestTree
tests = testGroup "C / SPEC"
      [ testGroup "field"
        [ testProperty "fe_is_zero" prop_fe_is_zero
        , testProperty "fe_negate" prop_fe_negate
        , testProperty "fe_add" prop_fe_add
        , testProperty "fe_multiply" prop_fe_multiply
        , testProperty "fe_square" prop_fe_square
        , testProperty "fe_invert" prop_fe_invert
        , testProperty "fe_square_root" prop_fe_square_root
        ]
      , testGroup "group"
        [ testProperty "gej_rescale" prop_gej_rescale
        , testProperty "gej_rescale_zero" prop_gej_rescale_zero
        , testProperty "gej_rescale_inf" prop_gej_rescale_inf
        , testProperty "gej_double_inf" prop_gej_double_inf
        , testProperty "gej_double" prop_gej_double
        , testProperty "gej_add" prop_gej_add
        , testProperty "gej_add_double" prop_gej_add_double
        , testProperty "gej_add_opp" prop_gej_add_opp
        , testProperty "gej_add_inf" prop_gej_add_inf
        , testProperty "gej_add_inf_l" prop_gej_add_inf_l
        , testProperty "gej_add_inf_r" prop_gej_add_inf_r
        , testProperty "gej_ge_add_ex_all" prop_gej_ge_add_ex_all
        , testProperty "gej_ge_add_ex_double" prop_gej_ge_add_ex_double
        , testProperty "gej_ge_add_ex_opp" prop_gej_ge_add_ex_opp
        , testProperty "gej_ge_add_ex_inf" prop_gej_ge_add_ex_inf
        , testProperty "gej_ge_add_zinv_all" prop_gej_ge_add_zinv_all
        , testProperty "gej_ge_add_zinv_double" prop_gej_ge_add_zinv_double
        , testProperty "gej_ge_add_zinv_opp" prop_gej_ge_add_zinv_opp
        , testProperty "gej_ge_add_zinv_inf" prop_gej_ge_add_zinv_inf
        , testProperty "gej_x_equiv" prop_gej_x_equiv
        , testProperty "gej_x_equiv_inf" prop_gej_x_equiv_inf
        , testProperty "gej_x_equiv_true" prop_gej_x_equiv_true
        , testProperty "gej_x_equiv_inf_zero" prop_gej_x_equiv_inf_zero
        , testProperty "ge_scale_lambda" prop_ge_scale_lambda
        ]
      , testGroup "scalar"
        [ testCase "scalar_negate_zero" hunit_scalar_negate_zero
        , testProperty "scalar_negate" prop_scalar_negate
        , testProperty "scalar_split_lambda" prop_scalar_split_lambda
        , testProperty "scalar_split_128" prop_scalar_split_128
        ]
      , testGroup "ecMult"
        [ testProperty "wnaf 5" (prop_wnaf 5)
        , testProperty "wnaf 15" (prop_wnaf 15)
        , testProperty "linear_combination_1_inf" prop_linear_combination_1_inf
        , testProperty "linear_combination_1_0" prop_linear_combination_1_0
        , testProperty "linear_combination_1" prop_linear_combination_1
        ]
      , testGroup "ecMult"
        [ testProperty "bip0340_almost_always_false" bip0340_almost_always_false
        , hunit_bip0340
      ] ]

instance Arbitrary Word256 where
  arbitrary = arbitrarySizedBoundedIntegral
  shrink = shrinkIntegral

instance Arbitrary FE where
  arbitrary = mkFE <$> arbitrary
   where
    mkFE :: Word256 -> FE
    mkFE = fe . toInteger

instance Arbitrary GE where
  arbitrary = GE <$> arbitrary <*> arbitrary

instance Arbitrary GEJ where
  arbitrary = review gej arbitrary

instance Arbitrary Scalar where
  arbitrary = mkScalar <$> arbitrary
   where
    mkScalar :: Word256 -> Scalar
    mkScalar = scalar . toInteger

eq_ge (GE x1 y1) (GE x2 y2) = (x1 == x2) && (y1 == y2)
eq_gej = zipWithOf (allOf gej) (==)
eq_fe_gej (a0,a1) (b0,b1) = (a0 == b0) && (eq_gej a1 b1)

prop_fe_is_zero a = C.fe_is_zero a == Spec.fe_is_zero a -- fe_is_zero will essentially always be false on random inputs.
prop_fe_negate a = C.fe_negate a == Spec.fe_negate a
prop_fe_add a b = C.fe_add a b == Spec.fe_add a b
prop_fe_multiply a b = C.fe_multiply a b == Spec.fe_multiply a b
prop_fe_square a = C.fe_square a == Spec.fe_square a
prop_fe_invert a = C.fe_invert a == Spec.fe_invert a
prop_fe_square_root a = C.fe_square_root a == Spec.fe_square_root a

gen_inf = GEJ <$> arbitrary <*> arbitrary <*> pure fe_zero

prop_gej_rescale c a = C.gej_rescale c a `eq_gej` Spec.gej_rescale c a
prop_gej_rescale_zero = prop_gej_rescale fe_zero
prop_gej_rescale_inf c = forAll gen_inf (prop_gej_rescale c)

prop_gej_double_inf = forAll gen_inf prop_gej_double
prop_gej_double a = C.gej_double a `eq_gej` Spec.gej_double a

prop_gej_add a b = C.gej_add a b `eq_gej` mappend a b
prop_gej_add_double z a = prop_gej_add a b
 where
  z2 = C.fe_square z
  z3 = z .*. z2
  b = GEJ (a^._x .*. z2) (a^._y .*. z3) (a^._z .*. z)
prop_gej_add_opp z a = prop_gej_add a b
 where
  z2 = C.fe_square z
  z3 = z .*. z2
  b = GEJ (a^._x .*. z2) (C.fe_negate (a^._y .*. z3)) (a^._z .*. z)
prop_gej_add_inf = forAll gen_inf $ \a -> forAll gen_inf $ \b -> prop_gej_add a b
prop_gej_add_inf_l b = forAll gen_inf $ \a -> prop_gej_add a b
prop_gej_add_inf_r a = forAll gen_inf $ \b -> prop_gej_add a b
prop_gej_ge_add_ex a b = C.gej_ge_add_ex a b `eq_fe_gej` Spec.gej_ge_add_ex a b
prop_gej_ge_add_ex_all a bx by = prop_gej_ge_add_ex a b
 where
  b = GE bx by
prop_gej_ge_add_ex_double z bx by = prop_gej_ge_add_ex a b
 where
  z2 = C.fe_square z
  z3 = z .*. z2
  a = GEJ (bx .*. z2) (by .*. z3) z
  b = GE bx by
prop_gej_ge_add_ex_opp z bx by = prop_gej_ge_add_ex a b
 where
  z2 = C.fe_square z
  z3 = z .*. z2
  a = GEJ (bx .*. z2) (C.fe_negate (by .*. z3)) z
  b = GE bx by
prop_gej_ge_add_ex_inf bx by = forAll gen_inf $ \a -> prop_gej_ge_add_ex a b
 where
  b = GE bx by
prop_gej_ge_add_zinv a b bz = C.gej_ge_add_zinv a b bz `eq_gej` Spec.gej_ge_add_zinv a b bz
prop_gej_ge_add_zinv_all a b = prop_gej_ge_add_zinv a (GE bx by) bz
 where
  GEJ bx by bz = b
prop_gej_ge_add_zinv_double z b = prop_gej_ge_add_zinv a (GE bx by) bz
 where
  z2 = C.fe_square z
  z3 = z .*. z2
  a = GEJ (bx .*. z2) (by .*. z3) (C.fe_invert bz .*. z)
  GEJ bx by bz = b
prop_gej_ge_add_zinv_opp z b = prop_gej_ge_add_zinv a (GE bx by) bz
 where
  z2 = C.fe_square z
  z3 = z .*. z2
  a = GEJ (bx .*. z2) (C.fe_negate (by .*. z3)) (C.fe_invert bz .*. z)
  GEJ bx by bz = b
prop_gej_ge_add_zinv_inf b = forAll gen_inf $ \a -> prop_gej_ge_add_zinv a (GE bx by) bz
 where
  GEJ bx by bz = b

prop_ge_scale_lambda a = C.ge_scale_lambda a `eq_ge` Spec.ge_scale_lambda a

prop_gej_x_equiv a x0 = C.gej_x_equiv a x0 == Spec.gej_x_equiv a x0 -- gej_x_equiv will essentially always be false on random inputs.
prop_gej_x_equiv_inf x y x0 = prop_gej_x_equiv (GEJ x y fe_zero) x0
prop_gej_x_equiv_true x y z = prop_gej_x_equiv (GEJ (x .*. z2) y z) x
 where
  z2 = C.fe_square z
prop_gej_x_equiv_inf_zero x y = prop_gej_x_equiv (GEJ x y fe_zero) fe_zero

hunit_scalar_negate_zero = C.scalar_negate scalar_zero @?= Spec.scalar_negate scalar_zero
prop_scalar_negate a = C.scalar_negate a == Spec.scalar_negate a

prop_wnaf n a = C.wnaf n (scalar a) == map f (Spec.wnaf n a)
 where
  f Nothing = 0
  f (Just x) = 2*x+1

prop_scalar_split_lambda x = C.scalar_split_lambda x == (scalar *** scalar) (Spec.scalar_split_lambda x)
prop_scalar_split_128 x = C.scalar_split_128 x == (scalar *** scalar) (Spec.scalar_split_128 x)

prop_linear_combination_1 x y z = C.linear_combination_1 x y z `eq_gej` Spec.linear_combination_1 x y z
prop_linear_combination_1_0 y z = prop_linear_combination_1 x y z
 where
  x = scalar_zero
prop_linear_combination_1_inf x z = forAll gen_inf $ \y -> prop_linear_combination_1 x y z

bip0340_almost_always_false px m r s = not $ bip0340_check (PubKey px) (review (over be256) m) (Sig r s)

hunit_bip0340 = testGroup "bip0340"
              $ [ testCase "vector 0" (assertBool "bip0340_check" $
                  bip0340_check (PubKey 0xF9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9)
                                (conv 0)
                                (Sig 0xE907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA8215
                                     0x25F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0))
                , testCase "vector 1" (assertBool "bip0340_check" $
                  bip0340_check (PubKey 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659)
                                (conv pi)
                                (Sig 0x6896BD60EEAE296DB48A229FF71DFE071BDE413E6D43F917DC8DCF8C78DE3341
                                     0x8906D11AC976ABCCB20B091292BFF4EA897EFCB639EA871CFA95F6DE339E4B0A))
                , testCase "vector 2" (assertBool "bip0340_check" $
                  bip0340_check (PubKey 0xDD308AFEC5777E13121FA72B9CC1B7CC0139715309B086C960E18FD969774EB8)
                                (conv 0x7E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                                (Sig 0x5831AAEED7B44BB74E5EAB94BA9D4294C49BCF2A60728D8B4C200F50DD313C1B
                                     0xAB745879A5AD954A72C45A91C3A51D3C7ADEA98D82F8481E0E1E03674A6F3FB7))
                , testCase "vector 3" (assertBool "bip0340_check" $
                  bip0340_check (PubKey 0x25D1DFF95105F5253C4022F628A996AD3A0D95FBF21D468A1B33F8C160D8F517)
                                (conv (-1))
                                (Sig 0x7EB0509757E246F19449885651611CB965ECC1A187DD51B64FDA1EDC9637D5EC
                                     0x97582B9CB13DB3933705B32BA982AF5AF25FD78881EBB32771FC5922EFC66EA3))
                , testCase "vector 4" (assertBool "bip0340_check" $
                  bip0340_check (PubKey 0xD69C3509BB99E412E68B0FE8544E72837DFA30746D8BE2AA65975F29D22DC7B9)
                                (conv bla)
                                (Sig 0x00000000000000000000003B78CE563F89A0ED9414F5AA28AD0D96D6795F9C63
                                     0x76AFB1548AF603B3EB45C9F8207DEE1060CB71C04E80F593060B07D28308D7F4))
                , testCase "vector 5" (assertBool "not bip0340_check" . not $
                  bip0340_check (PubKey 0xEEFDEA4CDB677750A420FEE807EACF21EB9898AE79B9768766E4FAA04A2D4A34)
                                (conv pi)
                                (Sig 0x6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E177769
                                     0x69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B))
                , testCase "vector 6" (assertBool "not bip0340_check" . not $
                  bip0340_check (PubKey 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659)
                                (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                                (Sig 0xFFF97BD5755EEEA420453A14355235D382F6472F8568A18B2F057A1460297556
                                     0x3CC27944640AC607CD107AE10923D9EF7A73C643E166BE5EBEAFA34B1AC553E2))
                , testCase "vector 7" (assertBool "not bip0340_check" . not $
                  bip0340_check (PubKey 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659)
                                (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                                (Sig 0x1FA62E331EDBC21C394792D2AB1100A7B432B013DF3F6FF4F99FCB33E0E1515F
                                     0x28890B3EDB6E7189B630448B515CE4F8622A954CFE545735AAEA5134FCCDB2BD))
                , testCase "vector 8" (assertBool "not bip0340_check" . not $
                  bip0340_check (PubKey 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659)
                                (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                                (Sig 0x6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E177769
                                     0x961764B3AA9B2FFCB6EF947B6887A226E8D7C93E00C5ED0C1834FF0D0C2E6DA6))
                , testCase "vector 9" (assertBool "not bip0340_check" . not $
                  bip0340_check (PubKey 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659)
                                (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                                (Sig 0x0000000000000000000000000000000000000000000000000000000000000000
                                     0x123DDA8328AF9C23A94C1FEECFD123BA4FB73476F0D594DCB65C6425BD186051))
                , testCase "vector 10" (assertBool "not bip0340_check" . not $
                  bip0340_check (PubKey 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659)
                                (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                                (Sig 0x0000000000000000000000000000000000000000000000000000000000000001
                                     0x7615FBAF5AE28864013C099742DEADB4DBA87F11AC6754F93780D5A1837CF197))
                , testCase "vector 11" (assertBool "not bip0340_check" . not $
                  bip0340_check (PubKey 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659)
                                (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                                (Sig 0x4A298DACAE57395A15D0795DDBFD1DCB564DA82B0F269BC70A74F8220429BA1D
                                     0x69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B))
                , testCase "vector 12" (assertBool "not bip0340_check" . not $
                  bip0340_check (PubKey 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659)
                                (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                                (Sig 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
                                     0x69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B))
                , testCase "vector 13" (assertBool "not bip0340_check" . not $
                  bip0340_check (PubKey 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659)
                                (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                                (Sig 0x6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E177769
                                     0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141))
                , testCase "vector 14" (assertBool "not bip0340_check" . not $
                  bip0340_check (PubKey 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC30)
                                (conv 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C)
                                (Sig 0x6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E177769
                                     0x69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B))
                ]
 where
  conv :: Word256 -> Hash256
  conv = review (over be256)
  pi = 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  bla = 0x4DF3C3F68FCC83B27E9D42C90431A72499F17875C81A599B566C9889B9696703
