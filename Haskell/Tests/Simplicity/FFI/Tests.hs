module Simplicity.FFI.Tests
 ( tests
 , main
 ) where

import Control.Arrow ((***))
import Lens.Family2 ((^.), (^..), over, allOf, review, zipWithOf)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.QuickCheck ( Arbitrary(..), Property, arbitrarySizedBoundedIntegral, shrinkIntegral
                             , choose, forAll, discard, testProperty
                             )
import Test.Tasty.HUnit (Assertion, (@=?), assertBool, testCase)

import Simplicity.Digest
import Simplicity.FFI.Jets as C
import Simplicity.Programs.LibSecp256k1.Lib as Prog
import Simplicity.LibSecp256k1.Spec as Spec
import Simplicity.TestEval
import Simplicity.Ty.Arbitrary
import Simplicity.Bip0340
import Simplicity.Word

main = defaultMain tests

tests :: TestTree
tests = testGroup "C / SPEC"
      [ testGroup "field"
        [ testProperty "fe_normlaize"     prop_fe_normalize
        , testProperty "fe_negate"        prop_fe_negate
        , testProperty "fe_add"           prop_fe_add
        , testProperty "fe_square"        prop_fe_square
        , testProperty "fe_multiply"      prop_fe_multiply
        , testProperty "fe_multiply_beta" prop_fe_multiply_beta
        , testProperty "fe_invert"        prop_fe_invert
        , testProperty "fe_square_root"   prop_fe_square_root
        , testProperty "fe_is_zero"       prop_fe_is_zero
        , testProperty "fe_is_odd"        prop_fe_is_odd
        ]
      , testGroup "scalar"
        [ testProperty "scalar_normalize"       prop_scalar_normalize
        , testProperty "scalar_negate"          prop_scalar_negate
        , testProperty "scalar_add"             prop_scalar_add
        , testProperty "scalar_square"          prop_scalar_square
        , testProperty "scalar_multiply"        prop_scalar_multiply
        , testProperty "scalar_multiply_lambda" prop_scalar_multiply_lambda
        , testProperty "scalar_invert"          prop_scalar_invert
        , testProperty "scalar_is_zero"         prop_scalar_is_zero
        ]
      , testGroup "group"
        [ testCase     "gej_infinity"             assert_gej_infinity
        , testProperty "gej_rescale"              prop_gej_rescale
        , testProperty "gej_rescale_inf"          prop_gej_rescale_inf
        , testProperty "gej_normalize"            prop_gej_normalize
        , testProperty "gej_normalize_inf"        prop_gej_normalize_inf
        , testProperty "gej_negate"               prop_gej_negate
        , testProperty "gej_negate_inf"           prop_gej_negate_inf
        , testProperty "ge_negate"                prop_ge_negate
        , testProperty "gej_double"               prop_gej_double
        , testProperty "gej_double_inf"           prop_gej_double_inf
        , testProperty "gej_double_zero"          prop_gej_double_zero
        , testProperty "gej_add"                  prop_gej_add
        , testProperty "gej_add_double"           prop_gej_add_double
        , testProperty "gej_add_opp"              prop_gej_add_opp
        , testProperty "gej_add_infl"             prop_gej_add_infl
        , testProperty "gej_add_infr"             prop_gej_add_infr
        , testProperty "gej_ge_add_ex_double"     prop_gej_ge_add_ex_double
        , testProperty "gej_ge_add_ex_opp"        prop_gej_ge_add_ex_opp
        , testProperty "gej_ge_add_ex_inf"        prop_gej_ge_add_ex_inf
        , testProperty "gej_ge_add"               prop_gej_ge_add
        , testProperty "gej_is_infinity"          prop_gej_is_infinity
        , testProperty "gej_x_equiv"              prop_gej_x_equiv
        , testProperty "gej_x_equiv_inf"          prop_gej_x_equiv_inf
        , testProperty "gej_x_equiv_true"         prop_gej_x_equiv_true
        , testProperty "gej_x_equiv_inf_zero"     prop_gej_x_equiv_inf_zero
        , testProperty "gej_y_is_odd"             prop_gej_y_is_odd
        , testProperty "gej_is_on_curve"          prop_gej_is_on_curve
        , testProperty "gej_is_on_curve_inf"      prop_gej_is_on_curve_inf
        , testProperty "gej_is_on_curve_half"     prop_gej_is_on_curve_half
        , testProperty "gej_is_on_curve_inf_half" prop_gej_is_on_curve_inf_half
        , testProperty "ge_is_on_curve"           prop_ge_is_on_curve
        , testProperty "ge_is_on_curve_half"      prop_ge_is_on_curve_half
        ]
      , testGroup "ecMult"
        [ testCase     "linear_combination_1_order_6" assert_linear_combination_1_order_6
        , testProperty "linear_combination_1_inf"     prop_linear_combination_1_inf
        , testProperty "linear_combination_1_0"       prop_linear_combination_1_0
        , testProperty "linear_combination_1"         prop_linear_combination_1
        , testProperty "generate"                     prop_generate
        , testProperty "scale"                        prop_scale
        , testProperty "scale_0"                      prop_scale_0
        , testProperty "scale_inf"                    prop_scale_inf
        , testProperty "linear_verify_1_true_half"    prop_linear_verify_1_true_half
        , testProperty "linear_verify_1_0"            prop_linear_verify_1_0
        , testProperty "linear_verify_1"              prop_linear_verify_1
        ]
      , testGroup "point"
        [ testProperty "point_verify_1"      prop_point_verify_1
        , testProperty "point_verify_1_true" prop_point_verify_1
        , testProperty "decompress"          prop_decompress
        ]
      , testGroup "bip0340" $
        [ testProperty "bip0340_verify"   prop_bip0340_verify
        ] ++ zipWith case_bip0340_verify_vector [0..] bip0340Vectors
      ]

fe_unary_prop f g = \a -> fastF (feAsTy a) == g (feAsTy a)
 where
  fastF = testCoreEval f

fe_binary_prop f g = \a b -> fastF (feAsTy a, feAsTy b) == g (feAsTy a, feAsTy b)
 where
  fastF = testCoreEval f

prop_fe_normalize :: FieldElement -> Bool
prop_fe_normalize = fe_unary_prop Prog.fe_normalize C.fe_normalize

prop_fe_negate :: FieldElement -> Bool
prop_fe_negate = fe_unary_prop Prog.fe_negate C.fe_negate

prop_fe_add :: FieldElement -> FieldElement -> Bool
prop_fe_add = fe_binary_prop Prog.fe_add C.fe_add

prop_fe_square :: FieldElement -> Bool
prop_fe_square = fe_unary_prop Prog.fe_square C.fe_square

prop_fe_multiply :: FieldElement -> FieldElement -> Bool
prop_fe_multiply = fe_binary_prop Prog.fe_multiply C.fe_multiply

prop_fe_multiply_beta :: FieldElement -> Bool
prop_fe_multiply_beta = fe_unary_prop Prog.fe_multiply_beta C.fe_multiply_beta

prop_fe_invert :: FieldElement -> Bool
prop_fe_invert = fe_unary_prop Prog.fe_invert C.fe_invert

prop_fe_square_root :: FieldElement -> Bool
prop_fe_square_root = fe_unary_prop Prog.fe_square_root C.fe_square_root

prop_fe_is_zero :: FieldElement -> Bool
prop_fe_is_zero = fe_unary_prop Prog.fe_is_zero C.fe_is_zero

prop_fe_is_odd :: FieldElement -> Bool
prop_fe_is_odd = fe_unary_prop Prog.fe_is_odd C.fe_is_odd

scalar_unary_prop f g = \a -> fastF (scalarAsTy a) == g (scalarAsTy a)
 where
  fastF = testCoreEval f

scalar_binary_prop f g = \a b -> fastF (scalarAsTy a, scalarAsTy b) == g (scalarAsTy a, scalarAsTy b)
 where
  fastF = testCoreEval f

prop_scalar_normalize :: ScalarElement -> Bool
prop_scalar_normalize = scalar_unary_prop Prog.scalar_normalize C.scalar_normalize

prop_scalar_negate :: ScalarElement -> Bool
prop_scalar_negate = scalar_unary_prop Prog.scalar_negate C.scalar_negate

prop_scalar_add :: ScalarElement -> ScalarElement -> Bool
prop_scalar_add = scalar_binary_prop Prog.scalar_add C.scalar_add

prop_scalar_square :: ScalarElement -> Bool
prop_scalar_square = scalar_unary_prop Prog.scalar_square C.scalar_square

prop_scalar_multiply :: ScalarElement -> ScalarElement -> Bool
prop_scalar_multiply = scalar_binary_prop Prog.scalar_multiply C.scalar_multiply

prop_scalar_multiply_lambda :: ScalarElement -> Bool
prop_scalar_multiply_lambda = scalar_unary_prop Prog.scalar_multiply_lambda C.scalar_multiply_lambda

prop_scalar_invert :: ScalarElement -> Bool
prop_scalar_invert = scalar_unary_prop Prog.scalar_invert C.scalar_invert

prop_scalar_is_zero :: ScalarElement -> Bool
prop_scalar_is_zero = scalar_unary_prop Prog.scalar_is_zero C.scalar_is_zero

assert_gej_infinity :: Assertion
assert_gej_infinity =  fast_gej_infinity () @=? C.gej_infinity ()
 where
  fast_gej_infinity = testCoreEval Prog.gej_infinity

prop_gej_rescale :: GroupElementJacobian -> FieldElement -> Bool
prop_gej_rescale = \a c -> fast_gej_rescale (gejAsTy a, feAsTy c) == C.gej_rescale (gejAsTy a, feAsTy c)
 where
  fast_gej_rescale = testCoreEval Prog.gej_rescale

prop_gej_rescale_inf :: FieldElement -> Property
prop_gej_rescale_inf c = forAll gen_inf $ flip prop_gej_rescale c

prop_gej_normalize :: GroupElementJacobian -> Bool
prop_gej_normalize = \a -> fast_gej_normalize (gejAsTy a) == C.gej_normalize (gejAsTy a)
 where
  fast_gej_normalize = testCoreEval Prog.gej_normalize

prop_gej_normalize_inf :: Property
prop_gej_normalize_inf = forAll gen_inf $ prop_gej_normalize

prop_gej_negate :: GroupElementJacobian -> Bool
prop_gej_negate = \a -> fast_gej_negate (gejAsTy a) == C.gej_negate (gejAsTy a)
 where
  fast_gej_negate = testCoreEval Prog.gej_negate

prop_gej_negate_inf :: Property
prop_gej_negate_inf = forAll gen_inf $ prop_gej_negate

prop_ge_negate :: GroupElement -> Bool
prop_ge_negate = \a -> fast_ge_negate (geAsTy a) == C.ge_negate (geAsTy a)
 where
  fast_ge_negate = testCoreEval Prog.ge_negate

prop_gej_double :: GroupElementJacobian -> Bool
prop_gej_double = \a -> fast_gej_double (gejAsTy a) == C.gej_double (gejAsTy a)
 where
  fast_gej_double = testCoreEval Prog.gej_double

prop_gej_double_inf :: Property
prop_gej_double_inf = forAll gen_inf $ prop_gej_double

prop_gej_double_zero :: FieldElement -> FieldElement -> Bool
prop_gej_double_zero x z = prop_gej_double a
 where
  x' = feAsSpec x
  z' = feAsSpec z
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ x')
                           (FieldElement . Spec.fe_pack $ Spec.fe_zero)
                           (FieldElement . Spec.fe_pack $ z')

prop_gej_add :: GroupElementJacobian -> GroupElementJacobian -> Bool
prop_gej_add = \a b -> fast_gej_add (gejAsTy a, gejAsTy b) == C.gej_add (gejAsTy a, gejAsTy b)
 where
  fast_gej_add = testCoreEval Prog.gej_add

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
prop_gej_ge_add_ex = \a b -> fast_gej_ge_add_ex (gejAsTy a, geAsTy b) == C.gej_ge_add_ex (gejAsTy a, geAsTy b)
 where
  fast_gej_ge_add_ex = testCoreEval Prog.gej_ge_add_ex

prop_gej_ge_add_ex_double z b@(GroupElement bx by) = prop_gej_ge_add_ex a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack $ by' .*. z' .^. 3)
                           z
prop_gej_ge_add_ex_opp z b@(GroupElement bx by) = prop_gej_ge_add_ex a b
 where
  z' = feAsSpec z
  bx' = feAsSpec bx
  by' = feAsSpec by
  a = GroupElementJacobian (FieldElement . Spec.fe_pack $ bx' .*. z' .^. 2)
                           (FieldElement . Spec.fe_pack . Spec.fe_negate $ by' .*. z' .^. 3)
                           z
prop_gej_ge_add_ex_inf b = forAll gen_inf $ \a -> prop_gej_ge_add_ex a b

prop_gej_ge_add :: GroupElementJacobian -> GroupElement -> Bool
prop_gej_ge_add = \a b -> fast_gej_ge_add (gejAsTy a, geAsTy b) == C.gej_ge_add (gejAsTy a, geAsTy b)
 where
  fast_gej_ge_add = testCoreEval Prog.gej_ge_add

prop_gej_is_infinity :: GroupElementJacobian -> Bool
prop_gej_is_infinity = \a -> fast_gej_is_infinity (gejAsTy a) == C.gej_is_infinity (gejAsTy a)
 where
  fast_gej_is_infinity = testCoreEval Prog.gej_is_infinity

prop_gej_x_equiv :: FieldElement -> GroupElementJacobian -> Bool
prop_gej_x_equiv = \a b -> fast_gej_x_equiv (feAsTy a, gejAsTy b) == C.gej_x_equiv (feAsTy a, gejAsTy b)
 where
  fast_gej_x_equiv = testCoreEval Prog.gej_x_equiv

prop_gej_x_equiv_inf x0 = forAll gen_inf $ prop_gej_x_equiv x0
prop_gej_x_equiv_true y z x0 = prop_gej_x_equiv x0 a
  where
   z' = feAsSpec z
   x0' = feAsSpec x0
   a = GroupElementJacobian (FieldElement . Spec.fe_pack $ x0' .*. z' .^. 2) y z

prop_gej_x_equiv_inf_zero = prop_gej_x_equiv_inf (FieldElement 0)

prop_gej_y_is_odd :: GroupElementJacobian -> Bool
prop_gej_y_is_odd = \a -> fast_gej_y_is_odd (gejAsTy a) == C.gej_y_is_odd (gejAsTy a)
 where
  fast_gej_y_is_odd = testCoreEval Prog.gej_y_is_odd

prop_gej_is_on_curve :: GroupElementJacobian -> Bool
prop_gej_is_on_curve = \a -> fast_gej_is_on_curve (gejAsTy a) == C.gej_is_on_curve (gejAsTy a)
 where
  fast_gej_is_on_curve = testCoreEval Prog.gej_is_on_curve

prop_ge_is_on_curve :: GroupElement -> Bool

prop_gej_is_on_curve_inf = forAll gen_inf prop_gej_is_on_curve
prop_gej_is_on_curve_inf_half = forAll gen_half_curve_inf prop_gej_is_on_curve
prop_gej_is_on_curve_half = forAll gen_half_curve_jacobian prop_gej_is_on_curve

prop_ge_is_on_curve = \a -> fast_ge_is_on_curve (geAsTy a) == C.ge_is_on_curve (geAsTy a)
 where
  fast_ge_is_on_curve = testCoreEval Prog.ge_is_on_curve

prop_ge_is_on_curve_half = forAll gen_half_curve prop_ge_is_on_curve

prop_generate = \ng -> fast_generate (scalarAsTy ng)
                    == C.generate (scalarAsTy ng)
 where
  fast_generate = testCoreEval Prog.generate

prop_scale = \na a -> fast_scale (scalarAsTy na, gejAsTy a)
                   == C.scale (scalarAsTy na, gejAsTy a)
 where
  fast_scale = testCoreEval Prog.scale
prop_scale_0 a = prop_scale na a
 where
  na = ScalarElement 0
prop_scale_inf na = forAll gen_inf $ \a -> prop_scale na a

prop_linear_combination_1 = \na a ng -> fast_linear_combination_1 ((scalarAsTy na, gejAsTy a), scalarAsTy ng)
                                     == C.linear_combination_1 ((scalarAsTy na, gejAsTy a), scalarAsTy ng)
 where
  fast_linear_combination_1 = testCoreEval Prog.linear_combination_1
prop_linear_combination_1_0 a ng = prop_linear_combination_1 na a ng
 where
  na = ScalarElement 0

prop_linear_combination_1_inf na ng = forAll gen_inf $ \a -> prop_linear_combination_1 na a ng

-- :TODO: expand test coverage on low-order (off-curve) points.
-- This particular test case will fail if the gej_double_var function in the C implementation isn't "fixed" to handle
-- setting the infinity flag for off-curve points of order 2.
assert_linear_combination_1_order_6 :: Assertion
assert_linear_combination_1_order_6 = True @=? prop_linear_combination_1 na a ng
 where
  na = ScalarElement 6
  a = GroupElementJacobian (FieldElement 106586213356003376052770626926523423124273824193112332847656463919061591657353)
                           (FieldElement 26101920679609057376888884124959740524626979187904654689991505285331895977061)
                           (FieldElement 1)
  ng = ScalarElement 1

prop_linear_verify_1 = \na a ng r -> fast_linear_verify_1 (((scalarAsTy na, geAsTy a), scalarAsTy ng), geAsTy r)
                                 == C.linear_verify_1 (((scalarAsTy na, geAsTy a), scalarAsTy ng), geAsTy r)
 where
  fast_linear_verify_1 = testCoreEval Prog.linear_verify_1

prop_linear_verify_1_0 a ng = prop_linear_verify_1 na a ng
 where
  na = ScalarElement 0

prop_linear_verify_1_true_half na ng = forAll gen_half_curve $ \a -> prop_linear_verify_1_true na a ng
 where
  prop_linear_verify_1_true na a ng = prop_linear_verify_1 na a ng r
   where
    na' = scalarAsSpec na
    a' = geAsSpec a
    ng' = scalarAsSpec ng
    toGEJ (GE x y) = (GEJ x y Spec.fe_one)
    (GE rx' ry') = Spec.gej_normalize $ Spec.linear_combination [(na', toGEJ a')] ng'
    r = GroupElement (FieldElement (Spec.fe_pack rx')) (FieldElement (Spec.fe_pack ry'))

prop_point_verify_1 = \na a ng r -> fast_point_verify_1 (((scalarAsTy na, pointAsTy a), scalarAsTy ng), pointAsTy r)
                                 == C.point_verify_1 (((scalarAsTy na, pointAsTy a), scalarAsTy ng), pointAsTy r)
 where
  fast_point_verify_1 = testCoreEval Prog.point_verify_1

prop_point_verify_1_true na p ng | Just a' <- Spec.decompress p' = prop a'
                                 | otherwise = discard
 where
  na' = scalarAsSpec na
  ng' = scalarAsSpec ng
  p' = pointAsSpec p
  prop a' = prop_point_verify_1 na p ng r
   where
    toGEJ (GE x y) = (GEJ x y Spec.fe_one)
    (GE rx' ry') = Spec.gej_normalize $ Spec.linear_combination [(na', toGEJ a')] ng'
    r = PointElement (Spec.fe_is_odd ry') (FieldElement (Spec.fe_pack rx'))

prop_decompress = \a -> fast_decompress (pointAsTy a)
                     == C.decompress (pointAsTy a)
 where
  fast_decompress = testCoreEval Prog.decompress

prop_bip0340_verify = \pk m sig -> fast_bip0340_verify ((pk, m), sig)
                                == C.bip0340_verify ((pk, m), sig)
 where
  fast_bip0340_verify = testCoreEval Prog.bip0340_verify

assert_bip0340_verify_vector tv = True @=? prop_bip0340_verify pk m sig
 where
  ((pk, m), sig) = (bip0340TestAsTy tv)

case_bip0340_verify_vector n tv = testCase name (assert_bip0340_verify_vector tv)
 where
  name = "bip0340_vector_" ++ show n
