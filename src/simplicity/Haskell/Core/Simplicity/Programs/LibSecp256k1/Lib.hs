{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module unpacks the 'Simplicity.Programs.LibSecp256k1.lib' library instance into individual functions.
-- Users should prefer to use 'Simplicity.Programs.LibSecp256k1.mkLib' in order to share library dependencies.
-- This module is provided mostly for testing purposes.
module Simplicity.Programs.LibSecp256k1.Lib
  (
  -- * Field operations
    LibSecp256k1.FE, fe_zero, fe_one, fe_is_zero
  , fe_normalize
  , fe_add, fe_negate, fe_square, fe_multiply, fe_multiply_beta, fe_invert, fe_square_root
  , fe_is_odd, fe_is_quad
  -- * Point operations
  , LibSecp256k1.Point, LibSecp256k1.GE, LibSecp256k1.GEJ, gej_is_on_curve
  , gej_infinity, gej_is_infinity
  , gej_rescale, gej_normalize, gej_negate, gej_scale_lambda
  , gej_double, gej_add_ex, gej_add, gej_ge_add_ex, gej_ge_add
  , ge_is_on_curve, ge_negate, ge_scale_lambda
  , {-gej_equiv,-} gej_x_equiv, gej_y_is_odd
  , decompress
  -- * Scalar operations
  , LibSecp256k1.Scalar, LibSecp256k1.Word129
  , scalar_normalize, scalar_add, scalar_negate, scalar_square, scalar_multiply, scalar_multiply_lambda, scalar_invert
  , scalar_split_lambda, scalar_split_128
  , scalar_is_zero
  -- * Elliptic curve multiplication related operations
  , LibSecp256k1.Vector129
  , wnaf5, wnaf15
  , generate, scale
  , linear_combination_1, linear_check_1, linear_verify_1
  , point_check_1, point_verify_1
  -- * Schnorr signature operations
  , LibSecp256k1.PubKey, pubkey_unpack, pubkey_unpack_neg
  , LibSecp256k1.Sig, signature_unpack
  , bip0340_check, bip0340_verify
  ) where

import qualified Simplicity.Programs.LibSecp256k1 as LibSecp256k1

-- Maybe this ought to be Template Haskell.
fe_zero = LibSecp256k1.fe_zero LibSecp256k1.lib
fe_one = LibSecp256k1.fe_one LibSecp256k1.lib
fe_is_zero = LibSecp256k1.fe_is_zero LibSecp256k1.lib
fe_normalize = LibSecp256k1.fe_normalize LibSecp256k1.lib
fe_add = LibSecp256k1.fe_add LibSecp256k1.lib
fe_negate = LibSecp256k1.fe_negate LibSecp256k1.lib
fe_square = LibSecp256k1.fe_square LibSecp256k1.lib
fe_multiply = LibSecp256k1.fe_multiply LibSecp256k1.lib
fe_multiply_beta = LibSecp256k1.fe_multiply_beta LibSecp256k1.lib
fe_invert = LibSecp256k1.fe_invert LibSecp256k1.lib
fe_square_root = LibSecp256k1.fe_square_root LibSecp256k1.lib
fe_is_odd = LibSecp256k1.fe_is_odd LibSecp256k1.lib
fe_is_quad = LibSecp256k1.fe_is_quad LibSecp256k1.lib
gej_is_on_curve = LibSecp256k1.gej_is_on_curve LibSecp256k1.lib
gej_infinity = LibSecp256k1.gej_infinity LibSecp256k1.lib
gej_is_infinity = LibSecp256k1.gej_is_infinity LibSecp256k1.lib
gej_rescale = LibSecp256k1.gej_rescale LibSecp256k1.lib
gej_normalize = LibSecp256k1.gej_normalize LibSecp256k1.lib
gej_negate = LibSecp256k1.gej_negate LibSecp256k1.lib
gej_scale_lambda = LibSecp256k1.gej_scale_lambda LibSecp256k1.lib
gej_double = LibSecp256k1.gej_double LibSecp256k1.lib
gej_add_ex = LibSecp256k1.gej_add_ex LibSecp256k1.lib
gej_add = LibSecp256k1.gej_add LibSecp256k1.lib
gej_ge_add_ex = LibSecp256k1.gej_ge_add_ex LibSecp256k1.lib
gej_ge_add = LibSecp256k1.gej_ge_add LibSecp256k1.lib
ge_is_on_curve = LibSecp256k1.ge_is_on_curve LibSecp256k1.lib
ge_negate = LibSecp256k1.ge_negate LibSecp256k1.lib
ge_scale_lambda = LibSecp256k1.ge_scale_lambda LibSecp256k1.lib
gej_x_equiv = LibSecp256k1.gej_x_equiv LibSecp256k1.lib
gej_y_is_odd = LibSecp256k1.gej_y_is_odd LibSecp256k1.lib
scalar_normalize = LibSecp256k1.scalar_normalize LibSecp256k1.lib
scalar_add = LibSecp256k1.scalar_add LibSecp256k1.lib
scalar_negate = LibSecp256k1.scalar_negate LibSecp256k1.lib
scalar_square = LibSecp256k1.scalar_square LibSecp256k1.lib
scalar_multiply = LibSecp256k1.scalar_multiply LibSecp256k1.lib
scalar_multiply_lambda = LibSecp256k1.scalar_multiply_lambda LibSecp256k1.lib
scalar_invert = LibSecp256k1.scalar_invert LibSecp256k1.lib
scalar_split_lambda = LibSecp256k1.scalar_split_lambda LibSecp256k1.lib
scalar_split_128 = LibSecp256k1.scalar_split_128 LibSecp256k1.lib
scalar_is_zero = LibSecp256k1.scalar_is_zero LibSecp256k1.lib
wnaf5 = LibSecp256k1.wnaf5 LibSecp256k1.lib
wnaf15 = LibSecp256k1.wnaf15 LibSecp256k1.lib
generate = LibSecp256k1.generate LibSecp256k1.lib
scale = LibSecp256k1.scale LibSecp256k1.lib
linear_combination_1 = LibSecp256k1.linear_combination_1 LibSecp256k1.lib
linear_check_1 = LibSecp256k1.linear_check_1 LibSecp256k1.lib
linear_verify_1 = LibSecp256k1.linear_verify_1 LibSecp256k1.lib
decompress = LibSecp256k1.decompress LibSecp256k1.lib
point_check_1 = LibSecp256k1.point_check_1 LibSecp256k1.lib
point_verify_1 = LibSecp256k1.point_verify_1 LibSecp256k1.lib
pubkey_unpack = LibSecp256k1.pubkey_unpack LibSecp256k1.lib
pubkey_unpack_neg = LibSecp256k1.pubkey_unpack_neg LibSecp256k1.lib
signature_unpack = LibSecp256k1.signature_unpack LibSecp256k1.lib
bip0340_check = LibSecp256k1.bip0340_check LibSecp256k1.lib
bip0340_verify = LibSecp256k1.bip0340_verify LibSecp256k1.lib
