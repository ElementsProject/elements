-- | This module binds the C implementation of jets for Simplicity for assertions.
{-# LANGUAGE ForeignFunctionInterface #-}
module Simplicity.FFI.Jets
 ( add_32, full_add_32
 , subtract_32, full_subtract_32
 , multiply_32, full_multiply_32
 , sha_256_block
 , fe_normalize, fe_negate, fe_add, fe_square, fe_multiply, fe_multiply_beta, fe_invert, fe_square_root, fe_is_zero, fe_is_odd
 , scalar_normalize, scalar_negate, scalar_add, scalar_square, scalar_multiply, scalar_multiply_lambda, scalar_invert, scalar_is_zero
 , gej_infinity, gej_rescale, gej_normalize, gej_negate, ge_negate, gej_double, gej_add, gej_ge_add_ex, gej_ge_add, gej_is_infinity, gej_x_equiv, gej_y_is_odd, gej_is_on_curve, ge_is_on_curve
 , scale, generate, linear_combination_1, linear_verify_1
 , decompress, point_verify_1
 , bip0340_verify
 ) where

import Foreign.Ptr (Ptr)

import Simplicity.FFI.Frame
import qualified Simplicity.Programs.Sha256.Lib as Sha256
import Simplicity.Programs.LibSecp256k1.Lib (FE, Scalar, GE, GEJ, Point, PubKey, Sig)
import qualified Simplicity.Programs.LibSecp256k1.Lib as LibSecp256k1
import Simplicity.Ty.Word

foreign import ccall unsafe "" c_add_32 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_full_add_32 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_subtract_32 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_full_subtract_32 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_multiply_32 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_full_multiply_32 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool

foreign import ccall unsafe "" c_sha_256_block :: Ptr FrameItem -> Ptr FrameItem -> IO Bool

foreign import ccall unsafe "" c_fe_normalize :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_fe_negate :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_fe_add :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_fe_square :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_fe_multiply :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_fe_multiply_beta :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_fe_invert :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_fe_square_root :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_fe_is_zero :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_fe_is_odd :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_scalar_normalize :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_scalar_negate :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_scalar_add :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_scalar_square :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_scalar_multiply :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_scalar_multiply_lambda :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_scalar_invert :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_scalar_is_zero :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_gej_infinity :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_gej_rescale :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_gej_normalize :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_gej_negate :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_ge_negate :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_gej_double :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_gej_add :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_gej_ge_add_ex :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_gej_ge_add :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_gej_is_infinity :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_gej_x_equiv :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_gej_y_is_odd :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_gej_is_on_curve :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_ge_is_on_curve :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_scale :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_generate :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_linear_combination_1 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_linear_verify_1 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_decompress :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_point_verify_1 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_bip0340_verify :: Ptr FrameItem -> Ptr FrameItem -> IO Bool

add_32 :: (Word32, Word32) -> Maybe (Bit, Word32)
add_32 = unsafeLocalCoreJet c_add_32

full_add_32 :: ((Word32, Word32), Bit) -> Maybe (Bit, Word32)
full_add_32 = unsafeLocalCoreJet c_full_add_32

subtract_32 :: (Word32, Word32) -> Maybe (Bit, Word32)
subtract_32 = unsafeLocalCoreJet c_subtract_32

full_subtract_32 :: ((Word32, Word32), Bit) -> Maybe (Bit, Word32)
full_subtract_32 = unsafeLocalCoreJet c_full_subtract_32

multiply_32 :: (Word32, Word32) -> Maybe Word64
multiply_32 = unsafeLocalCoreJet c_multiply_32

full_multiply_32 :: ((Word32, Word32), (Word32, Word32)) -> Maybe Word64
full_multiply_32 = unsafeLocalCoreJet c_full_multiply_32

sha_256_block :: (Sha256.Hash, Sha256.Block) -> Maybe Sha256.Hash
sha_256_block = unsafeLocalCoreJet c_sha_256_block

fe_normalize :: FE -> Maybe FE
fe_normalize = unsafeLocalCoreJet c_fe_normalize

fe_negate :: FE -> Maybe FE
fe_negate = unsafeLocalCoreJet c_fe_negate

fe_add :: (FE, FE) -> Maybe FE
fe_add = unsafeLocalCoreJet c_fe_add

fe_square :: FE -> Maybe FE
fe_square = unsafeLocalCoreJet c_fe_square

fe_multiply :: (FE, FE) -> Maybe FE
fe_multiply = unsafeLocalCoreJet c_fe_multiply

fe_multiply_beta :: FE -> Maybe FE
fe_multiply_beta = unsafeLocalCoreJet c_fe_multiply_beta

fe_invert :: FE -> Maybe FE
fe_invert = unsafeLocalCoreJet c_fe_invert

fe_square_root :: FE -> Maybe (Either () FE)
fe_square_root = unsafeLocalCoreJet c_fe_square_root

fe_is_zero :: FE -> Maybe Bit
fe_is_zero = unsafeLocalCoreJet c_fe_is_zero

fe_is_odd :: FE -> Maybe Bit
fe_is_odd = unsafeLocalCoreJet c_fe_is_odd

scalar_normalize :: Scalar -> Maybe Scalar
scalar_normalize = unsafeLocalCoreJet c_scalar_normalize

scalar_negate :: Scalar -> Maybe Scalar
scalar_negate = unsafeLocalCoreJet c_scalar_negate

scalar_add :: (Scalar, Scalar) -> Maybe Scalar
scalar_add = unsafeLocalCoreJet c_scalar_add

scalar_square :: Scalar -> Maybe Scalar
scalar_square = unsafeLocalCoreJet c_scalar_square

scalar_multiply :: (Scalar, Scalar) -> Maybe Scalar
scalar_multiply = unsafeLocalCoreJet c_scalar_multiply

scalar_multiply_lambda :: Scalar -> Maybe Scalar
scalar_multiply_lambda = unsafeLocalCoreJet c_scalar_multiply_lambda

scalar_invert :: Scalar -> Maybe Scalar
scalar_invert = unsafeLocalCoreJet c_scalar_invert

scalar_is_zero :: Scalar -> Maybe Bit
scalar_is_zero = unsafeLocalCoreJet c_scalar_is_zero

gej_infinity :: () -> Maybe GEJ
gej_infinity = unsafeLocalCoreJet c_gej_infinity

gej_rescale :: (GEJ, FE) -> Maybe GEJ
gej_rescale = unsafeLocalCoreJet c_gej_rescale

gej_normalize :: GEJ -> Maybe GE
gej_normalize = unsafeLocalCoreJet c_gej_normalize

gej_negate :: GEJ -> Maybe GEJ
gej_negate = unsafeLocalCoreJet c_gej_negate

ge_negate :: GE -> Maybe GE
ge_negate = unsafeLocalCoreJet c_ge_negate

gej_double :: GEJ -> Maybe GEJ
gej_double = unsafeLocalCoreJet c_gej_double

gej_add :: (GEJ, GEJ) -> Maybe GEJ
gej_add = unsafeLocalCoreJet c_gej_add

gej_ge_add_ex :: (GEJ, GE) -> Maybe (FE, GEJ)
gej_ge_add_ex = unsafeLocalCoreJet c_gej_ge_add_ex

gej_ge_add :: (GEJ, GE) -> Maybe GEJ
gej_ge_add = unsafeLocalCoreJet c_gej_ge_add

gej_is_infinity :: GEJ -> Maybe Bit
gej_is_infinity = unsafeLocalCoreJet c_gej_is_infinity

gej_x_equiv :: (FE, GEJ) -> Maybe Bit
gej_x_equiv = unsafeLocalCoreJet c_gej_x_equiv

gej_y_is_odd :: GEJ -> Maybe Bit
gej_y_is_odd = unsafeLocalCoreJet c_gej_y_is_odd

gej_is_on_curve :: GEJ -> Maybe Bit
gej_is_on_curve = unsafeLocalCoreJet c_gej_is_on_curve

ge_is_on_curve :: GE -> Maybe Bit
ge_is_on_curve = unsafeLocalCoreJet c_ge_is_on_curve

scale :: (Scalar, GEJ) -> Maybe GEJ
scale = unsafeLocalCoreJet c_scale

generate :: Scalar -> Maybe GEJ
generate = unsafeLocalCoreJet c_generate

linear_combination_1 :: ((Scalar, GEJ), Scalar) -> Maybe GEJ
linear_combination_1 = unsafeLocalCoreJet c_linear_combination_1

linear_verify_1 :: (((Scalar, GE), Scalar), GE) -> Maybe ()
linear_verify_1 = unsafeLocalCoreJet c_linear_verify_1

decompress :: Point -> Maybe (Either () GE)
decompress = unsafeLocalCoreJet c_decompress

point_verify_1 :: (((Scalar, Point), Scalar), Point) -> Maybe ()
point_verify_1 = unsafeLocalCoreJet c_point_verify_1

bip0340_verify :: ((PubKey, Word256), Sig) -> Maybe ()
bip0340_verify = unsafeLocalCoreJet c_bip0340_verify
