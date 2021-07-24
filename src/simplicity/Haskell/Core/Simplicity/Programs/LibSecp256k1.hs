{-# LANGUAGE ScopedTypeVariables, GADTs, RankNTypes, RecordWildCards #-}
-- | This module defines a library of Simplicity expressions that replicate the functional behaviour of (a specific version of) libsecp256k1's elliptic curve operations <https://github.com/bitcoin-core/secp256k1/tree/1e6f1f5ad5e7f1e3ef79313ec02023902bf8175c>.
-- The functions defined here return precisely the same field and point representatives that the corresponding libsecp256k1's functions do, with a few exceptions with the way the point at infinity is handled.
-- This makes these expressions suitable for being jetted by using libsecp256k1 functions.
module Simplicity.Programs.LibSecp256k1
  (
    Lib(Lib), mkLib
  -- * Field operations
  , FE, fe_zero, fe_one, fe_is_zero
  , fe_normalize
  , fe_add, fe_negate, fe_square, fe_multiply, fe_multiply_beta, fe_invert, fe_square_root
  , fe_is_odd, fe_is_quad
  -- * Point operations
  , Point, GE, GEJ, gej_is_on_curve
  , gej_infinity, gej_is_infinity
  , gej_rescale, gej_normalize, gej_negate, gej_scale_lambda
  , gej_double, gej_add_ex, gej_add, gej_ge_add_ex, gej_ge_add
  , ge_is_on_curve, ge_negate, ge_scale_lambda
  , {-gej_equiv,-} gej_x_equiv, gej_y_is_odd
  , decompress
  -- * Scalar operations
  , Scalar, Word129
  , scalar_normalize, scalar_add, scalar_negate, scalar_square, scalar_multiply, scalar_multiply_lambda, scalar_invert
  , scalar_split_lambda, scalar_split_128
  , scalar_is_zero
  -- * Elliptic curve multiplication related operations
  , Vector129
  , wnaf5, wnaf15
  , generate, scale
  , linear_combination_1, linear_check_1, linear_verify_1
  , point_check_1, point_verify_1
  -- * Schnorr signature operations
  , PubKey, pubkey_unpack, pubkey_unpack_neg
  , Sig, signature_unpack
  , bip0340_check, bip0340_verify
  -- * Example instances
  , lib
  ) where

import Prelude hiding (drop, take, and, or, not, Word)

import Simplicity.Digest
import Simplicity.Functor
import qualified Simplicity.LibSecp256k1.Spec as LibSecp256k1
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Programs.Word
import qualified Simplicity.Programs.Sha256 as Sha256
import Simplicity.Programs.Sha256 hiding (Lib(Lib), lib)
import Simplicity.Ty
import Simplicity.Term.Core

-- | Simplicity's representation of field elements.
type FE = Word256

-- | A point in compressed coordinates.
-- The point at infinity isn't representable.
type Point = (Bit, FE)

-- | A point in affine coordinates.
-- Usually expected to be on the elliptic curve.
-- The point at infinity isn't representable.
type GE = (FE, FE)

-- | A point in Jacobian coordinates.
-- Usually expected to be on the elliptic curve.
-- The point at infinity's representatives are of the form @((a^2, a^3), 0)@, with @((0, 0), 0)@ being the canonical representative.
type GEJ = (GE, FE)

-- | Scalar values, those less than the order of secp256's elliptic curve, are represented by a 256-bit word type.
type Scalar = Word256

-- | 129 entry vector of values.
type Vector129 x = (x, Vector128 x)

-- | 129-bit signed word that is returned by 'scalar_split_lambda' and 'scalar_split_128'.
type Word129 = Vector129 Bit

-- | A format for (Schnorr) elliptic curve x-only public keys.
-- The y-coordinate is implicity the one on the curve that has an even y coordinate.
-- The point at infinity isn't representable (nor is it a valid public key to begin with).
type PubKey = Word256

-- | A format for Schnorr signatures.
type Sig = (Word256, Word256)

-- | A collection of core Simplicity expressions for LibSecp256k1.
-- Use 'mkLib' to construct an instance of this library.
data Lib term =
 Lib
  { -- | Reduce the representation of a field element to its canonical represenative.
    fe_normalize :: term Word256 FE

    -- | The normalized reprsentative for the field element 0.
  , fe_zero :: term () FE

    -- | The normalized reprsentative for the field element 1.
  , fe_one :: term () FE

    -- | Tests if the input value is a representative of the field element 0.
  , fe_is_zero :: term FE Bit

    -- | Adds two field elements.
  , fe_add :: term (FE, FE) FE

    -- | Negates a field element.
  , fe_negate :: term FE FE

    -- | Multiplies two field elements.
  , fe_multiply :: term (FE, FE) FE

    -- | Multiplies a field element by the canonical primitive cube root of unity.
  , fe_multiply_beta :: term FE FE

    -- | Squares a field element.
  , fe_square :: term FE FE

    -- | Computes the modular inverse of a field element.
  , fe_invert :: term FE FE

    -- | Computes the modular square root of a field element if it exists.
  , fe_square_root :: term FE (Either () FE)

    -- | Tests if the canonical representative of the field element is odd.
  , fe_is_odd :: term FE Bit

    -- | Tests if the field element is a quadratic residue.
  , fe_is_quad :: term FE Bit

    -- | Returns the canonical represenative of the point at infinity.
  , gej_infinity :: term () GEJ

    -- | Computes the negation of a point.
  , gej_negate :: term GEJ GEJ

    -- | Tests if the point is a representative of infinity.
  , gej_is_infinity :: term GEJ Bit

    -- | Doubles a point.
    -- If the result is the point at infinity, it is returned in canonical form.
  , gej_double :: term GEJ GEJ

    -- | Adds points 'a' and 'b'.
    -- Also returns the ratio of 'a''s z-coordinate and the result's z-coordinate.
    --
    -- If the result is the point at infinity, it is returned in canonical form.
  , gej_add_ex :: term (GEJ, GEJ) (FE, GEJ)

    -- | Adds points 'a' and 'b'.
  , gej_add :: term (GEJ, GEJ) GEJ

    -- | Adds a point 'a' in Jacobian coordinates with a point 'b' in affine coordinates.
    -- Also returns the ratio of 'a''s z-coordinate and the result's z-coordinate.
    --
    -- If the result is the point at infinity, it is returned in canonical form.
  , gej_ge_add_ex :: term (GEJ, GE) (FE, GEJ)

    -- | Adds a point in Jacobian coordinates with a point in affine coordinates.
    --
    -- If the result is the point at infinity, it is returned in canonical form.
  , gej_ge_add :: term (GEJ, GE) GEJ

    -- | Multiply a point by the canonical cube root of unity.
  , gej_scale_lambda :: term GEJ GEJ

    -- | Negates a point in affine coordinates.
  , ge_negate :: term GE GE

    -- | Multiply a point in affine coordinates by the canonical cube root of unity.
  , ge_scale_lambda :: term GE GE

    -- | Changes represenative of a point in Jacobian coordintes by multiplying the z-coefficent by a given value.
  , gej_rescale :: term (GEJ, FE) GEJ

    -- | Converts a point in Jacobian coordintes to the same point in affine coordinates, and normalizes the field represenatives.
    -- Returns the point (0, 0) when given the point at infinity.
  , gej_normalize :: term GEJ GE

--    -- | Tests if two points in jacobian coordinates represent the same point.
--  , gej_equiv :: term (GEJ, GEJ) Bit

    -- | Given a field element and a point in Jacobian coordiantes, test if the point represents one whose affine x-coordinate is equal to the given field element.
  , gej_x_equiv :: term (FE, GEJ) Bit

    -- | Given a point in Jacobian coordiantes, test if the point represents one whose affine y-coordinate is odd.
  , gej_y_is_odd :: term GEJ Bit

    -- | Check if a given point in Jacobian coordinate satifies the secp256k1 curve equation Y^2 = X^3 + 7Z^6.
  , gej_is_on_curve :: term GEJ Bit

    -- | Check if a given point in affine coordinate satifies the secp256k1 curve equation Y^2 = X^3 + 7.
  , ge_is_on_curve :: term GE Bit

    -- | Reduce the representation of a scalar element to its canonical represenative.
  , scalar_normalize :: term Word256 Scalar

    -- | Tests if the input value is a representative of the scalar element 0.
  , scalar_is_zero :: term Scalar Bit

    -- | Adds two scalar elements.
  , scalar_add :: term (Scalar, Scalar) Scalar

    -- | Negates a scalar element.
  , scalar_negate :: term Scalar Scalar

    -- | Multiplies two scalar elements.
  , scalar_square :: term Scalar Scalar

    -- | Multiplies two scalar elements.
  , scalar_multiply :: term (Scalar, Scalar) Scalar

    -- | Multiplies a scalar element by the canonical primitive cube root of unity.
  , scalar_multiply_lambda :: term Scalar Scalar

    -- | Computes the modular inverse of a scalar element.
  , scalar_invert :: term Scalar Scalar

    -- | Divide a scalar element into two short integers 'k1' and 'k2' such that @'k1' + 'k2' * 'Simplicity.LibSecp256k1.Spec.lambda'@ is the orginal scalar element.
  , scalar_split_lambda :: term Scalar (Word129, Word129)

    -- | Divide a scalar element into two short integers 'k1' and 'k2' such that @'k1' + 'k2' * 2^128@ is the orginal scalar element.
  , scalar_split_128 :: term Scalar (Word129, Word129)

    -- | Convert a scalar value to wnaf form, with a window of 5 bits.
  , wnaf5 :: term Word129 (Vector129 (Either () Word4))

    -- | Convert a scalar value to wnaf form, with a window of 15 bits.
  , wnaf15 :: term Word129 (Vector129 (Either () Word16))

    -- | Returns a multiple of the secp256k1's generator.
  , generate :: term Scalar GEJ

    -- | Multiply a point by a scalar element.
  , scale :: term (Scalar, GEJ) GEJ

    -- | Given an elliptic curve point, @a@, and two scalar values @na@ and @ng@, return @na * a + ng * g@ where @g@ is secp256k1's generator.
    -- If the result is the point at infinity, it is returned in canonical form.
  , linear_combination_1 :: term ((Scalar, GEJ), Scalar) GEJ

    -- | Verifies that all points are on the secp256k1 curve and checks if @na * a + ng * g == r@ on the input @(((na, a), ng), r)@ where @g@ is secp256k1's generator.
  , linear_check_1 :: term (((Scalar, GE), Scalar), GE) Bit

    -- | Decompress a compressed point into affine coordinates.  Fails if the x-coordinate is no on the secp256k1, but it will succeed even if the x-coordinate is not normalized.
  , decompress :: term Point (Either () GE)

    -- | Decompresses and verifies that all points are on the secp256k1 curve as 'linear_check_1' does.
    -- This will fail if either point decompression fails or if the 'linear_check_1' would fail.
  , point_check_1 :: term (((Scalar, Point), Scalar), Point) Bit

    -- | This function unpacks a 'PubKey' as a elliptic curve point in compressed coordinates.
    --
    -- If the x-coordinate isn't on the elliptice curve, the funtion returns @Left ()@.
    -- This does not check that the x-coordinate in on-curve.  That would have to be performed by `decompress`.
  , pubkey_unpack :: term PubKey (Either () Point)

    -- | This function unpacks the negation of a 'PubKey' as a elliptic curve point in compressed coordinates.
    --
    -- If the x-coordinate isn't on the elliptice curve, the funtion returns @Left ()@.
    -- This does not check that the x-coordinate in on-curve.  That would have to be performed by `decompress`.
  , pubkey_unpack_neg :: term PubKey (Either () Point)

    -- | This function unpackes a 'Sig' as a pair of a field element and a scalar value.
    --
    -- If the field element's value is greater than or equal to the field order, the function return @Left ()@.
    -- If the scalar element's value is greater than or equal to secp256k1's curve order, the function returns @Left ()@.
  , signature_unpack :: term Sig (Either () (FE, Scalar))

    -- | This function is given a public key, a 256-bit message, and a signature, and checks if the signature is valid for the given message and public key.
  , bip0340_check :: term ((PubKey, Word256), Sig) Bit
  }

instance SimplicityFunctor Lib where
  sfmap m Lib{..} =
   Lib
    { fe_normalize = m fe_normalize
    , fe_zero = m fe_zero
    , fe_one = m fe_one
    , fe_is_zero = m fe_is_zero
    , fe_is_odd = m fe_is_odd
    , fe_add = m fe_add
    , fe_negate = m fe_negate
    , fe_multiply = m fe_multiply
    , fe_multiply_beta = m fe_multiply_beta
    , fe_square = m fe_square
    , fe_invert = m fe_invert
    , fe_square_root = m fe_square_root
    , fe_is_quad = m fe_is_quad
    , gej_infinity = m gej_infinity
    , gej_negate = m gej_negate
    , gej_is_infinity = m gej_is_infinity
    , gej_double = m gej_double
    , gej_add_ex = m gej_add_ex
    , gej_add = m gej_add
    , gej_ge_add_ex = m gej_ge_add_ex
    , gej_ge_add = m gej_ge_add
    , gej_scale_lambda = m gej_scale_lambda
    , ge_negate = m ge_negate
    , ge_scale_lambda = m ge_scale_lambda
    , gej_rescale = m gej_rescale
    , gej_normalize = m gej_normalize
--    , gej_equiv = m gej_equiv
    , gej_x_equiv = m gej_x_equiv
    , gej_y_is_odd = m gej_y_is_odd
    , gej_is_on_curve = m gej_is_on_curve
    , ge_is_on_curve = m ge_is_on_curve
    , scalar_normalize = m scalar_normalize
    , scalar_is_zero = m scalar_is_zero
    , scalar_add = m scalar_add
    , scalar_negate = m scalar_negate
    , scalar_square = m scalar_square
    , scalar_multiply = m scalar_multiply
    , scalar_multiply_lambda = m scalar_multiply_lambda
    , scalar_invert = m scalar_invert
    , scalar_split_lambda = m scalar_split_lambda
    , scalar_split_128 = m scalar_split_128
    , wnaf5 = m wnaf5
    , wnaf15 = m wnaf15
    , generate = m generate
    , scale = m scale
    , linear_combination_1 = m linear_combination_1
    , linear_check_1 = m linear_check_1
    , decompress = m decompress
    , point_check_1 = m point_check_1
    , pubkey_unpack = m pubkey_unpack
    , pubkey_unpack_neg = m pubkey_unpack_neg
    , signature_unpack = m signature_unpack
    , bip0340_check = m bip0340_check
    }

-- | Build the LibSecp256k1 'Lib' library from its dependencies.
mkLib :: forall term. Core term => Sha256.Lib term -- ^ "Simplicity.Programs.Sha256"
                                -> Lib term
mkLib Sha256.Lib{..} = lib
 where
  -- A constant expression for a 64-bit value.
  scribe64 :: TyC a => Integer -> term a Word64
  scribe64 = scribe . toWord64

  -- A constant expression for a 128-bit value.
  scribe128 :: TyC a => Integer -> term a Word128
  scribe128 = scribe . toWord128

  -- A constant expression for a 256-bit value.
  scribe256 :: TyC a => Integer -> term a Word256
  scribe256 = scribe . toWord256

  scribeFeOrder :: term () Word256
  scribeFeOrder = scribe256 LibSecp256k1.fieldOrder

  scribeGroupOrder :: term () Word256
  scribeGroupOrder = scribe256 LibSecp256k1.groupOrder

  scribeGroupOrder512 :: term () Word512
  scribeGroupOrder512 = zero256 &&& scribeGroupOrder

  fe_beta :: term () FE
  fe_beta = scribe256 LibSecp256k1.beta

  scalar_lambda :: term () Scalar
  scalar_lambda = scribe256 LibSecp256k1.lambda

  -- 256 bit addition.
  add256 :: term (Word256, Word256) (Bit, Word256)
  add256 = Arith.add word256

  -- 256 bit subtraction.
  sub256 :: term (Word256, Word256) (Bit, Word256)
  sub256 = Arith.subtract word256

  sub128 = Arith.subtract word128

  -- Multiplication modulo 2^64.
  mul64 :: term (Word64, Word64) Word128
  mul64 = Arith.multiply word64

  mul128 = Arith.multiply word128
  mul256 = Arith.multiply word256

  -- 256 bit less-than
  lt256 = Arith.lt word256

  -- 128 bit zero.
  zero128 = Arith.zero word128

  -- 256 bit zero.
  zero256 = Arith.zero word256

  -- 256 bit one.
  one256 = Arith.one word256

  msb256 = Arith.msb word256
  msb128 = Arith.msb word128

  lsb256 = Arith.lsb word256
  lsb128 = Arith.lsb word128

  mod512 = Arith.modulo word512

  -- | computes a 512 bit number modulo the field order.
  fe_normalize512 :: term Word512 FE
  fe_normalize512 = iden &&& (unit >>> zero256 &&& scribeFeOrder) >>> mod512 >>> ih

  -- | computes a 512 bit number modulo the group order.
  scalar_normalize512 :: term Word512 FE
  scalar_normalize512 = iden &&& (unit >>> zero256 &&& scribeGroupOrder) >>> mod512 >>> ih

  signResize4 = left_extend word4 (DoubleV . DoubleV . DoubleV . DoubleV . DoubleV $ SingleV)
  signResize16 = left_extend word16 (DoubleV . DoubleV . DoubleV $ SingleV)
  fullShift128 = full_shift word1 word128 >>> oh
  wnafsub128 :: term ((Bit, Word128), Word128) (Bit, Word128)
  wnafsub128 = xor ooh (drop msb128) &&& (oih &&& ih >>> sub128) >>> xor oh ioh &&& iih

  wnaf5step1 :: term (Bit, Word128) ((Bit, Word128), (Either () Word4))
  wnaf5step1 = drop lsb128 &&& (oh &&& fullShift128)
           >>> cond body (iden &&& injl unit)
   where
    body = iden &&& (drop . drop . drop $ iiih) >>> (oh &&& drop signResize4 >>> wnafsub128) &&& injr ih

  wnaf15step1 :: term (Bit,Word128) ((Bit,Word128), (Either () Word16))
  wnaf15step1 = drop lsb128 &&& iden
            >>> cond body ((oh &&& fullShift128) &&& injl unit)
   where
    mask = take (take (take (ih &&& ih) &&& ih) &&& ih) &&& ih
    body = iden &&& (drop iiih >>> mask)
       >>> ((ooh &&& take fullShift128) &&& drop (signResize16 >>> msb128 &&& iden >>> fullShift128) >>> wnafsub128)
       &&& injr ih

  wnafstepD :: (TyC s, TyC v) => term s (s, v) -> term s (s, (v, v))
  wnafstepD rec = rec >>> take rec &&& ih >>> ooh &&& (oih &&& ih)

  wnaf5step16 = wnafstepD . wnafstepD . wnafstepD . wnafstepD $ wnaf5step1
  wnaf5step128 = wnafstepD . wnafstepD . wnafstepD $ wnaf5step16
  wnaf15step16 = wnafstepD . wnafstepD . wnafstepD . wnafstepD $ wnaf15step1
  wnaf15step128 = wnafstepD . wnafstepD . wnafstepD $ wnaf15step16

  wnafpre :: term Scalar Word256
  wnafpre = msb256 &&& iden
        >>> cond (iden &&& (unit >>> scribeGroupOrder) >>> sub256 >>> ih) iden

  generate0 :: term () GE
  generate0 = scribe g
   where
     g = (toWord256 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798, toWord256 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8)

  -- 2^128 * generate0
  generate128 :: term () GE
  generate128 = scribe g128
   where
     g128 = (toWord256 0x8f68b9d2f63b5f339239c1ad981f162ee88c5678723ea3351b7b444c9ec4c0da, toWord256 0x662a9f2dba063986de1d90c2b6be215dbbea2cfe95510bfdf23cbf79501fff82)

  scaleConstant :: term () GE -> Word a -> term (a, GEJ) GEJ
  scaleConstant base = go
   where
    go :: Word a -> term (a, GEJ) GEJ
    go SingleV = cond (gej_double &&& (unit >>> base) >>> gej_ge_add) gej_double
    go (DoubleV w) = oih &&& (ooh &&& ih >>> rec) >>> rec
     where
      rec = go w

  lib@Lib{..} = Lib {
    fe_normalize = (iden &&& (unit >>> scribeFeOrder) >>> sub256) &&& iden
               >>> ooh &&& (oih &&& ih)
               >>> cond ih oh

  , fe_zero = zero256

  , fe_one = one256

  , fe_is_zero = or (Arith.is_zero word256)
                  ((unit >>> scribeFeOrder) &&& iden >>> eq)

  , fe_is_odd = fe_normalize >>> lsb256

  , fe_add = add256 >>> cond ((unit >>> one256) &&& iden) ((unit >>> zero256) &&& iden) >>> fe_normalize512

  , fe_negate = fe_multiplyInt (-1)

  , fe_multiply = mul256 >>> fe_normalize512

  , fe_multiply_beta = (unit >>> fe_beta) &&& iden >>> fe_multiply

  , fe_square = iden &&& iden >>> fe_multiply

  , fe_invert = (unit >>> scribeFeOrder) &&& iden >>> Arith.bezout word256 >>> copair (drop fe_negate) ih

  , fe_square_root = iden &&& tower
          >>> oh &&& drop ((oh &&& drop fe_square >>> fe_multiply) >>> fe_square >>> fe_square)
          >>> (take fe_negate &&& drop fe_square >>> fe_add >>> fe_is_zero) &&& ih
          >>> cond (injr iden) (injl unit)

  , fe_is_quad = elimS fe_square_root false true

  , gej_infinity =
     let
      zero = fe_zero
     in
      (zero &&& zero) &&& zero

  , gej_negate = take ge_negate &&& drop fe_normalize

  , gej_is_infinity = drop fe_is_zero

  , gej_double =
     let
      body = (take (oh &&& (take fe_square >>> fe_multiplyInt (-3)) &&& (drop fe_square >>> fe_multiplyInt 2))                                                               -- (x, (-3*x^2, 2*y^2))
          >>> (((drop (take fe_square)) &&& (iih &&& oh >>> fe_multiply)) &&& drop (oh &&& (drop fe_square >>> fe_multiplyInt (-2))))                                        -- ((9*x^4, 2*x*y^2), (-3*x^2, -8*y^4))
          >>> take (oh &&& (drop (fe_multiplyInt (-4))) >>> fe_add) &&& (iih &&& (ioh &&& take (oh &&& drop (fe_multiplyInt (-6)) >>> fe_add) >>> fe_multiply) >>> fe_add))  -- (9*x^4 - 8*x*y^2, 36*x^3*y^2 - 27*x^6 - 8*y^4)
         &&& (oih &&& ih >>> fe_multiply >>> fe_multiplyInt 2)                                                                                                               -- 2*y*z
     in
      gej_is_infinity &&& iden >>> cond (unit >>> gej_infinity) body

  , gej_add_ex =
     let
      body = ((oooh &&& (iih >>> fe_square) >>> fe_multiply) &&& (drop (take (take fe_negate)) &&& (oih >>> fe_square) >>> fe_multiply) >>> fe_add &&& oh)
         &&& ((ooih  &&& (iih >>> fe_cube) >>> fe_multiply)   &&& (drop (take (drop fe_negate)) &&& (oih >>> fe_cube) >>> fe_multiply) >>> fe_add &&& oh) &&&
             (oh &&& drop (drop fe_negate))                                                                                                                                     -- ((-h,u1),((-i,s1),(a,-bz))))
         >>> take (take fe_is_zero) &&& iden >>> cond (drop zeroH) nonZeroH
      zeroH = take (take fe_is_zero) &&& ioh >>> cond (take (drop (fe_multiplyInt 2)) &&& gej_double) (unit >>> fe_zero &&& gej_infinity)
      nonZeroH = (ooh &&& ((ooh &&& drop ioih >>> fe_multiply) &&& iiih)) &&& ((take (take fe_square) &&& oih >>> fe_multiply) &&& ioh)                                         -- ((-h,(-h*az,-bz)),(t,(i,s1)))
             >>> ((ooh &&& oiih >>> fe_multiply) &&& take (drop fe_multiply)) &&& (((ooh >>> fe_cube) &&& ioh) &&& iih)                                            -- ((h*bz),z),((-h^3,t),(i,s1)))
             >>> ooh &&& drop ((((take (oh &&& drop (fe_multiplyInt (-2)) >>> fe_add) &&& drop (take fe_square) >>> fe_add) &&& oih) &&& (ioh &&& (ooh &&& iih >>> fe_multiply)))  -- (h*bz,(((x,t),(i,(-h^3*s1))),z))
                          >>> ooh &&& (iih &&& (ioh &&& take (oh &&& drop fe_negate >>> fe_add) >>> fe_multiply) >>> fe_add))                                                   -- ..,(x,y),...
                     &&& oih
     in
      take gej_is_infinity &&& iden
  >>> cond ((unit >>> fe_zero) &&& (drop (take (take fe_normalize &&& drop fe_normalize) &&& (drop fe_normalize))))
           (drop gej_is_infinity &&& iden
        >>> cond ((unit >>> fe_one) &&& (take (take (take fe_normalize &&& drop fe_normalize) &&& (drop fe_normalize)))) body)

  , gej_add = gej_add_ex >>> ih

  , gej_ge_add_ex = oh &&& (ih &&& (unit >>> fe_one)) >>> gej_add_ex

  , gej_ge_add = gej_ge_add_ex >>> ih

  , gej_scale_lambda = take ge_scale_lambda &&& drop fe_normalize

  , ge_negate = take fe_normalize &&& drop fe_negate

  , ge_scale_lambda = take fe_multiply_beta &&& drop fe_normalize

  , gej_rescale = (ooh &&& ih >>> zinv) &&& (oih &&& ih >>> fe_multiply)

  , gej_normalize = oh &&& (ih >>> fe_invert) >>> zinv

--  , gej_equiv = :TODO:

  , gej_x_equiv = and (not (drop gej_is_infinity))
                     (drop (take (take fe_negate)) &&& (drop (drop fe_square) &&& oh >>> fe_multiply)
                  >>> fe_add >>> fe_is_zero)

  , gej_y_is_odd = oih &&& (ih >>> fe_invert >>> fe_cube) >>> fe_multiply >>> fe_is_odd

  , gej_is_on_curve = ((unit >>> scribe256 7) &&& (ih >>> fe_cube >>> fe_square) >>> fe_multiply)
                  &&& (take (take fe_cube &&& (drop fe_square >>> fe_negate)) >>> fe_add) >>> fe_add
                  >>> fe_is_zero

  , ge_is_on_curve = iden &&& (unit >>> fe_one) >>> gej_is_on_curve

  , scalar_normalize = (iden &&& (unit >>> scribeGroupOrder) >>> sub256) &&& iden
                  >>> ooh &&& (oih &&& ih)
                  >>> cond ih oh

  , scalar_is_zero = or (Arith.is_zero word256)
                  ((unit >>> scribeGroupOrder) &&& iden >>> eq)

  , scalar_add = add256 >>> cond ((unit >>> one256) &&& iden) ((unit >>> zero256) &&& iden) >>> scalar_normalize512

  , scalar_negate = (unit >>> scribe256 ((-1) `mod` LibSecp256k1.groupOrder)) &&& iden >>> scalar_multiply

  , scalar_square = iden &&& iden >>> scalar_multiply

  , scalar_multiply = mul256 >>> scalar_normalize512

  , scalar_multiply_lambda = (unit >>> scalar_lambda) &&& iden >>> scalar_multiply

  , scalar_invert = (unit >>> scribeGroupOrder) &&& iden >>> Arith.bezout word256 >>> copair (drop scalar_negate) ih

  , scalar_split_lambda = let
        g1 = scribe256 0x3086d221a7d46bcde86c90e49284eb153daa8a1471e8ca7fe893209a45dbb031
        g2 = scribe256 0xe4437ed6010e88286f547fa90abfe4c4221208ac9df506c61571b4ae8ac47f71
        negB1 = scribe128 0xe4437ed6010e88286f547fa90abfe4c3
        b2 = scribe128 0x3086d221a7d46bcde86c90e49284eb15
        roundDivTwo384 = take (drop (Arith.msb word128) &&& oh >>> Arith.full_increment word128) >>> ih
        c1 = ((iden &&& (unit >>> g1) >>> mul256) >>> roundDivTwo384) &&& (unit >>> negB1) >>> mul128
        c2 = ((iden &&& (unit >>> g2) >>> mul256) >>> roundDivTwo384) &&& (unit >>> b2) >>> mul128
        k1 = oh &&& drop (cond (((unit >>> high word128) &&& iden) &&& (unit >>> scribeGroupOrder) >>> add256 >>> ih)
                               ((unit >>> zero128) &&& iden)
                          &&& (unit >>> scalar_lambda) >>> scalar_multiply >>> scalar_negate) >>> scalar_add
         >>> msb256 &&& iden >>> cond (iden &&& (unit >>> scribeGroupOrder) >>> sub256 >>> injr unit &&& iih) (injl unit &&& ih)
      in
        scalar_normalize >>> iden &&& (c1 &&& c2 >>> sub256 >>> oh &&& iih) >>> k1 &&& ih

  , scalar_split_128 = scalar_normalize >>> (false &&& ih) &&& (false &&& oh)

  , wnaf5 = wnaf5step128 >>> (take wnaf5step1 >>> ih) &&& ih

  , wnaf15 = wnaf15step128 >>> (take wnaf15step1 >>> ih) &&& ih

  , generate =
     let
      step = iih &&& (ioh &&& take gej_double >>> match ih (ih &&& take generateSmall >>> gej_ge_add))
         >>> match ih (ih &&& take generate128Small >>> gej_ge_add)
      step2 = (oh &&& (iooh &&& iioh) >>> step) &&& (ioih &&& iiih) >>> step
      step4 = (oh &&& (iooh &&& iioh) >>> step2) &&& (ioih &&& iiih) >>> step2
      step8 = (oh &&& (iooh &&& iioh) >>> step4) &&& (ioih &&& iiih) >>> step4
      step16 = (oh &&& (iooh &&& iioh) >>> step8) &&& (ioih &&& iiih) >>> step8
      step32 = (oh &&& (iooh &&& iioh) >>> step16) &&& (ioih &&& iiih) >>> step16
      step64 = (oh &&& (iooh &&& iioh) >>> step32) &&& (ioih &&& iiih) >>> step32
      step128 = (oh &&& (iooh &&& iioh) >>> step64) &&& (ioih &&& iiih) >>> step64
      step129 = (oh &&& (iooh &&& iioh) >>> step) &&& (ioih &&& iiih) >>> step128
     in
      (unit >>> gej_infinity) &&& split128 >>> step129

  , linear_combination_1 =
     let
      splitLambda = scalar_split_lambda >>> take wnaf5 &&& drop wnaf5
      body = (unit >>> gej_infinity) &&& (oih >>> scalarTable5) &&& (ooh >>> splitLambda) &&& (ih >>> split128)
         >>> iooh &&& step129
         >>> ioh &&& (oh &&& iih >>> fe_multiply)
      step = drop iiih
        &&& (drop iioh
         &&& (drop ioih
          &&& (drop iooh &&& take gej_double &&& ioih
                     >>> match ioh (ioh &&& (oh &&& iih >>> lookupTable5) >>> gej_ge_add))
          &&& ioih
          >>> match ioh (ioh &&& (oh &&& iih >>> lookupTable5 >>> ge_scale_lambda) >>> gej_ge_add))
         &&& iooh
         >>> match ioh (ioh &&& (take generateSmall &&& iih >>> zinv) >>> gej_ge_add))
        &&& iooh
        >>> match ioh (ioh &&& (take generate128Small &&& iih >>> zinv) >>> gej_ge_add)
      step2 = (oh &&& drop (oh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh))) >>> step)
                  &&& drop (oh &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> step
      step4 = (oh &&& drop (oh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh))) >>> step2)
                  &&& drop (oh &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> step2
      step8 = (oh &&& drop (oh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh))) >>> step4)
                  &&& drop (oh &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> step4
      step16 = (oh &&& drop (oh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh))) >>> step8)
                   &&& drop (oh &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> step8
      step32 = (oh &&& drop (oh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh))) >>> step16)
                   &&& drop (oh &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> step16
      step64 = (oh &&& drop (oh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh))) >>> step32)
                   &&& drop (oh &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> step32
      step128 = (oh &&& drop (oh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh))) >>> step64)
                    &&& drop (oh &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> step64
      step129 = (oh &&& drop (oh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh))) >>> step)
                    &&& drop (oh &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> step128
     in
      -- In the case that the 'a' parameter is infinity or the 'na' parameter is 0, then scalarTable5 is not built.
      -- In particular the globalZ is set to 1 instead of whatever would have been generated by the table.
      or (take (drop gej_is_infinity)) (take (take scalar_is_zero)) &&& iden
  >>> cond (drop generate) body

  , linear_check_1 = and (drop ge_is_on_curve)
                    (and (take (take (drop ge_is_on_curve)))
                         ((take (take (oh &&& (ih &&& (unit >>> fe_one))) &&& ih >>> linear_combination_1))
                      &&& drop ge_negate >>> gej_ge_add >>> gej_is_infinity))

  , scale = iden &&& (unit >>> zero256) >>> linear_combination_1

  , decompress =
     let
      k = drop (drop fe_normalize) &&& (xor (take fe_is_odd) ioh &&& oh >>> cond fe_negate iden)
     in
      (scribe256 7 &&& drop fe_cube >>> fe_add >>> fe_square_root) &&& iden
       >>> match (injl unit) (injr k)

  , point_check_1 =
     let
       k1 = drop (take (drop decompress)) &&& (drop (ooh &&& ih) &&& oh)
        >>> match false k2
       k2 = ((iooh &&& oh) &&& ioih) &&& iih >>> linear_check_1
     in
       drop decompress &&& oh >>> match false k1

  , pubkey_unpack = pubkey_check >>> cond (injr ((unit >>> false) &&& iden)) (injl unit)

  , pubkey_unpack_neg = pubkey_check >>> cond (injr ((unit >>> true) &&& iden)) (injl unit)

  , signature_unpack =
      and (oh &&& scribe (toWord256 LibSecp256k1.fieldOrder) >>> lt256)
          (ih &&& scribe (toWord256 LibSecp256k1.groupOrder) >>> lt256)
  &&& iden
  >>> cond (injr iden) (injl unit)

  , bip0340_check =
     let
      k1 = iih &&& (ioh &&& oh)
       >>> match false k2
      k2 = (ih &&& oih) &&& ((unit >>> false) &&& ooh) >>> point_check_1
      e = m >>> (iv &&& oh >>> hashBlock) &&& ih >>> hashBlock >>> scalar_normalize
      iv = scribe $ toWord256 . integerHash256 . ivHash . tagIv $ "BIP0340/challenge"
      m = (ioh &&& ooh) &&& (oih &&& (scribe (toWord256 0x8000000000000000000000000000000000000000000000000000000000000500)))
     in
      take (take pubkey_unpack_neg) &&& (e &&& drop signature_unpack) >>> match false k1
  }
   where
    fe_cube = iden &&& fe_square >>> fe_multiply

    fe_multiplyInt i = scribe256 (i `mod` LibSecp256k1.fieldOrder) &&& iden >>> fe_multiply

    -- Common code shared between 'fe_invert' and 'fe_square_root'.
    tower = iden &&& fe_cube
        >>> ih &&& (oh &&& drop fe_square >>> fe_multiply)
        >>> oh &&& ((ih &&& (oh &&& (drop (iden &&& (iden &&& (fe_square >>> fe_square >>> fe_square) >>> fe_multiply >>> fe_square >>> fe_square >>> fe_square) >>> fe_multiply) >>> fe_square >>> fe_square) >>> fe_multiply -- (x2,(x3,x11))
                          >>> iden &&& foldr1 (>>>) (replicate 11 fe_square) >>> fe_multiply))                      -- (x2,(x3,x22))
                 >>> ih &&& (oh &&& drop (iden &&& foldr1 (>>>) (replicate 22 fe_square) >>> fe_multiply            -- (x2,(x22,(x3,x44)))
                                     >>> (iden &&& (iden &&& foldr1 (>>>) (replicate 44 fe_square) >>> fe_multiply  -- (x2,(x22,(x3,(x44,x88))))
                                                 >>> iden &&& foldr1 (>>>) (replicate 88 fe_square) >>> fe_multiply -- (x2,(x22,(x3,(x44,x176))))
                                           >>> foldr1 (>>>) (replicate 44 fe_square)) >>> fe_multiply)              -- (x2,(x22,(x3,x220)))
                                    >>> fe_square >>> fe_square >>> fe_square) >>> fe_multiply                                  -- (x2,(x22,x223))
                           >>> foldr1 (>>>) (replicate 23 fe_square)) >>> fe_multiply                               -- (x2,t1)
                 >>> foldr1 (>>>) (replicate 5 fe_square))

    zinv = (ooh &&& drop fe_square >>> fe_multiply) &&& (oih &&& drop fe_cube >>> fe_multiply)

    -- Compute odd-multiples of a point for small (5-bit) multiples.
    -- The result is in Jacobian coordinates but the z-coordinate is identical for all outputs.
    scalarTable5 :: term GEJ (FE, Vector8 GE)
    scalarTable5 = iden &&& gej_double
               >>> iih &&& (((ooh &&& iih >>> zinv) &&& oih) &&& ioh -- (dz, (a', (dx,dy)))
                        >>> pass1_8)
               >>> (oh &&& iih >>> fe_multiply) &&& drop (take pass2_8)
     where
      pass1_2 = iden &&& gej_ge_add_ex >>> (ioh &&& (oooh &&& iioh)) &&& (iih &&& oih)
      pass1_4 = pass1_2 >>> oh &&& drop (gej_ge_add_ex &&& ih >>> ooh &&& (oih &&& ih >>> pass1_2)) >>> (ioh &&& (oh &&& iioh)) &&& iiih
      pass1_8 = pass1_4 >>> oh &&& drop (gej_ge_add_ex &&& ih >>> ooh &&& (oih &&& ih >>> pass1_4)) >>> (ioh &&& (oh &&& iioh)) &&& drop (drop ioih)
      pass2_1 = oh &&& ih >>> zinv
      pass2_2 = (oioh &&& (ooh &&& ih >>> fe_multiply)) &&& (oiih &&& ih >>> pass2_1) >>> (take pass2_1 &&& ih) &&& oih
      pass2_4 = (ooh &&& oioh) &&& (oiih &&& ih >>> pass2_2) >>> (oih &&& (ooh &&& iih >>> fe_multiply) >>> pass2_2) &&& ioh >>> (ooh &&& ih) &&& oih
      pass2_8 = ( oh &&&  ioh) &&& ( iih &&& (unit >>> fe_one) >>> pass2_4) >>> (oih &&& (ooh &&& iih >>> fe_multiply) >>> pass2_4) &&& ioh >>> ooh &&& ih

    -- Given an odd-multiples table of affinte points, extract the @i@th element of the table.
    -- If the index is negative @i@, then return the point negation of the @i@th element of the table.
    lookupTable5 :: term (Word4, Vector8 GE) GE
    lookupTable5 = oooh &&& ooih &&& oih &&& ih
               >>> cond neg pos
     where
      pos = ioih &&& (iooh &&& (oh &&& iih >>> cond ih oh) >>> cond ih oh) >>> cond ih oh
      neg = ioih &&& (iooh &&& (oh &&& iih >>> cond oh ih) >>> cond oh ih) >>> cond (take ge_negate) (drop ge_negate)

    split128 = scalar_split_128 >>> take wnaf15 &&& drop wnaf15

    -- Returns a small, signed integer multiple of the secp256k1's generator as a normalized affine point.
    generateSigned :: Word a -> term a GEJ
    generateSigned SingleV = copair gej_infinity ((generate0 >>> ge_negate) &&& fe_one)
    generateSigned (DoubleV w) = ih &&& take rec >>> scaleConstant generate0 w
     where
      rec = generateSigned w

    generateSmall :: term Word16 GE
    generateSmall = generateSigned word16 >>> gej_normalize

    generate128Signed :: Word a -> term a GEJ
    generate128Signed SingleV = copair gej_infinity ((generate128 >>> ge_negate) &&& fe_one)
    generate128Signed (DoubleV w) = ih &&& take rec >>> scaleConstant generate128 w
     where
      rec = generate128Signed w

    generate128Small :: term Word16 GE
    generate128Small = generate128Signed word16 >>> gej_normalize

    pubkey_check = (iden &&& scribe (toWord256 LibSecp256k1.fieldOrder) >>> lt256) &&& iden

linear_verify_1 :: Assert term => Lib term -> term (((Scalar, GE), Scalar), GE) ()
linear_verify_1 m = assert (linear_check_1 m)

point_verify_1 :: Assert term => Lib term -> term (((Scalar, Point), Scalar), Point) ()
point_verify_1 m = assert (point_check_1 m)

-- | This function is given a public key, a 256-bit message, and a signature, and asserts that the signature is valid for the given message and public key.
bip0340_verify :: Assert term => Lib term -> term ((PubKey, Word256), Sig) ()
bip0340_verify m = assert (bip0340_check m)

-- | An instance of the Sha256 'Lib' library.
-- This instance does not share its dependencies.
-- Users should prefer to use 'mkLib' in order to share library dependencies.
-- This instance is provided mostly for testing purposes.
lib :: Core term => Lib term
lib = mkLib Sha256.lib
