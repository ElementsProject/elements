{-# LANGUAGE ScopedTypeVariables, RankNTypes, RecordWildCards #-}
-- | This module defines a library of Simplicity expressions that replicate the functional behaviour of (a specific version of) libsecp256k1's elliptic curve operations <https://github.com/bitcoin-core/secp256k1/tree/1e6f1f5ad5e7f1e3ef79313ec02023902bf8175c>.
-- The functions defined here return precisely the same field and point representatives that the corresponding libsecp256k1's functions do, with a few exceptions with the way the point at infinity is handled.
-- This makes these expressions suitable for being jetted by using libsecp256k1 functions.
module Simplicity.Programs.LibSecp256k1
  (
    Lib(Lib), mkLib
  -- * Field operations
  , FE, fePack, feUnpack, feZero, feOne, feIsZero
  , normalizeWeak, normalize
  , add, neg, mulInt, sqr, mul, inv, sqrt
  , isQuad
  -- * Point operations
  , GE, GEJ, inf, isInf
  , normalizePoint
  , geNegate, double, offsetPoint, offsetPointZinv
  , eqXCoord, hasQuadY
  -- * Elliptic curve multiplication related operations
  , Scalar
  , wnaf5, wnaf16
  , ecMult
  -- * Schnorr signature operations
  , XOnlyPubKey, pkPoint
  , Sig, sigUnpack
  , scalarUnrepr
  , schnorrVerify, schnorrAssert
  -- * Types
  , X10
  -- * Example instances
  , lib
  ) where

import Prelude hiding (drop, take, and, or, not, sqrt)

import Simplicity.Functor
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Programs.Word
import qualified Simplicity.Programs.Sha256 as Sha256
import Simplicity.Programs.Sha256 hiding (Lib(Lib), lib)
import Simplicity.Ty
import Simplicity.Term.Core

-- The number of elements in secp256k1's field.
feOrder :: Integer
feOrder = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

-- The number of points on secp256k1's elliptic curve.
scalarOrder :: Integer
scalarOrder = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

-- | Right-nested 9-tuple.
type X9 x = (x, (x, (x, (x, (x, (x, (x, (x, x))))))))

-- | Right-nested 10-tuple.
type X10 x = (x, (x, (x, (x, (x, (x, (x, (x, (x, x)))))))))

-- | Simplicity's representation of 'fe' (field) elements in libsecp256k1's 10x26-bit form.
type FE = X10 Word32

-- | A point in affine coordinates.
-- Usually expected to be on the elliptic curve.
-- The point at infinity isn't representable.
type GE = (FE, FE)

-- | A point in Jacobian coordinates.
-- Usually expected to be on the elliptic curve.
-- The point at infinity's representatives are of the form @((a^2, a^3), 0)@, with @((1, 1), 0)@ being the canonical representative.
type GEJ = (GE, FE)

-- | Scalar values, those less than the order of secp256's elliptic curve, are represented by a 256-bit word type.
type Scalar = Word256

type Wnaf5State = (Either Word2 (), Bit) -- state consists of a counter for skiping upto for places and a bit indicating the current carry bit.
type Wnaf5Env b = (b, Vector4 b) -- the environment consists of the current bit in the scalar being considered and the following 4 bits afterwards (zero padded).

-- | A format for (Schnorr) elliptic curve x-only public keys.
-- The y-coordinate is implicity the one on the curve that is positive (i.e it is a quadratic residue).
-- The point at infinity isn't representable (nor is it a valid public key to begin with).
type XOnlyPubKey = Word256

-- | A format for Schnorr signatures.
type Sig = (Word256, Word256)

-- | A collection of core Simplicity expressions for LibSecp256k1.
-- Use 'mkLib' to construct an instance of this library.
data Lib term =
 Lib
  { -- | Change the representation of a field element to one with magnitude 1.
    --
    -- Corresponds to @secp256k1_fe_normalize_weak@.
    normalizeWeak :: term FE FE

    -- | Reduce the representation of a field element to its canonical represenative.
    --
    -- Corresponds to @secp256k1_fe_normalize_var@ (and @secp256k1_fe_normalize@).
  , normalize :: term FE FE

    -- | Pack a field element into a 256-bit packed representation.
    -- The input is required to be 'normalize'd.
    --
    -- Corresponds to @secp256k1_fe_get_b32@.
  , fePack :: term FE Word256

    -- | Unpack a field element from a 256-bit packed representation.
    --
    -- Corresponds to @secp256k1_fe_set_b32@
  , feUnpack :: term Word256 FE

    -- | The normalized reprsentative for the field element 0.
  , feZero :: forall a. TyC a => term a FE

    -- | The normalized reprsentative for the field element 1.
  , feOne :: forall a. TyC a => term a FE

    -- | Tests if the input value is a representative of the field element 0.
    -- Some preconditions apply.
    --
    -- Corresponds to @secp256k1_fe_is_zero@.
  , feIsZero :: term FE Bit

    -- | Adds two field elements.
    -- The resulting magnitude is the sum of the input magnitudes.
    --
    -- Corresponds to @secp256k1_fe_add@.
  , add :: term (FE, FE) FE

    -- | Multiplies a field element by a small, static integer.
    -- The resulting magnitude is the input magnitude multiplied by the small integer.
    --
    -- Corresponds to @secp256k1_fe_mul_int@.
  , mulInt :: Integer -> term FE FE

    -- | Negates a field element.
    -- The resulting magnitude is one more than the input magnitude.
    --
    -- Corresponds to @secp256k1_fe_negate@.
  , neg :: Integer -> term FE FE

    -- | Multiplies two field elements.
    -- The input magnitudes must be at most 8 (okay maybe up to 10).
    -- The resulting magnitude is 1 (which isn't necessarily normalized).
    --
    -- Corresponds to @secp256k1_fe_mul@.
  , mul :: term (FE, FE) FE

    -- | Squares a field element.
    -- The input magnitude must be at most 8.
    -- The resulting magnitude is 1 (which isn't necessarily normalized).
    --
    -- Corresponds to @secp256k1_fe_sqr@.
  , sqr :: term FE FE

    -- | Computes the modular inverse of a field element.
    -- The input magnitude must be at most 8.
    -- The resulting magnitude is 1 (which isn't necessarily normalized).
    -- Returns a represenative of 0 when given 0.
    --
    -- Corresponds to @secp256k1_fe_inv@.
  , inv :: term FE FE

    -- | Computes the modular square root of a field element if it exists.
    -- The input magnitude must be at most 8.
    -- If the result exists, magnitude is 1 (which isn't necessarily normalized) and it is a quadratic residue
    --
    -- Corresponds to @secp256k1_fe_sqrt@.
    -- If @secp256k1_fe_sqrt@ would return 0, then @'Left' ()@ is returned by 'sqrt'.
    -- If @secp256k1_fe_sqrt@ would return 1, then @'Right' r@ is returned by 'sqrt' where @r@ is the result from @secp256k1_fe_sqrt@.
  , sqrt :: term FE (Either () FE)

    -- | Tests if the field element is a quadratic residue.
    --
    -- Corresponds to @secp256k1_fe_is_quad_var@.
  , isQuad :: term FE Bit

    -- | Returns the canonical represenative of the point at infinity.
  , inf :: forall a. TyC a => term a GEJ

    -- | Given a point on curve, or a represenativie of infinity, tests if the point is a representative of infinity.
  , isInf :: term GEJ Bit

    -- | Adds a point with itself.
    --
    -- Corresponds to @secp256k1_gej_double_var@.
    -- However if the input is infinity, it returns infinity in canonical form.
  , double :: term GEJ GEJ

    -- | Adds a point in Jacobian coordinates with a point in affine coordinates.
    -- Returns the result in Jacobian coordinates and the ratio of z-coordinates between the output and the input that is in Jacobain coordinates.
    -- If the input point in Jacobian coordinates is the point at infinity, the ratio returned is set to 0.
    --
    -- Corresponds to @secp256k1_gej_add_ge_var@ with a non-null @rzr@.
    -- If the result is the point at infinity, it is returned in canonical form.
  , offsetPoint :: term (GEJ, GE) (FE, GEJ)

    -- | Adds two point in Jacobian coordinates where the second point's z-coordinate is passed as the modular inverse of its true value.
    --
    -- Corresponds to @secp256k1_gej_add_zinv_var@.
    -- If the result is the point at infinity, it is returned in canonical form.
  , offsetPointZinv :: term (GEJ, (GE, FE)) GEJ

    -- | Negates a point in affine coordinates.
    --
    -- Corresponds to @secp256k1_ge_neg@.
  , geNegate :: term GE GE

    -- | Converts a point in Jacobian coordintes to the same point in affine coordinates, and normalizes the field represenatives.
    -- Returns the point (0, 0) when given the point at infinity.
  , normalizePoint :: term GEJ GE

    -- | Given a field element and a point in Jacobian coordiantes, test if the point represents one whose affine x-coordinate is equal to the given field element.
    --
    -- Corresponds to @secp256k1_gej_eq_x_var@.
  , eqXCoord :: term (FE, GEJ) Bit

    -- | Given a point in Jacobian coordiantes, test if the point represents one whose affine y-coordinate is a quadratic residue.
    --
    -- Corresponds to @secp256k1_gej_has_quad_y_var@.
  , hasQuadY :: term GEJ Bit

    -- | Convert a scalar value to wnaf form, with a window of 5 bits.
    -- The input must be strictly less than the order of secp256k1's elliptic curve.
    --
    -- Corresponds to @secp256k1_ecmult_wnaf@ with @w@ parameter set to 5.
  , wnaf5 :: term Scalar (Vector256 (Either () Word4))

    -- | Convert a scalar value to wnaf form, with a window of 16 bits.
    -- The input must be strictly less than the order of secp256k1's elliptic curve.
    --
    -- Corresponds to @secp256k1_ecmult_wnaf@ with @w@ parameter set to 16.
  , wnaf16 :: term Scalar (Vector256 (Either () Word16))

    -- | Returns an integer multiple of the secp256k1's generator.
    -- The input must be strictly less than the order of secp256k1's elliptic curve.
  , generator :: term Scalar GEJ

    -- | Given an elliptic curve point, @a@, and two scalar values @na@ and @ng@, return @na * a + ng * g@ where @g@ is secp256k1's generator.
    -- The scalar inputs must be strictly less than the order of secp256k1's elliptic curve.
    --
    -- Corresponds to @secp256k1_ecmult@.
    -- If the result is the point at infinity, it is returned in canonical form.
  , ecMult :: term ((GEJ, Scalar), Scalar) GEJ

    -- | This function unpacks a 'XOnlyPubKey' as a elliptic curve point in Jacobian coordinates.
    --
    -- If the x-coordinate isn't on the elliptice curve, the funtion returns @Left ()@.
    -- If the x-coordinate is greater than or equal the field order, the function returns @Left ()@.
  , pkPoint :: term XOnlyPubKey (Either () GEJ)

    -- | This function unpackes a 'Sig' as a pair of a field element and a scalar value.
    --
    -- If the field element's value is greater than or equal to the field order, the function return @Left ()@.
    -- If the scalar element's value is greater than or equal to secp256k1's curve order, the function returns @Left ()@.
  , sigUnpack :: term Sig (Either () (FE, Scalar))

    -- | This function reduces a 256-bit unsigned integer module the order of the secp256k1 curve, yielding a scalar value.
  , scalarUnrepr :: term Word256 Scalar

    -- | This function is given a public key, a 256-bit message, and a signature, and checks if the signature is valid for the given message and public key.
  , schnorrVerify :: term ((XOnlyPubKey, Word256), Sig) Bit
  }

instance SimplicityFunctor Lib where
  sfmap m Lib{..} =
   Lib
    { normalizeWeak = m normalizeWeak
    , normalize = m normalize
    , fePack = m fePack
    , feUnpack = m feUnpack
    , feZero = m feZero
    , feOne = m feOne
    , feIsZero = m feIsZero
    , add = m add
    , mulInt = m <$> mulInt
    , neg = m <$> neg
    , mul = m mul
    , sqr = m sqr
    , inv = m inv
    , sqrt = m sqrt
    , isQuad = m isQuad
    , inf = m inf
    , isInf = m isInf
    , double = m double
    , offsetPoint = m offsetPoint
    , offsetPointZinv = m offsetPointZinv
    , geNegate = m geNegate
    , normalizePoint = m normalizePoint
    , eqXCoord = m eqXCoord
    , hasQuadY = m hasQuadY
    , wnaf5 = m wnaf5
    , wnaf16 = m wnaf16
    , generator = m generator
    , ecMult = m ecMult
    , pkPoint = m pkPoint
    , sigUnpack = m sigUnpack
    , scalarUnrepr = m scalarUnrepr
    , schnorrVerify = m schnorrVerify
    }

-- | Build the LibSecp256k1 'Lib' library from its dependencies.
mkLib :: forall term. Core term => Sha256.Lib term -- ^ "Simplicity.Programs.Sha256"
                                -> Lib term
mkLib Sha256.Lib{..} = lib
 where
  -- A constant expression for a 8-bit value.
  scribe8 :: forall term a. (Core term, TyC a) => Integer -> term a Word8
  scribe8 = scribe . toWord8

  -- A constant expression for a 32-bit value.
  scribe32 :: forall term a. (Core term, TyC a) => Integer -> term a Word32
  scribe32 = scribe . toWord32

  -- A constant expression for a 64-bit value.
  scribe64 :: forall term a. (Core term, TyC a) => Integer -> term a Word64
  scribe64 = scribe . toWord64

  -- Addition modulo 2^32.
  add32 :: term (Word32, Word32) Word32
  add32 = adder word32 >>> ih

  -- Subtraction modulo 2^32.
  sub32 :: term (Word32, Word32) Word32
  sub32 = subtractor word32 >>> ih

  -- Multiplication modulo 2^32.
  mul32 :: term (Word32, Word32) Word32
  mul32 = multiplier word32 >>> ih

  -- Addition modulo 2^64.
  add64 :: term (Word64, Word64) Word64
  add64 = adder word64 >>> ih

  -- Multiplication modulo 2^64.
  mul64 :: term (Word64, Word64) Word64
  mul64 = multiplier word64 >>> ih

  -- Multiplication of two 32-bit values.
  wideMul32 :: term (Word32, Word32) Word64
  wideMul32 = multiplier word32

  -- Subtraction modulo 2^256.
  sub256 :: term (Word256, Word256) Word256
  sub256 = subtractor word256 >>> ih

  -- Reduction modulo 2^26.
  mod26 :: term Word32 Word32
  mod26 = take ((zero word4 &&& (zero word2 &&& oiih)) &&& ih) &&& ih

  -- Reduction modulo 2^22.
  mod22 :: term Word32 Word32
  mod22 = (zero word8 &&& take (drop ((zero word2 &&& oih) &&& ih))) &&& ih

  -- Shift right by 26 bits.
  shift26 :: term Word32 Word32
  shift26 = shift word32 26

  -- Shift right by 22 bits.
  shift22 :: term Word32 Word32
  shift22 = shift word32 22

  -- | The normalized reprsentative for the field element 7.
  feSeven :: TyC a => term a FE
  feSeven = scribe32 7 &&& z &&& z &&& z &&& z &&& z &&& z &&& z &&& z &&& z
   where
    z = zero word32

  -- A combinator for evaluating @k@ on the ith element of an @X10 x@ value.
  at :: (TyC x, TyC a) => term x a -> Integer -> term (X10 x) a
  at k 0 = take k
  at k 1 = drop . take $ k
  at k 2 = drop . drop . take $ k
  at k 3 = drop . drop . drop . take $ k
  at k 4 = drop . drop . drop . drop . take $ k
  at k 5 = drop . drop . drop . drop . drop . take $ k
  at k 6 = drop . drop . drop . drop . drop . drop . take $ k
  at k 7 = drop . drop . drop . drop . drop . drop . drop . take $ k
  at k 8 = drop . drop . drop . drop . drop . drop . drop . drop . take $ k
  at k 9 = drop . drop . drop . drop . drop . drop . drop . drop . drop $ k

  -- A combinator for applying the binary @k@ expression pointwise on pair of field elements.
  pointWise :: term (Word32, Word32) Word32 -> term (FE,FE) FE
  pointWise k = ((take (iden `at` 0) &&& drop (iden `at` 0)) >>> k)
            &&& ((take (iden `at` 1) &&& drop (iden `at` 1)) >>> k)
            &&& ((take (iden `at` 2) &&& drop (iden `at` 2)) >>> k)
            &&& ((take (iden `at` 3) &&& drop (iden `at` 3)) >>> k)
            &&& ((take (iden `at` 4) &&& drop (iden `at` 4)) >>> k)
            &&& ((take (iden `at` 5) &&& drop (iden `at` 5)) >>> k)
            &&& ((take (iden `at` 6) &&& drop (iden `at` 6)) >>> k)
            &&& ((take (iden `at` 7) &&& drop (iden `at` 7)) >>> k)
            &&& ((take (iden `at` 8) &&& drop (iden `at` 8)) >>> k)
            &&& ((take (iden `at` 9) &&& drop (iden `at` 9)) >>> k)

  -- Common code shared between 'normalizeWeak' and 'normalize'.
  reduce :: term (Word32, FE) FE
  reduce = ((ioh &&& ((oh &&& scribe32 0x3D1) >>> mul32) >>> add32)
       &&& ((iioh &&& (take (shift word32 (-6))) >>> add32)
       &&& iiih))
       >>> ((take mod26) &&& ((ioh &&& (take shift26) >>> add32) &&& iih
       >>> ((take mod26) &&& ((ioh &&& (take shift26) >>> add32) &&& iih
       >>> ((take mod26) &&& ((ioh &&& (take shift26) >>> add32) &&& iih
       >>> ((take mod26) &&& ((ioh &&& (take shift26) >>> add32) &&& iih
       >>> ((take mod26) &&& ((ioh &&& (take shift26) >>> add32) &&& iih
       >>> ((take mod26) &&& ((ioh &&& (take shift26) >>> add32) &&& iih
       >>> ((take mod26) &&& ((ioh &&& (take shift26) >>> add32) &&& iih
       >>> ((take mod26) &&& ((ioh &&& (take shift26) >>> add32) &&& iih
       >>> ((take mod26) &&& ((drop mod22) &&& (take shift26) >>> add32))
           ))))))))))))))))

  -- The first non-canonical representative of 0.
  -- It consists of the bits of feOrder
  bigZero :: term FE FE
  bigZero = scribe32 0x3FFFC2F
        &&& scribe32 0x3FFFFBF
        &&& scribe3FFFFFF
        &&& scribe3FFFFFF
        &&& scribe3FFFFFF
        &&& scribe3FFFFFF
        &&& scribe3FFFFFF
        &&& scribe3FFFFFF
        &&& scribe3FFFFFF
        &&& scribe32 0x03FFFFF
   where
    scribe3FFFFFF = scribe32 0x3FFFFFF

  wnaf5step1 :: term (Wnaf5State, Wnaf5Env Bit) (Wnaf5State, Either () Word4)
  wnaf5step1 = ooh &&& (oih &&& ih)
           >>> match (count &&& injl unit) (drop body)
   where
    count = ooh &&& (oih &&& ioh)
        >>> cond (cond (injl (true  &&& false) &&& iden) (injl (false &&& true) &&& iden))
                 (cond (injl (false &&& false) &&& iden) (injr unit             &&& iden))
    body = ((oh &&& ioh >>> eq) &&& (oh &&& iih))
       >>> cond ((injr unit &&& oh) &&& injl unit)
                ((injl (true &&& true) &&& iooh) &&& (injr ih))

  wnaf5stepD :: (TyC w, TyC v) => term (Wnaf5State, Wnaf5Env w) (Wnaf5State, v) -> term (Wnaf5State, Wnaf5Env (w,w)) (Wnaf5State, (v,v))
  wnaf5stepD rec = (oh &&& drop (oih &&& drop ((ooih &&& oiih) &&& (ioih &&& iiih))) >>> rec) &&& drop (ooh &&& drop ((oooh &&& oioh) &&& (iooh &&& iioh)))
               >>> oih &&& (ooh &&& ih >>> rec)
               >>> ioh &&& (oh &&& iih)

  wnaf5step16 :: term (Wnaf5State, Wnaf5Env Word16) (Wnaf5State, Vector16 (Either () Word4))
  wnaf5step16 = wnaf5stepD . wnaf5stepD . wnaf5stepD . wnaf5stepD $ wnaf5step1

  wnaf5Short :: term Word16 (Vector16 (Either () Word4))
  wnaf5Short = false &&& iden >>> go
   where
    go = (injr unit &&& oh) &&& (oh &&& drop (iden &&& ((shift word16 4 &&& shift word16 3) &&& (shift word16 2 &&& shift word16 1)))
                             >>> cond (take (bitwiseNot word16) &&& drop (bitwiseNot (DoubleV (DoubleV word16)))) iden)
     >>> wnaf5step16 >>> ih

  lib@Lib{..} = Lib {
    normalizeWeak = (shift22 `at` 9) &&& iden >>> reduce

  , normalize =
     let
      more = or (bit22 `at` 9)
          (and (scribe32 0x3FFFFFF &&& (scribe32 0x40 &&& (ioh &&& (scribe32 0x3D1 &&& oh >>> add32 >>> shift26) >>> add32) >>> add32) >>> subtractor word32 >>> oh)
               (drop (drop (and (scribe32 0x3FFFFFF &&& oh >>> eq)
                     (drop (and (scribe32 0x3FFFFFF &&& oh >>> eq)
                     (drop (and (scribe32 0x3FFFFFF &&& oh >>> eq)
                     (drop (and (scribe32 0x3FFFFFF &&& oh >>> eq)
                     (drop (and (scribe32 0x3FFFFFF &&& oh >>> eq)
                     (drop (and (scribe32 0x3FFFFFF &&& oh >>> eq)
                     (drop (and (scribe32 0x3FFFFFF &&& oh >>> eq)
                                (scribe32 0x03FFFFF &&& ih >>> eq)))))))))))))))))
      bit22 = take (drop ooih)
      modAt9 =       oh &&& drop (oh &&& drop (oh &&& drop (oh &&& drop (oh
           &&& drop (oh &&& drop (oh &&& drop (oh &&& drop (oh &&& drop mod22))))))))
     in
      normalizeWeak >>> more &&& iden
  >>> cond (scribe32 1 &&& iden >>> reduce >>> modAt9) iden

  , fePack =
     let
      w0 = ((drop (take (drop (drop (oih &&& ioh)))) &&& (drop (take (drop iiih)) &&& take (take oiih))) &&& ooih) &&& oih
      w1 = (drop (take (drop (oih &&& ioh))) &&& (drop (take iiih) &&& take (take (oiih &&& iooh)))) &&& take ((take (drop (oih &&& ioh)) &&& (take iiih &&& drop oooh) ) &&& drop (take (oih &&& ioh) &&& (oiih &&& iooh)))
      w2 = drop (take (((take iiih &&& drop oooh) &&& drop (take (oih &&& ioh))) &&& drop ((oiih &&& iooh) &&& drop (oih &&& ioh)))) &&& (((drop (take (drop iiih)) &&& take (take oiih)) &&& take oioh) &&& take (oiih &&& iooh))
      w3 = drop (take (oih &&& ioh)) &&& (drop (take iih) &&& take (take ((oiih &&& iooh) &&& drop (oih &&& ioh))))
      w4 = drop ((drop (take iiih) &&& take (take (oiih &&& iooh))) &&& take (take (drop (oih &&& ioh)) &&& (take iiih &&& drop oooh))) &&& (drop (take (drop (take (oih &&& ioh) &&& (oiih &&& iooh)))) &&& (drop (take (drop (drop (oih &&& ioh)))) &&& (drop (take (drop iiih)) &&& take (take oiih))))
      w5 = (drop (take (drop ((oiih &&& iooh) &&& drop (oih &&& ioh)))) &&& ((drop (take (drop iiih)) &&& take (take oiih)) &&& take oioh)) &&& take ((oiih &&& iooh) &&& drop (oih &&& ioh))
      w6 = drop (take ih) &&& take (take ((oiih &&& iooh) &&& drop (oih &&& ioh)) &&& ((take iiih &&& drop oooh) &&& drop (take (oih &&& ioh))))
      w7 = drop ((take (drop (oih &&& ioh)) &&& (take iiih &&& drop oooh)) &&& drop (take (oih &&& ioh) &&& (oiih &&& iooh))) &&& ((drop (drop (drop (oih &&& ioh))) &&& (drop (drop iiih) &&& take (take oiih))) &&& take oih)
     in
      drop (drop (drop (drop (drop (drop (drop (drop w7 &&& w6))) &&& (drop (drop w5) &&& w4)))))
  &&& (drop (drop (drop w3 &&& w2)) &&& (drop w1 &&& w0))

  , feUnpack = drop (drop (drop (take ((zero word4 &&& (zero word2 &&& oiih)) &&& ih) &&& ih)))
           &&& drop (drop (take ((zero word4 &&& (zero word2 &&& take (drop ioh))) &&& ((take iiih &&& drop oooh) &&& drop (take (oih &&& ioh)))) &&& (take (drop ((oiih &&& iooh) &&& drop (oih &&& ioh))) &&& ((take (drop iiih) &&& drop (take oooh)) &&& drop (take (take (oih &&& ioh)))))))
           &&& drop (take (drop (drop ((zero word4 &&& (zero word2 &&& ooih)) &&& (oih &&& ioh)))) &&& ((take (drop iiih) &&& drop (take oooh)) &&& drop (take (take (oih &&& ioh)))))
           &&& drop (take (((zero word4 &&& (zero word2 &&& take (drop iooh))) &&& (take (drop (drop (oih &&& ioh))) &&& (take (drop iiih) &&& drop (take oooh)))) &&& drop ((take (take (oih &&& ioh) &&& (oiih &&& iooh))) &&& (take (ioih &&& iioh) &&& (take iiih &&& drop oooh)))))
           &&& (((zero word4 &&& (zero word2 &&& take (drop (drop (drop iiih))))) &&& drop (take oooh)) &&& drop (take (take (oih &&& ioh))))
           &&& take ((drop (drop (take ((zero word4 &&& (zero word2 &&& oioh)) &&& ((oiih &&& iooh) &&& drop (oih &&& ioh))) &&& (((take iiih &&& drop oooh) &&& drop (take (oih &&& ioh))) &&& drop ((oiih &&& iooh) &&& drop (oih &&& ioh))))))
            &&& drop (take ((zero word4 &&& (zero word2 &&& take ioih)) &&& (oiih &&& iooh)) &&& (take (drop (oih &&& ioh)) &&& (take iiih &&& drop oooh)))
            &&& (take (drop (drop ((zero word4 &&& (zero word2 &&& oooh)) &&& (take (oih &&& ioh) &&& (oiih &&& iooh))))) &&& ((take (drop (drop (drop (oih &&& ioh)))) &&& (take (drop (drop iiih)) &&& drop (take (take oooh)))) &&& drop (take (take (take (oih &&& ioh) &&& (oiih &&& iooh))))))
            &&& take ((((zero word4 &&& (zero word2 &&& take (drop oiih))) &&& oiih) &&& ioh)
             &&& take (take (take (zero word8 &&& ((zero word2 &&& ooh) &&& (oih &&& ioh)))) &&& (take ((oiih &&& iooh) &&& drop (oih &&& ioh)) &&& ((take iiih &&& drop oooh) &&& drop (take (oih &&& ioh)))))))

  , feZero =
     let
      z = zero word32
     in
      z &&& z &&& z &&& z &&& z &&& z &&& z &&& z &&& z &&& z

  , feOne =
     let
      z = zero word32
     in
      scribe32 1 &&& z &&& z &&& z &&& z &&& z &&& z &&& z &&& z &&& z

  , feIsZero = normalizeWeak >>> or (feZero &&& iden >>> eq) (bigZero &&& iden >>> eq)

  , add = pointWise add32

  , mulInt = \x ->
     let
      scale = iden &&& scribe32 x >>> mul32
     in
      take scale &&& drop
    ( take scale &&& drop
    ( take scale &&& drop
    ( take scale &&& drop
    ( take scale &&& drop
    ( take scale &&& drop
    ( take scale &&& drop
    ( take scale &&& drop
    ( take scale &&& drop scale
    ))))))))

  , neg = \x -> (bigZero >>> mulInt (2*(x+1))) &&& iden >>> pointWise sub32

  , mul =
     let
      convlo i = mksum [larg j &&& rarg (i-j) >>> wideMul32|j<-[0..i]]
      convhi i = mksum [larg j &&& rarg (i-j) >>> wideMul32|j<-[i-9..9]]
      larg i = take (iden `at` i)
      rarg i = drop (iden `at` i)
      mksum = foldr1 (\t1 t2 -> t1 &&& t2 >>> add64)
     in
      (convlo 0 &&& convlo 1 &&& convlo 2 &&& convlo 3 &&& convlo 4 &&& convlo 5 &&& convlo 6 &&& convlo 7 &&& convlo 8)
  &&& (convhi 9 &&& convhi 10 &&& convhi 11 &&& convhi 12 &&& convhi 13 &&& convhi 14 &&& convhi 15 &&& convhi 16 &&& convhi 17 &&& convhi 18)
  >>> sum19

  , sqr =
     let
      convlo i = mksum $ [shift word32 (-1) `at` j &&& iden `at` (i-j) >>> wideMul32|j<-[0..(i-1) `div` 2]] ++ [iden `at` (i `div` 2) >>> iden &&& iden >>> wideMul32 | even i]
      convhi i = mksum $ [iden `at` j &&& shift word32 (-1) `at` (i-j) >>> wideMul32|j<-[(i+2) `div` 2..9]] ++ [iden `at` (i `div` 2) >>> iden &&& iden >>> wideMul32 | even i]
      mksum = foldr1 (\t1 t2 -> t1 &&& t2 >>> add64)
     in
      (convlo 0 &&& convlo 1 &&& convlo 2 &&& convlo 3 &&& convlo 4 &&& convlo 5 &&& convlo 6 &&& convlo 7 &&& convlo 8)
  &&& (convhi 9 &&& convhi 10 &&& convhi 11 &&& convhi 12 &&& convhi 13 &&& convhi 14 &&& convhi 15 &&& convhi 16 &&& convhi 17 &&& convhi 18)
  >>> sum19

  , inv = iden &&& tower
      >>> oh &&& (ioh &&& (oh &&& iih >>> mul >>> sqr >>> sqr >>> sqr) >>> mul >>> sqr >>> sqr) >>> mul

  , sqrt = iden &&& tower
       >>> oh &&& drop ((oh &&& drop sqr >>> mul) >>> sqr >>> sqr)
       >>> (oh &&& drop (sqr >>> neg 1) >>> add >>> feIsZero) &&& ih
       >>> cond (injr iden) (injl unit)

  , isQuad = sqrt &&& unit >>> match false true

  , inf =
     let
      one = feOne
     in
      (one &&& one) &&& feZero

  , isInf = drop feIsZero

  , double =
     let
      body = (take (oh &&& (take sqr >>> mulInt 3) &&& (drop sqr >>> mulInt 2))
          >>> (((drop (take sqr)) &&& (iih &&& oh >>> mul)) &&& drop (oh &&& (drop sqr >>> mulInt 2)))
          >>> take (oh &&& (drop (mulInt 4) >>> neg 4) >>> add) &&& (drop (drop (neg 2)) &&& (ioh &&& take (take (neg 1) &&& drop (mulInt 6) >>> add) >>> mul) >>> add))
         &&& (oih &&& ih >>> mul >>> mulInt 2)
     in
      isInf &&& iden >>> cond inf body

  , offsetPoint =
     let
      body = take (iden &&& take (take normalizeWeak &&& drop normalizeWeak)) &&& (ih &&& take (drop sqr))                                                           -- ((a,(u1,s1)),(b,z12))
         >>> ((take (drop (take (neg 1))) &&& drop (ooh &&& ih >>> mul) >>> add) &&& oioh)
         &&& ((take (drop (drop (neg 1))) &&& (ooih &&& drop (oih &&& ih >>> mul) >>> mul) >>> add) &&& take (iih &&& oh))                                           -- ((h,u1),(i,(s1,a)))
         >>> take (take feIsZero) &&& iden >>> cond (drop zeroH) nonZeroH
      zeroH = take feIsZero &&& ih >>> cond (take (mulInt 2) &&& drop double) (feZero &&& inf)
      nonZeroH = (ooh &&& (ooh &&& drop iiih >>> mul)) &&& ((take (take sqr) &&& oih) &&& (ioh &&& iioh))                                                            -- ((h,z),((h2,u1),(i s1)))
             >>> oh &&& (((ooh &&& iooh >>> mul) &&& drop (take mul)) &&& iih)                                                                                       -- ((h,z),((h3,t),(i,s1)))
             >>> oh &&& drop (((take (oh &&& drop (mulInt 2) >>> add >>> neg 3) &&& drop (take sqr) >>> add) &&& oih) &&& (ioh &&& (ooh &&& iih >>> mul >>> neg 1))) -- ((h,z),((x,t),(i,(-h3*s1))))
             >>> ooh &&& (drop (ooh &&& (iih &&& (ioh &&& (oih &&& take (take (neg 5)) >>> add) >>> mul) >>> add)) &&& oih)                                          -- (h,((x,y),z))
     in
      take isInf &&& iden >>> cond (feZero &&& (drop (iden &&& feOne))) body

  , offsetPointZinv =
     let
      infCase = iden &&& drop sqr
            >>> (oooh &&& ih >>> mul) &&& (ooih &&& (oih &&& ih >>> mul) >>> mul)
      body = take (iden &&& take (take normalizeWeak &&& drop normalizeWeak)) &&& (ioh &&& (iih &&& oih >>> mul >>> iden &&& sqr))                                   -- ((a,(u1,s1)),(b,(az,z12)))
         >>> ((take (drop (take (neg 1))) &&& drop (ooh &&& iih >>> mul) >>> add) &&& oioh)
         &&& ((take (drop (drop (neg 1))) &&& drop (ioh &&& (oih &&& iih >>> mul) >>> mul) >>> add) &&& take (iih &&& oh))                                           -- ((h,u1),(i,(s1,a)))
         >>> take (take feIsZero) &&& iden >>> cond (drop zeroH) nonZeroH
      zeroH = take feIsZero &&& ih >>> cond (drop double) inf
      nonZeroH = (ooh &&& (ooh &&& drop iiih >>> mul)) &&& ((take (take sqr) &&& oih) &&& (ioh &&& iioh))                                                            -- ((h,z),((h2,u1),(i s1)))
             >>> oih &&& (((ooh &&& iooh >>> mul) &&& drop (take mul)) &&& iih)                                                                                      -- (z,((h3,t),(i,s1)))
             >>> oh &&& drop (((take (oh &&& drop (mulInt 2) >>> add >>> neg 3) &&& drop (take sqr) >>> add) &&& oih) &&& (ioh &&& (ooh &&& iih >>> mul >>> neg 1))) -- (z,((x,t),(i,(-h3*s1))))
             >>> drop (ooh &&& (iih &&& (ioh &&& (oih &&& take (take (neg 5)) >>> add) >>> mul) >>> add)) &&& oh                                                     -- ((x,y),z)
     in
      take isInf &&& iden >>> cond (drop (infCase &&& feOne)) body

  , geNegate = oh &&& drop (normalizeWeak >>> neg 1)

  , normalizePoint = oh &&& (ih >>> inv >>> (sqr &&& iden))
                 >>> (ooh &&& ioh >>> mul >>> normalize) &&& (oih &&& (ioh &&& iih >>> mul) >>> mul >>> normalize)

  , eqXCoord = drop (take (take normalizeWeak)) &&& (drop (drop sqr) &&& oh >>> mul >>> neg 1)
           >>> add >>> feIsZero

  , hasQuadY = and (not isInf) (oih &&& ih >>> mul >>> isQuad)

  , wnaf5 =
     let
      -- a variant of shift that pulls in leading ones could be useful here instead of using bitwiseNot.
      go = (injr unit &&& oh) &&& (oh &&& drop (iden &&& ((shift word256 4 &&& shift word256 3) &&& (shift word256 2 &&& shift word256 1)))
                               >>> cond (take (bitwiseNot word256) &&& drop (bitwiseNot (DoubleV (DoubleV word256)))) iden)
       >>> wnaf5step256 >>> ih
      wnaf5step256 = wnaf5stepD . wnaf5stepD . wnaf5stepD . wnaf5stepD $ wnaf5step16
     in
      (take . take . take . take . take $ oooh) &&& iden
  >>> cond (true &&& (scribe (toWord256 scalarOrder) &&& iden >>> sub256) >>> go)
           (false &&& iden >>> go)

  , wnaf16 =
     let
      -- a variant of shift that pulls in leading ones could be useful here instead of using bitwiseNot.
      go = (injr unit &&& oh) &&& (oh &&& drop shifts
                               >>> cond (bitwiseNot (DoubleV (DoubleV (DoubleV (DoubleV word256))))) iden)
       >>> wnaf16step256 >>> ih
      shifts = (((shift word256 15 &&& shift word256 14) &&& (shift word256 13 &&& shift word256 12)) &&& ((shift word256 11 &&& shift word256 10) &&& (shift word256 9 &&& shift word256 8)))
           &&& (((shift word256 7 &&& shift word256 6) &&& (shift word256 5 &&& shift word256 4)) &&& ((shift word256 3 &&& shift word256 2) &&& (shift word256 1 &&& iden)))
      wnaf16step1 = ooh &&& (oih &&& ih)
               >>> match (count &&& injl unit) (drop body)
       where
        count = (zero word4 &&& oh >>> eq) &&& (oh &&& ioh)
            >>> cond (injr unit &&& ih) (injl ((oh &&& zero word4) &&& true >>> fullSubtractor word4 >>> ih) &&& ih)
        body = ((oh &&& drop (drop iiih) >>> eq) &&& iden)
           >>> cond ((injr unit &&& oh) &&& injl unit)
                    ((injl (scribe (toWord word4 14)) &&& drop (take oooh)) &&& (injr (drop setLowBit)))
        setLowBit = oh &&& drop (oh &&& drop (oh &&& drop (oh &&& true)))
      wnaf16stepD rec = (oh &&& drop dropV16 >>> rec) &&& drop takeV16
                >>> oih &&& (ooh &&& ih >>> rec)
                >>> ioh &&& (oh &&& iih)
       where
        takeV2 = ooh &&& ioh
        takeV4 = take takeV2 &&& drop takeV2
        takeV8 = take takeV4 &&& drop takeV4
        takeV16 = take takeV8 &&& drop takeV8
        dropV2 = oih &&& iih
        dropV4 = take dropV2 &&& drop dropV2
        dropV8 = take dropV4 &&& drop dropV4
        dropV16 = take dropV8 &&& drop dropV8
      wnaf16step256 = wnaf16stepD . wnaf16stepD . wnaf16stepD . wnaf16stepD . wnaf16stepD . wnaf16stepD . wnaf16stepD . wnaf16stepD $ wnaf16step1
     in
      (take . take . take . take . take $ oooh) &&& iden
  >>> cond (true &&& (scribe (toWord256 scalarOrder) &&& iden >>> sub256) >>> go)
           (false &&& iden >>> go)

  , generator =
     let
      step = match (drop double) (drop double &&& take generatorSmall &&& feOne >>> offsetPointZinv)
      step2 = ooh &&& (oih &&& ih >>> step) >>> step
      step4 = ooh &&& (oih &&& ih >>> step2) >>> step2
      step8 = ooh &&& (oih &&& ih >>> step4) >>> step4
      step16 = ooh &&& (oih &&& ih >>> step8) >>> step8
      step32 = ooh &&& (oih &&& ih >>> step16) >>> step16
      step64 = ooh &&& (oih &&& ih >>> step32) >>> step32
      step128 = ooh &&& (oih &&& ih >>> step64) >>> step64
      step256 = ooh &&& (oih &&& ih >>> step128) >>> step128
     in
      wnaf16 &&& inf >>> step256

  , ecMult =
     let
      body = inf &&& (ooh >>> scalarTable5) &&& (oih >>> wnaf5) &&& (ih >>> wnaf16)
         >>> iooh &&& step256
      step = iiih &&& (iioh &&& take double &&& ioih >>> match ioh (ioh &&& (oh &&& iih >>> lookupTable5) >>> offsetPoint >>> ih)) &&& iooh
         >>> match ioh (ioh &&& take generatorSmall &&& iih >>> offsetPointZinv)
      step2 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step) &&& drop (oh &&& iooh &&& iioh) >>> step
      step4 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step2) &&& drop (oh &&& iooh &&& iioh) >>> step2
      step8 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step4) &&& drop (oh &&& iooh &&& iioh) >>> step4
      step16 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step8) &&& drop (oh &&& iooh &&& iioh) >>> step8
      step32 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step16) &&& drop (oh &&& iooh &&& iioh) >>> step16
      step64 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step32) &&& drop (oh &&& iooh &&& iioh) >>> step32
      step128 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step64) &&& drop (oh &&& iooh &&& iioh) >>> step64
      step256 = (oh &&& drop (oh &&& ioih &&& iiih) >>> step128) &&& drop (oh &&& iooh &&& iioh) >>> step128
     in
      (scribe (toWord256 0) &&& oih >>> eq) &&& iden
  >>> cond (drop (feOne &&& generator)) body
  >>> ioh &&& (oh &&& iih >>> mul)

  , pkPoint =
     let
      k1 = (feSeven &&& (iden &&& sqr >>> mul) >>> add >>> sqrt) &&& iden
       >>> match (injl unit) (injr k2)
      k2 = (ih &&& oh) &&& feOne
      lt = subtractor word256 >>> oh
     in
      (iden &&& scribe (toWord256 feOrder) >>> lt) &&& feUnpack
  >>> cond k1 (injl unit)

  , sigUnpack =
     let
      lt = subtractor word256 >>> oh
     in
      and (oh &&& scribe (toWord256 feOrder) >>> lt)
          (ih &&& scribe (toWord256 scalarOrder) >>> lt)
  &&& (take feUnpack &&& ih)
  >>> cond (injr iden) (injl unit)

  , scalarUnrepr = (iden &&& scribe (toWord256 scalarOrder) >>> subtractor word256) &&& iden
               >>> ooh &&& (oih &&& ih)
               >>> cond ih oh

  , schnorrVerify =
     let
      k1 = ioh &&& (iih &&& oh)
       >>> match false k2
      k2 = iioh &&& ((oh &&& ioh) &&& iiih >>> ecMult)
       >>> and eqXCoord (drop hasQuadY)
      nege = (scribe (toWord256 scalarOrder) &&& (h >>> scalarUnrepr) >>> sub256)
      iv = scribe (toWord256 0x048d9a59fe39fb0528479648e4a660f9814b9e660469e80183909280b329e454)
      h = m >>> (iv &&& oh >>> hashBlock) &&& ih >>> hashBlock
      m = (ioh &&& ooh) &&& (oih &&& (scribe (toWord256 0x8000000000000000000000000000000000000000000000000000000000000500)))
     in
      drop sigUnpack &&& (take (take pkPoint) &&& nege)
  >>> match false k1
  }
   where
    -- Common code shared between 'mul' and 'sqr'.
    sum19 :: term (X9 Word64, X10 Word64) FE
    sum19 = (oh &&& iih) &&& (drop (take (shift26' &&& mod26')))
        >>> take (oih &&& iih) &&& (((oioh &&& ioh >>> add64) &&& oooh >>> circut) &&& iih)
        >>> take (oih &&& iih) &&& (((oioh &&& iooh >>> add64) &&& (oooh &&& drop oioh >>> add64) >>> circut) &&& (drop oiih &&& iih))
        >>> take (oih &&& iih) &&& (((oioh &&& iooh >>> add64) &&& (oooh &&& drop oioh >>> add64) >>> circut) &&& ((drop oiih &&& iioh) &&& iiih))
        >>> take (oih &&& iih) &&& (((oioh &&& iooh >>> add64) &&& (oooh &&& drop oioh >>> add64) >>> circut) &&& ((drop oiih &&& iioh) &&& iiih))
        >>> take (oih &&& iih) &&& (((oioh &&& iooh >>> add64) &&& (oooh &&& drop oioh >>> add64) >>> circut) &&& ((drop oiih &&& iioh) &&& iiih))
        >>> take (oih &&& iih) &&& (((oioh &&& iooh >>> add64) &&& (oooh &&& drop oioh >>> add64) >>> circut) &&& ((drop oiih &&& iioh) &&& iiih))
        >>> take (oih &&& iih) &&& (((oioh &&& iooh >>> add64) &&& (oooh &&& drop oioh >>> add64) >>> circut) &&& ((drop oiih &&& iioh) &&& iiih))
        >>> take (oih &&& iih) &&& (((oioh &&& iooh >>> add64) &&& (oooh &&& drop oioh >>> add64) >>> circut) &&& ((drop oiih &&& iioh) &&& iiih))
        >>> ((oih &&& iooh >>> add64) &&& (ooh &&& drop oioh >>> add64) >>> circut) &&& ((drop oiih &&& iioh) &&& iiih)
        >>> take (take (shift word64 (-14))) &&& ((((scribe64 0x3D10 &&& ooh >>> mul64) &&& (oioh &&& (zero word32 &&& iih) >>> add64) >>> add64) >>> (shift word64 22 &&& drop mod22)) &&& (oiih &&& ioh))
        >>> (oh &&& iooh >>> add64) &&& (ioih &&& iih)
        >>> ((zero word32 &&& drop (iden `at` 9)) &&& (oh &&& scribe64 0x3D1 >>> mul64) >>> add64) &&& iden
        >>> take mod26' &&& ((take shift26' &&& (drop ((zero word32 &&& drop (iden `at` 8)) &&& (take (shift word64 (-6))) >>> add64)) >>> add64) &&& iih
                        >>> (take mod26' &&& (((take shift26' >>> ih) &&& drop (iden `at` 7) >>> add32) &&& drop rest)))
     where
      shift26' = shift word64 26
      mod26' = drop mod26
      circut = take shift26' &&& (take mod26' &&& ih >>> (oh &&& (ih &&& (scribe32 0x3D10 &&& oh >>> wideMul32) >>> add64)) >>> ((take shiftk1 &&& drop shift26' >>> add64) &&& drop mod26'))
      shiftk1 = (zero word32 &&& iden >>> shift word64 (-10))
      rest = iden `at` 6 &&& iden `at` 5 &&& iden `at` 4 &&& iden `at` 3 &&& iden `at` 2 &&& iden `at` 1 &&& iden `at` 0

    -- Common code shared between 'inv' and 'sqrt'.
    tower = iden &&& (iden &&& sqr >>> mul)
        >>> ih &&& (oh &&& drop sqr >>> mul)
        >>> oh &&& ((ih &&& (oh &&& (drop (iden &&& (iden &&& (sqr >>> sqr >>> sqr) >>> mul >>> sqr >>> sqr >>> sqr) >>> mul) >>> sqr >>> sqr) >>> mul -- (x2,(x3,x11))
                          >>> iden &&& foldr1 (>>>) (replicate 11 sqr) >>> mul))                      -- (x2,(x3,x22))
                 >>> ih &&& (oh &&& drop (iden &&& foldr1 (>>>) (replicate 22 sqr) >>> mul            -- (x2,(x22,(x3,x44)))
                                     >>> (iden &&& (iden &&& foldr1 (>>>) (replicate 44 sqr) >>> mul  -- (x2,(x22,(x3,(x44,x88))))
                                                 >>> iden &&& foldr1 (>>>) (replicate 88 sqr) >>> mul -- (x2,(x22,(x3,(x44,x176))))
                                           >>> foldr1 (>>>) (replicate 44 sqr)) >>> mul)              -- (x2,(x22,(x3,x220)))
                                    >>> sqr >>> sqr >>> sqr) >>> mul                                  -- (x2,(x22,x223))
                           >>> foldr1 (>>>) (replicate 23 sqr)) >>> mul                               -- (x2,t1)
                 >>> foldr1 (>>>) (replicate 5 sqr))

    -- Compute odd-multiples of a point for small (5-bit) multiples.
    -- The result is in Jacobian coordinates but the z-coordinate is identical for all outputs.
    scalarTable5 :: term GEJ (FE, Vector8 GE)
    scalarTable5 = iden &&& double
               >>> iih &&& (((ooh &&& iih >>> scaleZ) &&& oih) &&& ioh) -- (dz, (a', (dx,dy)))
               >>> oh &&& drop pass1
               >>> (oh &&& drop oiih >>> mul) &&& drop (pass2
                   >>> (drop (drop (drop (drop (drop (drop (ih &&& oh)) &&& (ioh &&& oh)))))) &&&
                       ((drop (drop (ioh &&& oh))) &&& (ioh &&& oh)))
     where
      scaleZ = oh &&& (ih &&& (ih >>> sqr) >>> ih &&& mul) >>> (ooh &&& ioh >>> mul) &&& (oih &&& iih >>> mul)
      pass1 = (offsetPoint &&& oh) &&& ih
          >>> ((ooih &&& ih >>> offsetPoint) &&& oh) &&& ih
          >>> ((ooih &&& ih >>> offsetPoint) &&& oh) &&& ih
          >>> ((ooih &&& ih >>> offsetPoint) &&& oh) &&& ih
          >>> ((ooih &&& ih >>> offsetPoint) &&& oh) &&& ih
          >>> ((ooih &&& ih >>> offsetPoint) &&& oh) &&& ih
          >>> (ooih &&& ih >>> offsetPoint) &&& oh
      pass2 = (ooh &&& oioh) &&& ih >>> (oih &&& (((ooh &&& iooh >>> mul) &&& (drop oioh &&& ooh >>> scaleZ)) &&& iih))
          >>> oh &&& drop ((oih &&& (((ooh &&& iooh >>> mul) &&& (drop oioh &&& ooh >>> scaleZ)) &&& iih))
          >>> oh &&& drop ((oih &&& (((ooh &&& iooh >>> mul) &&& (drop oioh &&& ooh >>> scaleZ)) &&& iih))
          >>> oh &&& drop ((oih &&& (((ooh &&& iooh >>> mul) &&& (drop oioh &&& ooh >>> scaleZ)) &&& iih))
          >>> oh &&& drop ((oih &&& (((ooh &&& iooh >>> mul) &&& (drop oioh &&& ooh >>> scaleZ)) &&& iih))
          >>> oh &&& drop ((oih &&& (((ooh &&& iooh >>> mul) &&& (drop oioh &&& ooh >>> scaleZ)) &&& iih))
          >>> oh &&& drop (oih &&& (ioh &&& ooh >>> scaleZ)))))))
    -- Given an odd-multiples table of affinte points, extract the @i@th element of the table.
    -- If the index is negative @i@, then return the point negation of the @i@th element of the table.
    lookupTable5 :: term (Word4, Vector8 GE) GE
    lookupTable5 = oooh &&& ooih &&& oih &&& ih
               >>> cond neg pos
     where
      pos = ioih &&& (iooh &&& (oh &&& iih >>> cond ih oh) >>> cond ih oh) >>> cond ih oh
      neg = ioih &&& (iooh &&& (oh &&& iih >>> cond oh ih) >>> cond oh ih) >>> cond (take geNegate) (drop geNegate)

    -- Returns a small, signed integer multiple of the secp256k1's generator as a normalized affine point.
    generatorSmall :: term Word16 GE
    generatorSmall = signAbs
                 >>> oh &&& drop (wnaf5Short &&& (scribe g >>> scalarTable5) -- TODO directly scribe the scalarTable5 for g.
                              >>> ioh &&& (oh &&& inf &&& iih >>> step16)
                              >>> ioh &&& (oh &&& iih >>> mul)
                              >>> normalizePoint)
                 >>> cond (oh &&& drop (neg 1)) iden
     where
      signAbs = take oooh &&& iden
            >>> cond (true &&& negator) (false &&& iden)
      g = (((toWord32 49813400, (toWord32 10507973, (toWord32 42833311, (toWord32 57456440, (toWord32 50502652
            ,(toWord32 60932801, (toWord32 33958236, (toWord32 49197398, (toWord32 41875932, toWord32 1994649)))))))))
           ,(toWord32 51434680, (toWord32 32777214, (toWord32 21076420, (toWord32 19044885, (toWord32 16586676
            ,(toWord32 58999338, (toWord32 38780864, (toWord32 51484022, (toWord32 41363107, toWord32 1183414))))))))))
          ,(toWord32 1, (toWord32 0, (toWord32 0, (toWord32 0, (toWord32 0, (toWord32 0, (toWord32 0, (toWord32 0, (toWord32 0, toWord32 0))))))))))
      step = match (drop (take double))
                   (drop (take double) &&& (oh &&& iih >>> lookupTable5) >>> offsetPoint >>> ih)
      step2 = ooh &&& (oih &&& ih >>> step) &&& iih >>> step
      step4 = ooh &&& (oih &&& ih >>> step2) &&& iih >>> step2
      step8 = ooh &&& (oih &&& ih >>> step4) &&& iih >>> step4
      step16 = ooh &&& (oih &&& ih >>> step8) &&& iih >>> step8
      negator = zero word16 &&& iden >>> subtractor word16 >>> ih

-- | This function is given a public key, a 256-bit message, and a signature, and asserts that the signature is valid for the given message and public key.
schnorrAssert :: Assert term => Lib term -> term ((XOnlyPubKey, Word256), Sig) ()
schnorrAssert m = assert (schnorrVerify m)

-- | An instance of the Sha256 'Lib' library.
-- This instance does not share its dependencies.
-- Users should prefer to use 'mkLib' in order to share library dependencies.
-- This instance is provided mostly for testing purposes.
lib :: Core term => Lib term
lib = mkLib Sha256.lib
