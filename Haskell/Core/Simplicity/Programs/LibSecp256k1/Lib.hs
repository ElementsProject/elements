{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module unpacks the 'Simplicity.Programs.LibSecp256k1.lib' library instance into individual functions.
-- Users should prefer to use 'Simplicity.Programs.LibSecp256k1.mkLib' in order to share library dependencies.
-- This module is provided mostly for testing purposes.
module Simplicity.Programs.LibSecp256k1.Lib
  (
  -- * Field operations
    LibSecp256k1.FE, fePack, feUnpack, feZero, feOne, feIsZero
  , normalizeWeak, normalize
  , add, neg, mulInt, sqr, mul, inv, sqrt
  , isQuad
  -- * Point operations
  , LibSecp256k1.GE, LibSecp256k1.GEJ, inf, isInf
  , normalizePoint
  , geNegate, double, offsetPoint, offsetPointZinv
  , eqXCoord, hasQuadY
  -- * Elliptic curve multiplication related operations
  , LibSecp256k1.Scalar
  , wnaf5, wnaf16
  , ecMult
  -- * Schnorr signature operations
  , LibSecp256k1.XOnlyPubKey, pkPoint
  , LibSecp256k1.Sig, sigUnpack
  , scalarUnrepr
  , schnorrVerify, schnorrAssert
  -- * Types
  , LibSecp256k1.X10
  ) where

import Prelude hiding (sqrt)

import qualified Simplicity.Programs.LibSecp256k1 as LibSecp256k1

fePack = LibSecp256k1.fePack LibSecp256k1.lib
feUnpack = LibSecp256k1.feUnpack LibSecp256k1.lib
feZero = LibSecp256k1.feZero LibSecp256k1.lib
feOne = LibSecp256k1.feOne LibSecp256k1.lib
feIsZero = LibSecp256k1.feIsZero LibSecp256k1.lib
normalizeWeak = LibSecp256k1.normalizeWeak LibSecp256k1.lib
normalize = LibSecp256k1.normalize LibSecp256k1.lib
add = LibSecp256k1.add LibSecp256k1.lib
neg = LibSecp256k1.neg LibSecp256k1.lib
mulInt = LibSecp256k1.mulInt LibSecp256k1.lib
sqr = LibSecp256k1.sqr LibSecp256k1.lib
mul = LibSecp256k1.mul LibSecp256k1.lib
inv = LibSecp256k1.inv LibSecp256k1.lib
sqrt = LibSecp256k1.sqrt LibSecp256k1.lib
isQuad = LibSecp256k1.isQuad LibSecp256k1.lib
inf = LibSecp256k1.inf LibSecp256k1.lib
isInf = LibSecp256k1.isInf LibSecp256k1.lib
normalizePoint = LibSecp256k1.normalizePoint LibSecp256k1.lib
geNegate = LibSecp256k1.geNegate LibSecp256k1.lib
double = LibSecp256k1.double LibSecp256k1.lib
offsetPoint = LibSecp256k1.offsetPoint LibSecp256k1.lib
offsetPointZinv = LibSecp256k1.offsetPointZinv LibSecp256k1.lib
eqXCoord = LibSecp256k1.eqXCoord LibSecp256k1.lib
hasQuadY = LibSecp256k1.hasQuadY LibSecp256k1.lib
wnaf5 = LibSecp256k1.wnaf5 LibSecp256k1.lib
wnaf16 = LibSecp256k1.wnaf16 LibSecp256k1.lib
ecMult = LibSecp256k1.ecMult LibSecp256k1.lib
pkPoint = LibSecp256k1.pkPoint LibSecp256k1.lib
sigUnpack = LibSecp256k1.sigUnpack LibSecp256k1.lib
scalarUnrepr = LibSecp256k1.scalarUnrepr LibSecp256k1.lib
schnorrVerify = LibSecp256k1.schnorrVerify LibSecp256k1.lib
schnorrAssert = LibSecp256k1.schnorrAssert LibSecp256k1.lib
