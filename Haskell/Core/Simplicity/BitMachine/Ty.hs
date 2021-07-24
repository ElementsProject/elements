-- | This module has some functions operating on Simplicity types that are used for evaluating Simplicity on the Bit Machine.
module Simplicity.BitMachine.Ty
 ( bitSize, padL, padR
 , padLR, padRR, bitSizeR
 ) where

import Data.Functor.Fixedpoint (cata)

import Simplicity.Ty

-- | Compute the number of cells needed to represent values of a Simplicity type.
bitSize :: Ty -> Int
bitSize = cata bitSizeF
 where
  bitSizeF One = 0
  bitSizeF (Sum a b) = 1 + max a b
  bitSizeF (Prod a b) = a + b

-- | Compute the number of cells needed to represent values of a Simplicity type.
--
-- @'bitsizeR' a = 'bitSize' ('unreflect' a)@
bitSizeR :: TyReflect a -> Int
bitSizeR = bitSize . unreflect

-- | @'padL' a b@ is the number of cells of padding used for σ^L tagged values of the Simplicity type @'sum' a b@.
padL :: Ty -> Ty -> Int
padL a b = max bsa bsb - bsa
 where
  bsa = bitSize a
  bsb = bitSize b

-- | @'padLR' a b@ is the number of cells of padding used for σ^L tagged values of the Simplicity type @'SumR' a b@.
--
-- @'padLR' a = 'padL' ('unreflect' a)@
padLR :: TyReflect a -> TyReflect b -> Int
padLR a b = padL (unreflect a) (unreflect b)

-- | @'padR' a b@ is the number of cells of padding used for σ^R tagged values of the Simplicity type @'sum' a b@.
padR :: Ty -> Ty -> Int
padR a b = max bsa bsb - bsb
 where
  bsa = bitSize a
  bsb = bitSize b

-- | @'padRR' a b@ is the number of cells of padding used for σ^R tagged values of the Simplicity type @'SumR' a b@.
--
-- @'padRR' a = 'padR' ('unreflect' a)@
padRR :: TyReflect a -> TyReflect b -> Int
padRR a b = padR (unreflect a) (unreflect b)
