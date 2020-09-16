-- | This module has functions for computing static analysis of Bit Machine resources used during execution of naive translated Simplicity expressions.
module Simplicity.BitMachine.StaticAnalysis
 ( ExtraCellsBnd, cellsBnd
 ) where

import Simplicity.BitMachine.Ty
import Simplicity.Delegator.Impl
import Simplicity.Term.Core

-- | @'ExtraCellsBnd' a b@ is the data type for the Simplicity algebra used for computing the bound on the maximum number of Cells used by the Bit Machine.
newtype ExtraCellsBnd a b = ExtraCellsBnd { extraCellsBnd :: Int }

cellsBnd0 :: (TyC a, TyC b) => ExtraCellsBnd a b -> Int
cellsBnd0 t = bitSizeR a + bitSizeR b + extraCellsBnd t
 where
  (a,b) = reifyArrow t

-- | @'cellsBnd' t@ computes an upper bound on the maximum number of Cells used by the Bit Machine, including the cells used to hold the input and output,  when executing naive translated Simplicity expressions.
--
-- Simplicity terms are represented in tagless-final style, so any Simplicity term can be instantiated as @'ExtraCellsBnd' a b@ and can be passed to the 'cellsBnd' function.
cellsBnd :: (TyC a, TyC b) => Delegator ExtraCellsBnd a b -> Int
cellsBnd = cellsBnd0 . runDelegator

-- Below is the Simplicity algebra that is used for computing 'cellsBnd'
instance Core ExtraCellsBnd where
  iden = ExtraCellsBnd 0
  comp arrS@(ExtraCellsBnd s) (ExtraCellsBnd t) = ExtraCellsBnd (bitSizeR b + max s t)
   where
    b = reifyProxy arrS
  unit = ExtraCellsBnd 0
  injl (ExtraCellsBnd t) = ExtraCellsBnd t
  injr (ExtraCellsBnd t) = ExtraCellsBnd t
  match (ExtraCellsBnd s) (ExtraCellsBnd t) = ExtraCellsBnd (max s t)
  pair (ExtraCellsBnd s) (ExtraCellsBnd t) = ExtraCellsBnd (max s t)
  take (ExtraCellsBnd t) = ExtraCellsBnd t
  drop (ExtraCellsBnd t) = ExtraCellsBnd t

instance Assert ExtraCellsBnd where
  assertl (ExtraCellsBnd s) _ = ExtraCellsBnd s
  assertr _ (ExtraCellsBnd t) = ExtraCellsBnd t
  fail _ = ExtraCellsBnd 0
