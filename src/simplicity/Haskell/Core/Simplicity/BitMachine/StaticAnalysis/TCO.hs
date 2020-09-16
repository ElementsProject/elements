-- | This module has functions for computing static analysis of Bit Machine resources used during execution of tail call optimized translated Simplicity expressions.
module Simplicity.BitMachine.StaticAnalysis.TCO
 ( ExtraCellsBnd, cellsBnd
 ) where

import Simplicity.BitMachine.Ty
import Simplicity.Delegator.Impl
import Simplicity.Term.Core

-- | @'ExtraCellsBnd' a b@ is the data type for the Simplicity algebra used for computing the bound on the maximum number of Cells used by the Bit Machine.
data ExtraCellsBnd a b = ExtraCellsBnd Int Int

-- @extraCellBnd r@ is the number of extra cells that will be allocated by the TCOon program when the active read frame as 'r' number of cells.
-- The number of extra cells that will be allocated by TCOoff is (extraCellsBnd 0).
extraCellsBnd r (ExtraCellsBnd n m) = max (n - r) m

cellsBnd0 :: (TyC a, TyC b) => ExtraCellsBnd a b -> Int
cellsBnd0 t = bitSizeR a + bitSizeR b + extraCellsBnd 0 t
 where
  (a,b) = reifyArrow t

-- | @'cellsBnd' t@ computes an upper bound on the maximum number of Cells used by the Bit Machine, including the cells used to hold the input and output, when executing TCO translated Simplicity expressions.
--
-- Simplicity terms are represented in tagless-final style, so any Simplicity term can be instantiated as @'ExtraCellsBnd' a b@ and can be passed to the 'cellsBnd' function.
cellsBnd :: (TyC a, TyC b) => Delegator ExtraCellsBnd a b -> Int
cellsBnd = cellsBnd0 . runDelegator

-- Below is the Simplicity algebra that is used for computing 'cellsBnd'
instance Core ExtraCellsBnd where
  iden = ExtraCellsBnd 0 0
  comp arrS@(ExtraCellsBnd sn sm) (ExtraCellsBnd tn tm) = ExtraCellsBnd (maximum [s + sn, tn, s + tm]) (s + sm)
   where
    s = bitSizeR b
    b = reifyProxy arrS
  unit = ExtraCellsBnd 0 0
  injl (ExtraCellsBnd tn tm) = ExtraCellsBnd tn tm
  injr (ExtraCellsBnd tn tm) = ExtraCellsBnd tn tm
  match (ExtraCellsBnd sn sm) (ExtraCellsBnd tn tm) = ExtraCellsBnd (max sn tn) (max sm tm)
  pair (ExtraCellsBnd sn sm) (ExtraCellsBnd tn tm) = ExtraCellsBnd tn (maximum [sn, sm, tm])
  take (ExtraCellsBnd tn tm) = ExtraCellsBnd tn tm
  drop (ExtraCellsBnd tn tm) = ExtraCellsBnd tn tm

instance Assert ExtraCellsBnd where
  assertl (ExtraCellsBnd sn sm) _ = ExtraCellsBnd sn sm
  assertr _ (ExtraCellsBnd tn tm) = ExtraCellsBnd tn tm
  fail _ = ExtraCellsBnd 0 0

