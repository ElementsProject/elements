{-# LANGUAGE GADTs #-}
-- | This module is a collection of Simplicity expressions that are generic over a collection of Simplicity types.
-- 'TyReflect'ion is used to analyse the Simplicity type of arguments and generate different Simplicity expressions based on the required types.
module Simplicity.Programs.Generic
  ( scribe
  , eq
  ) where

import Prelude hiding (drop, take)

import Simplicity.Programs.Bit
import Simplicity.Term.Core

-- | For any Simplicity value, a Simplicity expression for a constant function returning that value.
--
-- @'scribe' v _ = v@
scribe :: (Core term, TyC a, TyC b) => b -> term a b
scribe = go reify
 where
  go :: (Core term, TyC a, TyC b) => TyReflect b -> b -> term a b
  go OneR          ()        = unit
  go (SumR l _)    (Left v)  = injl (go l v)
  go (SumR _ r)    (Right v) = injr (go r v)
  go (ProdR b1 b2) (v1, v2)  = pair (go b1 v1) (go b2 v2)

-- | Simplicity expression to compare a pair of inputs for equality.
eq :: (Core term, TyC a) => term (a, a) Bit
eq = go reify
 where
  go :: (TyC a, Core term) => TyReflect a -> term (a, a) Bit
  go OneR          = true
  go (SumR l r)    = match (swapP >>> match (go l) false)
                           (swapP >>> match false (go r))
  go (ProdR a1 a2) = pair (pair (take (take iden)) (drop (take iden)) >>> (go a1))
                          (pair (take (drop iden)) (drop (drop iden)))
                     >>> cond (go a2) false
