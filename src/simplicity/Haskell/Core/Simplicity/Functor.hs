{-# LANGUAGE RankNTypes #-}
-- | This module provides a product for computing multiple interpretations of Simplicity simutaneously.
-- Other tensors can be added when they are needed.
module Simplicity.Functor
  ( SimplicityFunctor(..)
  ) where

import Simplicity.Ty

class SimplicityFunctor h where
  sfmap :: (forall a b. (TyC a, TyC b) => f a b -> g a b) -> h f -> h g
