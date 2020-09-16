-- | This module provides the functional semantics of Simplicity with 'Delegate'.
module Simplicity.Delegator
 ( Delegator, runDelegatorCore, runDelegatorKleisli
 ) where

import Control.Arrow (Kleisli, runKleisli)
import Simplicity.Delegator.Impl

-- | @
-- runDelegatorCore :: (forall term. (Core term, Delegate term, Witness term) => term a b) -> a -> b
-- @
--
-- Returns the semantics of a Simplicity expression with 'Delegate'.
runDelegatorCore :: Delegator (->) a b -> a -> b
runDelegatorCore = runDelegator

-- | @
-- runDelegatorKleisli :: Fail.MonadFail m => (forall term. (Assert term, Delegate term, Witness term) => term a b) -> a -> m b
-- runDelegatorKleisli :: Monad m => (forall term. (Core term, Delegate term, Witness term) => term a b) -> a -> m b
-- @
--
-- Returns the semantics of a Simplicity expression with 'Delegate' and 'Assert'.
runDelegatorKleisli :: Delegator (Kleisli m) a b -> a -> m b
runDelegatorKleisli = runKleisli . runDelegator
