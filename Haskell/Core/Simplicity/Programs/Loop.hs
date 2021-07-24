{-# LANGUAGE ScopedTypeVariables #-}
-- | This module is a stub for supporting looping behaviour in Simplicity via self-delegation.
--
module Simplicity.Programs.Loop
  ( loop, loopDepth
  ) where

import Prelude hiding (take)

import Simplicity.Digest
import Simplicity.MerkleRoot
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Term.Core
import Simplicity.Tensor
import Simplicity.Ty.Word

loopTail :: (Assert term, Delegate term, TyC a, TyC b) => term (a, Word256) b -> term (a, Word256) b
loopTail k = disconnect (assert (iih &&& oh >>> eq) &&& ih) k >>> ih

loopBody :: (Assert term, Delegate term, TyC a, TyC b) => term a (Either a b) -> term (a, Word256) b -> term (a, Word256) b
loopBody t k = take t &&& ih >>> match (loopTail k) oh

loopEnd :: forall term a b. (Assert term, TyC a, TyC b) => term a (Either a b) -> term (a, Word256) b
loopEnd t = take t &&& ih >>> assertr (commitmentRoot cmrTail) oh
 where
  cmrTail :: CommitmentRoot (a, Word256) b
  cmrTail = loopTail undefined

-- | Builds an unbounded loop via a self-delegation construction.
-- While loopBody is recursive, generating an infinite term, we anticipate a pruner will evaluate the term as far as needed to replace the 'match' with an 'assertr'.
-- Thanks to Haskell's laziness, this is feasable.
loop :: (Assert term, Delegate term, TyC a, TyC b) => Product CommitmentRoot term a (Either a b) -> term a b
loop t = sndProduct $ iden &&& scribe cmr >>> lb
 where
  cmr = toWord256 . integerHash256 . commitmentRoot . fstProduct $ lb
  lb = loopBody t lb

-- | Builds an loop via a self-delegation construction upto a given maximum depth.
-- At the @n@th iteration, an assertion is uses.
-- This is variant of 'loop' that has been pre-pruned at the given depth.
-- Both @'loop' t@ and @'loopDepth' n t@ share the same 'commitmentRoot'.
loopDepth n t | 1 <= n = sndProduct $ iden &&& scribe cmr >>> lb
 where
  cmr = toWord256 . integerHash256 . commitmentRoot . fstProduct $ lb
  lb = loopBodyDepth n
  loopBodyDepth 1 = loopEnd t
  loopBodyDepth n = loopBody t (loopBodyDepth (n-1))
