-- | This module is a stub for supporting looping behaviour in Simplicity via self-delegation.
--
module Simplicity.Programs.Loop
  ( loop
  ) where

import Prelude hiding (take)

import Simplicity.Digest
import Simplicity.MerkleRoot
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Term.Core
import Simplicity.Tensor
import Simplicity.Ty.Word

-- While loopBody is recursive, generating an infinite term, we anticipate a pruner will evaluate the term as far as needed to replace the 'match' with an 'assertr'.
-- Thanks to Haskell's laziness, this is feasable.
loopBody :: (Assert term, Delegate term, TyC a, TyC b) => term a (Either a b) -> term (a, Word256) b
loopBody t = take t &&& ih
         >>> match (disconnect (assert (oih &&& ih >>> eq) &&& oh) (loopBody t) >>> ih) oh

-- | Builds an unbounded loop via a self-delegation construction.
loop :: (Assert term, Delegate term, TyC a, TyC b) => Product CommitmentRoot term a (Either a b) -> Product CommitmentRoot term a b
loop t = iden &&& scribe cmr >>> lb
 where
  lb = loopBody t
  cmr = toWord256 . integerHash256 . commitmentRoot . fstProduct $ lb
