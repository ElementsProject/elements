-- | This internal module provides a Deleator instance that perform a semantic conversion of the 'disconnect' combinator.
-- It should only be used for semantic operations, including BitMachine translation and static analysis.
module Simplicity.Delegator.Impl
 ( Delegator(Delegator), runDelegator
 ) where

import Prelude hiding (drop, take, fail)

import Simplicity.Digest
import Simplicity.MerkleRoot
import Simplicity.Programs.Generic
import Simplicity.Term.Core
import Simplicity.Ty.Word

-- Note: 'Delegator' differs from 'Simplicity.Tensor.Product CommitmentRoot' due to a different 'Delegate' instance.
-- | @'Delegator' p@ is a helper data type for creating a 'Delegate' instance.
-- @p@ is typically at least an instance of 'Core'.
data Delegator p a b = Delegator { delegatorRoot :: CommitmentRoot a b
                                 , runDelegator :: p a b -- ^ Extract the @p a b@ arrow from the 'Delegator'
                                 }

instance Core p => Core (Delegator p) where
  iden = Delegator iden iden
  comp ~(Delegator rs fs) ~(Delegator rt ft) = Delegator (comp rs rt) (comp fs ft)
  unit = Delegator unit unit
  injl ~(Delegator rt ft) = Delegator (injl rt) (injl ft)
  injr ~(Delegator rt ft) = Delegator (injr rt) (injr ft)
  match ~(Delegator rs fs) ~(Delegator rt ft) = Delegator (match rs rt) (match fs ft)
  pair ~(Delegator rs fs) ~(Delegator rt ft) = Delegator (pair rs rt) (pair fs ft)
  take ~(Delegator rt ft) = Delegator (take rt) (take ft)
  drop ~(Delegator rt ft) = Delegator (drop rt) (drop ft)

instance Assert p => Assert (Delegator p) where
  assertl ~(Delegator rs fs) t = Delegator (assertl rs t) (assertl fs t)
  assertr s ~(Delegator rt ft) = Delegator (assertr s rt) (assertr s ft)
  fail b = Delegator (fail b) (fail b)

instance Witness p => Witness (Delegator p) where
  witness b = Delegator (witness b) (witness b)

instance Core p => Delegate (Delegator p) where
  disconnect ~(Delegator rs fs) ~(Delegator rt ft) = Delegator (disconnect rs rt) f
   where
    root256 = toWord256 . integerHash256 $ commitmentRoot rt
    f = scribe root256 &&& iden >>> fs >>> take iden &&& drop ft
