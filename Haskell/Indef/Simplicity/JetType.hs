{-# LANGUAGE EmptyCase, EmptyDataDecls, EmptyDataDeriving, FlexibleContexts, TypeFamilies #-}
-- | This modules defines the 'JetType' class, and provides the trivial empty instance of this class, 'NoJets'.
module Simplicity.JetType
  ( JetType(..)
  , NoJets(..)
  ) where

import Control.Arrow (runKleisli)
import Control.Monad.Trans.Reader (runReaderT)
import Data.Void (Void, vacuous)

import Simplicity.Primitive
import Simplicity.Serialization
import Simplicity.Tensor
import Simplicity.Term

-- | A 'JetType' is a data structure that represets a set of known jets.
-- Every known jet has a 'specification' which is defined by some Simplicity expression (see 'Jet').
--
-- Each 'JetType' has an associated 'MatcherInfo' type that interprets Simplicity with jet expressions to
-- summerise a set of data needed to determine what jet, if any, a particular expression is.
-- Typically the 'MatcherInfo' consists of a 'Simplicity.MerkleRoot.IdentityRoot' value.
-- The 'matcher' function uses this interpretation to decide which known jet, a given Simplicity expression is, if any.
--
-- The 'implemenation' must match the 'specification' and is designed to be directly implemented using jets.
--
-- 'putJetBit' and 'getJetBit' provide canonical serialization and deserialization methods for the 'JetType'
-- (see "Simplicity.Serialization").
--
-- We require that given an expression @e :: forall term. ('Assert' term, 'Primitive' term) => term a b@,
--
-- if
--
-- @
--     'matcher' e === Just j
-- @
--
-- then
--
-- @
--     'Simplicity.Semantics.sem' ('specification' j) === 'Simplicity.Semantics.sem' e
-- @
--
-- The jetted 'implementation' is required to match the specification.
--
-- @
--     'implementation' j === 'Simplicity.Semantics.sem' ('specification' j)
-- @
--
-- We also require that serialized values can be deserialized:
--
-- @
--     'Simplicity.Serialization.evalStreamWithError' 'getJetBit' l === Right ('SomeArrow' j)
-- @
--
-- if and only if
--
-- @
--     'putJetBit' j === (l ++)
-- @
class (Assert (MatcherInfo jt), Primitive (MatcherInfo jt)) => JetType jt where
  type MatcherInfo jt :: * -> * -> *
  specification :: (TyC a, TyC b, Assert term, Primitive term) => jt a b -> term a b
  implementation :: (TyC a, TyC b) => jt a b -> PrimEnv -> a -> Maybe b
  implementation jt = flip $ runReaderT . runKleisli (specification jt)
  matcher :: (TyC a, TyC b) => MatcherInfo jt a b -> Maybe (jt a b)
  getJetBit :: Monad m => m Void -> m Bool -> m (SomeArrow jt)
  putJetBit :: (TyC a, TyC b) => jt a b -> DList Bool

-- | 'NoJets' is an empty type that is an instance of 'JetType'.
-- It allows one not to match any jets at all.
data NoJets a b deriving (Eq, Show)

instance JetType NoJets where
  type MatcherInfo NoJets = Unit
  specification noJets = case noJets of {}
  matcher _ = Nothing
  getJetBit abort next = vacuous abort
  putJetBit noJets = case noJets of {}
