-- | This module provides a cannonical set of known jets for Simplicity for Elements. (At the moment this just consists of 'CoreJet's.)
{-# LANGUAGE GADTs, StandaloneDeriving, TypeFamilies #-}
module Simplicity.Elements.Jets
  ( JetType
  , getTermStopCode, putTermStopCode
  , getTermLengthCode, putTermLengthCode
  ) where

import Prelude hiding (fail, drop, take)

import qualified Data.Map as Map
import Data.Proxy (Proxy(Proxy))
import Data.Type.Equality ((:~:)(Refl))
import Data.Void (Void, vacuous)

import Simplicity.Digest
import Simplicity.CoreJets (CoreJet, coreJetMap)
import qualified Simplicity.CoreJets as CoreJets
import Simplicity.Elements.Dag
import Simplicity.Elements.Term
import qualified Simplicity.Elements.JetType
import qualified Simplicity.Elements.Serialization.BitString as BitString
import Simplicity.MerkleRoot
import Simplicity.Ty

-- | A type of tokens for the cannonical set of known jets for Simplicity for Elements. (At the moment this just consists of 'CoreJet's.)
--
-- The tokens themselves are not exported.  You are expected to use 'Simplicity.Dag.jetDag' to substitute known jets found in Simplicity expressions.
data JetType a b where
  CoreJet :: CoreJet a b -> JetType a b

deriving instance Eq (JetType a b)
deriving instance Show (JetType a b)

data MatcherInfo a b = MatcherInfo (WitnessRoot a b)

instance Simplicity.Elements.JetType.JetType JetType where
  type MatcherInfo JetType = MatcherInfo

  specification (CoreJet jt) = CoreJets.specification jt

  matcher (MatcherInfo wr) = do
    SomeArrow jt <- Map.lookup (witnessRoot wr) jetMap
    let (wra, wrb) = reifyArrow wr
    let (jta, jtb) = reifyArrow jt
    -- If the error below is thrown it suggests there is some sort of type annotation mismatch in the map below
    case (equalTyReflect wra jta, equalTyReflect wrb jtb) of
      (Just Refl, Just Refl) -> return jt
      otherwise -> error "mathcher{Simplicity.Elements.Jets.JetType}: type match error"

  getJetBit abort next = someArrowMap CoreJet <$> CoreJets.getJetBit abort next

  putJetBit (CoreJet jt) = CoreJets.putJetBit jt

-- This map is used in the 'matcher' method above.
-- We have floated it out here to make sure the map is shared between invokations of the 'matcher' function.
jetMap :: Map.Map Hash256 (SomeArrow JetType)
jetMap = someArrowMap CoreJet <$> coreJetMap

-- | This is an instance of 'BitString.getTermStopCode' that specifically decodes the canonical 'JetType' set of known jets.
getTermStopCode :: (Monad m, Simplicity term, TyC a, TyC b) => m Void -> m Bool -> m (term a b)
getTermStopCode = BitString.getTermStopCode (Proxy :: Proxy (SomeArrow JetType))

-- | This is an instance of 'BitString.getTermLengthCode' that specifically decodes the canonical 'JetType' set of known jets.
getTermLengthCode :: (Monad m, Simplicity term, TyC a, TyC b) => m Void -> m Bool -> m (term a b)
getTermLengthCode = BitString.getTermLengthCode (Proxy :: Proxy (SomeArrow JetType))

-- | This is an instance of 'BitString.putTermStopCode' that specifically encodes the canonical 'JetType' set of known jets.
putTermStopCode :: (TyC a, TyC b) => JetDag JetType a b -> [Bool]
putTermStopCode = BitString.putTermStopCode

-- | This is an instance of 'BitString.putTermLengthCode' that specifically encodes the canonical 'JetType' set of known jets.
putTermLengthCode :: (TyC a, TyC b) => JetDag JetType a b -> [Bool]
putTermLengthCode = BitString.putTermLengthCode

instance Core MatcherInfo where
  iden = MatcherInfo iden
  unit = MatcherInfo unit
  injl (MatcherInfo wmr) = MatcherInfo (injl wmr)
  injr (MatcherInfo wmr) = MatcherInfo (injr wmr)
  drop (MatcherInfo wmr) = MatcherInfo (drop wmr)
  take (MatcherInfo wmr) = MatcherInfo (take wmr)
  pair (MatcherInfo wmrl) (MatcherInfo wmrr) = MatcherInfo (pair wmrl wmrr)
  match (MatcherInfo wmrl) (MatcherInfo wmrr) = MatcherInfo (match wmrl wmrr)
  comp (MatcherInfo wmrl) (MatcherInfo wmrr) = MatcherInfo (comp wmrl wmrr)

instance Assert MatcherInfo where
  assertl (MatcherInfo wmr) h = MatcherInfo (assertl wmr h)
  assertr h (MatcherInfo wmr) = MatcherInfo (assertr h wmr)
  fail b = MatcherInfo (fail b)

instance Primitive MatcherInfo where
  primitive p = MatcherInfo (primitive p)

instance Jet MatcherInfo where
  -- Please notice we WitnessRoot of the jet's specification rather that the witness root rather than of (jet j)!
  -- This lets match subexpressions that contain marked jets as if they didn't have marked jets.
  jet j = j
