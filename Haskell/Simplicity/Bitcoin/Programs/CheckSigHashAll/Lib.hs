{-# LANGUAGE ScopedTypeVariables, NoMonomorphismRestriction #-}
-- | This module unpacks the 'Simplicity.Bitcoin.Programs.CheckSigHashAll.lib' library instances into individual functions.
-- Users should prefer to use 'Simplicity.Bitcoin.Programs.CheckSigHashAll.mkLib' in order to share library dependencies.
-- This module is provided mostly for testing purposes.
module Simplicity.Bitcoin.Programs.CheckSigHashAll.Lib
  (
  -- * Operations
    hashAll
  , sigHashAll
  , checkSigHashAll
  -- * Types
  , CheckSigHashAll.Hash
  ) where

import qualified Simplicity.Bitcoin.Programs.CheckSigHashAll as CheckSigHashAll
import Simplicity.Bitcoin.Term
import Simplicity.Functor
import Simplicity.MerkleRoot
import qualified Simplicity.LibSecp256k1.Schnorr as Schnorr
import qualified Simplicity.Programs.Sha256 as Sha256
import qualified Simplicity.Programs.LibSecp256k1 as LibSecp256k1
import Simplicity.Tensor

hashAll = CheckSigHashAll.hashAll CheckSigHashAll.lib
sigHashAll = CheckSigHashAll.sigHashAll CheckSigHashAll.lib

checkSigHashAll :: forall term. (Assert term, Primitive term, Witness term) => Schnorr.PubKey -> Schnorr.Sig -> term () ()
checkSigHashAll = CheckSigHashAll.checkSigHashAll libSecp256k1 (CheckSigHashAll.mkLib libSha256P)
  where
  libSha256P :: Sha256.Lib (Product CommitmentRoot term)
  libSha256P = Sha256.lib
  libSha256 = sndProduct `sfmap` libSha256P
  libSecp256k1 = LibSecp256k1.mkLib libSha256
