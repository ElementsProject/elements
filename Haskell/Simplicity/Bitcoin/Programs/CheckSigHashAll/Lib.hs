{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module unpacks the 'Simplicity.Bitcoin.Programs.CheckSigHashAll.lib' library instances into individual functions.
-- Users should prefer to use 'Simplicity.Bitcoin.Programs.CheckSigHashAll.mkLib' in order to share library dependencies.
-- This module is provided mostly for testing purposes.
module Simplicity.Bitcoin.Programs.CheckSigHashAll.Lib
  (
  -- * Operations
    sigAllCMR
  , sigHashAll
  , checkSigHashAll
  , wCheckSigHashAll
  , pkwCheckSigHashAll
  -- * Types
  , CheckSigHashAll.Hash, CheckSigHashAll.XOnlyPubKey, CheckSigHashAll.Sig
  ) where

import Simplicity.Tensor
import qualified Simplicity.Bitcoin.Programs.CheckSigHashAll as CheckSigHashAll

sigAllCMR = CheckSigHashAll.sigAllCMR (CheckSigHashAll.lib :: CheckSigHashAll.Lib Unit)
sigHashAll = CheckSigHashAll.sigHashAll CheckSigHashAll.lib
checkSigHashAll = CheckSigHashAll.checkSigHashAll CheckSigHashAll.lib
wCheckSigHashAll = CheckSigHashAll.wCheckSigHashAll CheckSigHashAll.lib
pkwCheckSigHashAll = CheckSigHashAll.pkwCheckSigHashAll CheckSigHashAll.lib
