{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module unpacks the 'Simplicity.Programs.Sha256.lib' library instance into individual functions.
-- Users should prefer to use 'Simplicity.Programs.Sha256.lib' in order to share library dependencies.
-- This module is provided mostly for testing purposes.
module Simplicity.Programs.Sha256.Lib
 (
 -- * Operations
   Sha256.Block, Sha256.Hash
 , iv, hashBlock
 ) where

import qualified Simplicity.Programs.Sha256 as Sha256

iv = Sha256.iv Sha256.lib
hashBlock = Sha256.hashBlock Sha256.lib
