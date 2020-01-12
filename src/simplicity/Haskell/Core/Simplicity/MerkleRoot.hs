-- | This module provides functions for computing commitment Merkle roots and witness Merkle roots of Simplicity expressions and Merkle roots of Simplicity types.
-- It also provides some other functions for other hashing schemes that will avoid collisions with the aforementioned Merkle roots.
module Simplicity.MerkleRoot
  ( typeRoot, typeRootR
  , CommitmentRoot, commitmentRoot
  , WitnessRoot, witnessRoot
  , hiddenRoot
  , signatureIv
  , cmrFail0
  ) where

import Simplicity.MerkleRoot.Impl
