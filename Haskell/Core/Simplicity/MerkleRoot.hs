-- | This module provides functions for computing commitment, identity and annotated Merkle roots of Simplicity expressions and Merkle roots of Simplicity types.
-- It also provides some other functions for other hashing schemes that will avoid collisions with the aforementioned Merkle roots.
module Simplicity.MerkleRoot
  ( typeRoot, typeRootR
  , CommitmentRoot, commitmentRoot
  , IdentityRoot, identityRoot
  , AnnotatedRoot, annotatedRoot
  , hiddenRoot
  , signatureTag, sigHashTag
  , cmrFail0
  ) where

import Simplicity.MerkleRoot.Impl
