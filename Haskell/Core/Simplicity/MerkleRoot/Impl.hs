-- | This module provides functions for computing commitment, identity and annotated Merkle roots of Simplicity expressions and Merkle roots of Simplicity types.
-- It also provides some other functions for other hashing schemes that will avoid collisions with the aforementioned Merkle roots.
--
-- This module is internal only.  "Simplicity.MerkleRoot" is the public facing module.
module Simplicity.MerkleRoot.Impl
  ( typeRoot, typeRootR
  , CommitmentRoot, commitmentRoot
  , IdentityRoot, identityRoot
  , AnnotatedRoot, annotatedRoot
  , hiddenRoot
  , signatureTag, sigHashTag
  , cmrFail0
  -- * Internal functions
  -- | These functions are use internally to define commitment, identity, and annotated Merkle root instances for
  -- Primitives and expressions that depend on Primitives.
  , primitiveCommitmentImpl, jetCommitmentImpl
  , primitiveIdentityImpl, jetIdentityImpl
  , primitiveAnnotatedImpl, jetAnnotatedImpl
  ) where

import Data.List (intercalate)
import Data.Proxy (Proxy(..))

import Simplicity.Digest
import Simplicity.Term.Core
import Simplicity.Ty.Word

tag :: [String] -> IV
tag = tagIv . intercalate "\US"

prefix = ["Simplicity-Draft"]
typePrefix = prefix ++ ["Type"]
commitmentPrefix = prefix ++ ["Commitment"]
identityPrefix = prefix ++ ["Identity"]
annotatedPrefix = prefix ++ ["Annotated"]
primitivePrefix primPrefix = prefix ++ ["Primitive", primPrefix]

typeTag :: String -> IV
typeTag x = tag $ typePrefix ++ [x]

commitmentTag :: String -> IV
commitmentTag x = tag $ commitmentPrefix ++ [x]

identityRootTag :: IV
identityRootTag = tag identityPrefix

identityTag :: String -> IV
identityTag x = tag $ identityPrefix ++ [x]

annotatedTag :: String -> IV
annotatedTag x = tag $ annotatedPrefix ++ [x]

primTag :: String -> String -> IV
primTag primPrefix x = tag $ primitivePrefix primPrefix ++ [x]

jetTag :: IV
jetTag = tag $ prefix ++ ["Jet"]

hiddenTag :: IV
hiddenTag = tag $ prefix ++ ["Hidden"]

signatureTag :: IV
signatureTag = tag $ prefix ++ ["Signature"]

sigHashTag :: IV
sigHashTag = tag $ prefix ++ ["SigHash"]

-- | This function hashes a hash such that it will not collide with any 'typeRoot' or 'identityRoot'.
--
-- It is designed to be used as if it were a "identity root" for hidden nodes.
hiddenRoot :: Hash256 -> Hash256
hiddenRoot = ivHash . compressHalf hiddenTag

-- | Computes a hash committing to a Simplicity type.
-- This function is memoized.
typeRoot :: Ty -> Hash256
typeRoot = memoCataTy typeRootF
 where
  typeRootF :: TyF Hash256 -> Hash256
  typeRootF One        = ivHash $ typeTag "unit"
  typeRootF (Sum a b)  = ivHash $ compress (typeTag "sum") (a, b)
  typeRootF (Prod a b) = ivHash $ compress (typeTag "prod") (a, b)

-- | A variant of 'typeRoot' for @'TyReflect' a@ values.
--
-- @
-- typeRootR = typeRoot . unreflect
-- @
typeRootR :: TyReflect a -> Hash256
typeRootR = typeRoot . unreflect

newtype CommitmentRoot a b = CommitmentRoot {
 -- | A digest of a Simplicity expression that excludes 'witness' values and the 'disconnect'ed expressions.
 -- It also exclude typing information (with the exception of jets).
    commitmentRoot :: Hash256
  } deriving (Eq, Show)

commit = CommitmentRoot . ivHash

-- | The commitment root of a @'fail' 'hash0' 'hash0'@ expression.
--
-- This hash value can be used as a default value for assertions, but at the cost of not hidding the fact that it isn't a pruned alternative branch.
cmrFail0 :: Hash256
cmrFail0 = commitmentRoot (fail0 :: CommitmentRoot () ())

instance Core CommitmentRoot where
  iden                                        = commit $ commitmentTag "iden"
  comp (CommitmentRoot s) (CommitmentRoot t)  = commit $ compress (commitmentTag "comp") (s, t)
  unit                                        = commit $ commitmentTag "unit"
  injl (CommitmentRoot t)                     = commit $ compressHalf (commitmentTag "injl") t
  injr (CommitmentRoot t)                     = commit $ compressHalf (commitmentTag "injr") t
  match (CommitmentRoot s) (CommitmentRoot t) = commit $ compress (commitmentTag "case") (s, t)
  pair (CommitmentRoot s) (CommitmentRoot t)  = commit $ compress (commitmentTag "pair") (s, t)
  take (CommitmentRoot t)                     = commit $ compressHalf (commitmentTag "take") t
  drop (CommitmentRoot t)                     = commit $ compressHalf (commitmentTag "drop") t

instance Assert CommitmentRoot where
  assertl (CommitmentRoot s) t = commit $ compress (commitmentTag "case") (s, t)
  assertr s (CommitmentRoot t) = commit $ compress (commitmentTag "case") (s, t)
  fail b = commit $ compress (commitmentTag "fail") b

instance Witness CommitmentRoot where
  witness _ = commit $ commitmentTag "witness"

instance Delegate CommitmentRoot where
  disconnect (CommitmentRoot s) _ = commit $ compressHalf (commitmentTag "disconnect") s

newtype IdentityRoot a b = IdentityRoot Hash256

-- | A digest of a Simplicity expression that includes 'witness' values and 'disconnect'ed expressions.
-- This also includes the hash of the input and output types.
identityRoot :: (TyC a, TyC b) => IdentityRoot a b -> Hash256
identityRoot ir@(IdentityRoot t) = ivHash $ compress (compressHalf identityRootTag t) (typeRootR ra, typeRootR rb)
 where
  (ra, rb) = reifyArrow ir

identify = IdentityRoot . ivHash

instance Core IdentityRoot where
  iden                                    = identify $ commitmentTag "iden"
  comp (IdentityRoot s) (IdentityRoot t)  = identify $ compress (commitmentTag "comp") (s, t)
  unit                                    = identify $ commitmentTag "unit"
  injl (IdentityRoot t)                   = identify $ compressHalf (commitmentTag "injl") t
  injr (IdentityRoot t)                   = identify $ compressHalf (commitmentTag "injr") t
  match (IdentityRoot s) (IdentityRoot t) = identify $ compress (commitmentTag "case") (s, t)
  pair (IdentityRoot s) (IdentityRoot t)  = identify $ compress (commitmentTag "pair") (s, t)
  take (IdentityRoot t)                   = identify $ compressHalf (commitmentTag "take") t
  drop (IdentityRoot t)                   = identify $ compressHalf (commitmentTag "drop") t

instance Assert IdentityRoot where
  assertl (IdentityRoot s) t = identify $ compress (commitmentTag "case") (s, t)
  assertr s (IdentityRoot t) = identify $ compress (commitmentTag "case") (s, t)
  fail b = identify $ compress (commitmentTag "fail") b

instance Witness IdentityRoot where
  witness v = result
   where
    result = identify $ compress (identityTag "witness") (bitStringHash (putValue v), typeRootR rb)
    rb = reifyProxy result

instance Delegate IdentityRoot where
  disconnect (IdentityRoot s) (IdentityRoot t) = identify $ compress (identityTag "disconnect") (s, t)

newtype AnnotatedRoot a b = AnnotatedRoot {
 -- | A digest of a Simplicity expression that also includes all typing annotations.
    annotatedRoot :: Hash256
  } deriving (Eq, Show)

observe = AnnotatedRoot . ivHash

instance Core AnnotatedRoot where
  iden = result
   where
    result = observe $ compressHalf (annotatedTag "iden") (typeRootR (reifyProxy result))

  comp ws@(AnnotatedRoot s) wt@(AnnotatedRoot t) = result
   where
    result = observe $ compress (compress (compressHalf (annotatedTag "comp") (typeRootR (reifyProxy proxyA)))
                                          (typeRootR (reifyProxy proxyB), (typeRootR (reifyProxy proxyC))))
                                (s, t)
    proxy :: proxy a b -> proxy b c -> (Proxy a, Proxy b, Proxy c)
    proxy _ _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy ws wt

  unit = result
   where
    result = observe $ compressHalf (annotatedTag "unit") (typeRootR (fst (reifyArrow result)))

  injl (AnnotatedRoot t) = result
   where
    result = observe $ compress (compress (annotatedTag "injl") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                (typeRootR (reifyProxy proxyC), t)
    proxy :: proxy a (Either b c) -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

  injr (AnnotatedRoot t) = result
   where
    result = observe $ compress (compress (annotatedTag "injr") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                (typeRootR (reifyProxy proxyC), t)
    proxy :: proxy a (Either b c) -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

  match (AnnotatedRoot s) (AnnotatedRoot t) = result
   where
    result = observe $ compress (compress (compress (annotatedTag "case") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                          (typeRootR (reifyProxy proxyC), typeRootR (reifyProxy proxyD)))
                                (s, t)
    proxy :: proxy ((Either a b), c) d -> (Proxy a, Proxy b, Proxy c, Proxy d)
    proxy _ = (Proxy, Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC, proxyD) = proxy result

  pair (AnnotatedRoot s) (AnnotatedRoot t) = result
   where
    result = observe $ compress (compress (compressHalf (annotatedTag "pair") (typeRootR (reifyProxy proxyA)))
                                          (typeRootR (reifyProxy proxyB), (typeRootR (reifyProxy proxyC))))
                                (s, t)
    proxy :: proxy a (b,c) -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result
  take (AnnotatedRoot t) = result
   where
    result = observe $ compress (compress (annotatedTag "take") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                (typeRootR (reifyProxy proxyC), t)
    proxy :: proxy (a,b) c -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

  drop (AnnotatedRoot t) = result
   where
    result = observe $ compress (compress (annotatedTag "drop") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                (typeRootR (reifyProxy proxyC), t)
    proxy :: proxy (a,b) c -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

instance Assert AnnotatedRoot where
  assertl (AnnotatedRoot s) t = result
   where
    result = observe $ compress (compress (compress (annotatedTag "assertl") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                          (typeRootR (reifyProxy proxyC), typeRootR (reifyProxy proxyD)))
                                (s, t)
    proxy :: proxy ((Either a b), c) d -> (Proxy a, Proxy b, Proxy c, Proxy d)
    proxy _ = (Proxy, Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC, proxyD) = proxy result

  assertr s (AnnotatedRoot t) = result
   where
    result = observe $ compress (compress (compress (annotatedTag "assertr") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                          (typeRootR (reifyProxy proxyC), typeRootR (reifyProxy proxyD)))
                                (s, t)
    proxy :: proxy ((Either a b), c) d -> (Proxy a, Proxy b, Proxy c, Proxy d)
    proxy _ = (Proxy, Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC, proxyD) = proxy result
  -- This should never be called in practice, but we add it for completeness.
  fail b = observe $ compress (annotatedTag "fail") b

instance Witness AnnotatedRoot where
  witness v = result
   where
    result = observe $ compress (compressHalf (annotatedTag "witness") (typeRootR ra)) (typeRootR rb, bitStringHash (putValue v))
    (ra, rb) = reifyArrow result

instance Delegate AnnotatedRoot where
  disconnect ws@(AnnotatedRoot s) wt@(AnnotatedRoot t) = result
   where
    result = observe $ compress (compress (compress (annotatedTag "disconnect") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                          (typeRootR (reifyProxy proxyC), typeRootR (reifyProxy proxyD)))
                                (s, t)
    proxy :: proxy (w, a) (b, c) -> proxy c d -> (Proxy a, Proxy b, Proxy c, Proxy d)
    proxy _ _ = (Proxy, Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC, proxyD) = proxy ws wt

primitiveCommitmentImpl primPrefix primName = commit . primTag primPrefix . primName

-- Jets commit to their types, so we use 'identityRoot' here.
jetCommitmentImpl ir = commit $ compressHalf jetTag (identityRoot ir)

primitiveIdentityImpl primPrefix primName = identify . primTag primPrefix . primName

jetIdentityImpl ir = identify $ compressHalf jetTag (identityRoot ir)

primitiveAnnotatedImpl primPrefix primName = observe . primTag primPrefix . primName

jetAnnotatedImpl ir = observe $ compressHalf jetTag (identityRoot ir)
