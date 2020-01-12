-- | This module provides functions for computing commitment Merkle roots and witness Merkle roots of Simplicity expressions and Merkle roots of Simplicity types.
-- It also provides some other functions for other hashing schemes that will avoid collisions with the aforementioned Merkle roots.
--
-- This module is internal only.  "Simplicity.MerkleRoot" is the public facing module.
module Simplicity.MerkleRoot.Impl
  ( typeRoot, typeRootR
  , CommitmentRoot, commitmentRoot
  , WitnessRoot, witnessRoot
  , hiddenRoot
  , signatureIv
  , cmrFail0
  -- * Internal functions
  -- | These functions are use internally to define commitment and witness Merkle root instances for
  -- Primitives and expressions that depend on Primitives.
  , primitiveCommitmentImpl
  , jetCommitmentImpl
  , primitiveWitnessImpl
  , jetWitnessImpl
  ) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import qualified Data.ByteString.Lazy.Char8 as BSC
import Data.List (intercalate)
import Data.Serialize (encode)
import Data.Proxy (Proxy(..))

import Simplicity.Digest
import Simplicity.Term.Core
import Simplicity.Ty.Word

tag :: [String] -> IV
tag ws | length str < 56 = bsIv . BSC.pack $ str
       | otherwise = error $ "Simplicity.MerkleRoot.Tag.tag: tag is too long: " ++ show ws
 where
  str = intercalate "\US" ws

prefix = ["Simplicity"]
typePrefix = prefix ++ ["Type"]
commitmentPrefix = prefix ++ ["Commitment"]
witnessPrefix = prefix ++ ["Witness"]
primitivePrefix primPrefix = prefix ++ ["Primitive", primPrefix]

typeTag :: String -> IV
typeTag x = tag $ typePrefix ++ [x]

commitmentTag :: String -> IV
commitmentTag x = tag $ commitmentPrefix ++ [x]

witnessTag :: String -> IV
witnessTag x = tag $ witnessPrefix ++ [x]

primTag :: String -> String -> IV
primTag primPrefix x = tag $ primitivePrefix primPrefix ++ [x]

jetTag :: IV
jetTag = tag (prefix ++ ["Jet"])

hiddenTag :: IV
hiddenTag = tag $ (prefix ++ ["Hidden"])

-- | This function hashes a hash such that it will not collide with any 'typeRoot', 'commitmentRoot' or 'witnessRoot'.
--
-- This function is mainly designed for internal use within this Simplicity library.
hiddenRoot :: Hash256 -> Hash256
hiddenRoot = ivHash . compressHalf hiddenTag

-- | This function produces an initial value suitable for signatures such that it will not collide with any other of Simplicity's Merkle root construction.
signatureIv :: Hash256 -> IV
signatureIv h = tag $ (prefix ++ ["Signature\GS" ++ (BSC.unpack . BSL.fromStrict . encode $ h)])

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
-- | Interpret a Simplicity expression as a commitment hash.
-- This commitment exclude 'witness' values and the 'disconnect'ed expression.
-- It also exclude typing information (with the exception of jets).
    commitmentRoot :: Hash256
  } deriving (Eq, Show)

commit = CommitmentRoot . ivHash

-- | The commitment root of a 'fail 0' expression.
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

newtype WitnessRoot a b = WitnessRoot {
-- | Interpret a Simplicity expression as a witness hash.
-- This hash includes 'witness' values and the 'disconnect'ed expression.
-- It also includes all typing decorations.
    witnessRoot :: Hash256
  } deriving (Eq, Show)

observe = WitnessRoot . ivHash

instance Core WitnessRoot where
  iden = result
   where
    result = observe $ compressHalf (witnessTag "iden") (typeRootR (reifyProxy result))

  comp ws@(WitnessRoot s) wt@(WitnessRoot t) = result
   where
    result = observe $ compress (compress (compressHalf (witnessTag "comp") (typeRootR (reifyProxy proxyA)))
                                          (typeRootR (reifyProxy proxyB), (typeRootR (reifyProxy proxyC))))
                                (s, t)
    proxy :: proxy a b -> proxy b c -> (Proxy a, Proxy b, Proxy c)
    proxy _ _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy ws wt

  unit = result
   where
    result = observe $ compressHalf (witnessTag "unit") (typeRootR (fst (reifyArrow result)))

  injl (WitnessRoot t) = result
   where
    result = observe $ compress (compress (witnessTag "injl") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                (typeRootR (reifyProxy proxyC), t)
    proxy :: proxy a (Either b c) -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

  injr (WitnessRoot t) = result
   where
    result = observe $ compress (compress (witnessTag "injr") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                (typeRootR (reifyProxy proxyC), t)
    proxy :: proxy a (Either b c) -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

  match (WitnessRoot s) (WitnessRoot t) = result
   where
    result = observe $ compress (compress (compress (witnessTag "case") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                          (typeRootR (reifyProxy proxyC), typeRootR (reifyProxy proxyD)))
                                (s, t)
    proxy :: proxy ((Either a b), c) d -> (Proxy a, Proxy b, Proxy c, Proxy d)
    proxy _ = (Proxy, Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC, proxyD) = proxy result

  pair (WitnessRoot s) (WitnessRoot t) = result
   where
    result = observe $ compress (compress (compressHalf (witnessTag "pair") (typeRootR (reifyProxy proxyA)))
                                          (typeRootR (reifyProxy proxyB), (typeRootR (reifyProxy proxyC))))
                                (s, t)
    proxy :: proxy a (b,c) -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

  take (WitnessRoot t) = result
   where
    result = observe $ compress (compress (witnessTag "take") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                (typeRootR (reifyProxy proxyC), t)
    proxy :: proxy (a,b) c -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

  drop (WitnessRoot t) = result
   where
    result = observe $ compress (compress (witnessTag "drop") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                (typeRootR (reifyProxy proxyC), t)
    proxy :: proxy (a,b) c -> (Proxy a, Proxy b, Proxy c)
    proxy _ = (Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC) = proxy result

instance Assert WitnessRoot where
  assertl (WitnessRoot s) t = result
   where
    result = observe $ compress (compress (compress (witnessTag "assertl") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                          (typeRootR (reifyProxy proxyC), typeRootR (reifyProxy proxyD)))
                                (s, t)
    proxy :: proxy ((Either a b), c) d -> (Proxy a, Proxy b, Proxy c, Proxy d)
    proxy _ = (Proxy, Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC, proxyD) = proxy result

  assertr s (WitnessRoot t) = result
   where
    result = observe $ compress (compress (compress (witnessTag "assertr") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                          (typeRootR (reifyProxy proxyC), typeRootR (reifyProxy proxyD)))
                                (s, t)
    proxy :: proxy ((Either a b), c) d -> (Proxy a, Proxy b, Proxy c, Proxy d)
    proxy _ = (Proxy, Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC, proxyD) = proxy result
  -- This should never be called in practice, but we add it for completeness.
  fail b = observe $ compress (witnessTag "fail") b

instance Witness WitnessRoot where
  witness v = result
   where
    result = observe $ compress (compressHalf (witnessTag "witness") (typeRootR ra)) (typeRootR rb, bitStringHash (putValue v))
    (ra, rb) = reifyArrow result

instance Delegate WitnessRoot where
  disconnect ws@(WitnessRoot s) wt@(WitnessRoot t) = result
   where
    result = observe $ compress (compress (compress (witnessTag "disconnect") (typeRootR (reifyProxy proxyA), typeRootR (reifyProxy proxyB)))
                                          (typeRootR (reifyProxy proxyC), typeRootR (reifyProxy proxyD)))
                                (s, t)
    proxy :: proxy (a, w) (b, c) -> proxy c d -> (Proxy a, Proxy b, Proxy c, Proxy d)
    proxy _ _ = (Proxy, Proxy, Proxy, Proxy)
    (proxyA, proxyB, proxyC, proxyD) = proxy ws wt

primitiveCommitmentImpl primPrefix primName = commit . primTag primPrefix . primName

jetCommitmentImpl wrt = commit $ compressHalf jetTag wrt

primitiveWitnessImpl primPrefix primName = observe . primTag primPrefix . primName

jetWitnessImpl wrt = observe $ compressHalf jetTag wrt
  -- Idea for alternative WitnessRoot instance:
  --     jet t = t
  -- Trasparent jet witnesses would mean we could define the jet class as
  --     jet :: (TyC a, TyC b) => (forall term0. (Assert term0, Primitive term0, Jet term0) => term0 a b) -> term a b
  -- And then jets could contain jets such that their Sementics, WitnessRoots, and hence CommitmentRoots would all be transparent to jet sub-experssions.
  -- Need to think carefully what this would mean for concensus, but I think it is okay.
