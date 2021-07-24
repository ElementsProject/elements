{-# LANGUAGE ScopedTypeVariables, RecordWildCards #-}
-- | The module builds a Simplicity expression that mimics the behavour of a @CHECKSIG@ operation restricted to a @SIGHASH_ALL@ flag for Elements.
-- This forms the mimial Simiplicity expression needed to secure funds in a Elements-style blockchain.
-- This uses Schnorr signature verification specified in "Simplicity.Programs.LibSecp256k1".
module Simplicity.Elements.Programs.CheckSigHashAll
-- :TODO:
-- - Add other sighash modes to the library
-- - Eliminate checkSigHashAll in favor of a generic checkSigHashFixed combinator in Core
-- - Rename this module *.SigHash
  ( Lib(Lib), mkLib
  -- * Operations
  , hashAll
  , sigHashAll
  , checkSigHashAll
  -- * Types
  , Hash
  -- * Example instances
  , lib
  ) where

import Prelude hiding (drop, take)

import Simplicity.Digest
import Simplicity.Elements.Primitive
import Simplicity.Elements.Term
import Simplicity.Functor
import qualified Simplicity.LibSecp256k1.Schnorr as Schnorr
import Simplicity.MerkleRoot
import Simplicity.Programs.Arith
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Programs.Sha256 hiding (Lib(Lib), lib)
import qualified Simplicity.Programs.Sha256 as Sha256
import qualified Simplicity.Programs.LibSecp256k1 as LibSecp256k1
import Simplicity.Tensor
import Simplicity.Ty

-- | A collection of core Simplicity expressions for Elements-style signature hash modes.
-- Use 'mkLib' to construct an instance of this library.
data Lib term =
 Lib
  { -- | This expression returns a hash of basic signed transaction data.
    -- This includes:
    --
    -- * Hash of all the transaction inputs data.
    --
    -- * Hash of all the transaction output data.
    --
    -- * The transactions lock time.
    --
    -- * The transactions version data.
    --
    -- * The index of the input currently being spend.
    --
    -- * The asset and amount of this input's UTXO being redeemed.
    hashAll :: term () Hash
    -- | This expression creates a digest of the pair of the 'commitmentRoot' of 'hashAll' with the result of evaluating 'hashAll'.
    -- This is the digest that needs to be signed for 'checkSigHashAll' to pass.
  , sigHashAll :: term () Hash
  }

instance SimplicityFunctor Lib where
  sfmap m Lib{..} =
   Lib
    { hashAll = m hashAll
    , sigHashAll = m sigHashAll
    }

-- | Build the Elements signature hash 'Lib' library from its dependencies.
mkLib :: forall term. (Core term, Primitive term) => Sha256.Lib (Product CommitmentRoot term) -- ^ "Simplicity.Programs.Sha256"
                                                  -> Lib term
mkLib Sha256.Lib{..} = lib
 where
  hashAllProduct :: (Product CommitmentRoot term) () Hash
  hashAllProduct = blk2andMaybe3 &&& (scribe iv &&& blk1 >>> hb)
        >>> oih &&& (ih &&& ooh >>> hb)
        >>> match ih (ih &&& oh >>> hb)
   where
    iv = toWord256 . integerHash256 . ivHash $ sigHashTag
    hb = hashBlock
    curAsset = (primitive CurrentAsset &&& unit) >>>
               (match (take (cond (scribe (toWord8 11) &&& iden) (scribe (toWord8 10) &&& iden)))
                      (scribe (toWord8 1) &&& oh))
           >>> ((((oh &&& drop (take (take oooh))) &&& drop (take (take (take (oih &&& ioh))))) &&&
                drop (take (take  ((oiih &&& iooh) &&& drop (oih &&& ioh)) &&& ((take iiih &&& drop oooh) &&& drop (take (oih &&& ioh)))) &&&
                       (take (drop ((oiih &&& iooh) &&& drop (oih &&& ioh))) &&& ((take (drop iiih) &&& drop (take oooh)) &&& drop (take (take (oih &&& ioh))))))) &&&
                drop (drop ((take ((oiih &&& iooh) &&& drop (oih &&& ioh)) &&& ((take iiih &&& drop oooh) &&& drop (take (oih &&& ioh)))) &&&
                      drop  (((oiih &&& iooh) &&& drop (oih &&& ioh)) &&&   iiih))))
    curAmt = (primitive CurrentAmount &&& unit) >>>
             match (take curConfAmt) (take curExplAmt)
     where
      curExplAmt = ((scribe (toWord8 1)) &&& ooh) &&&
                   ((((oih &&& ioh) &&& (iih &&& (scribe (toWord16 0x8000)))) &&& scribe (toWord64 (512+2*256+3*32+8+256+8+64))) &&&
                   injl unit)
      curConfAmt = (oh &&& drop (take oooh) >>> cond (scribe (toWord8 9) &&& iden) (scribe (toWord8 8) &&& iden)) &&&
                   drop ((take (take (oih &&& ioh) &&& (oiih &&& iooh)) &&& (take (drop (oih &&& ioh)) &&& (take iiih &&& drop oooh))) &&&
                   drop (injr ((((take (oih &&& ioh) &&& (oiih &&& iooh)) &&& drop ((oih &&& ioh) &&& (iih &&& (scribe (toWord16 0x8000))))) &&& (unit >>> zero word128)) &&& scribe (toWord256 (512+2*256+3*32+8+256+8+256)))))
    blk1 = primitive InputsHash &&& primitive OutputsHash
    blk2andMaybe3 = (curAsset &&& curAmt) >>>
                ((take (take (((unit >>> ((primitive Version &&& primitive LockTime))) &&& (((unit >>> primitive CurrentIndex) &&& oh))) &&& ih)) &&&
                   ((oioh &&& (take iioh &&& ((take iiih &&& iooh) &&& ioih))) &&& iioh)) &&& iiih)
  hashAllCMR = fstProduct hashAllProduct
  lib@Lib{..} =
   Lib
    { hashAll = sndProduct hashAllProduct
    , sigHashAll =
       let
        iv = toWord256 . integerHash256 . ivHash $ signatureTag
        cmr = toWord256 . integerHash256 $ commitmentRoot hashAllCMR
        hb = sndProduct hashBlock
       in
            (scribe iv &&& (scribe cmr &&& hashAll) >>> hb)
         &&& scribe (toWord512 0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400)
         >>> hb
    }

-- | An instance of the Elements signature hash 'Lib' library.
-- This instance does not share its dependencies.
-- Users should prefer to use 'mkLib' in order to share library dependencies.
-- This instance is provided mostly for testing purposes.
lib :: (Core term, Primitive term) => Lib term
lib = mkLib libSha256
 where
  libSha256 = Sha256.lib

-- | Given a public key and a bip0340 signature, this Simplicity program asserts that the signature is valid for the public key and the message generated by 'sigHashAll'.
-- The signature is in a 'witness' combinator and is not commited by the 'commitmentRoot' of this program.
checkSigHashAll :: (Assert term, Primitive term, Witness term) => LibSecp256k1.Lib term -- ^ "Simplicity.Programs.LibSecp256k1"
                                                               -> Lib term
                                                               -> Schnorr.PubKey -> Schnorr.Sig -> term () ()
checkSigHashAll libsecp256k1 Lib{..} (Schnorr.PubKey x) ~(Schnorr.Sig r s) =
   (scribe (toWord256 . toInteger $ x) &&& sigHashAll) &&& (witness (toWord256 . toInteger $ r, toWord256 . toInteger $ s))
   >>> bip0340_verify
 where
  bip0340_verify = LibSecp256k1.bip0340_verify libsecp256k1
