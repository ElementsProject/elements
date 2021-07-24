{-# LANGUAGE RankNTypes, RecordWildCards #-}
-- | This module defines Simplicity expression and types that can be used for computing SHA-256 hashes.
-- Be aware that SHA-256 padding isn't provided and messages should be manually padded.
module Simplicity.Programs.Sha256
 ( Lib(Lib), lib
 -- * Operations
 , Block, Hash
 , iv, hashBlock
 ) where

import Prelude hiding (Word, drop, not, take)

import Simplicity.Functor
import Simplicity.Programs.Arith
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic
import Simplicity.Programs.Word
import Simplicity.Term.Core

-- | In SHA-256, each block of data passed to the compression function is a 512-bit 'Word'.
type Block = Word512

-- | In SHA-256, the inital vector and hash value are 256-bit 'Word's.
type Hash = Word256

-- | A collection of core Simplicity expressions for SHA-256.
-- Use 'lib' to construct an instance of this library.
data Lib term =
 Lib
  { -- | Simplicity expression for the constant function that returns the SHA-256 initial vector.
    iv :: forall a. (TyC a) => term a Hash
    -- | Simplicity expression for the SHA-256 compression function which takes a midstate (or initial vector) and a message block and outputs a hash value (which is used as a midstate if there are further message blocks).
  , hashBlock :: term (Hash, Block) Hash
  }

instance SimplicityFunctor Lib where
  sfmap m Lib{..} =
   Lib
    { iv = m iv
    , hashBlock = m hashBlock
    }


-- | Build the Sha256 'Lib' library.
lib :: Core term => Lib term
lib =
  Lib
   { iv = scribe . toWord256 $ 0x6a09e667bb67ae853c6ef372a54ff53a510e527f9b05688c1f83d9ab5be0cd19
   , hashBlock = oh &&& compression
             >>> ((collate oooh &&& collate ooih)
             &&&  (collate oioh &&& collate oiih))
             &&& ((collate iooh &&& collate ioih)
             &&&  (collate iioh &&& collate iiih))
   }
 where
  collate x = take x &&& drop x >>> add32
  compression = scribe32 k0 &&& iden >>> foldr (\k rec -> scribe32 k &&& step >>> rec) round ks
  k0:ks = [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
          ,0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
          ,0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
          ,0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
          ,0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
          ,0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
          ,0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
          ,0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]
  step = round &&& (drop (drop schedule))
  scribe32 x = scribe (toWord32 x)
  round = part1 >>> part2
   where
    part1 = ((t1 &&& io oooh) &&& io odiag)
        &&& io (bigDiag &&& idiag)
    part2 = ((t12 &&& ooih) &&& oih)
        &&& ((t1d &&& ioih) &&& iih)
    t1 = (oh &&& iio oooh >>> add32) &&& io (drop (iih &&& ((ooh >>> bigSigma1) &&& (ooh &&& diag >>> chWord32) >>> add32)) >>> add32) >>> add32
    t12 = take ((oih &&& ih >>> majWord32) &&& (take (oh &&& (ih >>> bigSigma0)) >>> add32)) >>> add32
    t1d = oooh &&& iooh >>> add32
    bigSigma0 = rotateW32 (-2) &&& rotateW32 (-13) &&& rotateW32 (-22) >>> xor3Word32
    bigSigma1 = rotateW32 (-6) &&& rotateW32 (-11) &&& rotateW32 (-25) >>> xor3Word32
    chWord32 = bitwise_ch word32
    majWord32 = bitwise_maj word32
  schedule = (take part1 &&& (take idiag &&& (take iiih &&& drop oooh)))
         &&& (drop part1 &&& (drop idiag &&& (drop iiih &&& smallSigma)))
   where
    part1 = odiag &&& bigDiag
    smallSigma = (take (oo (oh &&& (ih >>> smallSigma0))) >>> add32) &&& (drop (ooih &&& (iioh >>> smallSigma1)) >>> add32) >>> add32
    smallSigma0 = rotateW32 (-7)  &&& rotateW32 (-18) &&& shiftW32 (-3)  >>> xor3Word32
    smallSigma1 = rotateW32 (-17) &&& rotateW32 (-19) &&& shiftW32 (-10) >>> xor3Word32
  oo x = take (take x)
  io x = drop (take x)
  iio x = drop (io x)
  diag = oih &&& ioh
  odiag = take diag
  idiag = drop diag
  bigDiag = oiih &&& iooh
  add32 = add word32 >>> ih
  xor3Word32 = bitwise_xor3 word32
  rotateW32 = rotate_const word32
  shiftW32 = shift_const_by false word32
