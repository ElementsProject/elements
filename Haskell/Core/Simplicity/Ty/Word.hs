{-# LANGUAGE GADTs #-}
-- | This module defines 2^/n/ bit word Simplicity types.
module Simplicity.Ty.Word
  ( Vector(..)
  , Word, wordSize, fromWord, toWord
  -- * Type aliases
  -- | Below are type aliases for Simplicity 'Word' types upto 512-bit words.
  -- Note: This does not limit word sizes; arbitrarily large word sizes are allowed by making further pairs.
  , Word1, Word2, Word4, Word8, Word16, Word32, Word64, Word128, Word256, Word512
  , Vector1, Vector2, Vector4, Vector8, Vector16, Vector32, Vector64, Vector128, Vector256, Vector512
  -- * Specializations
  -- | The following are useful instances of 'Word' and specializations of 'fromWord' and 'toWord' for commonly used word sizes.
  -- Other word sizes can still be constructed using other 'Word' values.

  -- ** Word1
  , word1, fromWord1, toWord1
  -- ** Word2
  , word2, fromWord2, toWord2
  -- ** Word4
  , word4, fromWord4, toWord4
  -- ** Word8
  , word8, fromWord8, toWord8
  -- ** Word16
  , word16, fromWord16, toWord16
  -- ** Word32
  , word32, fromWord32, toWord32
  -- ** Word64
  , word64, fromWord64, toWord64
  -- ** Word128
  , word128, fromWord128, toWord128
  -- ** Word256
  , word256, fromWord256, toWord256
  -- ** Word512
  , word512, fromWord512, toWord512
  -- ** Bit
  , module Simplicity.Ty.Bit
  ) where

import Prelude hiding (Word)

import Control.Monad.Trans.State (State, evalState, get, put)

import Simplicity.Ty
import Simplicity.Ty.Bit

type Vector1 x = x
type Vector2 x = (x,x)
type Vector4 x = Vector2 (Vector2 x)
type Vector8 x = Vector2 (Vector4 x)
type Vector16 x = Vector2 (Vector8 x)
type Vector32 x = Vector2 (Vector16 x)
type Vector64 x = Vector2 (Vector32 x)
type Vector128 x = Vector2 (Vector64 x)
type Vector256 x = Vector2 (Vector128 x)
type Vector512 x = Vector2 (Vector256 x)

-- | @'Vector' x a@ specifies types, @a@, which are nested pairs of ... pairs of @x@'s.
--
-- The type @a@ contain 2^/n/ @x@ values for some /n/.
data Vector x a where
  SingleV :: TyC x => Vector x x
  DoubleV :: (TyC x, TyC a) => Vector x a -> Vector x (Vector2 a)

type Word1 = Vector1 Bit
type Word2 = Vector2 Bit
type Word4 = Vector4 Bit
type Word8 = Vector8 Bit
type Word16 = Vector16 Bit
type Word32 = Vector32 Bit
type Word64 = Vector64 Bit
type Word128 = Vector128 Bit
type Word256 = Vector256 Bit
type Word512 = Vector512 Bit

-- | @'Word' a@ specifies the types, @a@, which correspond to Simplicity word types.
--
-- These are the types of 2^/n/ bit words and are made up of nested pairs of identically sized words down to the single-'Bit' type.
type Word = Vector Bit

word1 :: Word Word1
word1 = SingleV

word2 :: Word Word2
word2 = DoubleV word1

word4 :: Word Word4
word4 = DoubleV word2

word8 :: Word Word8
word8 = DoubleV word4

word16 :: Word Word16
word16 = DoubleV word8

word32 :: Word Word32
word32 = DoubleV word16

word64 :: Word Word64
word64 = DoubleV word32

word128 :: Word Word128
word128 = DoubleV word64

word256 :: Word Word256
word256 = DoubleV word128

word512 :: Word Word512
word512 = DoubleV word256

-- | Computes the number of bits of the 'Word' 'a'.
--
-- @'wordSize' w = 'Simplicity.BitMachine.Ty.bitSizeR' ('reifyProxy' w)@
wordSize :: Word a -> Int
wordSize SingleV = 1
wordSize (DoubleV w) = 2*(wordSize w)

-- | Covert a value of a Simplicity word type into a standard Haskell integer.
--
-- @'toWord' w ('fromWord' w n) = n@
fromWord :: Word a -> a -> Integer
fromWord = go 0
 where
  go :: Integer -> Word a -> a -> Integer
  go i SingleV (Left ()) = 2 * i
  go i SingleV (Right ()) = 2 * i + 1
  go i (DoubleV w) (hi, lo) = go (go i w hi) w lo

-- | Covert a standard Haskell integer into a Simplicity word type.
-- The value is take modulo 2^@('wordSize' w)@ where @w :: 'Word' a@ is the first argument.
--
-- @'fromWord' w ('toWord' w n) = n \`mod\` 'wordSize' w@
toWord :: Word a -> Integer -> a
toWord w i = evalState (go w) i
 where
  go :: Word a -> State Integer a
  go SingleV = do
   i <- get
   put (i `div` 2)
   return $ toBit (odd i)
  go (DoubleV w) = do
   b <- go w
   a <- go w
   return (a, b)

fromWord1 :: Word1 -> Integer
fromWord1 = fromWord word1

fromWord2 :: Word2 -> Integer
fromWord2 = fromWord word2

fromWord4 :: Word4 -> Integer
fromWord4 = fromWord word4

fromWord8 :: Word8 -> Integer
fromWord8 = fromWord word8

fromWord16 :: Word16 -> Integer
fromWord16 = fromWord word16

fromWord32 :: Word32 -> Integer
fromWord32 = fromWord word32

fromWord64 :: Word64 -> Integer
fromWord64 = fromWord word64

fromWord128 :: Word128 -> Integer
fromWord128 = fromWord word128

fromWord256 :: Word256 -> Integer
fromWord256 = fromWord word256

fromWord512 :: Word512 -> Integer
fromWord512 = fromWord word512

toWord1 :: Integer -> Word1
toWord1 = toWord word1

toWord2 :: Integer -> Word2
toWord2 = toWord word2

toWord4 :: Integer -> Word4
toWord4 = toWord word4

toWord8 :: Integer -> Word8
toWord8 = toWord word8

toWord16 :: Integer -> Word16
toWord16 = toWord word16

toWord32 :: Integer -> Word32
toWord32 = toWord word32

toWord64 :: Integer -> Word64
toWord64 = toWord word64

toWord128 :: Integer -> Word128
toWord128 = toWord word128

toWord256 :: Integer -> Word256
toWord256 = toWord word256

toWord512 :: Integer -> Word512
toWord512 = toWord word512
