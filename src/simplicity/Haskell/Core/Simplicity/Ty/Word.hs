{-# LANGUAGE GADTs, TypeOperators #-}

-- | This module defines 2^/n/ bit word Simplicity types.
module Simplicity.Ty.Word
  ( Vector(..), vectorComp, vectorPromote, compareVectorSize
  , Word, wordSize, fromWord, toWord
  -- * Type aliases
  -- | Below are type aliases for Simplicity 'Word' types upto 512-bit words.
  -- Note: This does not limit word sizes; arbitrarily large word sizes are allowed by making further pairs.
  , Word1, Word2, Word4, Word8, Word16, Word32, Word64, Word128, Word256, Word512
  , Vector1, Vector2, Vector4, Vector8, Vector16, Vector32, Vector64, Vector128, Vector256, Vector512
  , vector1, vector2, vector4, vector8, vector16, vector32, vector64, vector128, vector256, vector512
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
  -- * Zip Vector
  , ZipVector(..)
  -- ** Bit
  , module Simplicity.Ty.Bit
  ) where

import Prelude hiding (Word)

import Control.Monad.Trans.State (State, evalState, get, put)
import Data.Type.Equality ((:~:)(Refl))

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

vector1 :: TyC x => Vector x (Vector1 x)
vector1 = SingleV

vector2 :: TyC x => Vector x (Vector2 x)
vector2 = DoubleV vector1

vector4 :: TyC x => Vector x (Vector4 x)
vector4 = DoubleV vector2

vector8 :: TyC x => Vector x (Vector8 x)
vector8 = DoubleV vector4

vector16 :: TyC x => Vector x (Vector16 x)
vector16 = DoubleV vector8

vector32 :: TyC x => Vector x (Vector32 x)
vector32 = DoubleV vector16

vector64 :: TyC x => Vector x (Vector64 x)
vector64 = DoubleV vector32

vector128 :: TyC x => Vector x (Vector128 x)
vector128 = DoubleV vector64

vector256 :: TyC x => Vector x (Vector256 x)
vector256 = DoubleV vector128

vector512 :: TyC x => Vector x (Vector512 x)
vector512 = DoubleV vector256

-- | @'Vector' x a@ specifies types, @a@, which are nested pairs of ... pairs of @x@'s.
--
-- The type @a@ contain 2^/n/ @x@ values for some /n/.
data Vector x a where
  SingleV :: TyC x => Vector x x
  DoubleV :: (TyC x, TyC a) => Vector x a -> Vector x (Vector2 a)

-- | A proof that a 'Vector' of 'Vector's is itself a 'Vector'.
vectorComp :: TyC a => Vector a b -> Vector b c -> Vector a c
vectorComp v SingleV = v
vectorComp v (DoubleV w) = DoubleV (vectorComp v w)

-- | A proof that if @y@ is a 'Vector' of @x@'s then @(y, y)@ is a vector of @(x, x)@'s
vectorPromote :: Vector x y -> Vector (x, x) (y, y)
vectorPromote SingleV = SingleV
vectorPromote (DoubleV v) = DoubleV (vectorPromote v)

-- | Given @a@ and @b@ which are both 'Vector's of @z@'s, then decide which of the two 'Vector's is longer or prove that they are equal.
compareVectorSize :: Vector z a -> Vector z b -> Either (Vector (b, b) a) (Either (a :~: b) (Vector (a, a) b))
compareVectorSize SingleV SingleV = Right (Left Refl)
compareVectorSize (DoubleV n) SingleV =
  case compareVectorSize n SingleV of
    Left v -> Left (DoubleV v)
    Right (Left Refl) -> Left SingleV
compareVectorSize SingleV (DoubleV m) =
  case compareVectorSize SingleV m of
    Right (Left Refl) -> Right (Right SingleV)
    Right (Right v) -> Right (Right (DoubleV v))
compareVectorSize (DoubleV n) (DoubleV m) =
  case compareVectorSize n m of
    Left v -> Left (vectorPromote v)
    Right (Left Refl) -> Right (Left Refl)
    Right (Right v) -> Right (Right (vectorPromote v))

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
word1 = vector1

word2 :: Word Word2
word2 = vector2

word4 :: Word Word4
word4 = vector4

word8 :: Word Word8
word8 = vector8

word16 :: Word Word16
word16 = vector16

word32 :: Word Word32
word32 = vector32

word64 :: Word Word64
word64 = vector64

word128 :: Word Word128
word128 = vector128

word256 :: Word Word256
word256 = vector256

word512 :: Word Word512
word512 = vector512

-- | Computes the number of entries in a 'Vector'.
--
-- @'wordSize' w = 'Simplicity.BitMachine.Ty.bitSizeR' ('reifyProxy' w)@
wordSize :: Vector x a -> Int
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

-- | A pair of 'Vector's of the same length that have different contents.
data ZipVector x a y b where
  SingleZV :: (TyC x, TyC y) => ZipVector x x y y
  DoubleZV :: (TyC x, TyC a, TyC y, TyC b) => ZipVector x a y b -> ZipVector x (Vector2 a) y (Vector2 b)
