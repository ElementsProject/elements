{-# LANGUAGE GADTs, ScopedTypeVariables, TypeOperators #-}
-- | This module defines Simplicity expressions and combinators that operate on Words.
module Simplicity.Programs.Word
  ( module Simplicity.Ty.Word
  -- * Arithmetic
  , zero
  , adder, fullAdder
  , subtractor, fullSubtractor
  , multiplier, fullMultiplier
  -- * Bit-wise operations
  , bitwiseNot
  , shift, rotate
  , bitwise, bitwiseTri
  ) where

import Prelude hiding (Word, drop, take, not, or)

import Data.Type.Equality ((:~:)(Refl))

import Simplicity.Programs.Bit
import Simplicity.Term.Core
import Simplicity.Ty.Word

-- | Simplicity expression for the constant function that returns the representation of 0.
--
-- @
-- 'fromWord' w ('zero' w _) = 0
-- @
zero :: (Core term, TyC a) => Word b -> term a b
zero SingleV = false
zero (DoubleV w) = rec &&& rec
 where
  rec = zero w

-- | Simplicity expression for computing the sum of two words, including the carry bit.
--
-- @
-- 'fromWord1' c * 2 ^ 'wordSize' w + 'fromWord' w z = 'fromWord' w x + 'fromWord' w y
--  where
--   (c, z) = 'adder' w (x, y)
-- @
adder :: Core term => Word a -> term (a, a) (Bit, a)
adder SingleV = cond (iden &&& not iden) (false &&& iden)
adder (DoubleV w) = (ooh &&& ioh) &&& (oih &&& iih >>> rec)
                >>> iih &&& (oh &&& ioh >>> fa)
                >>> ioh &&& (iih &&& oh)
 where
  rec = adder w
  fa = fullAdder w

-- | Simplicity expression for computing the difference of two words, also returning the borrow bit.
--
-- @
-- 'fromWord' w z = 'fromWord1' b * 2 ^ 'wordSize' + 'fromWord' w x - 'fromWord' w y
--  where
--   (b, z) = 'subtractor' w (x, y)
-- @
subtractor :: Core term => Word a -> term (a, a) (Bit, a)
subtractor SingleV = cond (false &&& not iden) (iden &&& iden)
subtractor (DoubleV w) = (ooh &&& ioh) &&& (oih &&& iih >>> rec)
                     >>> iih &&& (oh &&& ioh >>> fs)
                     >>> ioh &&& (iih &&& oh)
 where
  rec = subtractor w
  fs = fullSubtractor w

-- | Simplicity expression for computing the sum of two words and a carry input bit, including the carry output bit.
--
-- @
-- 'fromWord1' cout * 2 ^ 'wordSize' w + 'fromWord' w z = 'fromWord' w x + 'fromWord' w y + 'fromWord1' cin
--  where
--   (cout, z) = 'fullAdder' w ((x, y), cin)
-- @
fullAdder :: Core term => Word a -> term ((a, a), Bit) (Bit, a)
fullAdder SingleV = take add &&& ih
             >>> ooh &&& (oih &&& ih >>> add)
             >>> cond true oh &&& iih
 where
  add = adder SingleV
fullAdder (DoubleV w) = take (ooh &&& ioh) &&& (take (oih &&& iih) &&& ih >>> rec)
                    >>> iih &&& (oh &&& ioh >>> rec)
                    >>> ioh &&& (iih &&& oh)
 where
  rec = fullAdder w

-- | Simplicity expression for computing the difference of two words and a borrow input bit, also returning the borrow output bit.
--
-- @
-- 'fromWord' w z = 'fromWord1' bout * 2 ^ 'wordSize' + 'fromWord' w x - 'fromWord' w y - 'fromWord1' bin
--  where
--   (bout, z) = 'fullSubtractor' w ((x, y), bin)
-- @
fullSubtractor :: Core term => Word a -> term ((a, a), Bit) (Bit, a)
fullSubtractor SingleV = take sub &&& ih
                  >>> ooh &&& (oih &&& ih >>> sub)
                  >>> cond true oh &&& iih
 where
  sub = subtractor SingleV
fullSubtractor (DoubleV w) = take (ooh &&& ioh) &&& (take (oih &&& iih) &&& ih >>> rec)
                         >>> iih &&& (oh &&& ioh >>> rec)
                         >>> ioh &&& (iih &&& oh)
 where
  rec = fullSubtractor w

-- | 'fullMultiplier' is a Simplicity expression that helps compute products of larger word sizes from smaller word sizes.
--
-- @
-- 'fromWord' ('DoubleV' w) ('fullMultiplier' w ((a, b), (c, d))) = 'fromWord' w a * 'fromWord' w b  + 'fromWord' w c + 'fromWord' w d
-- @
fullMultiplier :: Core term => Word a -> term ((a, a), (a, a)) (a, a)
fullMultiplier SingleV = ih &&& take (cond iden false)
                  >>> fullAdder SingleV
fullMultiplier (DoubleV w) = take (ooh &&& (ioh &&& oih))
                         &&& ((take (ooh &&& iih) &&& drop (ooh &&& ioh) >>> rec)
                         &&& (take (oih &&& iih) &&& drop (oih &&& iih) >>> rec))
                         >>> take (oh &&& ioh)
                         &&& (drop (ooh &&& iih) &&& (oih &&& drop (oih &&& ioh) >>> rec))
                         >>> (oh &&& drop (ioh &&& ooh) >>> rec) &&& drop (iih &&& oih)
 where
  rec = fullMultiplier w

-- | Simplicity expression for computing the product of two words, returning a doubled size word.
--
-- @
-- 'fromWord' ('DoubleV' w) ('multiplier' w (x, y)) = 'fromWord' w x * 'fromWord' w y
-- @
multiplier :: Core term => Word a -> term (a, a) (a, a)
multiplier SingleV = false &&& cond iden false
multiplier (DoubleV w) = (ooh &&& (ioh &&& oih))
                     &&& ((ooh &&& iih >>> rec) &&& (oih &&& iih >>> rec))
                     >>> take (oh &&& ioh)
                     &&& (drop (ooh &&& iih) &&& (oih &&& drop (oih &&& ioh) >>> fm))
                     >>> (oh &&& drop (ioh &&& ooh) >>> fm) &&& drop (iih &&& oih)
 where
  rec = multiplier w
  fm = fullMultiplier w

-- | A Simplicity combinator for computing the bitwise complement of a binary word.
bitwiseNot :: forall term a. Core term => Word a -> term a a
bitwiseNot SingleV = not iden
bitwiseNot (DoubleV w) = (oh >>> rec) &&& (ih >>> rec)
   where
    rec = bitwiseNot w

-- | A Simplicity combinator for lifting a binary bit operation to a binary word operation that applies the bit operation bit-wise to each bit of the word.
bitwise :: forall term a. Core term => term (Bit, Bit) Bit -> Word a -> term (a, a) a
bitwise op = go
 where
  go :: forall a. Word a -> term (a, a) a
  go SingleV = op
  go (DoubleV w) = (ooh &&& ioh >>> rec) &&& (oih &&& iih >>> rec)
   where
    rec = go w

-- | A Simplicity combinator for lifting a trinary bit operation to a trinary word operation that applies the bit operation bit-wise to each bit of the word.
-- This is similar to 'bitwise' except works with trinary bit operations instead of binary operations.
bitwiseTri :: forall term a. Core term => term (Bit, (Bit, Bit)) Bit -> Word a -> term (a, (a, a)) a
bitwiseTri op = go
 where
  go :: forall a. Word a -> term (a, (a, a)) a
  go SingleV = op
  go (DoubleV w) = (ooh &&& (iooh &&& iioh) >>> rec)
               &&& (oih &&& (ioih &&& iiih) >>> rec)
   where
    rec = go w

-- @'BiggerWord' a b@ is a GADT where @a@ and @b@ are Simplicity word types and @a@ has fewer bits than @b@
-- This is a helper type that is used in the definitions of 'shift' and 'rotate'.
data BiggerWord a b where
  JustBigger :: TyC a => Word a -> BiggerWord a (a,a)
  MuchBigger :: (TyC a, TyC b) => BiggerWord a b -> BiggerWord a (b,b)

biggerWord :: BiggerWord a b -> Word b
biggerWord (JustBigger w) = DoubleV w
biggerWord (MuchBigger bw) = DoubleV (biggerWord bw)

doubleBigger :: BiggerWord a b -> BiggerWord (a,a) (b,b)
doubleBigger (JustBigger w) = JustBigger (DoubleV w)
doubleBigger (MuchBigger bw) = MuchBigger (doubleBigger bw)

compareWordSize :: Word a -> Word b -> Either (Either (BiggerWord a b) (BiggerWord b a)) (a :~: b)
compareWordSize SingleV SingleV = Right Refl
compareWordSize (DoubleV n) SingleV =
  case compareWordSize n SingleV of
    Right Refl -> Left (Right (JustBigger SingleV))
    Left (Right bw) -> Left (Right (MuchBigger bw))
compareWordSize SingleV (DoubleV m) =
  case compareWordSize SingleV m of
    Right Refl -> Left (Left (JustBigger SingleV))
    Left (Left bw) -> Left (Left (MuchBigger bw))
compareWordSize (DoubleV n) (DoubleV m) =
  case compareWordSize n m of
    Right Refl -> Right Refl
    Left (Left bw) -> Left (Left (doubleBigger bw))
    Left (Right bw) -> Left (Right (doubleBigger bw))

-- | Simplicity expression for a bit shift by a constant amount.
--
-- @'shift' w n x@ is a right shift of @n@ bits of the word @x@.
-- The value @n@ can be negative in which case a left shift is performed.

shift :: (Core term, TyC a) => Word a -> Int -> term a a
shift w = subseq w w
 where
  subseq :: (Core term, TyC a, TyC b) => Word a -> Word b -> Int -> term a b
  subseq n m z | z == 0 = subseq0 (compareWordSize n m)
               | wordSize n <= z = zero m
               | z + wordSize m <= 0 = zero m
  subseq (DoubleV n) m           z | wordSize n <= z              = take (subseq n m (z - wordSize n))
                                   | z + wordSize m <= wordSize n = drop (subseq n m z)
  subseq n           (DoubleV m) z = subseq n m (z + wordSize m) &&& subseq n m z

  subseq0 :: (Core term, TyC a) => Either (Either (BiggerWord a b) (BiggerWord b a)) (a :~: b) -> term a b
  subseq0 (Right Refl) = iden
  subseq0 (Left (Right (JustBigger w))) = drop iden
  subseq0 (Left (Right (MuchBigger bw))) = drop (subseq0 (Left (Right bw)))
  subseq0 (Left (Left (JustBigger w))) = zero w &&& iden
  subseq0 (Left (Left (MuchBigger bw))) = zero (biggerWord bw) &&& subseq0 (Left (Left bw))

-- | Simplicity expression for a bit rotation by a constant amount.
--
-- @'rotate' w n x@ is a right rotation of @n@ bits of the word @x@.
-- The value @n@ can be negative in which case a left rotation is performed.
rotate :: (Core term, TyC a) => Word a -> Int -> term a a
rotate w z = subseqWrap w w (z `mod` wordSize w)
 where
   -- Precondition: 0 <= z < wordSize n
   subseqWrap :: (Core term, TyC a, TyC b) => Word a -> Word b -> Int -> term a b
   subseqWrap n m z | z == 0 = subseqWrap0 (compareWordSize n m)
   subseqWrap (DoubleV n) m           z | wordSize n <= z && z + wordSize m <= 2 * wordSize n = take (subseqWrap n m (z - wordSize n))
                                        | z + wordSize m <= wordSize n                        = drop (subseqWrap n m z)
   subseqWrap n           (DoubleV m) z = subseqWrap n m ((z + wordSize m) `mod` wordSize n) &&& subseqWrap n m z

   subseqWrap0 :: (Core term, TyC a) => Either (Either (BiggerWord a b) (BiggerWord b a)) (a :~: b) -> term a b
   subseqWrap0 (Right Refl) = iden
   subseqWrap0 (Left (Right (JustBigger w))) = drop iden
   subseqWrap0 (Left (Right (MuchBigger bw))) = drop (subseqWrap0 (Left (Right bw)))
   subseqWrap0 (Left (Left (JustBigger w))) = iden &&& iden
   subseqWrap0 (Left (Left (MuchBigger bw))) = rec &&& rec
    where
     rec = subseqWrap0 (Left (Left bw))
