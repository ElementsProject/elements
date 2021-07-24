{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables, TypeOperators #-}
-- | This module defines Simplicity expressions and combinators that operate on Words.
module Simplicity.Programs.Word
  ( fill, low, high
  , complement
  , bitwise_bin, bitwise_tri
  , bitwise_and, bitwise_or, bitwise_xor
  , bitwise_maj, bitwise_xor3, bitwise_ch
  , some, all, eq
  , leftmost, left_pad_low, left_pad_high, left_extend
  , rightmost, right_pad_low, right_pad_high, right_extend
  , full_shift, shift_const_by, rotate_const
  , mapZV, transpose
  , module Simplicity.Ty.Word
  ) where

import Prelude hiding (Word, drop, take, not, or, and, last, all)

import qualified Data.Bits as Bits
import Data.Type.Equality ((:~:)(Refl))

import Simplicity.Programs.Generic (eq)
import Simplicity.Programs.Bit
import Simplicity.Term.Core
import Simplicity.Ty.Word

-- | 2^n-ary diagonal of a term.
fill :: (Core term, TyC c) => term c a -> Vector a b -> term c b
fill t SingleV = t
fill t (DoubleV w) = rec &&& rec
 where
  rec = fill t w

-- | Set all bits of a word to @0@.
low :: Core term => Word a -> term () a
low = fill false

-- | Set all bits of a word to @1@.
high :: Core term => Word a -> term () a
high = fill true

-- | Bitwise complement of a word.
complement :: Core term => Word a -> term a a
complement SingleV = not iden
complement (DoubleV w) = take rec &&& drop rec
 where
  rec = complement w

-- | Map a binary operation across a vecotor.
bitwise_bin :: forall term a v. Core term => term (a, a) a -> Vector a v -> term (v, v) v
bitwise_bin op = go
 where
  go :: forall v. Vector a v -> term (v, v) v
  go SingleV = op
  go (DoubleV w) = (ooh &&& ioh >>> rec) &&& (oih &&& iih >>> rec)
   where
    rec = go w

-- | Map a trinary operation across a vecotor.
bitwise_tri :: forall term a v. Core term => term (a, (a, a)) a -> Vector a v -> term (v, (v, v)) v
bitwise_tri op = go
 where
  go :: forall v. Vector a v -> term (v, (v, v)) v
  go SingleV = op
  go (DoubleV w) = (ooh &&& (iooh &&& iioh) >>> rec) &&& (oih &&& (ioih &&& iiih) >>> rec)
   where
    rec = go w

-- | Bitwise 'and' over a pair of words.
bitwise_and :: Core term => Word a -> term (a, a) a
bitwise_and = bitwise_bin (and oh ih)

-- | Bitwise 'or' over a pair of words.
bitwise_or :: Core term => Word a -> term (a, a) a
bitwise_or = bitwise_bin (or oh ih)

-- | Bitwise 'xor' over a pair of words.
bitwise_xor :: Core term => Word a -> term (a, a) a
bitwise_xor = bitwise_bin (xor oh ih)

-- | Bitwise 'maj' over a triple of words.
bitwise_maj :: Core term => Word a -> term (a, (a, a)) a
bitwise_maj = bitwise_tri maj

-- | Bitwise 'xor3' over a triple of words.
bitwise_xor3 :: Core term => Word a -> term (a, (a, a)) a
bitwise_xor3 = bitwise_tri xor3

-- | Bitwise 'ch' over a triple of words.
bitwise_ch :: Core term => Word a -> term (a, (a, a)) a
bitwise_ch = bitwise_tri ch

-- | Test if some bit of a word is non-zero.
some :: Core term => Word a -> term a Bit
some SingleV = iden
some (DoubleV w) = or (take rec) (drop rec)
 where
  rec = some w

-- | Test if all bits of a word are non-zero.
all :: Core term => Word a -> term a Bit
all SingleV = iden
all (DoubleV w) = and (take rec) (drop rec)
 where
  rec = all w

-- | Return the leftmost (a.k.a first) value from a vector.
--
-- Will return the most significant bit, MSB, of a word.
leftmost :: (Core term, TyC a, TyC b) => Vector a b -> term b a
leftmost SingleV = iden
leftmost (DoubleV v) = take (leftmost v)

-- | Return the leftmost (a.k.a first) value from a vector.
--
-- Will return the least signficant bit, LSB, of a word.
rightmost :: (Core term, TyC a, TyC b) => Vector a b -> term b a
rightmost SingleV = iden
rightmost (DoubleV v) = drop (rightmost v)

-- | Given the last element of a vector, pad the rest of the elements with a value (derived from the input).
left_pad_pad :: Core term => term a a -> Vector a b -> term a b
left_pad_pad _ SingleV = iden
left_pad_pad t (DoubleV v) = fill t v &&& left_pad_pad t v

-- | Increase the size of a word by padding the left (MSB) bits with @0@s.
left_pad_low :: (Core term, TyC a) => Word a -> Vector a b -> term a b
left_pad_low w v = left_pad_pad (unit >>> low w) v

-- | Increase the size of a word by padding the left (MSB) bits with @1@s.
left_pad_high :: (Core term, TyC a) => Word a -> Vector a b -> term a b
left_pad_high w v = left_pad_pad (unit >>> high w) v

-- | Increase the size of a word by padding the left (MSB) bits with the MSB of the input.
left_extend :: (Core term, TyC a, TyC b) => Word a -> Vector a b -> term a b
left_extend w v = leftmost w &&& iden >>> cond (left_pad_high w v) (left_pad_low w v)

-- | Given the first element of a vector, pad the rest of the elements with a value (derived from the input).
right_pad_pad :: Core term => term a a -> Vector a b -> term a b
right_pad_pad _ SingleV = iden
right_pad_pad t (DoubleV v) = right_pad_pad t v &&& fill t v

-- | Increase the size of a word by padding the right (LSB) bits with @0@s.
right_pad_low :: (Core term, TyC a) => Word a -> Vector a b -> term a b
right_pad_low w v = right_pad_pad (unit >>> low w) v

-- | Increase the size of a word by padding the right (LSB) bits with @1@s.
right_pad_high :: (Core term, TyC a) => Word a -> Vector a b -> term a b
right_pad_high w v = right_pad_pad (unit >>> high w) v

-- | Increase the size of a word by padding the right (LSB) bits with the LSB of the input.
right_extend :: (Core term, TyC a, TyC b) => Word a -> Vector a b -> term a b
right_extend w v = rightmost w &&& iden >>> cond (right_pad_high w v) (right_pad_low w v)

-- | Left shift the values of a given vector, shifting in the provided value, and returning the value shifted out.
full_left_shift1 :: Core term => Vector a va -> term (va, a) (a, va)
full_left_shift1 SingleV = iden
full_left_shift1 (DoubleV v) = ooh &&& (oih &&& ih >>> rec) >>> (oh &&& ioh >>> rec) &&& iih >>> ooh &&& (oih &&& ih)
 where
  rec = full_left_shift1 v

-- | Right shift the values of a given vector, shifting in the provided value, and returning the value shifted out.
full_right_shift1 :: Core term => Vector a va -> term (a, va) (va, a)
full_right_shift1 SingleV = iden
full_right_shift1 (DoubleV v) = (oh &&& ioh >>> rec) &&& iih >>> ooh &&& (oih &&& ih >>> rec) >>> (oh &&& ioh) &&& iih
 where
  rec = full_right_shift1 v

-- | Given a pair of vectors, rebalance the tuple to return a pair of vectors with their sizes exchanged.
--
-- This can be seen as a left shift of the vector @a@, shifting in the vector @b@ and returning the values shifted out.
-- This can also be seen as a right shift of the vector @b@, shifting in the vector @a@ and returning the values shifted out.
full_shift :: (Core term, TyC a, TyC b) => Vector x a -> Vector x b -> term (a, b) (b, a)
full_shift wa wb = go (compareVectorSize wb wa)
 where
  go :: (Core term, TyC a, TyC b) => Either (Vector (a, a) b) (Either (b :~: a) (Vector (b, b) a)) -> term (a, b) (b, a)
  go (Left v) = full_right_shift1 (vectorComp vector2 v)
  go (Right (Left Refl)) = iden
  go (Right (Right v)) = full_left_shift1 (vectorComp vector2 v)

-- | Left shift a vector by a constant number of places, shifting in copies the provided value.
-- Shifting by a negative number of places will perform a right shift instead.
shift_const_by :: (Core term, TyC a, TyC b) => term () a -> Vector a b -> Int -> term b b
shift_const_by t v n | wordSize v <= n = unit >>> fill t v
                     | n < 0 = right_shift_const_by t v (-n)
                     | otherwise = compose (go t v n)
 where
  compose [] = iden
  compose l = foldr1 (>>>) l
  go :: (Core term, TyC a, TyC b) => term () a -> Vector a b -> Int -> [term b b]
  go t SingleV 0 = []
  go t v@(DoubleV v') n | even n = rec (n `div` 2)
                        | otherwise = left_shift1 : rec ((n-1) `div` 2)
   where
    left_shift1 = iden &&& (unit >>> t) >>> full_left_shift1 v >>> ih
    rec = go (t &&& t) (vectorPromote v')

-- | Right shift a vector by a constant number of places, shifting in copies the provided value.
-- Shifting by a negative number of places will perform a left shift instead.
right_shift_const_by :: (Core term, TyC a, TyC b) => term () a -> Vector a b -> Int -> term b b
right_shift_const_by t v n | wordSize v <= n = unit >>> fill t v
                           | n < 0 = shift_const_by t v (-n)
                           | otherwise = compose (go t v n)
 where
  compose [] = iden
  compose l = foldr1 (>>>) l
  go :: (Core term, TyC a, TyC b) => term () a -> Vector a b -> Int -> [term b b]
  go t SingleV 0 = []
  go t v@(DoubleV v') n | even n = rec (n `div` 2)
                        | otherwise = right_shift1 : rec ((n-1) `div` 2)
   where
    right_shift1 = (unit >>> t) &&& iden >>> full_right_shift1 v >>> oh
    rec = go (t &&& t) (vectorPromote v')

-- | Left shift a vector by shifting in the value that is shifted out.
left_rotate1 :: (Core term, TyC a, TyC b) => Vector a b -> term b b
left_rotate1 v = iden &&& leftmost v >>> full_left_shift1 v >>> ih

-- | Right shift a vector by shifting in the value that is shifted out.
right_rotate1 :: (Core term, TyC a, TyC b) => Vector a b -> term b b
right_rotate1 v = rightmost v &&& iden >>> full_right_shift1 v >>> oh

-- | Left rotate a vector by a constant number of places.
-- Rotating by a negative number of places will perform a right rotate instead.
rotate_const :: (Core term, TyC a, TyC b) => Vector a b -> Int -> term b b
rotate_const v n = compose (go v n)
 where
  compose [] = iden
  compose l = foldr1 (>>>) l
  go :: (Core term, TyC a, TyC b) => Vector a b -> Int -> [term b b]
  go SingleV n = []
  go v@(DoubleV v') n | even n = rec (n `div` 2)
                      | 1 == n `mod` 4 = left_rotate1 v : rec ((n-1) `div` 2)
                      | 3 == n `mod` 4 = right_rotate1 v : rec ((n+1) `div` 2)
   where
    rec = go (vectorPromote v')

-- | Lift a provided term to map a vector of inputs to a vector of outputs of the same length.
mapZV :: (Core term) => ZipVector x nx y ny -> term x y -> term nx ny
mapZV SingleZV t = t
mapZV (DoubleZV zv) t = take rec &&& drop rec
 where
  rec = mapZV zv t

-- Polymorphic helper type isomorphic to @term a b@ via Yoneda embedding.
data Yoneda term a b = Yoneda (forall d. TyC d => term b d -> term a d)
runYoneda :: (Core term, TyC b) => Yoneda term a b -> term a b
runYoneda (Yoneda k) = k iden

-- An identity for the 'Yoneda' embedding.
yId :: Yoneda term a a
yId = Yoneda id

-- Take the first value of a pair.  Using the 'Yoneda' embedding avoids the 'comp' combinator.
yoh :: (Core term, TyC a, TyC b, TyC c) => Yoneda term c (a, b) -> Yoneda term c a
yoh (Yoneda k) = Yoneda (\t -> k (take t))

-- Take the second value of a pair.  Using the 'Yoneda' embedding avoids the 'comp' combinator.
yih :: (Core term, TyC a, TyC b, TyC c) => Yoneda term c (a, b) -> Yoneda term c b
yih (Yoneda k) = Yoneda (\t -> k (drop t))

-- | Transpose a matrix (i.e a vector of vectors) of the specified dimensions.
transpose :: (Core term, TyC mx, TyC nmx) => ZipVector x mx nx mnx -> ZipVector mx nmx x nx -> term nmx mnx
transpose mzv nzv = go mzv nzv yId
 where
  go :: (Core term, TyC nm, TyC m) => ZipVector x kx nx knx -> ZipVector m nm x nx -> Yoneda term m kx -> term nm knx
  go SingleZV nzv t = mapZV nzv (runYoneda t)
  go (DoubleZV zv) nzv t = go zv nzv (yoh t) &&& go zv nzv (yih t)
