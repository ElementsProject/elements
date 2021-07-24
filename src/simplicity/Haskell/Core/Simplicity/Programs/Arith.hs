{-# LANGUAGE GADTs, ScopedTypeVariables, TypeOperators #-}
-- | This module defines Simplicity expressions and combinators that operate on Words.
module Simplicity.Programs.Arith
  ( module Simplicity.Ty.Word
  , zero
  , one
  , add, full_add, increment, full_increment
  , subtract, full_subtract, negate, decrement, full_decrement
  , multiply, full_multiply
  , div2n1n, div_mod, divide, modulo, divides
  , eea, bezout, cofactors, gcd, lcm
  , is_zero, is_one
  , le, lt
  , min, max, median
  , msb, lsb
  , absolute_value, sign
  ) where

import Prelude hiding ( Word, drop, take, not, and, or, last
                      , subtract, negate, min, max, gcd, lcm
                      )
import Data.Type.Equality ((:~:)(Refl))

import Simplicity.Programs.Bit
import Simplicity.Programs.Word
import Simplicity.Term.Core hiding (one)
import Simplicity.Ty.Word

-- | Simplicity expression for the constant function that returns the representation of 0.
--
-- @
-- 'fromWord' w ('zero' w _) == 0
-- @
zero :: Core term => Word a -> term () a
zero = low

-- | Simplicity expression for the constant function that returns the representation of 1.
--
-- @
-- 'fromWord' w ('one' w _) == 1
-- @
one :: (Core term, TyC a) => Word a -> term () a
one w = true >>> left_pad_low word1 w

-- | Simplicity expression for computing the sum of two words and a carry input bit, including the carry output bit.
--
-- @
-- 'fromWord1' cout * 2 ^ 'wordSize' w + 'fromWord' w z == 'fromWord' w x + 'fromWord' w y + 'fromWord1' cin
--  where
--   (cout, z) = 'full_add' w (cin, (x, y))
-- @
full_add :: Core term => Word a -> term (Bit, (a, a)) (Bit, a)
full_add SingleV = maj &&& xor3
full_add (DoubleV w) = drop (ooh &&& ioh) &&& (oh &&& drop (oih &&& iih) >>> rec)
                   >>> iih &&& (ioh &&& oh >>> rec)
                   >>> ioh &&& (iih &&& oh)
 where
  rec = full_add w

-- | Simplicity expression for computing the sum of two words, including the carry bit.
--
-- @
-- 'fromWord1' c * 2 ^ 'wordSize' w + 'fromWord' w z == 'fromWord' w x + 'fromWord' w y
--  where
--   (c, z) = 'add' w (x, y)
-- @
add :: (Core term, TyC a) => Word a -> term (a, a) (Bit, a)
add w = false &&& iden >>> full_add w

-- | Simplicity expression for computing the sum a words and a bit, including the carry bit.
--
-- @
-- 'fromWord1' c * 2 ^ 'wordSize' w + 'fromWord' w z == 'fromWord1' x + 'fromWord' w y
--  where
--   (c, z) = 'full_increment' w (x, y)
-- @
full_increment :: (Core term, TyC a) => Word a -> term (Bit, a) (Bit, a)
full_increment w = oh &&& (ih &&& (unit >>> zero w)) >>> full_add w

-- | Simplicity expression for incrementing a word, including the carry bit.
--
-- @
-- 'fromWord1' c * 2 ^ 'wordSize' w + 'fromWord' w y == 1 + 'fromWord' w x
--  where
--   (c, y) = 'increment' w x
-- @
increment :: (Core term, TyC a) => Word a -> term a (Bit, a)
increment w = true &&& iden >>> full_increment w

-- | Simplicity expression for computing the difference of two words and a borrow input bit, also returning the borrow output bit.
--
-- @
-- 'fromWord' w z == 'fromWord1' bout * 2 ^ 'wordSize' w + 'fromWord' w x - 'fromWord' w y - 'fromWord1' bin
--  where
--   (bout, z) = 'full_subtract' w (bin, (x, y))
-- @
full_subtract :: (Core term, TyC a) => Word a -> term (Bit, (a, a)) (Bit, a)
full_subtract w = not oh &&& drop (oh &&& (ih >>> complement w))
              >>> full_add w
              >>> not oh &&& ih

-- | Simplicity expression for computing the difference of two words, also returning the borrow bit.
--
-- @
-- 'fromWord' w z == 'fromWord1' b * 2 ^ 'wordSize' w + 'fromWord' w x - 'fromWord' w y
--  where
--   (b, z) = 'subtract' w (x, y)
-- @
subtract :: (Core term, TyC a) => Word a -> term (a, a) (Bit, a)
subtract w = false &&& iden >>> full_subtract w

-- | Simplicity expression for negating a word, also returning the borrow bit.
--
-- @
-- 'fromWord' w y == 'fromWord1' b * 2 ^ 'wordSize' w - 'fromWord' w x
--  where
--   (b, y) = 'negate' w x
-- @
negate :: (Core term, TyC a) => Word a -> term a (Bit, a)
negate w = (unit >>> zero w) &&& iden >>> subtract w

-- | Simplicity expression for subtracting a bit from a word, also returning the borrow bit.
--
-- @
-- 'fromWord' w z == 'fromWord1' b * 2 ^ 'wordSize' w + 'fromWord' w y - 'fromWord1' x
--  where
--   (b, z) = 'full_decrement' w (x, y)
-- @
full_decrement :: (Core term, TyC a) => Word a -> term (Bit, a) (Bit, a)
full_decrement w = oh &&& (ih &&& (unit >>> zero w)) >>> full_subtract w

-- | Simplicity expression for decrementing a a word, also returning the borrow bit.
--
-- @
-- 'fromWord' w y == 'fromWord1' b * 2 ^ 'wordSize' w + 'fromWord' w x - 1
--  where
--   (b, y) = 'decrement' w x
-- @
decrement :: (Core term, TyC a) => Word a -> term a (Bit, a)
decrement w = true &&& iden >>> full_decrement w

-- | A Simplicity expression that helps compute products of larger word sizes from smaller word sizes.
--
-- @
-- 'fromWord' ('DoubleV' w) ('full_multiply' w ((a, b), (c, d))) == 'fromWord' w a * 'fromWord' w b  + 'fromWord' w c + 'fromWord' w d
-- @
full_multiply :: (Core term, TyC a) => Word a -> term ((a, a), (a, a)) (a, a)
full_multiply SingleV = take (cond iden false) &&& ih
                    >>> full_add SingleV
full_multiply (DoubleV w) = take (ooh &&& (ioh &&& oih))
                        &&& ((take (ooh &&& iih) &&& drop (ooh &&& ioh) >>> rec)
                        &&& (take (oih &&& iih) &&& drop (oih &&& iih) >>> rec))
                        >>> take (oh &&& ioh)
                        &&& (drop (ooh &&& iih) &&& (oih &&& drop (oih &&& ioh) >>> rec))
                        >>> (oh &&& drop (ioh &&& ooh) >>> rec) &&& drop (iih &&& oih)
 where
  rec = full_multiply w

-- | Simplicity expression for computing the product of two words, returning a doubled size word.
--
-- @
-- 'fromWord' ('DoubleV' w) ('multiply' w (x, y)) == 'fromWord' w x * 'fromWord' w y
-- @
multiply :: (Core term, TyC a) => Word a -> term (a, a) (a, a)
multiply w = iden &&& (unit >>> zero (DoubleV w)) >>> full_multiply w

-- | Test if a word is zero.
--
-- @
-- 'fromBit' ('is_zero' w x) == ('fromWord' w x == 0)
-- @
is_zero :: (Core term, TyC a) => Word a -> term a Bit
is_zero w = not (some w)

-- | Test if a word is one.
--
-- @
-- 'fromBit' ('is_one' w x) == ('fromWord' w x == 1)
-- @
is_one :: (Core term, TyC a) => Word a -> term a Bit
is_one w = decrement w >>> drop (is_zero w)

-- | Test if a word is less than another
--
-- @
-- 'fromBit' ('lt' w (x, y)) == ('fromWord' w x < 'fromWord' w y)
-- @
lt :: (Core term, TyC a) => Word a -> term (a,a) Bit
lt w = subtract w >>> oh

-- | Test if a word is less than or equal to another
--
-- @
-- 'fromBit' ('le' w (x, y)) == ('fromWord' w x <= 'fromWord' w y)
-- @
le :: (Core term, TyC a) => Word a -> term (a,a) Bit
le w = not (ih &&& oh >>> lt w)

-- | Compute the minimum of two words.
--
-- @
-- 'fromWord' w ('min' w (x, y)) == 'Prelude.min' ('fromWord' w x) ('fromWord' w y)
-- @
min :: (Core term, TyC a) => Word a -> term (a,a) a
min w = le w &&& iden >>> cond oh ih

-- | Compute the maximum of two words.
--
-- @
-- 'fromWord' w ('max' w (x, y)) == 'Prelude.max' ('fromWord' w x) ('fromWord' w y)
-- @
max :: (Core term, TyC a) => Word a -> term (a,a) a
max w = le w &&& iden >>> cond ih oh

-- | Compute the median of three words.
--
-- @
-- 'fromWord' w ('median' w (x, (y, z))) == 'sort' ['fromWord' w x,  'fromWord' w y, 'fromWord' w z] !! 1
-- @
median :: (Core term, TyC a) => Word a -> term (a, (a, a)) a
median w = ((oh &&& ioh >>> min w) &&& (oh &&& iih >>> min w) >>> max w)
           &&& drop (min w) >>> max w

-- | Return the most significant bit of a word.
--
-- @
-- 'fromBit' ('msb' w x) == (2 ^ ('wordSize' w - 1) <= 'fromWord' w x)
-- @
msb :: (Core term, TyC a) => Word a -> term a Bit
msb w = leftmost w

-- | Return the least significant bit of a word.
--
-- @
-- 'fromBit' ('lsb' w x) == odd ('fromWord' w x)
-- @
lsb :: (Core term, TyC a) => Word a -> term a Bit
lsb w = rightmost w

-- div3n2n (((a1,a2),a3), (b1,b2))
-- precondition
-- * [a1,a2,a3] < [b1,b2,0]
-- * 1000... <= [b1,b2]
-- postcondtion:
-- * div3n2n (((a1,a2),a3), (b1,b2)) = ([a1,a2,a3]/[b1,b2], [a1,a2,a3]%[b1,b2])
div3n2n :: (Core term, TyC a) => Word a -> term (((a, a), a), (a, a)) (a, (a, a))
div3n2n w = (ooh &&& ioh >>> approxDiv) &&& (oih &&& ih)
        >>> body
 where
  approxDiv = (ooh &&& ih >>> lt w) &&& iden >>> cond lt_case eq_case
  lt_case = false &&& div2n1n w
  eq_case = oih &&& ih >>> add w >>> oh &&& ((unit >>> high w) &&& ih)
  body = ooh &&& (((oiih &&& ioh) &&& (oioh &&& iiih >>> multiply w) >>> subtract (DoubleV w)) &&& (oioh &&& iih))
      >>> cond overflow loop0
  overflow = ioh &&& oih
  loop0 = ooh &&& (oih &&& ih) >>> cond loop1 (ioh &&& oh)
  loop1 = (oh &&& iih >>> add2w) &&& drop ((take (dec >>> ih)) &&& ih)
       >>> ooh &&& (oih &&& ih)
       >>> cond (ioh &&& oh) loop2
  loop2 = drop (take (dec >>> ih)) &&& (oh &&& iih >>> add2w >>> ih)
  dec = decrement w
  add2w = add (DoubleV w)

-- | A Simplicity expression that helps compute the division of words.
--
-- @
-- When 'fromWord' ('DoubleV' w) a < 2^'wordSize' w * 'fromWord' w b
-- and 2^('wordSize' w - 1) <= 'fromWord' w b
-- then 'fromWord' w (fst ('div2n1n' w (a, b))) == div ('fromWord' ('DoubleV' w) a) ('fromWord' w b)
-- and 'fromWord' w (snd ('div2n1n' w (a, b))) == mod ('fromWord' ('DoubleV' w) a) ('fromWord' w b)
-- otherwise
-- 'div2n1n' w (a, b) == 'Simplicity.Programs.Word.high' ('DoubleV' w) ()
-- @
div2n1n :: (Core term, TyC a) => Word a -> term ((a, a), a) (a, a)
div2n1n SingleV = oih &&& or ooh (not ih) >>> or oh ih &&& ih
div2n1n (DoubleV w) = conditions &&& iden >>> cond body (unit >>> high (DoubleV (DoubleV w)))
 where
  body = ((ooh &&& oioh) &&& ih >>> rec) &&& (oiih &&& ih)
     >>> ooh &&& ((oih &&& ioh) &&& iih >>> rec)
     >>> (oh &&& ioh) &&& iih
  rec = div3n2n w
  conditions = and (drop (msb (DoubleV w))) (ooh &&& ih >>> lt (DoubleV w))

-- Given a two words x and y, with x twice as wide as y, peform a left shift of both words by equal amounts until the msb of y becomes set.
divPreShift :: (Core term, TyC a) => Word b -> Vector b a -> term ((a, a), a) ((a, a), a)
divPreShift SingleV _ = iden
divPreShift (DoubleV w) v = drop (leftmost v' >>> is_zero w) &&& iden >>> cond shift iden >>> divPreShift w v'
 where
  v' = vectorComp vector2 v
  shift = (oh &&& zv >>> full_shift (DoubleV (vectorComp w v')) w >>> ih)
      &&& (ih &&& zv >>> full_shift (vectorComp w v') w >>> ih)
  zv = unit >>> zero w

-- Given a two words x and y, peform a right shift of the first word and a left shift of the second word by the same abount until the msb of y becomes set.
divPostShift :: (Core term, TyC a) => Word b -> Vector b a -> term (a, a) (a, a)
divPostShift SingleV _ = iden
divPostShift (DoubleV w) v = drop (leftmost v' >>> is_zero w) &&& iden >>> cond shift iden >>> divPostShift w v'
 where
  v' = vectorComp vector2 v
  shift = (zv &&& oh >>> full_shift w (vectorComp w v') >>> oh)
      &&& (ih &&& zv >>> full_shift (vectorComp w v') w >>> ih)
  zv = unit >>> zero w

-- | Divide two words, also returning the remainder.
--
-- @
-- 'fromWord' w (fst ('div_mod' w (x, 'zero' w))) == 0
--   && 'fromWord' w (snd ('div_mod' w (x, 'zero' w))) == 'fromWord' w x
--
-- 'fromWord' w (fst ('div_mod' w (x, y))) == div ('fromWord' w x) ('fromWord' w y)
--   && 'fromWord' w (snd ('div_mod' w (x, y))) == mod ('fromWord' w x) ('fromWord' w y)
--  when
--   'fromWord' w y != 0
-- @
div_mod :: (Core term, TyC a) => Word a -> term (a, a) (a, a)
div_mod w = (drop (is_zero w)) &&& iden
        >>> cond zero_case div_case
 where
  zero_case = ih &&& oh
  div_case = (((unit >>> zero w) &&& oh) &&& ih >>> divPreShift w SingleV >>> div2n1n w) &&& ih
         >>> ooh &&& (oih &&& ih >>> divPostShift w SingleV >>> oh)

-- | Divide two words.
--
-- @
-- 'fromWord' w ('divide' w (x, 'zero' w)) == 0
--
-- 'fromWord' w ('divide' w (x, y)) == div ('fromWord' w x) ('fromWord' w y)
--  when
--   'fromWord' w y != 0
-- @
divide :: (Core term, TyC a) => Word a -> term (a, a) a
divide w = div_mod w >>> oh

-- | Compute the remainder after dividing two words.
--
-- @
-- 'fromWord' w ('modulo' w (x, 'zero' w)) == 'fromWord' w x
--
-- 'fromWord' w ('modulo' w (x, y)) == mod ('fromWord' w x) ('fromWord' w y)
--  when
--   'fromWord' w y != 0
-- @
modulo :: (Core term, TyC a) => Word a -> term (a, a) a
modulo w = div_mod w >>> ih

-- | Check if one word divides another
--
-- @
-- 'fromBit' ('divides' w ('zero' w, y)) == True
--
-- 'fromBit' ('divides' w (x, y)) == (mod ('fromWord' w y) ('fromWord' w x) == 0)
--  when
--   'fromWord' w x != 0
-- @
divides :: (Core term, TyC a) => Word a -> term (a, a) Bit
divides w = ih &&& oh >>> modulo w >>> is_zero w

-- A single step of the extened eucliean algorithm.
-- Given a matrix
--  [ a -b | c ]
--  [ -d e | f ]
-- Then subtract either the largest possible multiple of the second row from the first such that c remains positive
-- or the largest possible multiple of the first row from the second such that f remains positive.
-- If either c of f is zero then this results in no change.
eeaStep :: (Core term, TyC a) => Word a -> term (((a,a), a), ((a,a),a)) (((a,a), a), ((a,a),a))
eeaStep w = (iih &&& oih >>> lt w) &&& iden
        >>> cond (step &&& ih) (oh &&& (ih &&& oh >>> step))
 where
  step = (oih &&& iih >>> div_mod w) &&& (ooh &&& ioh)
     >>> (((ooh &&& iioh) &&& (iooh &&& (unit >>> zero w)) >>> full_multiply w >>> ih)
      &&& ((ooh &&& iiih) &&& (ioih &&& (unit >>> zero w)) >>> full_multiply w >>> ih))
     &&& oih

-- Repeat eeaStep 2^wordsize (v :: Word b) many times..
eeaStep_iterate :: forall term a b. (Core term, TyC a) => Word a -> Word b -> term (((a,a), a), ((a,a),a)) (((a,a), a), ((a,a),a))
eeaStep_iterate w = go
 where
  go :: forall b. Word b -> term (((a,a), a), ((a,a),a)) (((a,a), a), ((a,a),a))
  go SingleV = base >>> base
   where
    base = eeaStep w
  go (DoubleV d) = rec >>> rec
   where
    rec = go d

-- | Compute the results of the extended euclidan algorithm.
--
-- @
-- 'eea' (x, y) == (('bezout' (x, y), 'cofactors' (x, y)), 'gcd' (x, y))
-- @
eea :: (Core term, TyC a) => Word a -> term (a, a) ((Either (a, a) (a, a), (a, a)), a)
eea w = pre >>> eeaStep_iterate w w >>> post
 where
  o = (unit >>> one w)
  z = (unit >>> zero w)
  pre = ((o &&& z) &&& oh) &&& ((z &&& o) &&& ih)
  post = drop (drop (is_zero w)) &&& iden
     >>> cond ((injl ooh &&& ioh) &&& oih)
              ((injr ioh &&& ooh) &&& iih)

-- | Compute minimal bezout coeffecients of two words.
--
-- @
--  'fromWord' w cx * 'fromWord' w x - 'fromWord' w cy * 'fromWord' w y == Prelude.gcd ('fromWord' w x) ('fromWord' w y)
--  when
--   Left (cx, cy) = 'bezout' w (x, y)
--
--  'fromWord' w cy * 'fromWord' w y - 'fromWord' w cx * 'fromWord' w x == Prelude.gcd ('fromWord' w x) ('fromWord' w y)
--  when
--   Right (cx, cy) = 'bezout' w (x, y)
-- @
bezout :: (Core term, TyC a) => Word a -> term (a, a) (Either (a, a) (a, a))
bezout w = eea w >>> ooh

-- | Compute the cofactors of two words.
--
-- @
-- 'fromWord' w cx * d == 'fromWord' w x
--   && 'fromWord' w cy * d == 'fromWord' w y y
--  where
--   (cx, cy) = 'cofactors' w (x, y)
--   d = Prelude.gcd ('fromWord' w x) ('fromWord' w y)
-- @
cofactors :: (Core term, TyC a) => Word a -> term (a, a) (a, a)
cofactors w = eea w >>> take (drop (ih &&& oh))

-- | Compute the greatest common divisor of two words.
--
-- @
-- 'fromWord' w ('gcd' w (x, y)) == 'Prelude.gcd' ('fromWord' w x) ('fromWord' w y)
-- @
gcd :: (Core term, TyC a) => Word a -> term (a, a) a
gcd w = eea w >>> ih

-- | Compute the least common multiple of two words.
--
-- @
-- 'fromWord' (DoubleV w) ('lcm' w (x, y)) == 'Prelude.lcm' ('fromWord' w x) ('fromWord' w y)
-- @
lcm :: (Core term, TyC a) => Word a -> term (a, a) (a,a)
lcm w = (cofactors w >>> oh) &&& ih >>> multiply w

-- | Compute the absolute value of a signed word.
--
-- @
-- 'fromWord' w ('absolute_value' w x) == 'abs' ('fromInt' w x)
-- @
absolute_value :: (Core term, TyC a) => Word a -> term a a
absolute_value w = msb w &&& iden
               >>> cond (negate w >>> ih) iden

-- | Compute the sign value of a signed word as a 2-bit value.
--
-- @
-- 'fromInt2' ('sign' w x) == 'signum' ('fromInt' w x)
-- @
sign :: (Core term, TyC a) => Word a -> term a Word2
sign w = msb w &&& some w
