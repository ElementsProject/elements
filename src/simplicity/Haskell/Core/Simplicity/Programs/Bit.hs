-- | This module defines Simplicity combinators and expressions that operate on bits.
module Simplicity.Programs.Bit
 ( module Simplicity.Ty.Bit
 , false, true
 , cond, ch, assert
 , not, and, or, xor
 , xor3, maj
 ) where

import Prelude hiding (drop, take, not, and, or)

import Simplicity.MerkleRoot
import Simplicity.Ty.Bit
import Simplicity.Term.Core

-- | Simplicity expression always returns the zero bit.
--
-- @'false' = 'Simplicity.Programs.Generic.scribe' ('toBit' 'False')@
false :: (Core term, TyC a) => term a Bit
false = injl unit

-- | Simplicity expression always returns the one bit.
--
-- @'true' = 'Simplicity.Programs.Generic.scribe' ('toBit' 'True')@
true :: (Core term, TyC a) => term a Bit
true = injr unit

-- | Simplicity's if-then-else combinator.
--
-- @
-- 'cond' t _ ('toBit' 'True', a) = t a
--
-- 'cond' _ e ('toBit' 'False', a) = e a
-- @
cond :: (Core term, TyC a, TyC b) => term a b -> term a b -> term (Bit, a) b
cond thn els = match (drop els) (drop thn)

-- | Simplicity expression that chooses from a pair of values.
--
-- @
-- 'ch' ('toBit' 'True', (a, _)) = a
--
-- 'ch' ('toBit' 'False', (_, b)) = b
-- @
ch :: (Core term, TyC a) => term (Bit, (a, a)) a
ch = cond oh ih

-- | Requires the bit produced by @t@ to be 'true' and fails otherwise.
assert :: (Assert term, TyC a) => term a Bit -> term a ()
assert t = t &&& unit
       >>> assertr cmrFail0 unit

-- | Simplicity combinator that computes inverts the Bit result of an expression.
not :: (Core term, TyC a) => term a Bit -> term a Bit
not t = t &&& unit >>> cond false true

-- | Simplicity combinator that computes the short-circut conjunction of the results of two expressions.
and :: (Core term, TyC a) => term a Bit -> term a Bit -> term a Bit
and s t = s &&& iden >>> cond t false

-- | Simplicity combinator that computes the short-circut disjunction of the results of two expressions.
or :: (Core term, TyC a) => term a Bit -> term a Bit -> term a Bit
or s t = s &&& iden >>> cond true t

-- | Simplicity expression that returns the three-way xor of three bits.
xor :: (Core term, TyC a) => term a Bit -> term a Bit -> term a Bit
xor s t = s &&& iden >>> cond (not t) t

-- | Simplicity expression that returns the three-way xor of three bits.
xor3 :: Core term => term (Bit, (Bit, Bit)) Bit
xor3 = cond (cond iden (not iden)) (cond (not iden) iden)

-- | Simplicity expression that returns the majority value of three bits.
maj :: Core term => term (Bit, (Bit, Bit)) Bit
maj = cond (cond true iden) (cond iden false)
