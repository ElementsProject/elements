{-# LANGUAGE NoMonomorphismRestriction #-}
-- | This module defines the term language for 'Core' Simplicity using
-- tagless-final style, plus a few extensions: 'Assert', 'Witness' and 'Delegate'.
module Simplicity.Term.Core
 ( module Simplicity.Ty
 , Core(..)
 , elimS, copair
 , swapP, swapS
 -- * Notation for 'Core' terms
 , (>>>), (&&&)
 -- | The following expressions are for short sequences of 'take' and 'drop', with 'iden' that is used to access components of Simplicity inputs.
 --
 -- * @o@ means 'take'
 -- * @i@ means 'drop'
 -- * @h@ means 'iden'
 --
 -- For example, @'oih' = 'take' ('drop' 'iden')@.
 --
 -- The string of @i@'s and @o@'s is meant to resemble a binary number that denotes an index to the leaves of a perfect binary tree.
 , oh, ih, ooh, oih, ioh, iih, oooh, ooih, oioh, oiih, iooh, ioih, iioh, iiih
 -- * Language extensions
 , Assert(..), fail0
 , Witness(..)
 , Delegate(..)
 ) where

import Prelude hiding (take, drop, fail)

import Control.Arrow (Kleisli(..))
import Control.Monad ((>=>))
import qualified Control.Monad.Fail as Fail

import Simplicity.Digest
import Simplicity.Tensor
import Simplicity.Ty
import Simplicity.Ty.Word

-- | Values of type @forall term. 'Core' term => term a b@ are well-typed terms of the core Simplicity language represented in tagless-final style.
--
-- Functions that consume terms in this style are defined by creating instances of the 'Core' class.
-- These instances are called /Simplicity Algebras/.
class Core term where
  iden :: TyC a => term a a
  comp :: (TyC a, TyC b, TyC c) => term a b -> term b c -> term a c
  unit :: TyC a => term a ()
  injl :: (TyC a, TyC b, TyC c) => term a b -> term a (Either b c)
  injr :: (TyC a, TyC b, TyC c) => term a c -> term a (Either b c)
  -- | Because @case@ is a reserved word in Haskell, we will be calling Simplicity's @case@ combinator 'match' instead.
  match :: (TyC a, TyC b, TyC c, TyC d) => term (a, c) d -> term (b, c) d -> term (Either a b, c) d
  pair :: (TyC a, TyC b, TyC c) => term a b -> term a c -> term a (b, c)
  take :: (TyC a, TyC b, TyC c) => term a c -> term (a, b) c
  drop :: (TyC a, TyC b, TyC c) => term b c -> term (a, b) c

-- | Natural deduction style elimination rule for Sums.
elimS :: (Core term, TyC a, TyC b, TyC c, TyC d) => term a (Either b c) -> term b d -> term c d -> term a d
elimS r s t = r &&& unit >>> match (take s) (take t)

-- | Categorical dual of 'pair'
copair :: (Core term, TyC a, TyC b, TyC c) => term a c -> term b c -> term (Either a b) c
copair = elimS iden

-- | Term for swapping positions in products (Commutativity of Multiplication): A * B |- B * A
swapP :: (Core term, TyC a, TyC b) => term (a, b) (b, a)
swapP = pair (drop iden) (take iden)

-- | Term for swapping positions in sums (Commutativity of Addition): A + B |- B + A
swapS :: (Core term, TyC a, TyC b) => term (Either a b) (Either b a)
swapS = copair (injr iden) (injl iden)

-- same precidence as in Control.Category.
infixr 1 >>>

-- | @s '>>>' t = 'comp' s t@
(>>>) :: (Core term, TyC a, TyC b, TyC c) => term a b -> term b c -> term a c
(>>>) = comp

-- same precidence as in Control.Arrow.
infixr 3 &&&

-- | @s '&&&' t = 'pair' s t@
(&&&) :: (Core term, TyC a, TyC b, TyC c) => term a b -> term a c -> term a (b, c)
(&&&) = pair

oh :: (Core term, TyC x, TyC b) => term (x, b) x
oh = take iden

ih :: (Core term, TyC a, TyC x) => term (a, x) x
ih = drop iden

ooh :: (Core term, TyC x, TyC b, TyC c) => term ((x, b), c) x
ooh = take oh

oih :: (Core term, TyC a, TyC x, TyC c) => term ((a, x), c) x
oih = take ih

ioh :: (Core term, TyC a, TyC x, TyC c) => term (a, (x, c)) x
ioh = drop oh

iih :: (Core term, TyC a, TyC b, TyC x) => term (a, (b, x)) x
iih = drop ih

oooh :: (Core term, TyC x, TyC b, TyC c, TyC d) => term (((x, b), c), d) x
oooh = take ooh

ooih :: (Core term, TyC a, TyC x, TyC c, TyC d) => term (((a, x), c), d) x
ooih = take oih

oioh :: (Core term, TyC a, TyC x, TyC c, TyC d) => term ((a, (x, c)), d) x
oioh = take ioh

oiih :: (Core term, TyC a, TyC b, TyC x, TyC d) => term ((a, (b, x)), d) x
oiih = take iih

iooh :: (Core term, TyC a, TyC x, TyC c, TyC d) => term (a, ((x, c), d)) x
iooh = drop ooh

ioih :: (Core term, TyC a, TyC b, TyC x, TyC d) => term (a, ((b, x), d)) x
ioih = drop oih

iioh :: (Core term, TyC a, TyC b, TyC x, TyC d) => term (a, (b, (x, d))) x
iioh = drop ioh

iiih :: (Core term, TyC a, TyC b, TyC c, TyC x) => term (a, (b, (c, x))) x
iiih = drop iih

instance Core (->) where
  iden = id
  comp s t = t . s
  unit = const ()
  injl t a = Left (t a)
  injr t a = Right (t a)
  match s _ (Left a, c)  = s (a, c)
  match _ t (Right b, c) = t (b, c)
  pair s t a = (s a, t a)
  take t (a, _) = t a
  drop t (_, b) = t b

-- | The Monad 'm' should be a commutative, idempotent monad.
instance Monad m => Core (Kleisli m) where
  iden = Kleisli $ return
  comp (Kleisli s) (Kleisli t) = Kleisli $ s >=> t
  unit = Kleisli $ const (return ())
  injl (Kleisli t) = Kleisli $ \a -> Left <$> t a
  injr (Kleisli t) = Kleisli $ \a -> Right <$> t a
  match (Kleisli s) (Kleisli t) = Kleisli $ go
   where
    go (Left a, c)  = s (a, c)
    go (Right b, c) = t (b, c)
  pair (Kleisli s) (Kleisli t) = Kleisli $ \a -> (,) <$> s a <*> t a
  take (Kleisli t) = Kleisli $ \(a, _) -> t a
  drop (Kleisli t) = Kleisli $ \(_, b) -> t b

-- | This class extends the 'Core' Simplicity language with two assertion expressions.
-- These expressions are use for assertions and for pruning 'match' (case) expressions.
-- This extension produces partial functions.
class Core term => Assert term where
  assertl :: (TyC a, TyC b, TyC c, TyC d) => term (a, c) d -> Hash256 -> term (Either a b, c) d
  assertr :: (TyC a, TyC b, TyC c, TyC d) => Hash256 -> term (b, c) d -> term (Either a b, c) d
  fail :: (TyC a, TyC b) => Block512 -> term a b

-- | A canonical version of the 'fail' combinator with the 'Block512' set to 0.
fail0 :: (Assert term, TyC a, TyC b) => term a b
fail0 = fail (hash0, hash0)

-- | The Monad 'm' should be a commutative, idempotent monad with a zero that is both a left and right zero.
instance Fail.MonadFail m => Assert (Kleisli m) where
  assertl (Kleisli s) _ = Kleisli $ go
   where
    go (Left a, c)  = s (a, c)
    go (Right _, _) = Fail.fail "Simplicity.Term.Core: assertl failed"
  assertr _ (Kleisli t) = Kleisli $ go
   where
    go (Left _, _)  = Fail.fail "Simplicity.Term.Core: assertr failed"
    go (Right b, c) = t (b, c)
  fail _ = Kleisli . const $ Fail.fail "Simplicity.Term.Core: fail"

-- | This class adds 'witness' expressions to the Simplicity language.
class Witness term where
  -- | The 'witness' expression denotes a constant function, however this value is not committed to the 'Simplicity.MerkleRoot.CommitmentRoot'.
  -- Compare this to 'Simplicity.Programs.Generic.scribe' which does commit to its value.
  --
  -- @witness v _ = v@
  witness :: (TyC a, TyC b) => b -> term a b

instance Witness (->) where
  witness = const

instance Monad m => Witness (Kleisli m) where
  witness = Kleisli . const . return

-- | This class adds 'disconnect' expressions to the Simplicity language, which can be used for delegation.
class Delegate term where
  disconnect :: (TyC a, TyC b, TyC c, TyC d) => term (Word256, a) (b, c) -> term c d -> term a (b, d)

instance (Core p, Core q) => Core (Product p q) where
  iden = Product iden iden
  comp ~(Product rs fs) ~(Product rt ft) = Product (comp rs rt) (comp fs ft)
  unit = Product unit unit
  injl ~(Product rt ft) = Product (injl rt) (injl ft)
  injr ~(Product rt ft) = Product (injr rt) (injr ft)
  match ~(Product rs fs) ~(Product rt ft) = Product (match rs rt) (match fs ft)
  pair ~(Product rs fs) ~(Product rt ft) = Product (pair rs rt) (pair fs ft)
  take ~(Product rt ft) = Product (take rt) (take ft)
  drop ~(Product rt ft) = Product (drop rt) (drop ft)

instance (Assert p, Assert q) => Assert (Product p q) where
  assertl ~(Product rs fs) t = Product (assertl rs t) (assertl fs t)
  assertr s ~(Product rt ft) = Product (assertr s rt) (assertr s ft)
  fail b = Product (fail b) (fail b)

instance (Witness p, Witness q) => Witness (Product p q) where
  witness b = Product (witness b) (witness b)

instance (Delegate p, Delegate q) => Delegate (Product p q) where
  disconnect ~(Product rs fs) ~(Product rt ft) = Product (disconnect rs rt) (disconnect fs ft)

instance Core Unit where
  iden = Unit
  comp _ _ = Unit
  unit = Unit
  injl _ = Unit
  injr _ = Unit
  match _ _ = Unit
  pair _ _ = Unit
  take _ = Unit
  drop _ = Unit

instance Assert Unit where
  assertl _ _ = Unit
  assertr _ _ = Unit
  fail _ = Unit

instance Witness Unit where
  witness _ = Unit

instance Delegate Unit where
  disconnect _ _ = Unit
