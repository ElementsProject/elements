{-# LANGUAGE DeriveTraversable, FlexibleInstances, GADTs, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables #-}
-- | This module defines a type for Simplicity DAGs (directed acyclic graph) as well as a type checking function to convert such a DAG into a well-typed Simplicity expression.
-- The expected progression is to first run 'typeInference' on an untyped Simplicity DAG.
-- Then use the inferred type annotations to transform witness data into 'UntypedValue' using 'witnessData'.
-- Finally use 'typeCheck' to create a Simplicity expression.
module Simplicity.Inference
  (
  -- * Type checking untyped Simplicity
    typeInference
  , typeCheck
  -- * Simplicity with type annotations
  , TermF(..)
  , UntypedTermF
  , SimplicityDag
  -- *  optical (like) accessors for TermF data.
  , tyAnnotation, witnessData, jetData
  -- * Constructors for 'UntypedTermF'.
  -- | There is no @uPrim@.  You must use 'Simplicity.Inference.Prim' instead.
  , uIden, uUnit, uInjl, uInjr
  , uTake, uDrop, uComp, uCase, uPair, uDisconnect
  , uHidden, uWitness, uJet, uFail
  ) where

import Prelude hiding (fail, take, drop)

import Control.Arrow ((+++), left)
import Control.Monad (foldM)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Except (ExceptT, catchE, runExceptT, throwE)
import Control.Unification (Fallible(..), UTerm(..), (=:=), applyBindingsAll, freeVar, unfreeze)
import Control.Unification.STVar (STBinding, STVar, runSTBinding)
import Control.Unification.Types (UFailure)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Fixedpoint (Fix(..))
import Data.Sequence (Seq, (|>), (!?), empty, index, mapWithIndex, ViewR(..), viewr)
import Data.Traversable (foldMapDefault, fmapDefault)
import Data.Type.Equality ((:~:)(Refl))
import qualified Data.Vector.Unboxed as UV

import Simplicity.Digest
import Simplicity.JetType
import Simplicity.MerkleRoot
import Simplicity.Primitive
import Simplicity.Term
import Simplicity.Ty
import Simplicity.Ty.Word

-- (UTy a) is the type of Simplicity types augmented with unification variables, a.
type UTy v = UTerm TyF v

-- Convert a Simplicity type with unification variables into a regular Ty.
-- Any remaining unification variables are turned into unit types, hence the name 'unital'.
unital :: UTy v -> Ty
unital (UVar _) = one
unital (UTerm t) = Fix (unital <$> t)

-- | An open recursive type for untyped Simplicity terms with type annotations.
-- The 'ty' parameter holds the typing annotations, which can be, for example, 'Ty', or @()@ for untyped Simplicity terms without annotations.
-- The 'j' parameter holds the data held by 'Jet' nodes.
-- The 'w' parameter holds the data held by 'Witness' nodes.
-- The 'a' parameter holds the (open) recursive subexpressions.
data TermF ty j w a = Iden ty
                    | Unit ty
                    | Injl ty ty ty a
                    | Injr ty ty ty a
                    | Take ty ty ty a
                    | Drop ty ty ty a
                    | Comp ty ty ty a a
                    | Case ty ty ty ty a a
                    | Pair ty ty ty a a
                    | Disconnect ty ty ty ty a a
                    | Hidden Hash256
                    | Witness ty ty w
                    | Prim (SomeArrow Prim)
                    | Jet j
  deriving (Functor, Foldable, Traversable)

instance (Show ty, Show j, Show w, Show a) => Show (TermF ty j w a) where
  showsPrec p (Iden a) = showParen (10 < p) $ showString "Iden " . showsPrec 11 a
  showsPrec p (Unit a) = showParen (10 < p) $ showString "Unit " . showsPrec 11 a
  showsPrec p (Injl a b c t) = showParen (10 < p)
                             $ showString "Injl " . showsPrec 11 a
                             . showString " " . showsPrec 11 b
                             . showString " " . showsPrec 11 c
                             . showString " " . showsPrec 11 t
  showsPrec p (Injr a b c t) = showParen (10 < p)
                             $ showString "Injr " . showsPrec 11 a
                             . showString " " . showsPrec 11 b
                             . showString " " . showsPrec 11 c
                             . showString " " . showsPrec 11 t
  showsPrec p (Take a b c t) = showParen (10 < p)
                             $ showString "Take " . showsPrec 11 a
                             . showString " " . showsPrec 11 b
                             . showString " " . showsPrec 11 c
                             . showString " " . showsPrec 11 t
  showsPrec p (Drop a b c t) = showParen (10 < p)
                             $ showString "Drop " . showsPrec 11 a
                             . showString " " . showsPrec 11 b
                             . showString " " . showsPrec 11 c
                             . showString " " . showsPrec 11 t
  showsPrec p (Comp a b c s t) = showParen (10 < p)
                               $ showString "Comp " . showsPrec 11 a
                               . showString " " . showsPrec 11 b
                               . showString " " . showsPrec 11 c
                               . showString " " . showsPrec 11 s
                               . showString " " . showsPrec 11 t
  showsPrec p (Case a b c d s t) = showParen (10 < p)
                                 $ showString "Case " . showsPrec 11 a
                                 . showString " " . showsPrec 11 b
                                 . showString " " . showsPrec 11 c
                                 . showString " " . showsPrec 11 d
                                 . showString " " . showsPrec 11 s
                                 . showString " " . showsPrec 11 t
  showsPrec p (Pair a b c s t) = showParen (10 < p)
                               $ showString "Pair " . showsPrec 11 a
                               . showString " " . showsPrec 11 b
                               . showString " " . showsPrec 11 c
                               . showString " " . showsPrec 11 s
                               . showString " " . showsPrec 11 t
  showsPrec p (Disconnect a b c d s t) = showParen (10 < p)
                                       $ showString "Disconnect " . showsPrec 11 a
                                       . showString " " . showsPrec 11 b
                                       . showString " " . showsPrec 11 c
                                       . showString " " . showsPrec 11 d
                                       . showString " " . showsPrec 11 s
                                       . showString " " . showsPrec 11 t
  showsPrec p (Hidden h) = showParen (10 < p)
                         $ showString "Hidden " . showsPrec 11 h
  showsPrec p (Witness a b w) = showParen (10 < p)
                              $ showString "Witness " . showsPrec 11 a
                              . showString " " . showsPrec 11 b
                              . showString " " . showsPrec 11 w
  showsPrec p (Prim (SomeArrow prim)) = showParen (10 < p)
                                      $ showString "Prim "
                                      . (showParen True $ showString "someArrow " . showString (primName prim))
  showsPrec p (Jet j) = showParen (10 < p)
                      $ showString "Jet " . showsPrec 11 j

-- 'FocusTy j w a ty' is isomorphic to 'TermF ty j w a'.  Its purpose is to provide functor instances to 'TermF's ty parameter.
newtype FocusTy j w a ty = FocusTy { unFocusTy :: TermF ty j w a }

instance Functor (FocusTy j w a)  where
  fmap = fmapDefault

instance Foldable (FocusTy j w a) where
  foldMap = foldMapDefault

instance Traversable (FocusTy j w a)  where
  traverse f (FocusTy (Iden a)) = FocusTy . Iden <$> f a
  traverse f (FocusTy (Unit a)) = FocusTy . Unit <$> f a
  traverse f (FocusTy (Injl a b c x)) = fmap FocusTy $ Injl <$> f a <*> f b <*> f c <*> pure x
  traverse f (FocusTy (Injr a b c x)) = fmap FocusTy $ Injr <$> f a <*> f b <*> f c <*> pure x
  traverse f (FocusTy (Take a b c x)) = fmap FocusTy $ Take <$> f a <*> f b <*> f c <*> pure x
  traverse f (FocusTy (Drop a b c x)) = fmap FocusTy $ Drop <$> f a <*> f b <*> f c <*> pure x
  traverse f (FocusTy (Comp a b c x y)) = fmap FocusTy $ Comp <$> f a <*> f b <*> f c <*> pure x <*> pure y
  traverse f (FocusTy (Case a b c d x y)) = fmap FocusTy $ Case <$> f a <*> f b <*> f c <*> f d <*> pure x <*> pure y
  traverse f (FocusTy (Pair a b c x y)) = fmap FocusTy $ Pair <$> f a <*> f b <*> f c <*> pure x <*> pure y
  traverse f (FocusTy (Disconnect a b c d x y)) = fmap FocusTy $ Disconnect <$> f a <*> f b <*> f c <*> f d <*> pure x <*> pure y
  traverse f (FocusTy (Hidden x)) = pure (FocusTy (Hidden x))
  traverse f (FocusTy (Witness a b x)) = fmap FocusTy $ Witness <$> f a <*> f b <*> pure x
  traverse f (FocusTy (Prim p)) = pure (FocusTy (Prim p))
  traverse f (FocusTy (Jet j)) = pure (FocusTy (Jet j))

-- | A traversal of the type annotations of 'TermF'.
tyAnnotation :: Applicative f => (ty0 -> f ty1) -> TermF ty0 j w a -> f (TermF ty1 j w a)
tyAnnotation f = fmap unFocusTy . traverse f . FocusTy

-- | A Traversal-like operation for 'TermF' that can be use to modify witness data in the context of witnesses type annotations.
-- The 'witnessData' is to let you take @TermF Ty j (Vector Bool) a@ values and turn them into @TermF Ty j UntypedValue a@ values
-- by parsing witness data stored as bit vector into Simplicity values after type inference.
-- Alternatively, 'witnessData' can help build a @TermF Ty j () a -> m Bool -> m (TermF Ty j Untyped a)@ function that parses witness data
-- after type inference from a 'Bool' stream accessable via a monadic effect.
witnessData :: Applicative m => (ty -> w0 -> m w1) -> TermF ty j w0 a -> m (TermF ty j w1 a)
witnessData f (Iden a) = pure $ Iden a
witnessData f (Unit a) = pure $ Unit a
witnessData f (Injl a b c x) = pure $ Injl a b c x
witnessData f (Injr a b c x) = pure $ Injr a b c x
witnessData f (Take a b c x) = pure $ Take a b c x
witnessData f (Drop a b c x) = pure $ Drop a b c x
witnessData f (Comp a b c x y) = pure $ Comp a b c x y
witnessData f (Case a b c d x y) = pure $ Case a b c d x y
witnessData f (Pair a b c x y) = pure $ Pair a b c x y
witnessData f (Disconnect a b c d x y) = pure $ Disconnect a b c d x y
witnessData f (Hidden x) = pure $ Hidden x
witnessData f (Witness a b x) = Witness a b <$> f b x
witnessData f (Prim p) = pure $ Prim p
witnessData f (Jet p) = pure $ Jet p

-- | An (affine) traversal for the 'Jet' values of a 'TermF'.
jetData :: Applicative f => (j0 -> f j1) -> TermF ty j0 w a -> f (TermF ty j1 w a)
jetData f (Iden a) = pure $ Iden a
jetData f (Unit a) = pure $ Unit a
jetData f (Injl a b c x) = pure $ Injl a b c x
jetData f (Injr a b c x) = pure $ Injr a b c x
jetData f (Take a b c x) = pure $ Take a b c x
jetData f (Drop a b c x) = pure $ Drop a b c x
jetData f (Comp a b c x y) = pure $ Comp a b c x y
jetData f (Case a b c d x y) = pure $ Case a b c d x y
jetData f (Pair a b c x y) = pure $ Pair a b c x y
jetData f (Disconnect a b c d x y) = pure $ Disconnect a b c d x y
jetData f (Hidden x) = pure $ Hidden x
jetData f (Witness a b x) = pure $ Witness a b x
jetData f (Prim p) = pure $ Prim p
jetData f (Jet j) = Jet <$> f j

-- InferenceError holds the possible errors that can occur during the 'inference' step.
data InferenceError s = UnificationFailure (UFailure TyF (STVar s TyF))
                      | IndexError Int Integer
                      | HiddenError
                      | Overflow
                      deriving Show

instance Fallible TyF (STVar s TyF) (InferenceError s) where
  occursFailure v t = UnificationFailure (occursFailure v t)
  mismatchFailure t1 t2 = UnificationFailure (mismatchFailure t1 t2)

-- | A type synonym for Simplicity terms without type annotations.
type UntypedTermF j w a = TermF () j w a

-- Constructors for untyped 'TermF'.
uIden :: UntypedTermF j w a
uIden = Iden ()

uUnit :: UntypedTermF j w a
uUnit = Unit ()

uInjl :: a -> UntypedTermF j w a
uInjl = Injl () () ()

uInjr :: a -> UntypedTermF j w a
uInjr = Injr () () ()

uTake :: a -> UntypedTermF j w a
uTake = Take () () ()

uDrop :: a -> UntypedTermF j w a
uDrop = Drop () () ()

uComp :: a -> a -> UntypedTermF j w a
uComp = Comp () () ()

uCase :: a -> a -> UntypedTermF j w a
uCase = Case () () () ()

uPair :: a -> a -> UntypedTermF j w a
uPair = Pair () () ()

uDisconnect :: a -> a -> UntypedTermF j w a
uDisconnect = Disconnect () () () ()

uHidden :: Hash256 -> UntypedTermF j w a
uHidden = Hidden

uWitness :: w -> UntypedTermF j w a
uWitness = Witness () ()

uJet :: j -> UntypedTermF j w a
uJet = Jet

-- | :TODO: NOT YET IMPLEMENTED
uFail :: Block512 -> UntypedTermF j w a
uFail = error "uFail: :TODO: NOT YET IMPLEMENTED"

-- Given a @'UTy' v@ annonated Simplicity 'TermF', return the implied input and output types given the annotations.
termFArrow :: Monad m => TermF (UTy v) (SomeArrow j) w a -> ExceptT (InferenceError s) m (UTy v, UTy v)
termFArrow (Iden a) = return (a, a)
termFArrow (Unit a) = return (a, UTerm One)
termFArrow (Injl a b c _) = return (a, UTerm (Sum b c))
termFArrow (Injr a b c _) = return (a, UTerm (Sum b c))
termFArrow (Take a b c _) = return (UTerm (Prod a b), c)
termFArrow (Drop a b c _) = return (UTerm (Prod a b), c)
termFArrow (Comp a b c _ _) = return (a, c)
termFArrow (Case a b c d _ _) = return (UTerm (Prod (UTerm (Sum a b)) c), d)
termFArrow (Pair a b c _ _) = return (a, UTerm (Prod b c))
termFArrow (Disconnect a b c d _ _) = return (a, UTerm (Prod b d))
termFArrow (Hidden _) = throwE HiddenError
termFArrow (Witness a b _) = return (a, b)
termFArrow (Prim (SomeArrow p)) = return (unfreeze (unreflect ra), unfreeze (unreflect rb))
 where
  (ra, rb) = reifyArrow p
termFArrow (Jet (SomeArrow j)) = return (unfreeze (unreflect ra), unfreeze (unreflect rb))
 where
  (ra, rb) = reifyArrow j

-- | Simplicity terms with explicit sharing of subexpressions to form a topologically sorted DAG (directed acyclic graph).
--
-- Every node in an Simplicity expression is an element of a finitary container with indices that reference the relative locations of their child subexpressions within that container.
-- This reference is the difference in positions between refering node's position and the referred node's position.
-- The number @1@ is a reference to the immediately preciding node. The number @0@ is not allowed as it would imply a node is refering to itself.
--
-- The last element of the vector is the root of the Simplicity expression DAG.
--
-- Invariant:
--
-- @
--     0 \<= /i/ && /i/ \< 'Foldable.length' /v/ ==> 'Foldable.all' (\\x -> 0 < x && x <= /i/) ('Foldable.toList' /v/ '!!' /i/)
-- @
type SimplicityDag f ty j w = f (TermF ty j w Integer)

-- 'inference' takes a 'SimplicityDag' and adds suitiable type annotations to the nodes in the DAG as well as unification constraints.
-- This can cause unification failures, however the occurs check isn't performed in this step.
-- This function also checks that the provided DAG is sorted in topological order.
inference :: Foldable f => SimplicityDag f x (SomeArrow j) w ->
             ExceptT (InferenceError s) (STBinding s) (Seq (TermF (UTy (STVar s TyF)) (SomeArrow j) w Int))
inference = foldM loop empty
 where
  tyWord256 = unreflect (reify :: TyReflect Word256)
  loop :: Seq (TermF (UTy (STVar s TyF)) (SomeArrow j) w Int)
       -> TermF x (SomeArrow j) w Integer
       -> ExceptT (InferenceError s) (STBinding s) (Seq (TermF (UTy (STVar s TyF)) (SomeArrow j) w Int))
  loop output node = (output |>) <$> go node
   where
    fresh :: ExceptT (InferenceError s) (STBinding s) (UTy (STVar s TyF))
    fresh = UVar <$> lift freeVar
    lenOutput = length output
    lookup i | i <= toInteger (maxBound :: Int) = maybe (throwE (IndexError lenOutput i)) return (output !? (lenOutput - fromInteger i))
             | otherwise = throwE Overflow
    go (Iden _) = Iden <$> fresh
    go (Unit _) = Unit <$> fresh
    go (Injl _ _ _ it) = do
      (a,b) <- termFArrow =<< lookup it
      c <- fresh
      return (Injl a b c (fromInteger it))
    go (Injr _ _ _ it) = do
      (a,c) <- termFArrow =<< lookup it
      b <- fresh
      return (Injr a b c (fromInteger it))
    go (Take _ _ _ it) = do
      (a,c) <- termFArrow =<< lookup it
      b <- fresh
      return (Take a b c (fromInteger it))
    go (Drop _ _ _ it) = do
      (b,c) <- termFArrow =<< lookup it
      a <- fresh
      return (Drop a b c (fromInteger it))
    go (Comp _ _ _ is it) = do
      (a,b0) <- termFArrow =<< lookup is
      (b1,c) <- termFArrow =<< lookup it
      b <- b0 =:= b1
      return (Comp a b c (fromInteger is) (fromInteger it))
    go (Case _ _ _ _ is it) = do
      a <- fresh
      b <- fresh
      c <- fresh
      d <- fresh
      ignoreHidden $ do
        (ac,d0) <- termFArrow =<< lookup is
        _ <- UTerm (Prod a c) =:= ac
        _ <- d =:= d0
        return ()
      ignoreHidden $ do
        (bc,d1) <- termFArrow =<< lookup it
        _ <- UTerm (Prod b c) =:= bc
        _ <- d =:= d1
        return ()
      return (Case a b c d (fromInteger is) (fromInteger it))
     where
      ignoreHidden m = catchE m handler
       where
        handler HiddenError = return ()
        handler e = throwE e
    go (Pair _ _ _ is it) = do
      (a0,b) <- termFArrow =<< lookup is
      (a1,c) <- termFArrow =<< lookup it
      a <- a0 =:= a1
      return (Pair a b c (fromInteger is) (fromInteger it))
    go (Disconnect _ _ _ _ is it) = do
      (aw,bc) <- termFArrow =<< lookup is
      (c,d) <- termFArrow =<< lookup it
      a <- fresh
      b <- fresh
      _ <- UTerm (Prod (unfreeze tyWord256) a) =:= aw
      _ <- UTerm (Prod b c) =:= bc
      return (Disconnect a b c d (fromInteger is) (fromInteger it))
    go (Hidden h) = pure (Hidden h)
    go (Witness _ _ w) = Witness <$> fresh <*> fresh <*> pure w
    go (Prim p) = pure (Prim p)
    go (Jet j) = pure (Jet j)

-- Given the output of 'inference', execute unification and return the container of type annotated Simplicity nodes.
-- Any free type variables left over after unification are instantiated at the unit type.
-- Errors, such as unification errors or occurs errors are retuned as 'String's.
runUnification :: Traversable t => (forall s. ExceptT (InferenceError s) (STBinding s) (t (TermF (UTy (STVar s TyF)) j w i))) -> Either String (t (TermF Ty j w i))
runUnification mv = runSTBinding $ left show <$> runExceptT (bindV mv)
 where
  bindV :: Traversable t => ExceptT (InferenceError s) (STBinding s) (t (TermF (UTy (STVar s TyF)) j w i)) -> ExceptT (InferenceError s) (STBinding s) (t (TermF Ty j w i))
  bindV mv = do
    v <- mv
    bv <- applyBindingsAll (Compose (FocusTy <$> v))
    return . fmap unFocusTy . getCompose $ unital <$> bv

-- | Given a 'SimplicityDag', throw away the existing type annotations, if any, and run type inference to compute a new set of type annotations.
-- The Simplicity types, @a@ and @b@, provides further constraints for the Simplicity expression for the 'SimplicityDag'.
-- If type inference fails, such as a unification error or an occurs error, return an error message.
typeInference :: forall proxy a b f x j w. (Foldable f, TyC a, TyC b) => proxy a b -> SimplicityDag f x (SomeArrow j) w -> Either String (SimplicityDag Seq Ty (SomeArrow j) w)
typeInference p v = fmap (fmap toInteger) <$> runUnification inferenced
 where
  inferenced :: forall s. ExceptT (InferenceError s) (STBinding s) (Seq (TermF (UTy (STVar s TyF)) (SomeArrow j) w Int))
  inferenced = do
    ev <- inference v
    _ <- case viewr ev of
        EmptyR -> return ()
        _ :> end -> do
          (a1, b1) <- termFArrow end
          let (a0, b0) = reifyArrow p
          _ <- a1 =:= unfreeze (unreflect a0)
          _ <- b1 =:= unfreeze (unreflect b0)
          return ()
    return ev

-- Note: we could make a variant of this function taking a @SimplicityDag Seq Ty (SomeArrow JetSpec) UntypedValue@ argument if that is needed, where
--
-- @
--    newtype JetSpec a b = JetSpec (forall term. (Assert term, Primitive term) => term a b)
-- @
--
-- | Transform a well-typed-annotated 'SimplicityDag' into a Simplicity expression of a specified type.
--
-- 'Jet' nodes must be contain @'SomeArrow' 'jt'@ value for a 'JetType'.
-- 'Witness' nodes must contain 'UntypedValue's.
--
-- If type checking fails, return an error message.
--
-- Note: The one calling 'typeCheck' determines the input and output Simplicity types of the resulting Simplicity expression.
-- They are __not__ inferered from the DAG input.
-- Instead the types @a@ and @b@ are used as constraints during type inference.
typeCheck :: forall term jt a b. (Simplicity term, JetType jt, TyC a, TyC b) => SimplicityDag Seq Ty (SomeArrow jt) UntypedValue -> Either String (term a b)
typeCheck s = result
 where
  resultProxy = let Right x = result in undefined `asTypeOf` x
  result = case viewr typeCheckedDag of
    _ :> Right (SomeArrow t) -> maybe (error "Simplicity.Inference.typeCheck: unexpect mismatched type at end.") return $ do
                                 let (ra, rb) = reifyArrow t
                                 let (a0, b0) = reifyArrow resultProxy
                                 Refl <- equalTyReflect ra a0
                                 Refl <- equalTyReflect rb b0
                                 return t
    _ :> Left s -> Left s
    EmptyR -> Left "Simplicity.Inference.typeCheck: empty vector input."
   where
    assertEqualTyReflect a b = maybe err Right (equalTyReflect a b)
     where
      err = Left "Simplicity.Inference.typeCheck: unexpected mismatched type"
    typeCheckedDag = mapWithIndex (\i -> left (++ " at index " ++ show i ++ ".") . typeCheckTermIx i) s
    typeCheckTermIx :: Int -> TermF Ty (SomeArrow jt) UntypedValue Integer -> Either String (SomeArrow term)
    typeCheckTermIx i = typeCheckTerm . fmap fromInteger
     where
      lookup j = index typeCheckedDag (i - j)
      typeCheckTerm (Iden a) = case reflect a of
                                 SomeTy ra -> return (someArrowR ra ra iden)
      typeCheckTerm (Unit a) = case reflect a of
                                 SomeTy ra -> return (someArrowR ra OneR unit)
      typeCheckTerm (Injl a b c it) = case reflect c of
                                       SomeTy rc -> do
                                         SomeArrow t <- lookup it
                                         let (ra, rb) = reifyArrow t
                                         return (someArrowR ra (SumR rb rc) (injl t))
      typeCheckTerm (Injr a b c it) = case reflect b of
                                       SomeTy rb -> do
                                         SomeArrow t <- lookup it
                                         let (ra, rc) = reifyArrow t
                                         return (someArrowR ra (SumR rb rc) (injr t))
      typeCheckTerm (Take a b c it) = case reflect b of
                                       SomeTy rb -> do
                                         SomeArrow t <- lookup it
                                         let (ra, rc) = reifyArrow t
                                         return (someArrowR (ProdR ra rb) rc (take t))
      typeCheckTerm (Drop a b c it) = case reflect a of
                                       SomeTy ra -> do
                                         SomeArrow t <- lookup it
                                         let (rb, rc) = reifyArrow t
                                         return (someArrowR (ProdR ra rb) rc (drop t))
      typeCheckTerm (Comp a b c is it) = do SomeArrow s <- lookup is
                                            SomeArrow t <- lookup it
                                            let (ra, rb0) = reifyArrow s
                                            let (rb1, rc) = reifyArrow t
                                            Refl <- assertEqualTyReflect rb0 rb1
                                            return (someArrowR ra rc (comp s t))
      typeCheckTerm (Case a b c d is it) | Hidden hs <- index s (i - is) =
                                             case reflect a of
                                               SomeTy ra -> do
                                                 SomeArrow t <- lookup it
                                                 let (rbc, rd) = reifyArrow t
                                                 case rbc of
                                                   ProdR rb rc -> return (someArrowR (ProdR (SumR ra rb) rc) rd (assertr hs t))
                                         | Hidden ht <- index s (i - it) =
                                             case reflect b of
                                               SomeTy rb -> do
                                                 SomeArrow s <- lookup is
                                                 let (rac, rd) = reifyArrow s
                                                 case rac of
                                                   ProdR ra rc -> return (someArrowR (ProdR (SumR ra rb) rc) rd (assertl s ht))
                                         | otherwise = do SomeArrow s <- lookup is
                                                          SomeArrow t <- lookup it
                                                          let (rac0, rd0) = reifyArrow s
                                                          let (rbc1, rd1) = reifyArrow t
                                                          case (rac0, rbc1) of
                                                            (ProdR ra rc0, ProdR rb rc1) -> do
                                                              Refl <- assertEqualTyReflect rc0 rc1
                                                              Refl <- assertEqualTyReflect rd0 rd1
                                                              return (someArrowR (ProdR (SumR ra rb) rc0) rd0 (match s t))
      typeCheckTerm (Pair a b c is it) = do SomeArrow s <- lookup is
                                            SomeArrow t <- lookup it
                                            let (ra0, rb) = reifyArrow s
                                            let (ra1, rc) = reifyArrow t
                                            Refl <- assertEqualTyReflect ra0 ra1
                                            return (someArrowR ra0 (ProdR rb rc) (pair s t))
      typeCheckTerm (Disconnect a b c d is it) = do SomeArrow s <- lookup is
                                                    SomeArrow t <- lookup it
                                                    let (rc1, rd) = reifyArrow t
                                                    case reifyArrow s of
                                                      ((ProdR rw ra), (ProdR rb rc0)) -> do
                                                        Refl <- assertEqualTyReflect rw (reify :: TyReflect Word256)
                                                        Refl <- assertEqualTyReflect rc0 rc1
                                                        return (someArrowR ra (ProdR rb rd) (disconnect s t))
      typeCheckTerm (Hidden _) = Left "Simplicity.Inference.typeCheck: encountered illegal use of Hidden node"
      typeCheckTerm (Witness a b w) = case (reflect a, reflect b) of
                                       (SomeTy ra, SomeTy rb) -> do
                                        vb <- maybe err return $ castUntypedValue w
                                        return (someArrowR ra rb (witness vb))
       where
        err = Left "Simplicity.Inference.typeCheck: decode error in Witness value"
      typeCheckTerm (Prim (SomeArrow p)) = return (SomeArrow (primitive p))
      typeCheckTerm (Jet (SomeArrow j)) = return . SomeArrow $ jet (specification j)
