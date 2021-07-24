-- | This module provides the functional semantics of the full 'Simplicity' language.
-- The 'Semantics' arrow is an instance of the 'Simplicity' class and 'sem' evaluates terms of the full Simplicity langauge.
-- The 'fastEval' implements the evalutation using the jets from the specified 'JetType'.
module Simplicity.Semantics
 ( Semantics, sem
 , fastEval
 , FastEval
 , PrimEnv
 ) where

import Prelude hiding (drop, take, fail)

import Control.Arrow (Kleisli(..), first)
import Control.Monad.Reader (ReaderT(..))

import Simplicity.Delegator.Impl
import Simplicity.JetType
import Simplicity.Primitive
import Simplicity.Term

-- | The functional semantics of the full Simplicity language consists of
--
-- * Partial effect via the 'Maybe' effect.
--
-- * Environment effects via the 'Control.Monad.Reader.Reader' effect for primitives to access the 'PrimEnv'.
--
-- * Delegation via the 'Delegator' helper.
type Semantics a b = Delegator (Kleisli (ReaderT PrimEnv Maybe)) a b

-- | @
-- sem :: (forall term. Simplicity term => term a b) -> PrimEnv -> a -> Maybe b
-- @
--
-- Execute the fuctional semantics of the full Simplicity language with delegation.
sem :: Semantics a b -> PrimEnv -> a -> Maybe b
sem = flip . (runReaderT .) . runKleisli . runDelegator

instance Primitive p => Primitive (Delegator p) where
  primitive p = Delegator (primitive p) (primitive p)

instance Jet p => Jet (Delegator p) where
  jet t = Delegator (jet t) (jet t)

instance (Jet p, Witness p) => Simplicity (Delegator p) where

-- | 'fastEval' optimizes Simplicity evaluation using jets.
-- Unlike using 'Simplicity.Dag.jetSubst', 'fastEval' will not modify the commitment roots and therefore will always return the same
-- result as 'sem' in the presence of 'disconnect'.
--
-- @
-- 'fastEval' t === 'sem' t
-- @
fastEval :: FastEval jt a b -> PrimEnv -> a -> Maybe b
fastEval = sem . fastEvalSem

-- | A Simplicity instance for 'fastEval'
data FastEval jt a b = FastEval { fastEvalSem :: Semantics a b
                                , fastEvalMatcher :: Maybe (MatcherInfo jt a b)
                                }

proxyImplementation :: (JetType jt, TyC a, TyC b) => proxy jt a b -> jt a b -> PrimEnv -> a -> Maybe b
proxyImplementation _proxy = implementation

withJets :: (JetType jt, TyC a, TyC b) => FastEval jt a b -> FastEval jt a b
withJets ~fe@(FastEval ~(Delegator rs fs) jm) | Just jt <- matcher =<< jm =
  -- 'withJets' does not adjust the commitment root.
  FastEval { fastEvalSem = Delegator rs . Kleisli $ ReaderT . flip (proxyImplementation fe jt)
           , fastEvalMatcher = fastEvalMatcher fe
           }
withJets fe | otherwise = fe

mkLeaf sComb jmComb = withJets $
  FastEval { fastEvalSem = sComb
           , fastEvalMatcher = jmComb
           }

mkUnary sComb jmComb t = withJets $
  FastEval { fastEvalSem = sComb (fastEvalSem t)
           , fastEvalMatcher = jmComb <*> fastEvalMatcher t
           }
mkBinary sComb jmComb s t = withJets $
  FastEval { fastEvalSem = sComb (fastEvalSem s) (fastEvalSem t)
           , fastEvalMatcher = jmComb <*> fastEvalMatcher s <*> fastEvalMatcher t
           }

instance JetType jt => Core (FastEval jt) where
  iden = mkLeaf iden (pure iden)
  comp = mkBinary comp (pure comp)
  unit = mkLeaf unit (pure unit)
  injl = mkUnary injl (pure injl)
  injr = mkUnary injr (pure injr)
  match = mkBinary match (pure match)
  pair = mkBinary pair (pure pair)
  take = mkUnary take (pure take)
  drop = mkUnary drop (pure drop)

instance JetType jt => Assert (FastEval jt) where
  assertl s h = mkUnary (flip assertl h) (pure (flip assertl h)) s
  assertr h t = mkUnary (assertr h) (pure (assertr h)) t
  fail b = mkLeaf (fail b) (pure (fail b))

instance Witness (FastEval jt) where
  witness v =
    FastEval { fastEvalSem = witness v
             , fastEvalMatcher = Nothing
             }

instance JetType jt => Delegate (FastEval jt) where
  disconnect = mkBinary disconnect Nothing

instance JetType jt => Primitive (FastEval jt)  where
  primitive p = mkLeaf (primitive p) (pure (primitive p))

instance JetType jt => Jet (FastEval jt) where
  jet t = result
   where
    result = FastEval { fastEvalSem = Delegator (jet t) fs
                      , fastEvalMatcher = jm
                      }
    FastEval (Delegator _ fs) jm = t `asTypeOf` result

instance JetType jt => Simplicity (FastEval jt) where
