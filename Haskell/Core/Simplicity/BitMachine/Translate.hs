-- | This module implements naive translation of Simplicity terms to Bit Machine 'MachineCode'.
module Simplicity.BitMachine.Translate
 ( Translation, translate
 ) where

import Data.Proxy (Proxy(..))

import Simplicity.BitMachine
import Simplicity.BitMachine.Ty
import Simplicity.Delegator.Impl
import Simplicity.Term.Core

-- | @'Translation' a b@ is the data type for the Simplicity algebra used for translating terms to 'MachineCode'
newtype Translation a b = Translation MachineCodeK

translate0 :: Translation a b -> MachineCode
translate0 (Translation f) = f end

-- | 'translate' coverts a Simplicity term to the Bit Machine's 'MachineCode'.
--
-- Simplicity terms are represented in tagless-final style, so any Simplicity term can be instantiated as @'Translation' a b@ and can be passed to the 'translate' function.
translate :: Delegator Translation a b -> MachineCode
translate = translate0 . runDelegator

-- Below is the Simplicity algebra that implements naive translation to 'MachineCodeK'.
instance Core Translation where
  iden = result
   where
    a = reifyProxy result
    result = Translation
           $ copy (bitSizeR a)

  comp arrS@(Translation s) (Translation t) =
    Translation
    $ newFrame (bitSizeR b)
    . s
    . moveFrame
    . t
    . dropFrame
   where
    b = reifyProxy arrS

  unit = Translation nop

  injl (Translation t) = result
   where
    proxyB :: arr a (Either b c) -> Proxy b
    proxyB _ = Proxy
    proxyC :: arr a (Either b c) -> Proxy c
    proxyC _ = Proxy
    pad = padLR (reifyProxy (proxyB result)) (reifyProxy (proxyC result))
    result = Translation
           $ write False
           . skip pad
           . t

  injr (Translation t) = result
   where
    proxyB :: arr a (Either b c) -> Proxy b
    proxyB _ = Proxy
    proxyC :: arr a (Either b c) -> Proxy c
    proxyC _ = Proxy
    pad = padRR (reifyProxy (proxyB result)) (reifyProxy (proxyC result))
    result = Translation
           $ write True
           . skip pad
           . t

  match (Translation s) (Translation t) = result
   where
    result = Translation $ bump padl s ||| bump padr t
    proxy :: arr (Either a b, c) d -> (Proxy a, Proxy b)
    proxy _ = (Proxy, Proxy)
    a = reifyProxy . fst $ proxy result
    b = reifyProxy . snd $ proxy result
    padl = 1 + padLR a b
    padr = 1 + padRR a b

  pair (Translation s) (Translation t) =
   Translation $ s . t

  take (Translation t) = Translation t

  drop (Translation t) = result
   where
    proxyA :: arr (a, b) c -> Proxy a
    proxyA _ = Proxy
    bs = bitSizeR (reifyProxy (proxyA result))
    result = Translation
           $ bump bs t

instance Assert Translation where
  assertl (Translation s) _ = result
   where
    result = Translation $ bump padl s ||| abort
    proxy :: arr (Either a b, c) d -> (Proxy a, Proxy b)
    proxy _ = (Proxy, Proxy)
    a = reifyProxy . fst $ proxy result
    b = reifyProxy . snd $ proxy result
    padl = 1 + padLR a b

  assertr _ (Translation t) = result
   where
    result = Translation $ abort ||| bump padr t
    proxy :: arr (Either a b, c) d -> (Proxy a, Proxy b)
    proxy _ = (Proxy, Proxy)
    a = reifyProxy . fst $ proxy result
    b = reifyProxy . snd $ proxy result
    padr = 1 + padRR a b

  fail _ = Translation $ abort
