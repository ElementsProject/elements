-- | This module implements naive translation of Simplicity terms to Bit Machine 'MachineCode'.
module Simplicity.BitMachine.Translate
 ( Translation
 , translate
 ) where

import Data.Proxy (Proxy(..))

import Simplicity.BitMachine
import Simplicity.BitMachine.Ty
import Simplicity.Term.Core

-- | @'Translation' a b@ is the data type for the Simplicity algebra used for translating terms to 'MachineCode'
newtype Translation a b = Translation MachineCodeK

-- | 'translate' coverts a Simplicity term to the Bit Machine's 'MachineCode'.
--
-- Simplicity terms are represented in tagless-final style, so any Simplicity term can be instantiated as @'Translation' a b@ and can be passed to the 'translate' function.
translate :: Translation a b -> MachineCode
translate (Translation f) = f end

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

  match arrS@(Translation s) arrT@(Translation t) =
    Translation $ bump padl s ||| bump padr t
   where
    proxy :: arr (a,b) d -> Proxy b
    proxy _ = Proxy
    b = reifyProxy (proxy arrS)
    c = reifyProxy (proxy arrT)
    padl = 1 + padLR b c
    padr = 1 + padRR b c

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
