-- | This module implements tail call optimized translation of Simplicity terms to Bit Machine 'MachineCode'.
module Simplicity.BitMachine.Translate.TCO
 ( Translation, translate
 ) where

import Data.Proxy (Proxy(..))

import Simplicity.BitMachine
import Simplicity.BitMachine.Ty
import Simplicity.Delegator.Impl
import Simplicity.Term.Core

-- | @'Translation' a b@ is the data type for the Simplicity algebra used for translating terms to 'MachineCode'
data Translation a b = Translation { tcoOn :: MachineCodeK
                                   , tcoOff :: MachineCodeK
                                   }

translate0 :: Translation a b -> MachineCode
translate0 trans = tcoOff trans end

-- | 'translate' coverts a Simplicity term to the Bit Machine's 'MachineCode' with tail call optimization.
--
-- Simplicity terms are represented in tagless-final style, so any Simplicity term can be instantiated as @'Translation' a b@ and can be passed to the 'translate' function.
translate :: Delegator Translation a b -> MachineCode
translate = translate0 . runDelegator

-- Below is the Simplicity algebra that implements TCO translation to 'MachineCodeK'.
-- Every term has two translations, one with TCO-on and one with TOC-off.
-- The two translations are mutually recursive, which is why the are computed together in this Simplicity algebra.
instance Core Translation where
  iden = result
   where
    a = reifyProxy result
    result = Translation
           { tcoOn  = copy (bitSizeR a)
                    . dropFrame
           , tcoOff = copy (bitSizeR a)
           }

  comp s t = Translation
    { tcoOn  = newFrame (bitSizeR b)
             . tcoOn s
             . moveFrame
             . tcoOn t
    , tcoOff = newFrame (bitSizeR b)
             . tcoOff s
             . moveFrame
             . tcoOn t
    }
   where
    b = reifyProxy s

  unit = Translation
       { tcoOn = dropFrame
       , tcoOff = nop
       }

  injl t = result
   where
    proxyB :: arr a (Either b c) -> Proxy b
    proxyB _ = Proxy
    proxyC :: arr a (Either b c) -> Proxy c
    proxyC _ = Proxy
    pad = padLR (reifyProxy (proxyB result)) (reifyProxy (proxyC result))
    result = Translation
           { tcoOn  = write False
                    . skip pad
                    . tcoOn t
           , tcoOff = write False
                    . skip pad
                    . tcoOff t
           }


  injr t = result
   where
    proxyB :: arr a (Either b c) -> Proxy b
    proxyB _ = Proxy
    proxyC :: arr a (Either b c) -> Proxy c
    proxyC _ = Proxy
    pad = padRR (reifyProxy (proxyB result)) (reifyProxy (proxyC result))
    result = Translation
           { tcoOn  = write True
                    . skip pad
                    . tcoOn t
           , tcoOff = write True
                    . skip pad
                    . tcoOff t
           }

  match s t = result
   where
    result = Translation
           { tcoOn  = (fwd padl . tcoOn s) ||| (fwd padr . tcoOn t)
           , tcoOff = bump padl (tcoOff s) ||| bump padr (tcoOff t)
           }
    proxy :: arr (Either a b, c) d -> (Proxy a, Proxy b)
    proxy _ = (Proxy, Proxy)
    a = reifyProxy . fst $ proxy result
    b = reifyProxy . snd $ proxy result
    padl = 1 + padLR a b
    padr = 1 + padRR a b

  pair s t = Translation
           { tcoOn  = tcoOff s
                    . tcoOn t
           , tcoOff = tcoOff s
                    . tcoOff t
           }

  take t = Translation
         { tcoOn  = tcoOn t
         , tcoOff = tcoOff t
         }

  drop t = result
   where
    proxyA :: arr (a, b) c -> Proxy a
    proxyA _ = Proxy
    bs = bitSizeR (reifyProxy (proxyA result))
    result = Translation
           { tcoOn  = fwd bs
                    . tcoOn t
           , tcoOff = bump bs (tcoOff t)
           }

instance Assert Translation where
  assertl s _ = result
   where
    result = Translation
           { tcoOn  = (fwd padl . tcoOn s) ||| abort
           , tcoOff = bump padl (tcoOff s) ||| abort
           }
    proxy :: arr (Either a b, c) d -> (Proxy a, Proxy b)
    proxy _ = (Proxy, Proxy)
    a = reifyProxy . fst $ proxy result
    b = reifyProxy . snd $ proxy result
    padl = 1 + padLR a b

  assertr _ t = result
   where
    result = Translation
           { tcoOn  = abort ||| (fwd padr . tcoOn t)
           , tcoOff = abort ||| bump padr (tcoOff t)
           }
    proxy :: arr (Either a b, c) d -> (Proxy a, Proxy b)
    proxy _ = (Proxy, Proxy)
    a = reifyProxy . fst $ proxy result
    b = reifyProxy . snd $ proxy result
    padr = 1 + padRR a b

  fail _  = Translation { tcoOn = abort, tcoOff = abort }
