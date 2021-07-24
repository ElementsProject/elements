-- | This module defines the 'Bit' type alais used in Simplicity.
module Simplicity.Ty.Bit
 ( Bit, fromBit, toBit
 ) where

-- | Simplicity types are composed from @()@, 'Either' and @(,)@.
-- We cannot use Haskell's 'Bool' type directly in Simplicity.
-- Instead we create use this isomorphic type in Simplicity to represent bits.
type Bit = Either () ()

-- | Canonically convert a Simplicty 'Bit' type to the Haskell 'Bool' type.
fromBit :: Bit -> Bool
fromBit (Left ()) = False
fromBit (Right ()) = True

-- | Canonically convert a Hasekll 'Bool' type to the Simplicity 'Bit' type.
toBit :: Bool -> Bit
toBit False = Left ()
toBit True = Right ()
