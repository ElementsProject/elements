module Simplicity.Word
  ( Word256, Word64, Word32, Word16, Word8
  , showHex256
  ) where

import Data.Bits
import Data.Ix
import Data.Serialize
import Data.Word (Word8, Word16, Word32, Word64)
import Numeric (showHex)
import Foreign.Ptr (castPtr)
import Foreign.Storable
import Lens.Family2 ((&), (%~))
import Lens.Family2.Stock (_1, both_, mapped)

-- | 256-bit unsigned integer type
data Word256 = Word256 !Word64 !Word64 !Word64 !Word64 deriving (Bounded, Eq, Ord)

liftUnary op x = fromInteger (op (toInteger x))
liftBinary op x y = fromInteger (op (toInteger x) (toInteger y))
pointwiseUnary op (Word256 a3 a2 a1 a0) = Word256 (op a3) (op a2) (op a1) (op a0)
pointwiseBinary op (Word256 a3 a2 a1 a0) (Word256 b3 b2 b1 b0) = Word256 (op a3 b3) (op a2 b2) (op a1 b1) (op a0 b0)

instance Show Word256 where
  showsPrec p a = showsPrec p (toInteger a)

instance Read Word256 where
  readsPrec p s = readsPrec p s & mapped._1 %~ fromInteger

instance Num Word256 where
  (+) = liftBinary (+)
  (-) = liftBinary (-)
  (*) = liftBinary (*)
  negate = liftUnary negate
  abs = id
  signum = liftUnary signum
  fromInteger i = Word256 (fromInteger a3) (fromInteger a2) (fromInteger a1) (fromInteger i)
   where
    a1 = i `div` (2^64)
    a2 = a1 `div` (2^64)
    a3 = a2 `div` (2^64)

instance Real Word256 where
  toRational a = toRational (toInteger a)

instance Integral Word256 where
  quot = liftBinary quot
  rem = liftBinary rem
  div = liftBinary div
  mod = liftBinary mod
  quotRem a b = quotRem (toInteger a) (toInteger b) & both_ %~ fromInteger
  divMod a b = divMod (toInteger a) (toInteger b) & both_ %~ fromInteger
  toInteger (Word256 a3 a2 a1 a0) = toInteger a0 + 2^64*(toInteger a1 + 2^64*(toInteger a2 + 2^64*toInteger a3))

instance Enum Word256 where
  succ a | a == maxBound = error "Enum.succ{Word256}: tried to take `succ' of maxBound"
         | otherwise = liftUnary succ a
  pred a | a == minBound = error "Enum.pred{Word256}: tried to take `pred' of minBound"
         | otherwise = liftUnary pred a
  toEnum i = fromInteger (toEnum i)
  fromEnum a = fromEnum (toInteger a)
  enumFrom a = enumFromTo a maxBound
  enumFromThen a b | a <= b = enumFromThenTo a b maxBound
                   | otherwise = enumFromThenTo a b minBound
  enumFromTo a b = fromInteger <$> enumFromTo (toInteger a) (toInteger b)
  enumFromThenTo a b c = fromInteger <$> enumFromThenTo (toInteger a) (toInteger b) (toInteger c)

instance Ix Word256 where
  range (a,b) = enumFromTo a b
  index (a,b) c = index (toInteger a, toInteger b) (toInteger c)
  inRange (a,b) c = a <= c && c <= b
  rangeSize (a,b) = rangeSize (toInteger a, toInteger b)

instance Bits Word256 where
  (.&.) = pointwiseBinary (.&.)
  (.|.) = pointwiseBinary (.|.)
  xor = pointwiseBinary xor
  complement = pointwiseUnary complement
  shift a i = liftUnary (flip shift i) a
  rotate a i = shiftL a i' .|. shiftR a (256-i')
   where
    i' = i `mod` 256
  zeroBits = fromInteger 0
  bit = bitDefault
  testBit a = testBit (toInteger a)
  bitSizeMaybe = Just . finiteBitSize
  bitSize = finiteBitSize
  isSigned _ = False
  popCount (Word256 a3 a2 a1 a0) = popCount a3 + popCount a2 + popCount a1 + popCount a0

instance FiniteBits Word256 where
  finiteBitSize _ = 4*64
  countLeadingZeros (Word256 0 0 0 a0) = 3*64 + countLeadingZeros a0
  countLeadingZeros (Word256 0 0 a1 _) = 2*64 + countLeadingZeros a1
  countLeadingZeros (Word256 0 a2 _ _) = 64 + countLeadingZeros a2
  countLeadingZeros (Word256 a3 _ _ _) = countLeadingZeros a3
  countTrailingZeros (Word256 a3 0 0 0) = 3*64 + countTrailingZeros a3
  countTrailingZeros (Word256 _ a2 0 0) = 2*64 + countTrailingZeros a2
  countTrailingZeros (Word256 _ _ a1 0) = 64 + countTrailingZeros a1
  countTrailingZeros (Word256 _ _ _ a0) = countTrailingZeros a0

instance Serialize Word256 where
  put (Word256 a3 a2 a1 a0) = put a3 >> put a2 >> put a1 >> put a0
  get = Word256 <$> get <*> get <*> get <*> get

-- | Show a Word256 value as a hex string padded with leading zeros.
showHex256 :: Word256 -> String
showHex256 w = replicate (64 - length hexStr) '0' ++ hexStr
 where
  hexStr = showHex w ""
