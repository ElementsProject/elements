module Simplicity.LibSecp256k1.Spec
 ( FE(..), _fe, fe, unrepr, feZero, bigZero, feOne
 , GEJ(..), _gej, gej, _x, _y, _z
 , GE(..)
 , Scalar(..), scalarUnrepr, scalarZero
 , normalizeWeak, normalize, fePack, feUnpack
 , feIsZero, neg, mulInt, add, mul, sqr, inv, sqrt, (.+.), (.*.)
 , double, offsetPoint, offsetPointZinv
 , eqXCoord, hasQuadY
 , scalarNegate
 , wnaf, ecMult
 , XOnlyPubKey(..), pkPoint
 , Sig(..), sigUnpack
 , schnorr
 ) where

import Prelude hiding (sqrt)
import Control.Monad (guard)
import Control.Monad.Trans.State (state, evalState)
import Data.Bits ((.&.), (.|.), complement, shiftL, shiftR, testBit)
import Data.ByteString.Short (ShortByteString, pack)
import qualified Data.ByteString.Char8 as BSC
import Data.Ix (inRange)
import Data.List (mapAccumL, mapAccumR, unfoldr)
import Data.Maybe (isJust)
import Data.Serialize (put)
import Data.Serialize.Put (putShortByteString, runPut)
import qualified Data.Vector as V
import Lens.Family2 ((^.), (^..), (&), (+~), (*~), (%~), over, review, under, zipWithOf)
import Lens.Family2.Stock (_1, lend_)

import Simplicity.Digest
import Simplicity.LibSecp256k1.Schnorr
import Simplicity.Word

infixl 7 .*.
infixl 6 .+.

horner :: Integral a => [a] -> Integer -> Integer
horner [] _ = 0
horner (c0:cs) x = toInteger c0 + x * horner cs x

data FE = FE !Word32
             !Word32
             !Word32
             !Word32
             !Word32
             !Word32
             !Word32
             !Word32
             !Word32
             !Word32
  deriving Show

repr :: FE -> Integer
repr a = horner (a^.._fe) (2^26) `mod` 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

unrepr :: Integer -> FE
unrepr n = FE a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
 where
  a0:a1:a2:a3:a4:a5:a6:a7:a8:a9:_ = fromInteger <$> unfoldr (\x -> Just (swap (x `divMod` (2^26)))) (n `mod` 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F)
  swap (x,y) = (y,x)

-- FE has a traversal.
_fe :: Applicative f => (Word32 -> f Word32) -> FE -> f FE
_fe = under fe

-- FE has both a traversal and a grate.
fe :: (Functor g, Applicative f) => (g Word32 -> f Word32) -> g FE -> f FE
fe f a = FE <$> p 0 <*> p 1 <*> p 2 <*> p 3 <*> p 4 <*> p 5 <*> p 6 <*> p 7 <*> p 8 <*> p 9
 where
  p i = f ((! i) <$> a)

(!) :: FE -> Int -> Word32
(FE a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) ! 0 = a0
(FE a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) ! 1 = a1
(FE a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) ! 2 = a2
(FE a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) ! 3 = a3
(FE a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) ! 4 = a4
(FE a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) ! 5 = a5
(FE a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) ! 6 = a6
(FE a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) ! 7 = a7
(FE a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) ! 8 = a8
(FE a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) ! 9 = a9
(FE a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) ! _ = 0

feZero :: FE
feZero = review (over fe) 0

feOne :: FE
feOne = FE 1 0 0 0 0 0 0 0 0 0

feSeven :: FE
feSeven = FE 7 0 0 0 0 0 0 0 0 0

bigZero :: FE
bigZero = FE 0x3FFFC2F 0x3FFFFBF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x03FFFFF

reduce :: Word32 -> FE -> FE
reduce x a =
  FE (ts'!!0) (ts'!!1) (ts'!!2) (ts'!!3) (ts'!!4) (ts'!!5) (ts'!!6) (ts'!!7) (ts'!!8) t9'
 where
  (t9',ts') = mapAccumL f t0 ts
   where
    t0 = a!0 + x * 0x3D1
    ts = (a!1 + (x * (2^6))):[a!i | i <- [2..8]]++[a!9 `mod` (2^22)]
    f t t' = (t `divMod` (2^26)) & _1 +~ t'

normalizeWeak :: FE -> FE
normalizeWeak a = reduce (a!9 `div` (2^22)) a

normalize :: FE -> FE
normalize a | more = FE r0 r1 r2 r3 r4 r5 r6 r7 r8 (r9 `mod` (2^22))
            | otherwise = a'
 where
  a' = normalizeWeak a
  more = testBit (a'!9) 22
      || (a'!9 == 0x03FFFFF && all (\i -> a'!i == 0x3FFFFFF) [2..8]
          && a'!1 + 0x40 + ((a'!0 + 0x3D1) `div` (2^26)) > 0x3FFFFFF)
  (FE r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) = reduce 1 a'

fePack :: FE -> ShortByteString
fePack (FE a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) = pack [fromInteger (n `div` (2^(8*i))) |i <- [31,30..0]]
 where
  n = horner [ a0 .&. 0x3FFFFFF
             , a1 .&. 0x3FFFFFF
             , a2 .&. 0x3FFFFFF
             , a3 .&. 0x3FFFFFF
             , a4 .&. 0x3FFFFFF
             , a5 .&. 0x3FFFFFF
             , a6 .&. 0x3FFFFFF
             , a7 .&. 0x3FFFFFF
             , a8 .&. 0x3FFFFFF
             , a9 .&. 0x03FFFFF
             ] (2^26)

feUnpack :: Word256 -> FE
feUnpack a = FE (fromIntegral $ a .&. 0x3FFFFFF)
                (fromIntegral $ (a `shiftR` 26) .&. 0x3FFFFFF)
                (fromIntegral $ (a `shiftR` (2*26)) .&. 0x3FFFFFF)
                (fromIntegral $ (a `shiftR` (3*26)) .&. 0x3FFFFFF)
                (fromIntegral $ (a `shiftR` (4*26)) .&. 0x3FFFFFF)
                (fromIntegral $ (a `shiftR` (5*26)) .&. 0x3FFFFFF)
                (fromIntegral $ (a `shiftR` (6*26)) .&. 0x3FFFFFF)
                (fromIntegral $ (a `shiftR` (7*26)) .&. 0x3FFFFFF)
                (fromIntegral $ (a `shiftR` (8*26)) .&. 0x3FFFFFF)
                (fromIntegral $ a `shiftR` (9*26))

feIsZero :: FE -> Bool
feIsZero a = na^.._fe `elem` [feZero^.._fe, bigZero^.._fe]
 where
  na = normalizeWeak a

-- First argument will be statically known.
neg :: Word32 -> FE -> FE
neg m = zipWithOf (over fe) (-) (mulInt (2*(m+1)) bigZero)

-- First argument will be statically known.
mulInt :: Word32 -> FE -> FE
mulInt m = _fe *~ m

add :: FE -> FE -> FE
add = zipWithOf (over fe) (+)

sum19 :: (Int -> Word64) -> FE
sum19 p =
  FE r0 r1 r2 (r!!3) (r!!4) (r!!5) (r!!6) (r!!7) (r!!8) r9
 where
  (d,(t9:u)) = mapAccumL (f 26) 0 [p i | i <- [9..18]]
  (c,r) =  mapAccumL (f 26) 0 $ zipWith3 g [p i | i <- [0..8]] u (0:u)
  (c',r9) = f 22 (fromIntegral t9) (c + d*fromIntegral k0 + wideMul (last u) k1)
  c'' = c' + d * (fromIntegral k1 * (2^4))
  (d0,r0) = f 26 0 (fromIntegral (r!!0) + c'' * fromIntegral (k0 `div` (2^4)))
  (d1,r1) = f 26 d0 (fromIntegral (r!!1) + c'' * fromIntegral (k1 `div` (2^4)))
  r2 = r!!2 + (fromIntegral d1)
  f :: Int -> Word64 -> Word64 -> (Word64,Word32)
  f n a pi = (q, fromIntegral r)
   where
    (q,r) = (a + pi) `divMod` (2^n)
  g :: Word64 -> Word32 -> Word32 -> Word64
  g pi ui ui' = pi + wideMul k0 ui + wideMul k1 ui'
  k0, k1 :: Word32
  k0 = 0x3D10
  k1 = 0x400

mul :: FE -> FE -> FE
mul a b = sum19 p
 where
  p i = sum [wideMul (a ! j) (b ! (i - j)) | j <- [0..9]]

sqr :: FE -> FE
sqr a = sum19 p
 where
  f x y = wideMul (2*x) y
  p i = sum [f (a ! j) (a ! (i - j)) | j <- [0..top]] + remainder
   where
    top = (i - 1) `div` 2
    remainder | odd i = 0
              | otherwise = let x = a ! (top + 1) in wideMul x x

wideMul :: Word32 -> Word32 -> Word64
wideMul a b = (fromIntegral a) * (fromIntegral b)

tower :: FE -> (FE,FE)
tower a = (x2, foldr ($) t1 (replicate 5 sqr))
 where
  x2 = sqr a .*. a
  x3 = sqr x2 .*. a
  x6 = foldr ($) x3 (replicate 3 sqr) .*. x3
  x9 = foldr ($) x6 (replicate 3 sqr) .*. x3
  x11 = foldr ($) x9 (replicate 2 sqr) .*. x2
  x22 = foldr ($) x11 (replicate 11 sqr) .*. x11
  x44 = foldr ($) x22 (replicate 22 sqr) .*. x22
  x88 = foldr ($) x44 (replicate 44 sqr) .*. x44
  x176 = foldr ($) x88 (replicate 88 sqr) .*. x88
  x220 = foldr ($) x176 (replicate 44 sqr) .*. x44
  x223 = foldr ($) x220 (replicate 3 sqr) .*. x3
  t1 = foldr ($) x223 (replicate 23 sqr) .*. x22

inv :: FE -> FE
inv a = t4
 where
  (x2, t1') = tower a
  t2 = t1' .*. a
  t3 = foldr ($) t2 (replicate 3 sqr) .*. x2
  t4 = foldr ($) t3 (replicate 2 sqr) .*. a

sqrt :: FE -> Maybe FE
sqrt a | feIsZero (neg 1 t4 .+. a) = Just t3
       | otherwise = Nothing
 where
  (x2, t1') = tower a
  t2 = sqr t1' .*. x2
  t3 = sqr (sqr t2)
  t4 = sqr t3

isQuad :: FE -> Bool
isQuad = isJust . sqrt

(.+.) = add
(.*.) = mul

data GEJ = GEJ !FE !FE !FE
  deriving Show

-- GEJ has a traversal.
_gej :: Applicative f => (FE -> f FE) -> GEJ -> f GEJ
_gej = under gej

-- GEJ has both a traversal and a grate.
gej :: (Functor g, Applicative f) => (g FE -> f FE) -> g GEJ -> f GEJ
gej f a = GEJ <$> f ((^._x) <$> a)
              <*> f ((^._y) <$> a)
              <*> f ((^._z) <$> a)

_x f (GEJ x y z) = (\x -> GEJ x y z) <$> f x
_y f (GEJ x y z) = (\y -> GEJ x y z) <$> f y
_z f (GEJ x y z) = (\z -> GEJ x y z) <$> f z

isInf :: GEJ -> Bool
isInf a = feIsZero (a^._z)

double :: GEJ -> GEJ
double a | isInf a = mempty
         | otherwise = GEJ x y z
 where
  z = mulInt 2 (a^._z .*. a^._y)
  t1 = mulInt 3 (sqr (a^._x))
  t2 = sqr t1
  t3 = mulInt 2 (sqr (a^._y))
  t4 = mulInt 2 (sqr t3)
  t3' = t3 .*. (a^._x)
  x = neg 4 (mulInt 4 t3') .+. t2
  y = t1 .*. (mulInt 6 t3' .+. neg 1 t2) .+. neg 2 t4

instance Semigroup GEJ where
  (<>) = mappend

instance Monoid GEJ where
  mempty = GEJ feOne feOne feZero
  mappend a b | isInf a = b
              | isInf b = a
              | isZeroH && isZeroI = double a
              | isZeroH = mempty
              | otherwise = GEJ x y z
   where
    z22 = sqr (b^._z)
    z12 = sqr (a^._z)
    u1 = a^._x .*. z22
    u2 = b^._x .*. z12
    s1 = (a^._y .*. z22) .*. b^._z
    s2 = (b^._y .*. z12) .*. a^._z
    h = neg 1 u1 .+. u2
    i = neg 1 s1 .+. s2
    isZeroH = feIsZero h
    isZeroI = feIsZero i
    i2 = sqr i
    h2 = sqr h
    h3 = h .*. h2
    zr = h .*. b^._z
    z = a^._z .*. zr
    t = u1 .*. h2
    x = neg 3 (mulInt 2 t .+. h3) .+. i2
    y = ((neg 5 x .+. t) .*. i) .+. (neg 1 (h3 .*. s1))

eqXCoord :: FE -> GEJ -> Bool
eqXCoord x a = feIsZero $ neg 1 (sqr (a^._z) .*. x) .+. normalizeWeak (a^._x)

hasQuadY :: GEJ -> Bool
hasQuadY a@(GEJ _ y z) | isInf a = False
                       | otherwise = isQuad (y .*. z)

data GE = GE !FE !FE -- Infinity not included.
        deriving Show

offsetPoint :: GEJ -> GE -> (FE, GEJ)
a `offsetPoint` (GE bx by) | isInf a = (feZero, GEJ bx by feOne)
                           | isZeroH && isZeroI = (doublerz, double a)
                           | isZeroH = (feZero, mempty)
                           | otherwise = (h, GEJ x y z)
 where
  doublerz = mulInt 2 s1
  z12 = sqr (a^._z)
  u1 = normalizeWeak $ a^._x
  u2 = bx .*. z12
  s1 = normalizeWeak $ a^._y
  s2 = (by .*. z12) .*. a^._z
  h = neg 1 u1 .+. u2
  i = neg 1 s1 .+. s2
  isZeroH = feIsZero h
  isZeroI = feIsZero i
  i2 = sqr i
  h2 = sqr h
  h3 = h .*. h2
  z = a^._z .*. h
  t = u1 .*. h2
  x = neg 3 (mulInt 2 t .+. h3) .+. i2
  y = ((neg 5 x .+. t) .*. i) .+. (neg 1 (h3 .*. s1))

offsetPointZinv :: GEJ -> GE -> FE -> GEJ
offsetPointZinv a (GE bx by) bzinv | isInf a = GEJ (bx .*. bzinv2) (by .*. bzinv3) feOne
                                   | isZeroH && isZeroI = double a
                                   | isZeroH = mempty
                                   | otherwise = GEJ x y z
 where
  az = a^._z .*. bzinv
  z12 = sqr az
  u1 = normalizeWeak $ a^._x
  u2 = bx .*. z12
  s1 = normalizeWeak $ a^._y
  s2 = (by .*. z12) .*. az
  h = neg 1 u1 .+. u2
  i = neg 1 s1 .+. s2
  isZeroH = feIsZero h
  isZeroI = feIsZero i
  i2 = sqr i
  h2 = sqr h
  h3 = h .*. h2
  z = a^._z .*. h
  t = u1 .*. h2
  x = neg 3 (mulInt 2 t .+. h3) .+. i2
  y = ((neg 5 x .+. t) .*. i) .+. (neg 1 (h3 .*. s1))
  bzinv2 = sqr bzinv
  bzinv3 = bzinv2 .*. bzinv

pointNegate :: GE -> GE
pointNegate (GE x y) = GE x (neg 1 . normalizeWeak $ y)

scalarModulus :: Word256
scalarModulus = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

newtype Scalar = Scalar Word256 deriving (Eq, Ord, Show)

instance Bounded Scalar where
  minBound = Scalar 0
  maxBound = Scalar $ scalarModulus - 1

scalarUnrepr :: Integer -> Scalar
scalarUnrepr x = Scalar $ fromInteger (x `mod` toInteger scalarModulus)

scalarValid :: Scalar -> Bool
scalarValid x = x <= maxBound

scalarZero :: Scalar
scalarZero = Scalar 0

scalarIsZero :: Scalar -> Bool
scalarIsZero (Scalar a) = a==0

scalarNegate :: Scalar -> Scalar
scalarNegate a@(Scalar 0) = a
scalarNegate (Scalar a) = Scalar $ scalarModulus - a

scalarMult :: Scalar -> GEJ -> GEJ
scalarMult na a = ecMult a na scalarZero

ecMult :: GEJ -> Scalar -> Scalar -> GEJ
ecMult a na ng = foldr f mempty (zipEx wnafa (wnaf wg ng)) & _z %~ (.*. globalZ)
 where
  wa = 5
  wnafa = wnaf wa na
  (tableA, globalZ) | null wnafa = (V.empty, feOne)
                    | otherwise = scalarTable wa a
  f (Nothing, Nothing) r0 = double r0
  f (Just x, Nothing) r0 | x >= 0 = snd $ f (Nothing, Nothing) r0 `offsetPoint` (tableA V.! x)
                         | otherwise = snd $ f (Nothing, Nothing) r0 `offsetPoint` pointNegate (tableA V.! complement x)
  f (x, Just y) r0 | y >= 0 = offsetPointZinv (f (x, Nothing) r0) (lookupG y) globalZ
                   | otherwise = offsetPointZinv (f (x, Nothing) r0) (pointNegate (lookupG (complement y))) globalZ
  zipEx [] [] = []
  zipEx [] bs = map (\b -> (Nothing,b)) bs
  zipEx as [] = map (\a -> (a,Nothing)) as
  zipEx (a:as) (b:bs) = (a,b) : zipEx as bs
  lookupG n = norm $ scalarMult (Scalar (fromIntegral (2*n+1))) g
  norm p = GE (normalize (p^._x .*. zinv2)) (normalize (p^._y .*. zinv3))
   where
    zinv = inv (p^._z)
    zinv2 = sqr zinv
    zinv3 = zinv2 .*. zinv

wnaf :: Int -> Scalar -> [Maybe Int]
wnaf w s@(Scalar ws) = post $ go False [] (s'^..lend_)
 where
  hibit = last (ws^..lend_)
  (Scalar s') | hibit = scalarNegate s
              | otherwise = s
  post | hibit = fmap (fmap complement)
       | otherwise = id
  go :: Bool -> [Maybe Int] -> [Bool] -> [Maybe Int]
  go _ _ [] = []
  go carry acc (bit:bits) | bit == carry = go carry (Nothing:acc) bits
  go carry acc bits = acc ++ (Just word') : go carry' (replicate (w-1) Nothing) post
   where
    (pre,post) = splitAt w bits
    word = foldr (\x y -> y*2 + if x then 1 else 0) 0 (tail pre)
    carry' = testBit word (w-2)
    word' = word - if carry' then 2^(w-1) else 0

-- a must not be infinity
scalarTable :: Int -> GEJ -> (V.Vector GE, FE)
scalarTable w a = (V.fromList r, globalZ)
 where
  d = double a
  len = 2^(w-2)
  l = take len $ iterate (\p -> offsetPoint (snd p) (GE (d^._x) (d^._y))) (error "scalarTable: Impossible to access", a')
   where
    z0 = d^._z
    z2 = sqr z0
    z3 = z2 .*. z0
    a' = a & _x %~ (.*. z2)
           & _y %~ (.*. z3)
  (Right (globalZ, _), r) = mapAccumR acc (Left (d^._z)) l
  acc (Left z0) (zr, b) = (Right (b^._z .*. z0, zr), GE (b^._x) (b^._y))
  acc (Right (globalZ, z0)) (zr, b) = (Right (globalZ, z0 .*. zr), GE (b^._x .*. z2) (b^._y .*. z3))
   where
    z2 = sqr z0
    z3 = z2 .*. z0

g :: GEJ
g = GEJ (unrepr 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798) (unrepr 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8) feOne

wg = 16
tableG = t & traverse %~ norm
 where
  (t,z) = scalarTable wg g
  zinv = inv z
  zinv2 = sqr zinv
  zinv3 = zinv2 .*. zinv
  norm (GE x y) = GE (normalize (x .*. zinv2)) (normalize (y .*. zinv3))

pkPoint :: XOnlyPubKey -> Maybe GEJ
pkPoint (XOnlyPubKey px) = do
  let x = feUnpack px
  guard $ (normalize x^.._fe) == (x^.._fe)
  y <- normalize <$> sqrt (sqr x .*. x .+. feSeven)
  return $ GEJ x y feOne

sigUnpack :: Sig -> Maybe (FE, Scalar)
sigUnpack (Sig r0 s0) = do
  guard $ (normalize r^.._fe) == (r^.._fe)
  guard $ scalarValid s
  return (r, s)
 where
  r = feUnpack r0
  s = Scalar s0

schnorr :: XOnlyPubKey  -- ^ public key
        -> Hash256      -- ^ message
        -> Sig          -- ^ signature
        -> Bool
schnorr pk m sg = Just () == do
  p <- pkPoint pk
  (rx, s) <- sigUnpack sg
  let tag = bsHash (BSC.pack "BIPSchnorr")
  let h = bsHash . runPut $ put tag >> put tag >> putShortByteString (fePack rx) >> put pk >> put m
  let nege = scalarNegate . scalarUnrepr . integerHash256 $ h
  let r = ecMult p nege s
  guard $ hasQuadY r
  guard $ eqXCoord rx r
