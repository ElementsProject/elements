module Simplicity.LibSecp256k1.Spec
 ( -- * Field operations.
   FE, fe, fe_repr, fe_pack
 , fe_zero, fe_one
 , fe_is_zero, fe_is_odd
 , fe_negate, fe_add, fe_multiply, fe_square, fe_invert, fe_square_root
 , (.+.), (.-.), (.*.), (.^.)
   -- * Group operations.
 , GEJ(..), _gej, gej, _x, _y, _z, g
 , gej_double, gej_add_ex
 , gej_x_equiv, gej_y_is_odd
 , gej_is_on_curve
 , GE(..)
 , gej_normalize, gej_rescale
 , gej_ge_add_ex, gej_ge_add_zinv
 , ge_negate, ge_scale_lambda
 , ge_is_on_curve
 , table, tableG, tableG128
   -- * Scalar operations
 , Scalar, scalar, scalar_repr, scalar_pack
 , scalar_zero, scalar_negate, scalar_add, scalar_square, scalar_multiply, scalar_invert, scalar_split_lambda, scalar_split_128
 , wnaf, scale, linear_combination, linear_combination_1
 , linear_check, linear_check_1
   -- * Point operations
 , Point(..), decompress, point_check
   -- * Public key / Signature operations
 , PubKey(..), pubkey_unpack, pubkey_unpack_neg
 , Sig(..), signature_unpack
 , bip0340_check
 -- * Some large integer constants for secp256k1.
 , fieldOrder, groupOrder, beta, lambda
 -- * points on other twists
 , ge_115792089237316195423570985008687907853508896131558604026424249738214906721757
 , ge_115792089237316195423570985008687907853031073199722524052490918277602762621571
 , ge_57896044618658097711785492504343953926299326406578432197819248705606044722122
 , ge_38597363079105398474523661669562635951234135017402074565436668291433169282997
 , ge_8270863516951156815969356072049136275281522608437447405948333614614684278506
 , ge_199, ge_169, ge_39, ge_14, ge_13, ge_7, ge_6, ge_3
 ) where


import Control.Monad (guard)
import Control.Monad.Trans.RWS hiding (put)
import Control.Monad.Trans.State (state, evalState)
import Control.Monad.Trans.Tardis (Tardis, getFuture, getPast, getsPast, modifyBackwards, modifyForwards, runTardis, sendFuture)
import Data.Bits ((.&.), (.|.), finiteBitSize)
import Data.ByteString.Short (ShortByteString, pack)
import qualified Data.ByteString.Char8 as BSC
import Data.Ix (inRange)
import Data.List (foldl', mapAccumL, mapAccumR, unfoldr)
import Data.Maybe (isJust)
import Data.Serialize (put)
import Data.Serialize.Put (putShortByteString, runPut)
import qualified Data.Vector as V
import Lens.Family2 ((^.), (^..), (&), (+~), (*~), (%~), allOf, over, review, under, zipWithOf)
import Lens.Family2.Stock (_1, _2, lend_, some_)

import Simplicity.Digest
import Simplicity.LibSecp256k1.Schnorr
import Simplicity.Word

infixl 6 .+., .-.
infixl 7 .*.
infixr 8 .^.

-- | The secp256k1 field is @GF[p]@ where p is this prime number.
fieldOrder :: Integer
fieldOrder = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

-- | The secp256k1 group has order @n@ where @n@ is this prime number.
groupOrder :: Integer
groupOrder = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

-- | The canonical primitive cube root of 1 in @GF[p]@.
--
-- @
--    mod (beta ^ 2 + beta + 1) fieldOrder == 0
-- @
--
-- Note that @mod (beta ^ 2) fieldOrder@ is the other, non-canonical, cube root of 1.
beta :: Integer
beta = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee

-- | The canonical primitive cube root of 1 in the scalar field @GF[n]@.
--
-- @
--    mod (lambda ^ 2 + lambda + 1) groupOrder == 0
-- @
--
-- and
--
-- @
--    'gej_normalize' ('scalar_mulitply' ('scalar' 'lambda') p) == 'GE' ('fe' 'beta' .*. x) y
--      where (x, y) = 'gej_normalize' p
-- @
--
-- Note that @mod (lambda ^ 2) groupOrder@ is the other, non-canonical, cube root of 1.
lambda :: Integer
lambda = 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72

-- | An element of secp256k1's field is represented as a normalized value.
data FE = FE { fe_pack :: Word256 -- ^ Return the normalized represenative of a field element as a 'Word256'.
             }
  deriving (Eq, Show)

-- | Return the normalized integer representative of a field element.
fe_repr :: FE -> Integer
fe_repr = toInteger . fe_pack

-- | Construct a field element from an integer.
fe :: Integer -> FE
fe n = FE . fromInteger $ n `mod` fieldOrder

-- | The zero value of the field.
fe_zero :: FE
fe_zero = fe 0

-- | The one value of the field.
fe_one :: FE
fe_one = fe 1

-- | @'fe' 7@
fe_seven :: FE
fe_seven = fe 7

-- | @'fe' 'beta'@
fe_beta :: FE
fe_beta = fe beta

-- | Decode a 256-bit word value as a field element, failing if the value is non-canonical.
fe_unpack :: Word256 -> Maybe FE
fe_unpack x0 = guard (x == fe_repr a) >> return a
 where
  x = toInteger x0
  a = fe x

-- | Checks if the field element's represenative is odd.
fe_is_odd :: FE -> Bool
fe_is_odd = odd . fe_repr

-- | Checks if the field element is 0.
fe_is_zero :: FE -> Bool
fe_is_zero = (0 ==) . fe_repr

-- | Negate a field element.
fe_negate :: FE -> FE
fe_negate = fe . negate . fe_repr

-- | Add two field elements.
fe_add :: FE -> FE -> FE
fe_add a b = fe (fe_repr a + fe_repr b)

-- | Multiply two field elements.
fe_multiply :: FE -> FE -> FE
fe_multiply a b = fe (fe_repr a * fe_repr b)

-- | Square a field element.
fe_square :: FE -> FE
fe_square a = fe_multiply a a

-- | Multiply a field element by an integer.
--
-- @
--    mulInt i a == fe i .*. a
-- @
mulInt :: Integer -> FE -> FE
mulInt i a = fe_multiply (fe i) a

-- | Add two field elements.
(.+.) = fe_add

-- | Multiply two field elements.
(.*.) = fe_multiply

-- | Difference of two field elements.
x .-. y = fe_add x (fe_negate y)

-- | A field element raised to a given power.
x .^. n = go x (n `mod` (fieldOrder - 1))
 where
  go x 0 = fe_zero
  go x 1 = x
  go x n | even n = go (fe_square x) (n `div` 2)
         | odd n = fe_multiply x (go (fe_square x) (n `div` 2))

-- | The modulular inverse of a field element, with 'fe_zero' mapping to 'fe_zero'.
fe_invert :: FE -> FE
fe_invert a = a .^. (fieldOrder - 2)

-- | A modular square root of a field element if it exists.
-- If it exists it returns a value that is itself a square.
fe_square_root :: FE -> Maybe FE
fe_square_root a | 0 == (fieldOrder + 1) `mod` 4 = do
  let res = a .^. ((fieldOrder + 1) `div` 4)
  guard $ fe_is_zero (fe_square res .-. a)
  return res

-- | Checks if a field element has a square root.
isQuad :: FE -> Bool
isQuad = isJust . fe_square_root

-- | A "compressed" point on the secp256k1 curve.  Infinity not included.
data Point = Point Bool FE

-- | A point in Jacobian coordinates.
-- A '_z' component of 'fe_zero' represents a point at infinity.
--
-- A value @p :: 'GEJ'@ where @p^.'_z'@ is not 'fe_zero' represents a point with x-coordinate @p.^'_x' .*. ('fe_invert' p.^_z) .^. 2@
-- and with y-coordinate @p.^'_y' .*. ('fe_invert' p.^_z) .^. 3@.
--
-- A canonical point has a z-component of 1, except for the point at infinity whose canonical value has all components 0.
data GEJ = GEJ !FE !FE !FE
  deriving Show

-- | A traversal of the 3 'GEJ' components.
_gej :: Applicative f => (FE -> f FE) -> GEJ -> f GEJ
_gej = under gej

-- | A grid of the 3 'GEJ' components.
gej :: (Functor g, Applicative f) => (g FE -> f FE) -> g GEJ -> f GEJ
gej f a = GEJ <$> f ((^._x) <$> a)
              <*> f ((^._y) <$> a)
              <*> f ((^._z) <$> a)

-- | A lens for the x-component of 'GEJ'.
_x :: Functor f => (FE -> f FE) -> GEJ -> f GEJ
_x f (GEJ x y z) = (\x -> GEJ x y z) <$> f x

-- | A lens for the y-component of 'GEJ'.
_y :: Functor f => (FE -> f FE) -> GEJ -> f GEJ
_y f (GEJ x y z) = (\y -> GEJ x y z) <$> f y

-- | A lens for the z-component of 'GEJ'.
_z :: Functor f => (FE -> f FE) -> GEJ -> f GEJ
_z f (GEJ x y z) = (\z -> GEJ x y z) <$> f z

-- | Checks if the point is a representation of infinity.
gej_is_infinity :: GEJ -> Bool
gej_is_infinity a = fe_is_zero (a^._z)

-- | Returns an equivalent point with the z-coefficent multiplied by the given constant.
-- This will return infinity if the constant is zero.
gej_rescale :: GEJ -> FE -> GEJ
gej_rescale (GEJ x y z) c = GEJ (x .*. c .^. 2) (y .*. c .^. 3) (z .*. c)

-- | Compute the point doubling formula for a 'GEJ'.
gej_double :: GEJ -> GEJ
gej_double a@(GEJ x y z) | gej_is_infinity a = mempty
                         | otherwise = GEJ x' y' z'
 where
  x' = mulInt 9 (x .^. 4) .+. mulInt (-8) (x .*. y .^. 2)
  y' = mulInt 36 (x .^. 3 .*. y .^. 2) .+. mulInt (-27) (x .^. 6) .+. mulInt (-8) (y .^. 4)
  z' = mulInt 2 (y .*. z)

-- | Compute the point addition formula for a 'GEJ'.
-- This also returns the ratio between z-component of 'a' and z-component of the result.
--
-- @
--    a^.'_z' .*. r = p^.'_z'
-- @
--
-- where
--
-- @
--    (r, p) = 'gej_add_ex' a b
-- @
gej_add_ex :: GEJ -> GEJ -> (FE, GEJ)
gej_add_ex a@(GEJ ax ay az) b@(GEJ bx by bz) | gej_is_infinity a = (fe_zero, GEJ bx by bz)
                                             | gej_is_infinity b = (fe_one, a)
                                             | isZeroH && isZeroI = (mulInt 2 ay, gej_double a)
                                             | isZeroH = (fe_zero, mempty)
                                             | otherwise = (bz .*. h, GEJ x y z)
 where
  u1 = ax .*. bz .^. 2
  u2 = bx .*. az .^. 2
  s1 = ay .*. bz .^. 3
  s2 = by .*. az .^. 3
  h = u2 .-. u1
  i = s2 .-. s1
  isZeroH = fe_is_zero h
  isZeroI = fe_is_zero i
  z = az .*. bz .*. h
  t = u1 .*. h .^. 2
  x = i .^. 2 .+. mulInt (-2) t .-. h .^. 3
  y = (t .-. x) .*. i .-. h .^. 3 .*. s1

instance Semigroup GEJ where
  (<>) = mappend

instance Monoid GEJ where
  mempty = GEJ fe_zero fe_zero fe_zero
  mappend a b = snd $ gej_add_ex a b

-- | Check if the x-coordinate of the point represented by a 'GEJ' has a given value.
gej_x_equiv :: FE -> GEJ -> Bool
gej_x_equiv x a | gej_is_infinity a = False
                | otherwise = fe_is_zero $ (fe_square (a^._z) .*. x) .-. (a^._x)

-- | Check if the y-coordinate of the point represented by a 'GEJ' is odd.
gej_y_is_odd :: GEJ -> Bool
gej_y_is_odd a@(GEJ _ y z) | gej_is_infinity a = False
                           | otherwise = fe_is_odd $ y .*. invz .^. 3
 where
  invz = fe_invert z

-- | Validates the secp256k1 curve equation: Y^2 = X^3 + 7Z^6
gej_is_on_curve :: GEJ -> Bool
gej_is_on_curve (GEJ x y z) = fe_is_zero $ x.^.3 .+. fe_seven.*.z.^.6 .-. y.^.2

-- | An uncompressed point.  Infinity not included
data GE = GE !FE !FE -- Infinity not included.
        deriving Show

-- | Compute the point addition formula for a 'GEJ' and a 'GE'.
-- This also returns the ratio between z-component of 'a' and z-component of the result.
--
-- @
--    a^.'_z' .*. r = p^.'_z'
-- @
--
-- where
--
-- @
--    (r, p) = 'gej_add_ex' a b
-- @
gej_ge_add_ex :: GEJ -> GE -> (FE, GEJ)
gej_ge_add_ex a (GE bx by) = gej_add_ex a (GEJ bx by fe_one)

-- | Compute a point addition formula for a 'GEJ' and another point with an inverted z coordinate.
--
-- @
--    'gej_is_infinity' $ ('gej_ge_add_zinv' a (GE bx by) bzinv) <> ('gej_negate' (a <> ('GEJ' bx by ('fe_invert' bzinf))))
-- @
--
-- where
--
-- @
--    (r, p) = 'gej_add_ex' a b
-- @
gej_ge_add_zinv :: GEJ -> GE -> FE -> GEJ
gej_ge_add_zinv a (GE bx by) bzinv = snd $ gej_ge_add_ex a (GE (bx .*. bzinv .^. 2) (by .*. bzinv .^. 3))

-- | Convert a 'GEJ' to a 'GE'.
-- This sends a point at infinity the the point @(GE fe_zero fe_zero)@.
gej_normalize :: GEJ -> GE
gej_normalize (GEJ x y z) = GE (x .*. invz .^. 2) (y .*. invz .^. 3)
 where
  invz = fe_invert z

-- | Negates a 'GE'.
ge_negate :: GE -> GE
ge_negate (GE x y) = GE x (fe_negate y)

-- | Scale a 'GE' by 'lambda'.
--
-- @
--    'ge_scale_lambda' ('ge_normalze' p) == 'ge_normalize' ('scalar_multiply' 'scalar_lambda' p)
-- @
ge_scale_lambda :: GE -> GE
ge_scale_lambda (GE x y) = GE (x .*. fe_beta) y

-- | Validates the secp256k1 curve equation: y^2 = x^3 + 7
ge_is_on_curve :: GE -> Bool
ge_is_on_curve (GE x y) = gej_is_on_curve (GEJ x y fe_one)

-- | An element of secp256k1's scalar field is represented as a normalized value.
newtype Scalar = Scalar { scalar_pack :: Word256 -- ^ Return the normalized represenative of a scalar element as a 'Word256'.
                        } deriving (Eq, Show)

instance Bounded Scalar where
  minBound = scalar 0
  maxBound = scalar $ groupOrder - 1

-- | The zero value of the scalar field.
scalar_zero :: Scalar
scalar_zero = Scalar 0

-- | @'scalar' 'lambda'@
scalar_lambda :: Scalar
scalar_lambda = scalar lambda

-- | Construct a scalar element from an integer.
scalar :: Integer -> Scalar
scalar x = Scalar $ fromInteger (x `mod` groupOrder)

-- | Return the normalized integer representative of a scalar element.
scalar_repr :: Scalar -> Integer
scalar_repr = toInteger . scalar_pack

-- | Decode a 256-bit word value as a scalar element, failing if the value is non-canonical.
scalar_unpack :: Word256 -> Maybe Scalar
scalar_unpack x0 = guard (x == scalar_repr s) >> return s
 where
  x = toInteger x0
  s = scalar x

-- | Checks if the scalar element is 0.
scalar_is_zero :: Scalar -> Bool
scalar_is_zero a = scalar_repr a == 0

-- | Negate a scalar element.
scalar_negate :: Scalar -> Scalar
scalar_negate = scalar . negate . scalar_repr

-- | Add two scalar elements.
scalar_add :: Scalar -> Scalar -> Scalar
scalar_add a b = scalar (scalar_repr a + scalar_repr b)

-- | Multiply two scalar elements.
scalar_multiply :: Scalar -> Scalar -> Scalar
scalar_multiply a b = scalar (scalar_repr a * scalar_repr b)

-- | Square a scalar element.
scalar_square :: Scalar -> Scalar
scalar_square a = scalar_multiply a a

-- | The modulular inverse of a scalar element, with 'scalar_zero' mapping to 'scalar_zero'.
scalar_invert :: Scalar -> Scalar
scalar_invert a = a `scalar_power` (groupOrder - 2)
 where
  scalar_power x n = go x (n `mod` (groupOrder - 1))
   where
    go x 0 = scalar_zero
    go x 1 = x
    go x n | even n = go (scalar_square x) (n `div` 2)
           | odd n = scalar_multiply x (go (scalar_square x) (n `div` 2))

-- | Scale a 'GEJ' by a scalar element.
scale :: Scalar -> GEJ -> GEJ
scale na a = linear_combination_1 na a scalar_zero

-- | Decompose a scalar value in short components.
--
-- @
--    'scalar' (k1 + 'lambda' * k2) == a
--    abs k1 < 2^128 && abs k2 < 2^128
-- @
--
-- where
--
-- @
--    (k1, k2) = 'scalar_split_lambda' a
-- @
scalar_split_lambda :: Scalar -> (Integer, Integer)
scalar_split_lambda k0 = (k1, k2)
 where
  n = groupOrder
  n2 = n `div` 2
  k = scalar_repr k0
  g1 = 0x3086d221a7d46bcde86c90e49284eb153daa8a1471e8ca7fe893209a45dbb031
  g2 = 0xe4437ed6010e88286f547fa90abfe4c4221208ac9df506c61571b4ae8ac47f71
  b1 = -0xe4437ed6010e88286f547fa90abfe4c3
  b2 =  0x3086d221a7d46bcde86c90e49284eb15
  c1 = (k * g1 + 2^383) `div` (2^384)
  c2 = (k * g2 + 2^383) `div` (2^384)
  k2 = - c1*b1 - c2*b2
  k1 = (k - k2 * lambda + n2) `mod` n - n2

-- | Decompose a scalar value in short components.
--
-- @
--    'scalar' (k1 + 2^128 * k2) == a
--    0 <= k1 < 2^128 && 0 <= k2 < 2^128
-- @
--
-- where
--
-- @
--    (k1, k2) = 'scalar_split_128' a
-- @
scalar_split_128 :: Scalar -> (Integer, Integer)
scalar_split_128 k0 = (k1, k2)
 where
  k = scalar_repr k0
  (k2, k1) = k `divMod` (2^128)

-- | Fast computation of a linear combination of the secp256k1 curve generator and other points.
--
-- @
--    'gej_is_infinity' $ 'linear_combination' [] ng <> 'gej_negate' ('scalar_multiply' ng 'g')
-- @
--
-- @
--    'gej_is_infinity' $ 'linear_combination' ((na, a):tl) ng <> 'gej_negate' ('scalar_multiply' ng 'g' <> 'linear_combination' tl ng)
-- @
linear_combination :: [(Scalar, GEJ)] -> Scalar -> GEJ
linear_combination l ng = foldr f mempty zips & _z %~ (.*. globalZ)
 where
  wa = 5
  (l', globalZ) = runTableM . sequence $
    [(,) <$> pure na <*> scalarTable wa s | (na, s) <- l, not (gej_is_infinity s) && not (scalar_is_zero na)]
  (ng1, ng2) = scalar_split_128 ng
  split_l = do
    (na, table) <- l'
    let (na1, na2) = scalar_split_lambda na
    let table_lam = ge_scale_lambda <$> table
    [(na1, table), (na2, table_lam)]
  f (as, Nothing, Nothing) r0 = foldl' gej_ge_add (gej_double r0) as
  f (as, Just g1, Nothing) r0
                   = gej_ge_add_zinv (f (as, Nothing, Nothing) r0) (tableG ! g1) globalZ
  f (as, g1, Just g2) r0
                   = gej_ge_add_zinv (f (as, g1, Nothing) r0) (tableG128 ! g2) globalZ
  gej_ge_add p q = snd $ gej_ge_add_ex p q
  zip3Ex [] [] [] = []
  zip3Ex [] bs cs = zip3Ex [[]] bs cs
  zip3Ex as [] cs = zip3Ex as [Nothing] cs
  zip3Ex as bs [] = zip3Ex as bs [Nothing]
  zip3Ex (a:as) (b:bs) (c:cs) = (a,b,c) : zip3Ex as bs cs
  zips = zip3Ex (transposeTables split_l) (wnaf wg ng1) (wnaf wg ng2)
  transposeTables [] = []
  transposeTables ((na, ts):rest) = merge (wnaf wa na) ts (transposeTables rest)
   where
    merge [] _ tbls = tbls
    merge l t [] = [[t ! i | Just i <- [x]] | x <- l]
    merge (Just i : tl) t (htbls : ttbls) = ((t ! i) : htbls) : merge tl t ttbls
    merge (Nothing : tl) t (htbls : ttbls) = htbls : merge tl t ttbls

-- | Fast computation of a linear combination of the secp256k1 curve generator and another point.
--
-- @
--    'gej_is_infinity' $ 'linear_combination_1' na a ng <> 'gej_negate' ('scalar_multiply' na 'a' <> 'scalar_multiply' ng 'g')
-- @
linear_combination_1 :: Scalar -> GEJ -> Scalar -> GEJ
linear_combination_1 na a = linear_combination [(na, a)]

-- | Decompose an integer in windowed non-adjacent form
wnafInteger :: Int -> Integer -> [Int]
wnafInteger w | 0 < w && w <= finiteBitSize w = unfoldr f
 where
  f 0 = Nothing
  f i = Just (fromInteger x, (i - x) `div` 2)
   where
    x | odd i = ((i + 2^(w-1)) `mod` 2^w) - 2^(w-1)
      | otherwise = 0

-- | Decompose an integer in windowed non-adjacent form.
-- Odd values have their least significant bit dropped.
-- Zero values are returned as Nothing.
wnaf :: Int -> Integer -> [Maybe Int]
wnaf w s = post <$> wnafInteger w s
 where
  post 0 = Nothing
  post i | odd i = Just $ i `div` 2
         | otherwise = error "Simplicity.LibSecp256k1.Spec: invalid result from wnafInteger"

-- | A monad used to help construct scalar tables with a common z-coordinate.
type TableM a = Tardis FE GEJ a

-- | Execute a 'TableM' computation, also returning the combon z-coordinate value.
runTableM :: TableM a -> (a, FE)
runTableM tardis = (a, p^._z)
 where
  (a,(_,p)) = runTardis tardis (fe_one, GEJ fe_zero fe_zero fe_one)

-- | Get the current table point, scalining it by the future z-factor.
getTable :: TableM GE
getTable = do
  a <- getPast
  zf <- getFuture
  return $ GE (a^._x .*. zf .^. 2) (a^._y .*. zf .^. 3)

-- | Put a new table point into the 'TableM'.
-- Requres the (true) z-ratio between the new point and the previous point.
putTable :: FE -> GEJ -> TableM ()
putTable zr a = do
  modifyBackwards (.*. zr)
  sendFuture a

-- | Precompute small odd muliplies of a 'GEJ' and give them a common z-coordinate.
-- The point must not be at infinity.
scalarTable :: Int -> GEJ -> TableM (V.Vector GE)
scalarTable w a = do
  z0 <- getsPast (^._z)
  let a' = gej_rescale a z0
  let d = gej_double a'
  let dz = d^._z
  let a'' = GEJ (a'^._x .*. dz .^. 2) (a'^._y .*. dz .^. 3) (a'^._z)
  putTable (a^._z .*. dz) a''
  let tableNext = uncurry putTable =<< (gej_ge_add_ex <$> getPast <*> pure (GE (d^._x) (d^._y)))
  result <- V.cons <$> getTable <*> V.replicateM (len - 1) (tableNext >> getTable)
  modifyForwards $ _z %~ (.*. dz)
  return result
 where
  len = 2^(w-2)

-- | The specified generator of the secp256k1 curve.
g :: GEJ
g = GEJ (fe 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798)
        (fe 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)
        fe_one

-- | A representation of 2^128 * 'g'.
g128 :: GEJ
g128 = iterate gej_double g !! 128

-- | The default window size for scalars multiplying by 'g'.
wg = 15

-- | A precomputate table of odd multiples of 'g'.
tableG = table wg g

-- | A precomputate table of odd multiples of 'g128'.
tableG128 = table wg g128

-- | Compute a table of odd multiple of a point and 'gej_normalize' all of them.
table w p = t & traverse %~ norm
 where
  (t,z) = runTableM (scalarTable w p)
  zinv = fe_invert z
  norm (GE x y) = GE (x .*. zinv .^. 2) (y .*. zinv .^. 3)

-- | An index into a precomputed odd multiple table of 'GE'.
-- Negative indexes are accepted and automatically return the negation of the corresponding point.
(!) :: V.Vector GE -> Int -> GE
t ! i | i >= 0 = t V.! i
      | otherwise = ge_negate (t V.! (-i-1))

-- | Validates that all points are 'ge_is_on_curve' and that
-- @'linear_check' l ng r@ implies
--
-- @
--    'gej_is_infinity' $ 'linear_combination' l ng <> 'ge_negate' r
-- @
linear_check :: [(Scalar, GE)] -> Scalar -> GE -> Bool
linear_check l ng r = isJust $ do
  guard $ ge_is_on_curve r
  guard $ allOf (traverse._2) ge_is_on_curve l
  guard $ gej_is_infinity (linear_combination l' ng <> negR)
 where
  negR = toGEJ (ge_negate r)
  l' = l & (traverse._2) %~ toGEJ
  toGEJ (GE x y) = (GEJ x y fe_one)

-- | Validates that all points are 'ge_is_on_curve' and that
-- @'linear_check_1' na a ng r@ implies
--
-- @
--    'gej_is_infinity' $ 'linear_combination_1' na a ng <> 'ge_negate' r
-- @
linear_check_1 :: Scalar -> GE -> Scalar -> GE -> Bool
linear_check_1 na a = linear_check [(na, a)]

-- | Convert a point from compressed coordinates to affine coordinates.
-- Fails if the x-coordinate of the point is not on the secp256k1 curve.
decompress :: Point -> Maybe GE
decompress (Point yodd x) = do
  y <- fe_square_root (x .^. 3 .+. fe_seven)
  return (GE x (if fe_is_odd y == yodd then y else (fe_negate y)))

-- | Given an (x-only) public key, check that the x-coordinate is normalized and returns a Point representing that pubkey.
-- This does not check that the point is on-curve, which needed to be done by a subsequent call to `decompress`.
pubkey_unpack :: PubKey -> Maybe Point
pubkey_unpack (PubKey px) = Point False <$> fe_unpack px

-- | Given an (x-only) public key, check that the x-coordinate is normalized and returns a Point representing the negation of that pubkey.
-- This does not check that the point is on-curve, which needed to be done by a subsequent call to `decompress`.
pubkey_unpack_neg :: PubKey -> Maybe Point
pubkey_unpack_neg (PubKey px) = Point True <$> fe_unpack px

-- | Given a bip0340 signature, unpack it r value as an 'FE', and its s value as a 'Scalar'.
-- Fails if the signature components are out of range.
signature_unpack :: Sig -> Maybe (FE, Scalar)
signature_unpack (Sig r s) = (,) <$> fe_unpack r <*> scalar_unpack s

-- | Validates that all points are 'decompress'able and that the 'linear_check' of the decompressed points is satified.
point_check :: [(Scalar, Point)] -> Scalar -> Point -> Bool
point_check l ng r = isJust $ do
  l' <- l & (traverse._2) decompress
  r' <- decompress r
  guard $ linear_check l' ng r'

-- | Verify a bip0340 signature for a given public key on a given message.
bip0340_check :: PubKey  -- ^ public key
              -> Hash256 -- ^ message
              -> Sig     -- ^ signature
              -> Bool
bip0340_check pk m sg = isJust $ do
  negp <- pubkey_unpack_neg pk
  (rx, s) <- signature_unpack sg
  let tag = bsHash (BSC.pack "BIP0340/challenge")
  let h = bsHash . runPut $ put tag >> put tag >> put (fe_pack rx) >> put pk >> put m
  let e = scalar . integerHash256 $ h
  let r = Point False rx
  guard $ point_check [(e, negp)] s r


-- | Point of order 3 * 199 * 18979 * 5128356331187950431517 * 1992751017769525324118900703535975744264170999967
ge_115792089237316195423570985008687907853508896131558604026424249738214906721757 :: GE
ge_115792089237316195423570985008687907853508896131558604026424249738214906721757 = GE fe_one (fe 47) 

-- | Point of order 109903 * 12977017 * 383229727 * 211853322379233867315890044223858703031485253961775684523
ge_115792089237316195423570985008687907853031073199722524052490918277602762621571 :: GE
ge_115792089237316195423570985008687907853031073199722524052490918277602762621571 = GE fe_one (fe 2) 

-- | Point of order 2 * 3 * 20412485227 * 83380711482738671590122559 * 5669387787833452836421905244327672652059
ge_57896044618658097711785492504343953926299326406578432197819248705606044722122 :: GE
ge_57896044618658097711785492504343953926299326406578432197819248705606044722122 = GE fe_one (fe 3) 

-- | Point of order 3 * 13^2 * 3319 * 22639 * 1013176677300131846900870239606035638738100997248092069256697437031
ge_38597363079105398474523661669562635951234135017402074565436668291433169282997 :: GE
ge_38597363079105398474523661669562635951234135017402074565436668291433169282997 = GE fe_one (fe 4) 

-- | Point of order 2 * 7 * 10903 * 5290657 * 10833080827 * 22921299619447 * 41245443549316649091297836755593555342121
ge_8270863516951156815969356072049136275281522608437447405948333614614684278506 :: GE
ge_8270863516951156815969356072049136275281522608437447405948333614614684278506 = GE fe_one (fe 9) 

-- | Point of order 199
ge_199 :: GE
ge_199 = GE (fe 70687250180557772597302152869007174094074882915196773732325669623429152815718) (fe 33705998260714715075689047715894246886612372461530560867300550015040889896278) 

-- | Point of order 13^2
ge_169 :: GE
ge_169 = GE (fe 76143429403124191739648005988712146536970826737586076805285435910939811650235) (fe 79206108477852635180125138589256689828047073885928765425620364817661860808444) 

-- | Point of order 3 * 13
ge_39 :: GE
ge_39 = GE (fe 106383153246165320275512998590184975158094311190930717121540544272958714969874) (fe 60732340993648917667778372165513456197562368078430634464262139756474636012620) 

-- | Point of order 2 * 7 
ge_14 :: GE
ge_14 = GE (fe 23022798600391872912114696699513327158948857432264427056250729177241370144563) (fe 42638903475844439756199347045463393577799965344626237613274902440780224637754) 

-- | Point of order 13
ge_13 :: GE
ge_13 = GE (fe 64527622301014718397267236002495618081577172385398418064146870396180094467254) (fe 64805533305984530191801092315596539809224403998577052480080063250771024326631) 

-- | Point of order 7
ge_7 :: GE
ge_7 = GE (fe 114109980193979926462125731765358310155031959372310767812063216697230157494741) (fe 101398216421584366967138431919489099535284823381455250476556676772183350055487) 

-- | Point of order 2 * 3 
ge_6 :: GE
ge_6 = GE (fe 106586213356003376052770626926523423124273824193112332847656463919061591657353) (fe 26101920679609057376888884124959740524626979187904654689991505285331895977061) 

-- | Point of order 3 
ge_3 :: GE
ge_3 = GE (fe 93163632785783131583621179645788501141364174486796116157579303931124646196327) (fe 67800883132571304345368516576619608502750474897195575578939869419018063089619) 
