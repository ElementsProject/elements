-- This module tests the Simplicity programs on arbitrary inputs.
module Simplicity.Programs.Tests (tests) where

import Prelude hiding (sqrt)
import Control.Arrow ((***))
import Data.Bits ((.|.))
import qualified Data.Bits as W
import Data.ByteString (pack)
import Data.ByteString.Short (toShort)
import qualified Data.List as L
import qualified Data.Word as W
import Lens.Family2 ((^..), allOf, zipWithOf)
import Lens.Family2.Stock (both_)

import Simplicity.Digest
import Simplicity.LibSecp256k1.Spec ((.*.))
import qualified Simplicity.LibSecp256k1.Spec as LibSecp
import Simplicity.Programs.Bit
import Simplicity.Programs.LibSecp256k1.Lib
import Simplicity.Programs.Sha256.Lib
import Simplicity.Programs.Word
import Simplicity.Term.Core
import qualified Simplicity.Ty.Word as Ty

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (Gen, Property, arbitrary, choose, elements, forAll, testProperty)

-- This collects the tests for the various Simplicity programs.
tests :: TestTree
tests = testGroup "Programs"
      [ testGroup "Arith"
        [ testProperty "fullAdder word8" prop_fullAdder8
        , testProperty "adder word8" prop_adder8
        , testProperty "fullSubtractor word8" prop_fullSubtractor8
        , testProperty "subtractor word8" prop_subtractor8
        , testProperty "fullMultiplier word8" prop_fullMultiplier8
        , testProperty "multiplier word8" prop_multiplier8
        , testProperty "bitwiseNot word8" prop_bitwiseNot8
        , testProperty "shift word8" prop_shift8
        , testProperty "rotate word8" prop_rotate8
        ]
      , testProperty "sha256" prop_sha256
      ]

-- The specification for full adder on Word8
prop_fullAdder8 :: Word8 -> Word8 -> Bit -> Bool
prop_fullAdder8 x y z = (if fromBit carry then 2^8 else 0) + fromWord8 result8 == fromWord8 x + fromWord8 y + if fromBit z then 1 else 0
 where
  (carry, result8) = fullAdder word8 ((x, y), z)

-- The specification for adder on Word8
prop_adder8 :: Word8 -> Word8 -> Bool
prop_adder8 x y = (if fromBit carry then 2^8 else 0) + fromWord8 result8 == fromWord8 x + fromWord8 y
 where
  (carry, result8) = adder word8 (x, y)

-- The specification for full subtractor on Word8
prop_fullSubtractor8 :: Word8 -> Word8 -> Bit -> Bool
prop_fullSubtractor8 x y z =  fromWord8 result8 == (if fromBit borrow then 2^8 else 0) + fromWord8 x - fromWord8 y - if fromBit z then 1 else 0
 where
  (borrow, result8) = fullSubtractor word8 ((x, y), z)

-- The specification for subtractor on Word8
prop_subtractor8 :: Word8 -> Word8 -> Bool
prop_subtractor8 x y =  fromWord8 result8 == (if fromBit borrow then 2^8 else 0) + fromWord8 x - fromWord8 y
 where
  (borrow, result8) = subtractor word8 (x, y)

-- The specification for full multiplier on Word8
prop_fullMultiplier8 :: Word8 -> Word8 -> Word8 -> Word8 -> Bool
prop_fullMultiplier8 w x y z = fromWord16 (fullMultiplier word8 ((x, y), (w, z))) == fromWord8 x * fromWord8 y + fromWord8 w + fromWord8 z

-- The specification for multiplier on Word8
prop_multiplier8 :: Word8 -> Word8 -> Bool
prop_multiplier8 x y = fromWord16 (multiplier word8 (x, y)) == fromWord8 x * fromWord8 y

-- The specification for bitwiseNot on Word8
prop_bitwiseNot8 :: Word8 -> Bool
prop_bitwiseNot8 x = conv (bitwiseNot word8 x) == W.complement (conv x)
 where
  conv :: Word8 -> W.Word8
  conv = fromInteger . fromWord8

-- The specification for shifts on Word8
prop_shift8 :: Word8 -> Property
prop_shift8 x = forAll small (\z -> convert (shift word8 z x) == W.shift (convert x) (-z))
 where
  convert :: Word8 -> W.Word8
  convert = fromInteger . fromWord8
  small = elements [-16..16]

-- The specification for rotates on Word8
prop_rotate8 :: Word8 -> Property
prop_rotate8 x = forAll small (\z -> convert (rotate word8 z x) == W.rotate (convert x) (-z))
 where
  convert :: Word8 -> W.Word8
  convert = fromInteger . fromWord8
  small = elements [-16..16]

-- The specification for SHA-256's block compression function.
prop_sha256 :: [W.Word8] -> Bool
prop_sha256 x0 = integerHash256 (bsHash (pack x)) == fromWord256 ((iv &&& iden >>> hashBlock) (toWord512 paddedInteger))
 where
  x = L.take 55 x0
  len = length x
  mkInteger l = go l 0
   where
    go [] n     = n
    go (w:ws) n = go ws (W.shiftL n 8 .|. toInteger w)
  paddedInteger = W.shiftL (mkInteger (x ++ [0x80])) (8*(64 - (len + 1))) .|. toInteger len*8

fromFE :: FE -> LibSecp.FE
fromFE (a0,(a1,(a2,(a3,(a4,(a5,(a6,(a7,(a8,a9))))))))) =
  LibSecp.FE (conv a0)
             (conv a1)
             (conv a2)
             (conv a3)
             (conv a4)
             (conv a5)
             (conv a6)
             (conv a7)
             (conv a8)
             (conv a9)
 where
  conv = fromInteger . fromWord32

toFE :: LibSecp.FE -> FE
toFE (LibSecp.FE a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) =
   (conv a0
  ,(conv a1
  ,(conv a2
  ,(conv a3
  ,(conv a4
  ,(conv a5
  ,(conv a6
  ,(conv a7
  ,(conv a8
  , conv a9)))))))))
 where
  conv = toWord32 . toInteger

eq_fe = zipWithOf (allOf LibSecp.fe) (==)

prop_normalizeWeak :: FE -> Bool
prop_normalizeWeak a = fromFE (normalizeWeak a) `eq_fe` LibSecp.normalizeWeak (fromFE a)

prop_normalize :: FE -> Bool
prop_normalize a = fromFE (normalize a) `eq_fe` LibSecp.normalize (fromFE a)
over_low x y = toFE $ LibSecp.FE (0x3FFFFFF-x) (0x3FFFFFF-y) 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x03FFFFF
over_high x y = toFE $ LibSecp.FE (0x3FFFFFF-x) (0x3FFFFFF-y) 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x3FFFFFF 0x07FFFFF
prop_normalize_over_low x y = prop_normalize (over_low x y)
prop_normalize_over_high x y = prop_normalize (over_high x y)

prop_fePack :: FE -> Bool
prop_fePack a = toBS (fePack a) == LibSecp.fePack (fromFE a)
 where
  toBS x = toShort . pack . map conv $ x^..(both_.both_.both_.both_.both_)
  conv = fromInteger . fromWord8
prop_fePack_over_low x y = prop_fePack (over_low x y)
prop_fePack_over_high x y = prop_fePack (over_high x y)

prop_feUnpack :: Word256 -> Bool
prop_feUnpack w = fromFE (feUnpack w) `eq_fe` LibSecp.feUnpack (fromInteger (fromWord256 w))

prop_add :: FE -> FE -> Bool
prop_add a b = fromFE (add (a, b)) `eq_fe` LibSecp.add (fromFE a) (fromFE b)

prop_mul :: FE -> FE -> Bool
prop_mul a b = fromFE (mul (a, b)) `eq_fe` LibSecp.mul (fromFE a) (fromFE b)

prop_sqr :: FE -> Bool
prop_sqr a = fromFE (sqr a) `eq_fe` LibSecp.sqr (fromFE a)

prop_mulInt :: FE -> Property
prop_mulInt a = forAll (choose (0, 32)) (\m -> fromFE (mulInt m a) `eq_fe` LibSecp.mulInt (fromInteger m) (fromFE a))

prop_neg :: FE -> Property
prop_neg a = forAll (choose (0, 32)) (\m -> fromFE (neg m a) `eq_fe` LibSecp.neg (fromInteger m) (fromFE a))

prop_inv :: FE -> Bool
prop_inv a = fromFE (inv a) `eq_fe` LibSecp.inv (fromFE a)

prop_sqrt :: FE -> Bool
prop_sqrt a = conv (sqrt a) `eq_mfe` LibSecp.sqrt (fromFE a)
 where
  conv = either (const Nothing) (Just . fromFE)
  eq_mfe (Just x) (Just y) = x `eq_fe` y
  eq_mfe Nothing Nothing = True
  eq_mfe _ _ = False

fromGE :: GE -> LibSecp.GE
fromGE (x, y) = LibSecp.GE (fromFE x) (fromFE y)

toGE :: LibSecp.GE -> GE
toGE (LibSecp.GE x y) = (toFE x, toFE y)

fromGEJ :: GEJ -> LibSecp.GEJ
fromGEJ ((x, y), z) = LibSecp.GEJ (fromFE x) (fromFE y) (fromFE z)

toGEJ :: LibSecp.GEJ -> GEJ
toGEJ (LibSecp.GEJ x y z) = ((toFE x, toFE y), toFE z)

eq_gej = zipWithOf (allOf LibSecp.gej) eq_fe

gen_inf :: Gen GEJ
gen_inf = (\xy -> (xy, feZero ())) <$> arbitrary

prop_double_inf :: Property
prop_double_inf = forAll gen_inf $ prop_double

prop_double :: GEJ -> Bool
prop_double a = fromGEJ (double a) `eq_gej` LibSecp.double (fromGEJ a)

prop_offsetPoint :: GEJ -> GE -> Bool
prop_offsetPoint a b = fromFE rz `eq_fe` rz' && fromGEJ c `eq_gej` c'
 where
  (rz,c) = offsetPoint (a, b)
  (rz',c') = LibSecp.offsetPoint (fromGEJ a) (fromGE b)

prop_offsetPoint_double z b = prop_offsetPoint a b
 where
  z' = fromFE z
  z'2 = LibSecp.sqr z'
  z'3 = z' .*. z'2
  LibSecp.GE b'x b'y = fromGE b
  a = ((toFE (b'x .*. z'2), toFE (b'y .*. z'3)), z)

prop_offsetPoint_opp z b = prop_offsetPoint a b
 where
  z' = fromFE z
  z'2 = LibSecp.sqr z'
  z'3 = z' .*. z'2
  LibSecp.GE b'x b'y = fromGE b
  a = ((toFE (b'x .*. z'2), toFE (LibSecp.neg 1 (b'y .*. z'3))), z)

prop_offsetPoint_inf b = forAll gen_inf $ \a -> prop_offsetPoint a b

prop_offsetPointZinv :: GEJ -> GE -> FE -> Bool
prop_offsetPointZinv a b zinv = fromGEJ (offsetPointZinv (a,(b,zinv))) `eq_gej` LibSecp.offsetPointZinv (fromGEJ a) (fromGE b) (fromFE zinv)

prop_offsetPointZinv_double z b bz = prop_offsetPointZinv a b bz
 where
  b'z = fromFE bz
  z' = fromFE z
  z'2 = LibSecp.sqr z'
  z'3 = z' .*. z'2
  LibSecp.GE b'x b'y = fromGE b
  a = ((toFE (b'x .*. z'2), toFE (b'y .*. z'3)), toFE (LibSecp.inv b'z .*. z'))

prop_offsetPointZinv_opp z b bz = prop_offsetPointZinv a b bz
 where
  b'z = fromFE bz
  z' = fromFE z
  z'2 = LibSecp.sqr z'
  z'3 = z' .*. z'2
  LibSecp.GE b'x b'y = fromGE b
  a = ((toFE (b'x .*. z'2), toFE (LibSecp.neg 1 (b'y .*. z'3))), toFE (LibSecp.inv b'z .*. z'))

prop_offsetPointZinv_inf :: GE -> FE -> Property
prop_offsetPointZinv_inf b zinv = forAll gen_inf $ \a -> prop_offsetPointZinv a b zinv

fromScalar :: Ty.Word256 -> LibSecp.Scalar
fromScalar = LibSecp.Scalar . fromInteger . fromWord256

prop_wnaf5 :: Ty.Word256 -> Bool
prop_wnaf5 n = L.and $ zipWith (==) lhs (fmap (fmap unsign) (LibSecp.wnaf 5 (fromScalar n) ++ repeat Nothing))
 where
  lhs = either (const Nothing) (Just . fromInteger . fromWord4) <$> wnaf5 n^..both_.both_.both_.both_.both_.both_.both_.both_
  unsign x | x < 0 = 2^4 + x
           | otherwise = x
prop_wnaf5_hi :: Ty.Word128 -> Bool
prop_wnaf5_hi n10 = prop_wnaf5 (toWord128 (-1), n10)

prop_wnaf16 :: Ty.Word256 -> Bool
prop_wnaf16 n = L.and $ zipWith (==) lhs (fmap (fmap unsign) (LibSecp.wnaf 16 (fromScalar n) ++ repeat Nothing))
 where
  lhs = either (const Nothing) (Just . fromInteger . fromWord16) <$> wnaf16 n^..both_.both_.both_.both_.both_.both_.both_.both_
  unsign x | x < 0 = 2^16 + 2*x+1
           | otherwise = 2*x+1
prop_wnaf16_hi :: Ty.Word128 -> Bool
prop_wnaf16_hi n10 = prop_wnaf16 (toWord128 (-1), n10)

prop_ecMult :: GEJ -> Word256 -> Word256 -> Bool
prop_ecMult a na ng = fromGEJ (ecMult ((a, na), ng)) `eq_gej` LibSecp.ecMult (fromGEJ a) (fromScalar na) (fromScalar ng)

prop_ecMult0 :: GEJ -> Word256 -> Bool
prop_ecMult0 a ng = prop_ecMult a na ng
 where
  na = toWord256 0

prop_pkPoint :: XOnlyPubKey -> Bool
prop_pkPoint pk = conv (pkPoint pk) `eq_mgej` LibSecp.pkPoint pk'
 where
  pk' = LibSecp.XOnlyPubKey (fromInteger (fromWord256 pk))
  conv = either (const Nothing) (Just . fromGEJ)
  eq_mgej (Just x) (Just y) = x `eq_gej` y
  eq_mgej Nothing Nothing = True
  eq_mgej _ _ = False

prop_sigUnpack :: Sig -> Bool
prop_sigUnpack sig@(r, s) = conv (sigUnpack sig) `eq_mfeW256` LibSecp.sigUnpack sig'
 where
  sig' = LibSecp.Sig (fromInteger (fromWord256 r)) (fromInteger (fromWord256 s))
  conv = either (const Nothing) (Just . (fromFE *** fromScalar))
  eq_mfeW256 (Just (a0, a1)) (Just (b0, b1)) = (a0 `eq_fe` b0) && a1 == b1
  eq_mfeW256 Nothing Nothing = True
  eq_mfeW256 _ _ = False

prop_scalarUnrepr :: Word256 -> Bool
prop_scalarUnrepr w = fromScalar (scalarUnrepr w) == LibSecp.scalarUnrepr (fromWord256 w)
prop_scalarUnrepr_hi w = prop_scalarUnrepr (toWord128 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, w)

schnorr0 :: Bool
schnorr0 = fromBit $ schnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
  m = toWord256 0
  sig = toWord512 0x528F745793E8472C0329742A463F59E58F3A3F1A4AC09C28F6F8514D4D0322A258BD08398F82CF67B812AB2C7717CE566F877C2F8795C846146978E8F04782AE

schnorr1 :: Bool
schnorr1 = fromBit $ schnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0x667C2F778E0616E611BD0C14B8A600C5884551701A949EF0EBFD72D452D64E844160BCFC3F466ECB8FACD19ADE57D8699D74E7207D78C6AEDC3799B52A8E0598

schnorr2 :: Bool
schnorr2 = fromBit $ schnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDD308AFEC5777E13121FA72B9CC1B7CC0139715309B086C960E18FD969774EB8
  m = toWord256 0x5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C
  sig = toWord512 0x2D941B38E32624BF0AC7669C0971B990994AF6F9B18426BF4F4E7EC10E6CDF386CF646C6DDAFCFA7F1993EEB2E4D66416AEAD1DDAE2F22D63CAD901412D116C6

schnorr3 :: Bool
schnorr3 = fromBit $ schnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0x25D1DFF95105F5253C4022F628A996AD3A0D95FBF21D468A1B33F8C160D8F517
  m = toWord256 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  sig = toWord512 0x8BD2C11604B0A87A443FCC2E5D90E5328F934161B18864FB48CE10CB59B45FB9B5B2A0F129BD88F5BDC05D5C21E5C57176B913002335784F9777A24BD317CD36

schnorr4 :: Bool
schnorr4 = fromBit $ schnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xD69C3509BB99E412E68B0FE8544E72837DFA30746D8BE2AA65975F29D22DC7B9
  m = toWord256 0x4DF3C3F68FCC83B27E9D42C90431A72499F17875C81A599B566C9889B9696703
  sig = toWord512 0x00000000000000000000003B78CE563F89A0ED9414F5AA28AD0D96D6795F9C63EE374AC7FAE927D334CCB190F6FB8FD27A2DDC639CCEE46D43F113A4035A2C7F

schnorr5 :: Bool
schnorr5 = fromBit $ schnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xEEFDEA4CDB677750A420FEE807EACF21EB9898AE79B9768766E4FAA04A2D4A34
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0x667C2F778E0616E611BD0C14B8A600C5884551701A949EF0EBFD72D452D64E844160BCFC3F466ECB8FACD19ADE57D8699D74E7207D78C6AEDC3799B52A8E0598

schnorr6 :: Bool
schnorr6 = fromBit $ schnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0xF9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9935554D1AA5F0374E5CDAACB3925035C7C169B27C4426DF0A6B19AF3BAEAB138

schnorr7 :: Bool
schnorr7 = fromBit $ schnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0x10AC49A6A2EBF604189C5F40FC75AF2D42D77DE9A2782709B1EB4EAF1CFE9108D7003B703A3499D5E29529D39BA040A44955127140F81A8A89A96F992AC0FE79

schnorr8 :: Bool
schnorr8 = fromBit $ schnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0x667C2F778E0616E611BD0C14B8A600C5884551701A949EF0EBFD72D452D64E84BE9F4303C0B9913470532E6521A827951D39F5C631CFD98CE39AC4D7A5A83BA9

schnorr9 :: Bool
schnorr9 = fromBit $ schnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0x000000000000000000000000000000000000000000000000000000000000000099D2F0EBC2996808208633CD9926BF7EC3DAB73DAAD36E85B3040A698E6D1CE0

schnorr10 :: Bool
schnorr10 = fromBit $ schnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0x000000000000000000000000000000000000000000000000000000000000000124E81D89F01304695CE943F7D5EBD00EF726A0864B4FF33895B4E86BEADC5456

schnorr11 :: Bool
schnorr11 = fromBit $ schnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0x000000000000000000000000000000000000000000000000000000000000000124E81D89F01304695CE943F7D5EBD00EF726A0864B4FF33895B4E86BEADC5456

schnorr12 :: Bool
schnorr12 = fromBit $ schnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F4160BCFC3F466ECB8FACD19ADE57D8699D74E7207D78C6AEDC3799B52A8E0598

schnorr13 :: Bool
schnorr13 = fromBit $ schnorrVerify ((pk,m),sig)
 where
  pk = toWord256 0xDFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659
  m = toWord256 0x243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89
  sig = toWord512 0x667C2F778E0616E611BD0C14B8A600C5884551701A949EF0EBFD72D452D64E84FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

schnorr_tests :: Bool
schnorr_tests = Prelude.and [schnorr0, schnorr1, schnorr2, schnorr3, schnorr4]
             && Prelude.not (Prelude.or [schnorr5, schnorr6, schnorr7, schnorr8, schnorr9, schnorr10, schnorr11, schnorr12, schnorr13])
