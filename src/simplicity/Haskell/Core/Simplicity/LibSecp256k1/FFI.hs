module Simplicity.LibSecp256k1.FFI
 ( normalizeWeak, normalize, fePack, feUnpack
 , feIsZero, neg, mulInt, add, mul, sqr, inv, sqrt
 , double, addPoint, offsetPoint, offsetPointZinv
 , eqXCoord, hasQuadY
 , scalarNegate
 , wnaf, ecMult
 ) where

import Prelude hiding (sqrt)

import Control.Monad (forM_)
import Data.Bits (shiftR)
import Data.ByteString (packCStringLen, useAsCStringLen)
import Data.ByteString.Short (ShortByteString, toShort)
import Data.Serialize (encode)
import Foreign.ForeignPtr (ForeignPtr, addForeignPtrFinalizer, mallocForeignPtr, withForeignPtr)
import Foreign.Marshal.Alloc (alloca)
import Foreign.Marshal.Array (allocaArray, peekArray)
import Foreign.Marshal.Utils (with)
import Foreign.Ptr (FunPtr, Ptr, alignPtr, castPtr, plusPtr, nullFunPtr, nullPtr)
import Foreign.C.Types (CInt(..), CChar)
import Foreign.Storable (Storable(..))
import System.IO.Unsafe (unsafeDupablePerformIO, unsafePerformIO)

import Simplicity.Word
import Simplicity.LibSecp256k1.Spec ( FE(..), feZero, feOne
                                    , GEJ(..), GE(..)
                                    , Scalar(..), scalarZero
                                    )

instance Storable FE where
  sizeOf x = 10*sizeOf (undefined :: Word32)
  alignment _ = alignment (undefined :: Word32)
  peek ptr = FE <$> (peekElemOff ptr' 0)
                <*> (peekElemOff ptr' 1)
                <*> (peekElemOff ptr' 2)
                <*> (peekElemOff ptr' 3)
                <*> (peekElemOff ptr' 4)
                <*> (peekElemOff ptr' 5)
                <*> (peekElemOff ptr' 6)
                <*> (peekElemOff ptr' 7)
                <*> (peekElemOff ptr' 8)
                <*> (peekElemOff ptr' 9)
   where
    ptr' = castPtr ptr

  poke ptr (FE a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) = do
    pokeElemOff ptr' 0 a0
    pokeElemOff ptr' 1 a1
    pokeElemOff ptr' 2 a2
    pokeElemOff ptr' 3 a3
    pokeElemOff ptr' 4 a4
    pokeElemOff ptr' 5 a5
    pokeElemOff ptr' 6 a6
    pokeElemOff ptr' 7 a7
    pokeElemOff ptr' 8 a8
    pokeElemOff ptr' 9 a9
   where
    ptr' = castPtr ptr

instance Storable GEJ where
  sizeOf x = 3*sizeOf (undefined :: FE) + sizeOf (undefined :: CInt)
  alignment _ = alignment (undefined :: FE)
  peek ptr = do
    CInt flag <- peek (alignPtr (ptr `plusPtr` (3 * sizeOf (undefined :: FE))) (alignment (undefined :: CInt)))
    GEJ <$> peekElemOff ptr' 0 <*> peekElemOff ptr' 1 <*> if flag == 0 then peekElemOff ptr' 2 else pure feZero
   where
    ptr' = castPtr ptr
  poke ptr (GEJ x y z) = do
    pokeElemOff ptr' 0 x
    pokeElemOff ptr' 1 y
    pokeElemOff ptr' 2 z
    poke (alignPtr (ptr `plusPtr` (3 * sizeOf x)) (alignment flag)) flag
   where
    ptr' = castPtr ptr
    flag | feIsZero z = CInt 1 -- Note that we set the flag even for false feZeros.
         | otherwise = CInt 0

instance Storable GE where
  sizeOf x = 2*sizeOf (undefined :: FE) + sizeOf (undefined :: CInt)
  alignment _ = alignment (undefined :: FE)
  peek ptr = do
    CInt flag <- peek (alignPtr (ptr' `plusPtr` (2 * sizeOf (undefined :: FE))) (alignment (undefined :: CInt)))
    if flag == 0
     then GE <$> peekElemOff ptr' 0 <*> peekElemOff ptr' 1
     else error "peek GE.Infinity"
   where
    ptr' = castPtr ptr
  poke ptr (GE x y) = do
    pokeElemOff ptr' 0 x
    pokeElemOff ptr' 1 y
    poke (alignPtr (ptr `plusPtr` (2 * sizeOf x)) (alignment flag)) flag
   where
    ptr' = castPtr ptr
    flag = CInt 0

instance Storable Scalar where
  sizeOf x = 8*sizeOf (undefined :: Word32)
  alignment _ = alignment (undefined :: Word32)
  peek ptr = mkScalar <$> (peekElemOff ptr' 0)
                      <*> (peekElemOff ptr' 1)
                      <*> (peekElemOff ptr' 2)
                      <*> (peekElemOff ptr' 3)
                      <*> (peekElemOff ptr' 4)
                      <*> (peekElemOff ptr' 5)
                      <*> (peekElemOff ptr' 6)
                      <*> (peekElemOff ptr' 7)
   where
    ptr' = castPtr ptr
    mkScalar :: Word32 -> Word32 -> Word32 -> Word32 -> Word32 -> Word32 -> Word32 -> Word32 -> Scalar
    mkScalar a0 a1 a2 a3 a4 a5 a6 a7 = Scalar $ fromIntegral a0 + 2^32*
                                               (fromIntegral a1 + 2^32*
                                               (fromIntegral a2 + 2^32*
                                               (fromIntegral a3 + 2^32*
                                               (fromIntegral a4 + 2^32*
                                               (fromIntegral a5 + 2^32*
                                               (fromIntegral a6 + 2^32*
                                                fromIntegral a7))))))

  poke ptr (Scalar a) = forM_ [0..7] (\i -> pokeElemOff ptr' i (fromIntegral (a `shiftR` (i*32))))
   where
    ptr' :: Ptr Word32
    ptr' = castPtr ptr

type Context = Ptr Word32
data Callback

foreign import ccall unsafe "secp256k1_fe_normalize_weak" c_secp256k1_fe_normalize_weak :: Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_fe_normalize_var" c_secp256k1_fe_normalize_var :: Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_fe_set_b32" c_secp256k1_fe_set_b32 :: Ptr FE -> Ptr CChar -> IO CInt
foreign import ccall unsafe "secp256k1_fe_get_b32" c_secp256k1_fe_get_b32 :: Ptr CChar -> Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_fe_normalizes_to_zero_var" c_secp256k1_fe_normalizes_to_zero_var :: Ptr FE -> IO CInt
foreign import ccall unsafe "secp256k1_fe_negate" c_secp256k1_fe_negate :: Ptr FE -> Ptr FE -> CInt -> IO ()
foreign import ccall unsafe "secp256k1_fe_mul_int" c_secp256k1_fe_mul_int :: Ptr FE -> CInt -> IO ()
foreign import ccall unsafe "secp256k1_fe_add" c_secp256k1_fe_add :: Ptr FE -> Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_fe_mul" c_secp256k1_fe_mul :: Ptr FE -> Ptr FE -> Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_fe_sqr" c_secp256k1_fe_sqr :: Ptr FE -> Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_fe_inv" c_secp256k1_fe_inv :: Ptr FE -> Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_fe_sqrt" c_secp256k1_fe_sqrt :: Ptr FE -> Ptr FE -> IO CInt
foreign import ccall unsafe "secp256k1_gej_double_var" c_secp256k1_gej_double_var :: Ptr GEJ -> Ptr GEJ -> Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_gej_add_var" c_secp256k1_gej_add_var :: Ptr GEJ -> Ptr GEJ -> Ptr GEJ -> Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_gej_add_ge_var" c_secp256k1_gej_add_ge_var :: Ptr GEJ -> Ptr GEJ -> Ptr GE -> Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_gej_add_zinv_var" c_secp256k1_gej_add_zinv_var :: Ptr GEJ -> Ptr GEJ -> Ptr GE -> Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_gej_eq_x_var" c_secp256k1_gej_eq_x_var :: Ptr FE -> Ptr GEJ -> IO CInt
foreign import ccall unsafe "secp256k1_gej_has_quad_y_var" c_secp256k1_gej_has_quad_y_var :: Ptr GEJ -> IO CInt
foreign import ccall unsafe "secp256k1_scalar_negate" c_secp256k1_scalar_negate :: Ptr Scalar -> Ptr Scalar -> IO ()
foreign import ccall unsafe "secp256k1_ecmult_wnaf" c_secp256k1_ecmult_wnaf :: Ptr CInt -> CInt -> Ptr Scalar -> CInt -> IO CInt
foreign import ccall unsafe "secp256k1_ecmult_context_init" c_secp256k1_ecmult_context_init :: Ptr Context -> IO ()
foreign import ccall "secp256k1_ecmult_context_build" c_secp256k1_ecmult_context_build :: Ptr Context -> FunPtr Callback -> IO ()
foreign import ccall unsafe "&secp256k1_ecmult_context_clear" c_secp256k1_ecmult_context_clear :: FunPtr (Ptr Context -> IO ())
foreign import ccall unsafe "secp256k1_ecmult" c_secp256k1_ecmult :: Ptr Context -> Ptr GEJ -> Ptr GEJ -> Ptr Scalar -> Ptr Scalar -> IO ()

normalizeWeak :: FE -> FE
normalizeWeak a = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
   c_secp256k1_fe_normalize_weak aptr
   peek aptr

normalize :: FE -> FE
normalize a = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
   c_secp256k1_fe_normalize_var aptr
   peek aptr

fePack :: FE -> ShortByteString
fePack a = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
 allocaArray 32 $ \rptr -> do
   c_secp256k1_fe_get_b32 rptr aptr
   toShort <$> packCStringLen (rptr, 32)

feUnpack :: Word256 -> FE
feUnpack a = unsafeDupablePerformIO $ do
 useAsCStringLen (encode a) $ \(aptr, 32) -> do
 alloca $ \rptr -> do
   _ <- c_secp256k1_fe_set_b32 rptr aptr
   peek rptr

feIsZero :: FE -> Bool
feIsZero a = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
   r <- c_secp256k1_fe_normalizes_to_zero_var aptr
   return $ r /= 0

neg :: CInt -> FE -> FE
neg m a = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
   c_secp256k1_fe_negate aptr aptr m
   peek aptr

mulInt :: CInt -> FE -> FE
mulInt m a = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
   c_secp256k1_fe_mul_int aptr m
   peek aptr

add :: FE -> FE -> FE
add a b = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
 with b $ \bptr -> do
   c_secp256k1_fe_add aptr bptr
   peek aptr

mul :: FE -> FE -> FE
mul a b = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
 with b $ \bptr -> do
   c_secp256k1_fe_mul aptr aptr bptr
   peek aptr

sqr :: FE -> FE
sqr a = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
   c_secp256k1_fe_sqr aptr aptr
   peek aptr

inv :: FE -> FE
inv a = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
   c_secp256k1_fe_inv aptr aptr
   peek aptr

sqrt :: FE -> Maybe FE
sqrt a = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
 alloca $ \rptr -> do
   CInt flag <- c_secp256k1_fe_sqrt rptr aptr
   if flag == 0 then return Nothing else Just <$> peek rptr

double :: GEJ -> GEJ
double a = unsafeDupablePerformIO $ do
  with a $ \aptr -> do
  with mempty $ \rptr -> do
    c_secp256k1_gej_double_var rptr aptr nullPtr
    peek rptr

addPoint :: GEJ -> GEJ -> GEJ
addPoint a b = unsafeDupablePerformIO $ do
  with a $ \aptr -> do
  with b $ \bptr -> do
  with mempty $ \rptr -> do
    c_secp256k1_gej_add_var rptr aptr bptr nullPtr
    peek rptr

offsetPoint :: GEJ -> GE -> (FE, GEJ)
offsetPoint a b = unsafeDupablePerformIO $ do
  with a $ \aptr -> do
  with b $ \bptr -> do
  with mempty $ \rptr -> do
  with feZero $ \zrptr -> do
    c_secp256k1_gej_add_ge_var rptr aptr bptr zrptr
    (,) <$> peek zrptr <*> peek rptr

offsetPointZinv :: GEJ -> GE -> FE -> GEJ
offsetPointZinv a b bzinv = unsafeDupablePerformIO $ do
  with a $ \aptr -> do
  with b $ \bptr -> do
  with bzinv $ \bzinvptr -> do
  with mempty $ \rptr -> do
    c_secp256k1_gej_add_zinv_var rptr aptr bptr bzinvptr
    peek rptr

eqXCoord :: FE -> GEJ -> Bool
eqXCoord x a = unsafeDupablePerformIO $ do
  with x $ \xptr -> do
  with a $ \aptr -> do
    CInt flag <- c_secp256k1_gej_eq_x_var xptr aptr
    return (flag /= 0)

hasQuadY :: GEJ -> Bool
hasQuadY a = unsafeDupablePerformIO $ do
  with a $ \aptr -> do
    CInt flag <- c_secp256k1_gej_has_quad_y_var aptr
    return (flag /= 0)

scalarNegate :: Scalar -> Scalar
scalarNegate a = unsafeDupablePerformIO $ do
  with a $ \aptr -> do
    c_secp256k1_scalar_negate aptr aptr
    peek aptr

wnaf :: Int -> Scalar -> [Int]
wnaf w a = unsafeDupablePerformIO $ do
  allocaArray (fromIntegral len) $ \wnafptr -> do
  with a $ \aptr -> do
    n <- c_secp256k1_ecmult_wnaf wnafptr len aptr (fromIntegral w)
    map fromIntegral <$> peekArray (fromIntegral n) wnafptr
 where
  len :: CInt
  len = 256

{-# NOINLINE ecMultContext #-}
ecMultContext :: ForeignPtr Context
ecMultContext = unsafePerformIO $ do
  p <- mallocForeignPtr
  withForeignPtr p $ \p -> do
    c_secp256k1_ecmult_context_init p
    c_secp256k1_ecmult_context_build p nullFunPtr -- TODO: Make a proper callback
  addForeignPtrFinalizer c_secp256k1_ecmult_context_clear p
  return p

ecMult :: GEJ -> Scalar -> Scalar -> GEJ
ecMult a na ng | na == scalarZero && ng == scalarZero = mempty
               | otherwise = unsafeDupablePerformIO $ do
  with a $ \aptr -> do
  with na $ \naptr -> do
  with ng $ \ngptr -> do
  with mempty $ \rptr -> do
  withForeignPtr ecMultContext $ \ctxptr -> do
    c_secp256k1_ecmult ctxptr rptr aptr naptr ngptr
    CInt flag <- peek (alignPtr (rptr `plusPtr` (3 * sizeOf (undefined :: FE))) (alignment (undefined :: CInt)))
    if flag == 0 then peek rptr else return mempty
