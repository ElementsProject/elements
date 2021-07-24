module Simplicity.LibSecp256k1.FFI
 ( Simplicity.LibSecp256k1.FFI.fe_pack, fe_unpack
 , fe_is_zero, fe_is_odd, fe_negate, fe_multiply_int, fe_add, fe_multiply, fe_square, fe_invert, fe_square_root
 , gej_double, gej_rescale, gej_add, gej_ge_add_ex, gej_ge_add_zinv
 , ge_scale_lambda
 , gej_x_equiv, has_quad_y
 , scalar_negate, scalar_split_lambda, scalar_split_128
 , wnaf, linear_combination, linear_combination_1
 ) where

import Control.Monad (forM_)
import Data.Bits (shiftR)
import Data.ByteString (packCStringLen, useAsCStringLen)
import Data.ByteString.Short (ShortByteString, toShort)
import Data.Serialize (decode, encode)
import Foreign.ForeignPtr (ForeignPtr, addForeignPtrFinalizer, mallocForeignPtr, withForeignPtr)
import Foreign.Marshal.Alloc (alloca, allocaBytes)
import Foreign.Marshal.Array (allocaArray, peekArray, withArray)
import Foreign.Marshal.Utils (with)
import Foreign.Ptr (FunPtr, Ptr, alignPtr, castPtr, plusPtr, nullFunPtr, nullPtr)
import Foreign.C.Types (CInt(..), CChar, CSize(..))
import Foreign.Storable (Storable(..))
import System.IO.Unsafe (unsafeDupablePerformIO, unsafePerformIO)

import Simplicity.Word
import qualified Simplicity.LibSecp256k1.Spec as Spec
import Simplicity.LibSecp256k1.Spec ( FE(..), fe_zero
                                    , GEJ(..), GE(..)
                                    , Scalar(..), scalar_zero
                                    )

instance Storable FE where
  sizeOf x = 10*sizeOf (undefined :: Word32)
  alignment _ = alignment (undefined :: Word32)
  peek ptr = allocaArray 32 $ \buf -> do
    c_secp256k1_fe_normalize_var ptr
    c_secp256k1_fe_get_b32 buf ptr
    Right fe <- decode <$> packCStringLen (buf,32)
    return $ fe_unpack fe
   where
    fe_unpack :: Word256 -> FE
    fe_unpack = Spec.fe . toInteger
  poke ptr fe =
    useAsCStringLen (encode (Spec.fe_pack fe)) $ \(buf, 32) -> do
      CInt 1 <- c_secp256k1_fe_set_b32 ptr buf
      return ()

instance Storable GEJ where
  sizeOf x = 3*sizeOf (undefined :: FE) + sizeOf (undefined :: CInt)
  alignment _ = alignment (undefined :: FE)
  peek ptr = do
    CInt flag <- peek (alignPtr (ptr `plusPtr` (3 * sizeOf (undefined :: FE))) (alignment (undefined :: CInt)))
    GEJ <$> peekElemOff ptr' 0 <*> peekElemOff ptr' 1 <*> if flag == 0 then peekElemOff ptr' 2 else pure fe_zero
   where
    ptr' = castPtr ptr
  poke ptr (GEJ x y z) = do
    pokeElemOff ptr' 0 x
    pokeElemOff ptr' 1 y
    pokeElemOff ptr' 2 z
    poke (alignPtr (ptr `plusPtr` (3 * sizeOf x)) (alignment flag)) flag
   where
    ptr' = castPtr ptr
    flag | fe_is_zero z = CInt 1 -- Note that we set the flag even for false fe_zeros.
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
  peek ptr = allocaArray 32 $ \buf -> do
    c_secp256k1_scalar_get_b32 buf ptr
    Right s <- decode <$> packCStringLen (buf,32)
    return $ scalar_unpack s
   where
    scalar_unpack :: Word256 -> Scalar
    scalar_unpack = Spec.scalar . toInteger
  poke ptr fe =
    useAsCStringLen (encode (Spec.scalar_pack fe)) $ \(buf, 32) -> do
      c_secp256k1_scalar_set_b32 ptr buf nullPtr
      return ()

data Context = Context (Ptr Word32) (Ptr Word32)

instance Storable Context where
  sizeOf x = 2*sizeOf (undefined :: Ptr Word32)
  alignment _ = alignment (undefined :: Ptr Word32)
  peek ptr = Context <$> (peekElemOff ptr' 0)
                     <*> (peekElemOff ptr' 1)
   where
    ptr' = castPtr ptr
  poke ptr (Context p0 p1) = pokeElemOff ptr' 0 p0
                          >> pokeElemOff ptr' 1 p1
   where
    ptr' = castPtr ptr

data StraussPointState = StraussPointState
data StraussState = StraussState (Ptr GEJ) (Ptr FE) (Ptr GE) (Ptr GE) (Ptr StraussPointState)

instance Storable StraussState where
  sizeOf x = 5*sizeOf (undefined :: Ptr a)
  alignment _ = alignment (undefined :: Ptr a)
  peek ptr = StraussState <$> (peekElemOff ptr' 0)
                          <*> (peekElemOff ptr' 1)
                          <*> (peekElemOff ptr' 2)
                          <*> (peekElemOff ptr' 3)
                          <*> (peekElemOff ptr' 4)
   where
    ptr' = castPtr ptr
  poke ptr (StraussState p0 p1 p2 p3 p4) = pokeElemOff ptr' 0 p0
                                        >> pokeElemOff ptr' 1 p1
                                        >> pokeElemOff ptr' 2 p2
                                        >> pokeElemOff ptr' 3 p3
                                        >> pokeElemOff ptr' 4 p4
   where
    ptr' = castPtr ptr

foreign import ccall safe "static &secp256k1_ecmult_prealloc" c_secp256k1_ecmult_prealloc :: Ptr CChar
foreign import ccall unsafe "secp256k1_fe_normalize_weak" c_secp256k1_fe_normalize_weak :: Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_fe_normalize_var" c_secp256k1_fe_normalize_var :: Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_fe_set_b32" c_secp256k1_fe_set_b32 :: Ptr FE -> Ptr CChar -> IO CInt
foreign import ccall unsafe "secp256k1_fe_get_b32" c_secp256k1_fe_get_b32 :: Ptr CChar -> Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_fe_normalizes_to_zero_var" c_secp256k1_fe_normalizes_to_zero_var :: Ptr FE -> IO CInt
foreign import ccall unsafe "secp256k1_fe_is_odd" c_secp256k1_fe_is_odd :: Ptr FE -> IO CInt
foreign import ccall unsafe "secp256k1_fe_negate" c_secp256k1_fe_negate :: Ptr FE -> Ptr FE -> CInt -> IO ()
foreign import ccall unsafe "secp256k1_fe_mul_int" c_secp256k1_fe_mul_int :: Ptr FE -> CInt -> IO ()
foreign import ccall unsafe "secp256k1_fe_add" c_secp256k1_fe_add :: Ptr FE -> Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_fe_mul" c_secp256k1_fe_mul :: Ptr FE -> Ptr FE -> Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_fe_sqr" c_secp256k1_fe_sqr :: Ptr FE -> Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_fe_inv" c_secp256k1_fe_inv :: Ptr FE -> Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_fe_sqrt" c_secp256k1_fe_sqrt :: Ptr FE -> Ptr FE -> IO CInt
foreign import ccall unsafe "secp256k1_gej_rescale" c_secp256k1_gej_rescale :: Ptr GEJ -> Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_gej_double_var" c_secp256k1_gej_double_var :: Ptr GEJ -> Ptr GEJ -> Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_gej_add_var" c_secp256k1_gej_add_var :: Ptr GEJ -> Ptr GEJ -> Ptr GEJ -> Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_gej_add_ge_var" c_secp256k1_gej_add_ge_var :: Ptr GEJ -> Ptr GEJ -> Ptr GE -> Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_gej_add_zinv_var" c_secp256k1_gej_add_zinv_var :: Ptr GEJ -> Ptr GEJ -> Ptr GE -> Ptr FE -> IO ()
foreign import ccall unsafe "secp256k1_gej_eq_x_var" c_secp256k1_gej_eq_x_var :: Ptr FE -> Ptr GEJ -> IO CInt
foreign import ccall unsafe "secp256k1_gej_has_quad_y_var" c_secp256k1_gej_has_quad_y_var :: Ptr GEJ -> IO CInt
foreign import ccall unsafe "secp256k1_ge_mul_lambda" c_secp256k1_ge_mul_lambda :: Ptr GE -> Ptr GE -> IO CInt
foreign import ccall unsafe "secp256k1_scalar_set_b32" c_secp256k1_scalar_set_b32 :: Ptr Scalar -> Ptr CChar -> Ptr CInt -> IO ()
foreign import ccall unsafe "secp256k1_scalar_get_b32" c_secp256k1_scalar_get_b32 :: Ptr CChar -> Ptr Scalar -> IO ()
foreign import ccall unsafe "secp256k1_scalar_negate" c_secp256k1_scalar_negate :: Ptr Scalar -> Ptr Scalar -> IO ()
foreign import ccall unsafe "secp256k1_scalar_split_lambda" c_secp256k1_scalar_split_lambda :: Ptr Scalar ->Ptr Scalar -> Ptr Scalar -> IO ()
foreign import ccall unsafe "secp256k1_scalar_split_128" c_secp256k1_scalar_split_128 :: Ptr Scalar ->Ptr Scalar -> Ptr Scalar -> IO ()
foreign import ccall unsafe "secp256k1_ecmult_wnaf" c_secp256k1_ecmult_wnaf :: Ptr CInt -> CInt -> Ptr Scalar -> CInt -> IO CInt
foreign import ccall unsafe "secp256k1_ecmult_context_init" c_secp256k1_ecmult_context_init :: Ptr Context -> IO ()
foreign import ccall "secp256k1_ecmult_context_build" c_secp256k1_ecmult_context_build :: Ptr Context -> Ptr (Ptr CChar) -> IO ()
foreign import ccall unsafe "&secp256k1_ecmult_context_clear" c_secp256k1_ecmult_context_clear :: FunPtr (Ptr Context -> IO ())
foreign import ccall unsafe "secp256k1_ecmult" c_secp256k1_ecmult :: Ptr Context -> Ptr GEJ -> Ptr GEJ -> Ptr Scalar -> Ptr Scalar -> IO ()
foreign import ccall unsafe "secp256k1_ecmult_strauss_wnaf" c_secp256k1_ecmult_strauss_wnaf :: Ptr Context -> Ptr StraussState -> Ptr GEJ -> CSize -> Ptr GEJ -> Ptr Scalar -> Ptr Scalar -> IO ()

fe_pack :: FE -> ShortByteString
fe_pack a = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
 allocaArray 32 $ \rptr -> do
   c_secp256k1_fe_get_b32 rptr aptr
   toShort <$> packCStringLen (rptr, 32)

fe_unpack :: Word256 -> FE
fe_unpack a = unsafeDupablePerformIO $ do
 useAsCStringLen (encode a) $ \(aptr, 32) -> do
 alloca $ \rptr -> do
   _ <- c_secp256k1_fe_set_b32 rptr aptr
   peek rptr

fe_is_zero :: FE -> Bool
fe_is_zero a = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
   r <- c_secp256k1_fe_normalizes_to_zero_var aptr
   return $ r /= 0

fe_is_odd :: FE -> Bool
fe_is_odd a = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
   r <- c_secp256k1_fe_is_odd aptr
   return $ r /= 0

fe_negate :: FE -> FE
fe_negate a = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
   c_secp256k1_fe_negate aptr aptr 1
   peek aptr

fe_multiply_int :: FE -> CInt -> FE
fe_multiply_int a b = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
   c_secp256k1_fe_mul_int aptr b
   peek aptr

fe_add :: FE -> FE -> FE
fe_add a b = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
 with b $ \bptr -> do
   c_secp256k1_fe_add aptr bptr
   peek aptr

fe_multiply :: FE -> FE -> FE
fe_multiply a b = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
 with b $ \bptr -> do
   c_secp256k1_fe_mul aptr aptr bptr
   peek aptr

fe_square :: FE -> FE
fe_square a = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
   c_secp256k1_fe_sqr aptr aptr
   peek aptr

fe_invert :: FE -> FE
fe_invert a = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
   c_secp256k1_fe_inv aptr aptr
   peek aptr

fe_square_root :: FE -> Maybe FE
fe_square_root a = unsafeDupablePerformIO $ do
 with a $ \aptr -> do
 alloca $ \rptr -> do
   CInt flag <- c_secp256k1_fe_sqrt rptr aptr
   if flag == 0 then return Nothing else Just <$> peek rptr

gej_rescale :: FE -> GEJ -> GEJ
gej_rescale c a | fe_is_zero c = mempty
                | otherwise = unsafeDupablePerformIO $ do
  with c $ \cptr -> do
  with a $ \aptr -> do
    c_secp256k1_gej_rescale aptr cptr
    peek aptr

gej_double :: GEJ -> GEJ
gej_double a = unsafeDupablePerformIO $ do
  with a $ \aptr -> do
  with mempty $ \rptr -> do
    c_secp256k1_gej_double_var rptr aptr nullPtr
    peek rptr

gej_add :: GEJ -> GEJ -> GEJ
gej_add a b = unsafeDupablePerformIO $ do
  with a $ \aptr -> do
  with b $ \bptr -> do
  with mempty $ \rptr -> do
    c_secp256k1_gej_add_var rptr aptr bptr nullPtr
    peek rptr

gej_ge_add_ex :: GEJ -> GE -> (FE, GEJ)
gej_ge_add_ex a b = unsafeDupablePerformIO $ do
  with a $ \aptr -> do
  with b $ \bptr -> do
  with mempty $ \rptr -> do
  with fe_zero $ \zrptr -> do
    c_secp256k1_gej_add_ge_var rptr aptr bptr zrptr
    (,) <$> peek zrptr <*> peek rptr

gej_ge_add_zinv :: GEJ -> GE -> FE -> GEJ
gej_ge_add_zinv a b bzinv = unsafeDupablePerformIO $ do
  with a $ \aptr -> do
  with b $ \bptr -> do
  with bzinv $ \bzinvptr -> do
  with mempty $ \rptr -> do
    c_secp256k1_gej_add_zinv_var rptr aptr bptr bzinvptr
    peek rptr

ge_scale_lambda :: GE -> GE
ge_scale_lambda a = unsafeDupablePerformIO $ do
  with a $ \aptr -> do
    c_secp256k1_ge_mul_lambda aptr aptr
    peek aptr

-- :TODO: c_secp256k1_gej_eq_x_var shouldn't be called with infinity.
gej_x_equiv :: GEJ -> FE -> Bool
gej_x_equiv a x = unsafeDupablePerformIO $ do
  with a $ \aptr -> do
  with x $ \xptr -> do
    CInt flag <- c_secp256k1_gej_eq_x_var xptr aptr
    return (flag /= 0)

has_quad_y :: GEJ -> Bool
has_quad_y a = unsafeDupablePerformIO $ do
  with a $ \aptr -> do
    CInt flag <- c_secp256k1_gej_has_quad_y_var aptr
    return (flag /= 0)

scalar_negate :: Scalar -> Scalar
scalar_negate a = unsafeDupablePerformIO $ do
  with a $ \aptr -> do
    c_secp256k1_scalar_negate aptr aptr
    peek aptr

scalar_split_lambda :: Scalar -> (Scalar, Scalar)
scalar_split_lambda a = unsafeDupablePerformIO $ do
  with a $ \aptr -> do
  with scalar_zero $ \r1ptr -> do
  with scalar_zero $ \r2ptr -> do
    c_secp256k1_scalar_split_lambda r1ptr r2ptr aptr
    (,) <$> peek r1ptr <*> peek r2ptr

scalar_split_128 :: Scalar -> (Scalar, Scalar)
scalar_split_128 a = unsafeDupablePerformIO $ do
  with a $ \aptr -> do
  with scalar_zero $ \r1ptr -> do
  with scalar_zero $ \r2ptr -> do
    c_secp256k1_scalar_split_128 r1ptr r2ptr aptr
    (,) <$> peek r1ptr <*> peek r2ptr

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
    with c_secp256k1_ecmult_prealloc $ \pa -> do
      c_secp256k1_ecmult_context_init p
      c_secp256k1_ecmult_context_build p pa
  addForeignPtrFinalizer c_secp256k1_ecmult_context_clear p
  return p

linear_combination_1 :: Scalar -> GEJ -> Scalar -> GEJ
linear_combination_1 na a ng = unsafeDupablePerformIO $ do
  with a $ \aptr -> do
  with na $ \naptr -> do
  with ng $ \ngptr -> do
  with mempty $ \rptr -> do
  withForeignPtr ecMultContext $ \ctxptr -> do
    c_secp256k1_ecmult ctxptr rptr aptr naptr ngptr
    CInt flag <- peek (alignPtr (rptr `plusPtr` (3 * sizeOf (undefined :: FE))) (alignment (undefined :: CInt)))
    if flag == 0 then peek rptr else return mempty

linear_combination :: [(Scalar, GEJ)] -> Scalar -> GEJ
linear_combination l ng = unsafeDupablePerformIO $ do
  allocaArray (n * wsize) $ \prejptr -> do
  allocaArray (n * wsize) $ \zrptr -> do
  allocaArray (n * wsize) $ \preaptr -> do
  allocaArray (n * wsize) $ \prealamptr -> do
  allocaBytes (n * sizeOfStraussPointState) $ \strausspointstateptr -> do
  with (StraussState prejptr zrptr preaptr prealamptr strausspointstateptr) $ \straussstateptr -> do
  withArray as $ \asptr -> do
  withArray nas $ \nasptr -> do
  with ng $ \ngptr -> do
  with mempty $ \rptr -> do
  withForeignPtr ecMultContext $ \ctxptr -> do
    c_secp256k1_ecmult_strauss_wnaf ctxptr straussstateptr rptr (fromIntegral n) asptr nasptr ngptr
    CInt flag <- peek (alignPtr (rptr `plusPtr` (3 * sizeOf (undefined :: FE))) (alignment (undefined :: CInt)))
    if flag == 0 then peek rptr else return mempty
 where
  (nas, as) = unzip l
  w = 5
  wsize = 2^(w - 2)
  n = length l
  sizeOfStraussPointState = 2 * sizeOf (undefined :: Scalar)
                          + (2 * 129 + 2) * sizeOf (undefined :: CInt)
                          + sizeOf (undefined :: CSize)
