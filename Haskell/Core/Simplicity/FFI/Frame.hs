{-# LANGUAGE ForeignFunctionInterface, GADTs #-}
module Simplicity.FFI.Frame
 ( unsafeCoreJet, unsafeLocalCoreJet
 , FrameItem
 ) where

import Control.Arrow (Kleisli(Kleisli))
import Data.Functor.Compose (Compose(..))
import Foreign.C.Types (CSize(..))
import Foreign.Ptr (Ptr, plusPtr)
import Foreign.Storable (Storable(..))
import Foreign.Marshal.Alloc (allocaBytes)
import Foreign.Marshal.Unsafe (unsafeLocalState)
import Foreign.Marshal.Utils (fillBytes)
import System.IO.Unsafe (unsafePerformIO)

import Simplicity.BitMachine.Ty (bitSizeR, padLR, padRR)
import Simplicity.Ty

-- Abstract types representing the C data types used in frame.c
newtype UWORD = UWORD UWORD
newtype FrameItem = FrameItem FrameItem

foreign import ccall unsafe "&" c_sizeof_UWORD :: Ptr CSize
foreign import ccall unsafe "&" c_sizeof_frameItem :: Ptr CSize

foreign import ccall unsafe "" c_readBit :: Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_writeBit :: Ptr FrameItem -> Bool -> IO ()
foreign import ccall unsafe "" c_skipBits :: Ptr FrameItem -> CSize -> IO ()
foreign import ccall unsafe "" c_initReadFrame :: Ptr FrameItem -> CSize -> Ptr UWORD -> IO ()
foreign import ccall unsafe "" c_initWriteFrame :: Ptr FrameItem -> CSize -> Ptr UWORD -> IO ()

sizeof_UWORD :: Int
sizeof_UWORD = fromIntegral . unsafeLocalState $ peek c_sizeof_UWORD

sizeof_frameItem :: Int
sizeof_frameItem = fromIntegral . unsafeLocalState $ peek c_sizeof_frameItem

allocaFrameItem :: (Ptr FrameItem -> IO a) -> IO a
allocaFrameItem = allocaBytes sizeof_frameItem

readFrameItem :: TyC a => Ptr FrameItem -> IO a
readFrameItem ptr = readFrameItemR reify ptr

writeFrameItem :: TyC a => a -> Ptr FrameItem -> IO ()
writeFrameItem ptr = writeFrameItemR reify ptr

readFrameItemR :: TyReflect a -> Ptr FrameItem -> IO a
readFrameItemR OneR _ = return ()
readFrameItemR (SumR a b) frame = do
  bit <- c_readBit frame
  if bit then Right <$> readFrameItemR b frame else Left <$> readFrameItemR a frame
readFrameItemR (ProdR a b) frame = (,) <$> readFrameItemR a frame <*> readFrameItemR b frame

writeFrameItemR :: TyReflect a -> a -> Ptr FrameItem -> IO ()
writeFrameItemR OneR _ _ = return ()
writeFrameItemR (SumR a b) (Left v) frame = do
  c_writeBit frame False
  c_skipBits frame (fromIntegral (padLR a b))
  writeFrameItemR a v frame
writeFrameItemR (SumR a b) (Right v) frame = do
  c_writeBit frame True
  c_skipBits frame (fromIntegral (padRR a b))
  writeFrameItemR b v frame
writeFrameItemR (ProdR a b) (va, vb) frame = writeFrameItemR a va frame >> writeFrameItemR b vb frame

withReadFrame :: Int -> Ptr UWORD -> (Ptr FrameItem -> IO a) -> IO a
withReadFrame n from k = allocaFrameItem $ \frame -> c_initReadFrame frame (fromIntegral n) from >> k frame

withWriteFrame :: Int -> Ptr UWORD -> (Ptr FrameItem -> IO a) -> IO a
withWriteFrame n from k = allocaFrameItem $ \frame -> c_initWriteFrame frame (fromIntegral n) from >> k frame

runCoreJet :: (TyC a, TyC b) => (Ptr FrameItem -> Ptr FrameItem -> IO Bool) -> a -> IO (Maybe b)
runCoreJet jet = go
 where
  (aR, bR) = reifyArrow . Kleisli $ Compose . go
  roundUWord n = -((-n) `div` (8 * sizeof_UWORD))
  aSize = roundUWord (bitSizeR aR) * sizeof_UWORD
  bSize = roundUWord (bitSizeR bR) * sizeof_UWORD
  arrSize = aSize + bSize
  go a = allocaBytes arrSize $ \arr -> do
    fillBytes arr 0 arrSize
    withWriteFrame (bitSizeR aR) (arr `plusPtr` aSize) $ writeFrameItem a
    result <- withReadFrame (bitSizeR aR) arr $ \readFrame ->
              withWriteFrame (bitSizeR bR) (arr `plusPtr` arrSize) $ \writeFrame ->
              jet writeFrame readFrame
    if result
      then Just <$> (withReadFrame (bitSizeR bR) (arr `plusPtr` aSize) $ readFrameItem)
      else return Nothing

-- | This cannot be used with jets that access global variables, which include some elliptic curve operations.
unsafeLocalCoreJet :: (TyC a, TyC b) => (Ptr FrameItem -> Ptr FrameItem -> IO Bool) -> a -> Maybe b
unsafeLocalCoreJet jet = unsafeLocalState . runCoreJet jet

unsafeCoreJet :: (TyC a, TyC b) => (Ptr FrameItem -> Ptr FrameItem -> IO Bool) -> a -> Maybe b
unsafeCoreJet jet = unsafePerformIO . runCoreJet jet
