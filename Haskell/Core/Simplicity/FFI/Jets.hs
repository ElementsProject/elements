{-# LANGUAGE ForeignFunctionInterface #-}
module Simplicity.FFI.Jets
 ( adder32, fullAdder32
 , subtractor32, fullSubtractor32
 , multiplier32, fullMultiplier32
 , sha256_hashBlock
 , fe_sqrt, offsetPoint, ecmult
 , schnorrAssert
 ) where

import Foreign.Ptr (Ptr)

import Simplicity.FFI.Frame
import qualified Simplicity.Programs.Sha256.Lib as Sha256
import qualified Simplicity.Programs.LibSecp256k1.Lib as LibSecp256k1
import Simplicity.Programs.Word

foreign import ccall unsafe "" c_adder32 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_fullAdder32 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_subtractor32 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_fullSubtractor32 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_multiplier32 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_fullMultiplier32 :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_sha256_hashBlock :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_fe_sqrt :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_offsetPoint :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_ecmult :: Ptr FrameItem -> Ptr FrameItem -> IO Bool
foreign import ccall unsafe "" c_schnorrAssert :: Ptr FrameItem -> Ptr FrameItem -> IO Bool

adder32 :: (Word32, Word32) -> Maybe (Bit, Word32)
adder32 = unsafeLocalCoreJet c_adder32

fullAdder32 :: ((Word32, Word32), Bit) -> Maybe (Bit, Word32)
fullAdder32 = unsafeLocalCoreJet c_fullAdder32

subtractor32 :: (Word32, Word32) -> Maybe (Bit, Word32)
subtractor32 = unsafeLocalCoreJet c_subtractor32

fullSubtractor32 :: ((Word32, Word32), Bit) -> Maybe (Bit, Word32)
fullSubtractor32 = unsafeLocalCoreJet c_fullSubtractor32

multiplier32 :: (Word32, Word32) -> Maybe Word64
multiplier32 = unsafeLocalCoreJet c_multiplier32

fullMultiplier32 :: ((Word32, Word32), (Word32, Word32)) -> Maybe Word64
fullMultiplier32 = unsafeLocalCoreJet c_fullMultiplier32

sha256_hashBlock :: (Sha256.Hash, Sha256.Block) -> Maybe Sha256.Hash
sha256_hashBlock = unsafeLocalCoreJet c_sha256_hashBlock

fe_sqrt :: LibSecp256k1.FE -> Maybe (Either () LibSecp256k1.FE)
fe_sqrt = unsafeLocalCoreJet c_fe_sqrt

offsetPoint :: (LibSecp256k1.GEJ, LibSecp256k1.GE) -> Maybe (LibSecp256k1.FE, LibSecp256k1.GEJ)
offsetPoint = unsafeLocalCoreJet c_offsetPoint

ecmult :: ((LibSecp256k1.GEJ, LibSecp256k1.Scalar), LibSecp256k1.Scalar) -> Maybe (LibSecp256k1.GEJ)
ecmult = unsafeCoreJet c_ecmult -- c_ecmult initializes global variables

schnorrAssert :: ((LibSecp256k1.XOnlyPubKey, Sha256.Hash), LibSecp256k1.Sig) -> Maybe ()
schnorrAssert = unsafeCoreJet c_schnorrAssert -- c_schnorrAssert initializes global variables
