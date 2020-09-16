{-# LANGUAGE GADTs, ScopedTypeVariables #-}
-- | This module provides the Simplicity primitives specific for Bitcoin or Bitcoin-like applications.
module Simplicity.Bitcoin.Primitive
  ( Prim(..), primPrefix, primName
  , getPrimBit, getPrimByte, putPrimBit, putPrimByte
  , PrimEnv, primEnv
  , primSem
  ) where

import Data.Array (Array, (!), bounds, elems, inRange)
import qualified Data.List as List
import Data.Serialize (Get, getWord8,
                       Putter, put, putWord8, putWord32le, putWord64le, runPutLazy)
import qualified Data.Word

import Simplicity.Digest
import Simplicity.Bitcoin.DataTypes
import Simplicity.Serialization
import Simplicity.Ty
import Simplicity.Ty.Word

data Prim a b where
  Version :: Prim () Word32
  LockTime :: Prim () Word32
  InputsHash :: Prim () Word256
  OutputsHash :: Prim () Word256
  NumInputs :: Prim () Word32
  TotalInputValue :: Prim () Word64
  CurrentPrevOutpoint :: Prim () (Word256,Word32)
  CurrentValue :: Prim () Word64
  CurrentSequence :: Prim () Word32
  CurrentIndex :: Prim () Word32
  InputPrevOutpoint :: Prim Word32 (Either () (Word256,Word32))
  InputValue :: Prim Word32 (Either () Word64)
  InputSequence :: Prim Word32 (Either () Word32)
  NumOutputs :: Prim () Word32
  TotalOutputValue :: Prim () Word64
  OutputValue :: Prim Word32 (Either () Word64)
  OutputScriptHash :: Prim Word32 (Either () Word256)
  ScriptCMR :: Prim () Word256
-- Other possible ideas:
  -- TxId :: Prim () Word256

instance Eq (Prim a b) where
  Version == Version = True
  LockTime == LockTime = True
  InputsHash == InputsHash = True
  OutputsHash == OutputsHash = True
  NumInputs == NumInputs = True
  TotalInputValue == TotalInputValue = True
  CurrentPrevOutpoint == CurrentPrevOutpoint = True
  CurrentValue == CurrentValue = True
  CurrentSequence == CurrentSequence = True
  CurrentIndex == CurrentIndex = True
  InputPrevOutpoint == InputPrevOutpoint = True
  InputValue == InputValue = True
  InputSequence == InputSequence = True
  NumOutputs == NumOutputs = True
  TotalOutputValue == TotalOutputValue = True
  OutputValue == OutputValue = True
  OutputScriptHash == OutputScriptHash = True
  ScriptCMR == ScriptCMR = True
  _ == _ = False

primPrefix :: String
primPrefix = "Bitcoin"

-- Consider deriving Show instead?
primName :: Prim a b -> String
primName Version = "version"
primName LockTime = "lockTime"
primName InputsHash = "inputsHash"
primName OutputsHash = "outputsHash"
primName NumInputs = "numInputs"
primName TotalInputValue = "totalInputValue"
primName CurrentPrevOutpoint = "currentPrevOutpoint"
primName CurrentValue = "currentValue"
primName CurrentSequence = "currentSequence"
primName CurrentIndex = "currentIndex"
primName InputPrevOutpoint = "inputPrevOutpoint"
primName InputValue = "inputValue"
primName InputSequence = "inputSequence"
primName NumOutputs = "maxOutputs"
primName TotalOutputValue = "totalOutputValue"
primName OutputValue = "outputValue"
primName OutputScriptHash = "outputScriptHash"
primName ScriptCMR = "scriptCMR"

getPrimBit :: Monad m => m Bool -> m (SomeArrow Prim)
getPrimBit next =
  ((((makeArrow Version & makeArrow LockTime) & (makeArrow InputsHash)) & (makeArrow OutputsHash & makeArrow NumInputs)) &
   ((makeArrow TotalInputValue & makeArrow CurrentPrevOutpoint) & (makeArrow CurrentValue & makeArrow CurrentSequence))) &
  ((((makeArrow CurrentIndex & makeArrow InputPrevOutpoint) & (makeArrow InputValue)) & (makeArrow InputSequence & makeArrow NumOutputs)) &
   ((makeArrow TotalOutputValue & makeArrow OutputValue) & (makeArrow OutputScriptHash & makeArrow ScriptCMR)))
 where
  l & r = next >>= \b -> if b then r else l
  makeArrow p = return (SomeArrow p)

getPrimByte :: Data.Word.Word8 -> Get (Maybe (SomeArrow Prim))
getPrimByte = return . decode
 where
  decode 0x24 = Just $ SomeArrow Version
  decode 0x25 = Just $ SomeArrow LockTime
  decode 0x26 = Just $ SomeArrow InputsHash
  decode 0x27 = Just $ SomeArrow OutputsHash
  decode 0x28 = Just $ SomeArrow NumInputs
  decode 0x29 = Just $ SomeArrow TotalInputValue
  decode 0x2a = Just $ SomeArrow CurrentPrevOutpoint
  decode 0x2b = Just $ SomeArrow CurrentValue
  decode 0x2c = Just $ SomeArrow CurrentSequence
  decode 0x2d = Just $ SomeArrow CurrentIndex
  decode 0x2e = Just $ SomeArrow InputPrevOutpoint
  decode 0x2f = Just $ SomeArrow InputValue
  decode 0x30 = Just $ SomeArrow InputSequence
  decode 0x31 = Just $ SomeArrow NumOutputs
  decode 0x32 = Just $ SomeArrow TotalOutputValue
  decode 0x33 = Just $ SomeArrow OutputValue
  decode 0x34 = Just $ SomeArrow OutputScriptHash
  decode 0x35 = Just $ SomeArrow ScriptCMR
  decode _ = Nothing

putPrimBit :: Prim a b -> DList Bool
putPrimBit Version             = ([False,False,False,False,False]++)
putPrimBit LockTime            = ([False,False,False,False,True]++)
putPrimBit InputsHash          = ([False,False,False,True]++)
putPrimBit OutputsHash         = ([False,False,True,False]++)
putPrimBit NumInputs           = ([False,False,True,True]++)
putPrimBit TotalInputValue     = ([False,True,False,False]++)
putPrimBit CurrentPrevOutpoint = ([False,True,False,True]++)
putPrimBit CurrentValue        = ([False,True,True,False]++)
putPrimBit CurrentSequence     = ([False,True,True,True]++)
putPrimBit CurrentIndex        = ([True,False,False,False,False]++)
putPrimBit InputPrevOutpoint   = ([True,False,False,False,True]++)
putPrimBit InputValue          = ([True,False,False,True]++)
putPrimBit InputSequence       = ([True,False,True,False]++)
putPrimBit NumOutputs          = ([True,False,True,True]++)
putPrimBit TotalOutputValue    = ([True,True,False,False]++)
putPrimBit OutputValue         = ([True,True,False,True]++)
putPrimBit OutputScriptHash    = ([True,True,True,False]++)
putPrimBit ScriptCMR           = ([True,True,True,True]++)

putPrimByte :: Putter (Prim a b)
putPrimByte = putWord8 . encode
 where
  encode :: Prim a b -> Data.Word.Word8
  encode Version             = 0x24
  encode LockTime            = 0x25
  encode InputsHash          = 0x26
  encode OutputsHash         = 0x27
  encode NumInputs           = 0x28
  encode TotalInputValue     = 0x29
  encode CurrentPrevOutpoint = 0x2a
  encode CurrentValue        = 0x2b
  encode CurrentSequence     = 0x2c
  encode CurrentIndex        = 0x2d
  encode InputPrevOutpoint   = 0x2e
  encode InputValue          = 0x2f
  encode InputSequence       = 0x30
  encode NumOutputs          = 0x31
  encode TotalOutputValue    = 0x32
  encode OutputValue         = 0x33
  encode OutputScriptHash    = 0x34
  encode ScriptCMR           = 0x35

data PrimEnv = PrimEnv { envTx :: SigTx
                       , envIx :: Data.Word.Word32
                       , envScriptCMR :: Hash256
                       , envInputsHash :: Hash256
                       , envOutputsHash :: Hash256
                       }

primEnv :: SigTx -> Data.Word.Word32 -> Hash256 -> Maybe PrimEnv
primEnv tx ix scmr | cond = Just $ PrimEnv { envTx = tx
                                           , envIx = ix
                                           , envScriptCMR = scmr
                                           , envInputsHash = sigTxInputsHash tx
                                           , envOutputsHash = sigTxOutputsHash tx
                                           }
                   | otherwise = Nothing
 where
  cond = inRange (bounds (sigTxIn tx)) ix

primSem :: Prim a b -> a -> PrimEnv -> Maybe b
primSem p a env = interpret p a
 where
  tx = envTx env
  ix = envIx env
  lookup a i | inRange range i = Just $ a ! i
             | otherwise       = Nothing
   where
    range = bounds a
  lookupInput = lookup (sigTxIn tx)
  lookupOutput = lookup (sigTxOut tx)
  currentInput = lookupInput ix
  maxInput = snd . bounds $ sigTxIn tx
  maxOutput = snd . bounds $ sigTxOut tx
  cast :: Maybe a -> Either () a
  cast (Just x) = Right x
  cast Nothing = Left ()
  atInput :: (SigTxInput -> a) -> Word32 -> Either () a
  atInput f = cast . fmap f . lookupInput . fromInteger . fromWord32
  atOutput :: (TxOutput -> a) -> Word32 -> Either () a
  atOutput f = cast . fmap f . lookupOutput . fromInteger . fromWord32
  encodeHash = toWord256 . integerHash256
  encodeOutpoint op = (toWord256 . integerHash256 $ opHash op, toWord32 . fromIntegral $ opIndex op)
  interpret Version = const . return . toWord32 . toInteger $ sigTxVersion tx
  interpret LockTime = const . return . toWord32 . toInteger $ sigTxLock tx
  interpret InputsHash = const . return . encodeHash $ envInputsHash env
  interpret OutputsHash = const . return . encodeHash $ envOutputsHash env
  interpret NumInputs = const . return . toWord32 . toInteger $ 1 + maxInput
  interpret TotalInputValue = const . return . toWord64 . fromIntegral . List.sum $ sigTxiValue <$> elems (sigTxIn tx)
  interpret CurrentPrevOutpoint = const $ encodeOutpoint . sigTxiPreviousOutpoint <$> currentInput
  interpret CurrentValue = const $ toWord64 . toInteger . sigTxiValue <$> currentInput
  interpret CurrentSequence = const $ toWord32 . toInteger . sigTxiSequence <$> currentInput
  interpret CurrentIndex = const . return . toWord32 . toInteger $ ix
  interpret InputPrevOutpoint = return . (atInput $ encodeOutpoint . sigTxiPreviousOutpoint)
  interpret InputValue = return . (atInput $ toWord64 . toInteger . sigTxiValue)
  interpret InputSequence = return . (atInput $ toWord32 . toInteger . sigTxiSequence)
  interpret NumOutputs = const . return . toWord32 . toInteger $ 1 + maxOutput
  interpret TotalOutputValue = const . return . toWord64 . fromIntegral . List.sum $ txoValue <$> elems (sigTxOut tx)
  interpret OutputValue = return . (atOutput $ toWord64 . fromIntegral . txoValue)
  interpret OutputScriptHash = return . (atOutput $ toWord256 . integerHash256 . bslHash . txoScript)
  interpret ScriptCMR = const . return . toWord256 . integerHash256 $ envScriptCMR env
