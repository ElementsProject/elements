-- | This module defines the data structures that make up the signed data in a Bitcoin transaction.
module Simplicity.Bitcoin.DataTypes
  ( Script, Lock, Value
  , Outpoint(Outpoint), opHash, opIndex
  , SigTxInput(SigTxInput), sigTxiPreviousOutpoint, sigTxiValue, sigTxiSequence
  , TxOutput(TxOutput), txoValue, txoScript
  , SigTx(SigTx), sigTxVersion, sigTxIn, sigTxOut, sigTxLock, sigTxInputsHash, sigTxOutputsHash
  ) where

import Control.Monad (guard)
import Data.Array (Array, elems)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import Data.Word (Word64, Word32, Word8)
import Data.Serialize ( Serialize
                      , Get, get, getWord8, getWord16le, getWord32le, getWord64le, getLazyByteString
                      , Put, put, putWord8, putWord16le, putWord32le, putWord64le, putLazyByteString, runPutLazy
                      )

import Simplicity.Digest

{-
getVarInteger :: Get Word64
getVarInteger = go =<< getWord8
 where
  go 0xff = getWord64le
  go 0xfe = fromIntegral `fmap` getWord32le
  go 0xfd = fromIntegral `fmap` getWord16le
  go x = return (fromIntegral x)

putVarInteger :: Word64 -> Put
putVarInteger x | x < 0xfd = putWord8 (fromIntegral x)
                | x <= 0xffff = putWord8 0xfd >> putWord16le (fromIntegral x)
                | x <= 0xffffffff = putWord8 0xfe >> putWord32le (fromIntegral x)
                | otherwise = putWord8 0xff >> putWord64le (fromIntegral x)

getVarByteString :: Get BSL.ByteString
getVarByteString = do l <- getVarInteger
                      let l' = fromIntegral l :: Word32 -- length must be strictly less than 2^32.
                                                        -- This is how Bitcoin Core reads bytestrings.
                      getLazyByteString (fromIntegral l')
  where

putVarByteString :: BSL.ByteString -> Put
putVarByteString s | len < 2^32 = putVarInteger len >> putLazyByteString s
 where
  len :: Word64
  len = BSL.foldlChunks (\a c -> a + fromIntegral (BS.length c)) 0 s
-}

-- | Unparsed Bitcoin Script.
-- Script in transactions outputs do not have to be parsable, so we encode this as a raw 'Data.ByteString.ByteString'.
type Script = BSL.ByteString

-- | Transaction locktime.
-- This represents either a block height or a block time.
-- It is encoded as a 32-bit value.
type Lock = Word32

-- | A type for Bitcoin amounts measured in units of satoshi.
type Value = Word64 -- bitcoin uses an Int64, but it doesn't really matter.

moneyRange :: Value -> Bool
moneyRange v = v <= 21000000 * 10^8

getValue :: Get Value
getValue = do
  v <- getWord64le
  guard $ moneyRange v
  return v

-- | An outpoint is an index into the TXO set.
data Outpoint = Outpoint { opHash :: Hash256
                         , opIndex :: Word32
                         } deriving Show

instance Serialize Outpoint where
  get = Outpoint <$> get <*> getWord32le
  put (Outpoint h i) = put h >> putWord32le i

-- | The data type for signed transaction inputs.
-- Note that signed transaction inputs for BIP 143 include the value of the input, which doesn't appear in the serialized transaction input format.
data SigTxInput = SigTxInput { sigTxiPreviousOutpoint :: Outpoint
                             , sigTxiValue :: Value
                             , sigTxiSequence :: Word32
                             } deriving Show

{-
instance Serialize SigTxInput where
  get = SigTxInput <$> get <*> getValue <*> getWord32le
  put (SigTxInput p v sq) = put p >> putWord64le v >> putWord32le sq
-}

-- | The data type for transaction outputs.
-- The signed transactin output format is identical to the serialized transaction output format.
data TxOutput = TxOutput { txoValue :: Value
                         , txoScript :: Script -- length must be strictly less than 2^32.
                         } deriving Show

{-
instance Serialize TxOutput where
  get = TxOutput <$> getValue <*> getVarByteString
  put (TxOutput v s) = putWord64le v >> putVarByteString s
-}

-- | The data type for transactions in the context of signatures.
-- The data signed in a BIP 143 directly covers input values.
data SigTx = SigTx { sigTxVersion :: Word32
                   , sigTxIn :: Array Word32 SigTxInput
                   , sigTxOut :: Array Word32 TxOutput
                   , sigTxLock :: Lock
                   } deriving Show

{-
instance Serialize Tx where
  get = Tx <$> getWord32le <*> getList <*> getList <*> get
  put (Tx v is os t) = putWord32le v >> putList is >> putList os >> put t
-}

sigTxInputsHash tx = bslHash . runPutLazy $ mapM_ go (elems (sigTxIn tx))
 where
  go txi = put (sigTxiPreviousOutpoint txi)
        >> putWord64le (sigTxiValue txi)
        >> putWord32le (sigTxiSequence txi)

sigTxOutputsHash tx = bslHash . runPutLazy $ mapM_ go (elems (sigTxOut tx))
 where
  go txo = putWord64le (txoValue txo)
        >> put (bslHash (txoScript txo))
