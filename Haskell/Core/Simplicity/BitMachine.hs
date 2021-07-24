{-# LANGUAGE DeriveTraversable, GADTs #-}
-- | This module defines encoding and decoding of values for the Bit Machine and the instructions for operating the Bit Machine.
module Simplicity.BitMachine
 ( Cell
 , encode, decode
 , Interpreter, executeUsing
 -- * Bit Machine Code
 , MachineCode, MachineCodeF(..), MachineCodeK
 , end, abort, write, copy, skip, fwd, bwd, newFrame, moveFrame, dropFrame, (|||)
 , bump, nop
 ) where

import Control.Monad (unless)
import Control.Monad.Fail (MonadFail)
import Data.Functor.Fixedpoint (Fix(..), cata)

import Simplicity.Ty
import Simplicity.BitMachine.Ty

-- | The type representing Cell's for the Bit Machine.
--
--    * @'Just' 'False'@ denotes a cell holding a @0@ value.
--    * @'Just' 'True'@ denotes a cell holding a @1@ value.
--    * 'Nothing' denotes a cell holding an unknown value @?@.
type Cell = Maybe Bool

safeSplitAt :: MonadFail m => Int -> [a] -> m ([a], [a])
safeSplitAt n l = do
  unless (0 <= n && n <= length l) (fail "safeSplitAt: index out of range")
  return (splitAt n l)

-- | Encodes a value of a Simplicity type as a list of cells.
--
-- @'length' ('encode' a) = 'bitSizeR' ('reifyProxy' ('Data.Functor.Identity.Identity' a))@
encode :: TyC a => a -> [Cell]
encode x = encodeR reify x []
 where
  encodeR :: TyReflect a -> a -> [Cell] -> [Cell]
  encodeR OneR () = id
  encodeR (SumR a b) (Left x) = ([Just False] ++) . (replicate (padLR a b) Nothing ++) . encodeR a x
  encodeR (SumR a b) (Right y) = ([Just True] ++) . (replicate (padRR a b) Nothing ++) . encodeR b y
  encodeR (ProdR a b) (x, y) = encodeR a x . encodeR b y

-- | Decodes a value of a Simplicity type from a list of cells.
--
-- 'decode' does strict checking of the padding used in sum types.
-- The padding must be filled with unknown values (represented by 'Nothing').
--
-- @'decode' ('encode' a) = 'return' a@
decode :: (MonadFail m, TyC a) => [Cell] -> m a
decode = decodeR reify
 where
  decodeR :: MonadFail m => TyReflect a -> [Cell] -> m a
  decodeR OneR [] = return ()
  decodeR (SumR a b) (Just v:l) = do
    (l0, l1) <- safeSplitAt (pad a b) l
    unless (all (==Nothing) l0) (fail "decodeR SumR: bad padding")
    if v then Right <$> decodeR b l1 else Left <$> decodeR a l1
   where
    pad = if v then padRR else padLR
  decodeR (ProdR a b) l = do
    (l0, l1) <- safeSplitAt (bitSizeR a) l
    (,) <$> decodeR a l0 <*> decodeR b l1
  decodeR _ _ = fail "decode: invalid encoding"

-- | @'Interpreter' m@ is a type capturing the form of Bit Machine execution functions.
--
-- The Bit Machine expects an initial read frame and the size of the initial write frame.
-- Execution of the Bit Machine returns the final write frame, which should be the same length as the initial size of the write frame.
-- The 'm' parameter is a monad that captures side effects of execution such as failure, logging for aggregated signature, instrumentation of the Bit Machine for analysis, etc.
type Interpreter m = [Cell] -> Int -> m [Cell]

-- | Given a "compiler" that transforms any Simplicity program into a Bit Machine 'Interpreter', and a Simplicity program, execute it by encoding the input and decoding the output.
--
-- This is largely a wrapper for handling encoding and decoding of values when executing Simplicity progams on an implementaiton of the Bit Machine.
--
-- Typically this function is called as
--
-- @'executeUsing' (runMachine . translator) program input@
--
-- where @translator@ converts a Simplicity term into a Bit Machine 'MachineCode', @runMachine@ executes 'MachineCode' and @program@ is a Simplicity term.
executeUsing :: (MonadFail m, TyC a, TyC b) => (term a b -> Interpreter m) -> term a b -> a -> m b
executeUsing interpreter program input = result
 where
  result = interpreter program (encode input) (bitSizeR (reifyProxy result)) >>= decode

-- | 'MachineCode' is the type of (complete) BitMachine programs.
-- 
-- It is a sequence of instructions with the exception of 'Read' which has two branches.
-- The sequence is terminated by 'End' or 'Abort'.
-- The semantics of Bit Machine program is defined by a model of execution found in 'Simplicity.BitMachine.Authentic'.
--
-- This type is defined as the explicit fixedpoint of the 'MachineCodeF' functor.
type MachineCode = Fix MachineCodeF

-- | This is the functor used to define 'MachineCode'.
data MachineCodeF a = End
                    | Abort
                    | Write Bool a
                    | Copy Int a
                    | Skip Int a
                    | Fwd Int a
                    | Bwd Int a
                    | NewFrame Int a
                    | MoveFrame a
                    | DropFrame a
                    | Read a a
                    deriving (Functor, Show)

-- | 'MachineCodeK' is a type used during construction of Bit Machine programs and can be viewed as a type holding incomplete programs.
-- It is used in the same manner as difference lists (or 'StringS') and used a continuation expecting the rest of the program.
--
-- The @p '.' q@ expression puts two 'MachineCodeK' values in sequence, and @p '|||' q@ is a 'MachineCodeK' value for a program that deterministically chooses between @p@ and @q@.
type MachineCodeK = MachineCode -> MachineCode

-- |'end' instructs the Bit Machine execution to terminate yeilding success.
end :: MachineCode
end = Fix End

-- | 'abort' instructs the Bit Machine execution to terminate by explicitly failing.
abort :: MachineCodeK
abort _ = Fix Abort

-- | @'write' b@ instructs the Bit Machine to write the value 'b' to the active write frame and advance its cursor.
write :: Bool -> MachineCodeK
write b k = Fix (Write b k)

-- | @'copy' n@ instructs the Bit Machine to copy 'n' values from the active read frame to the active write frame and advance the active write frame's cursor to the end of the written data.
copy :: Int -> MachineCodeK
copy i k = Fix (Copy i k)

-- | @'skip' n@ instructs the Bit Machine to advance the active write frame's cursor by 'n' cells.
skip :: Int -> MachineCodeK
skip i k = Fix (Skip i k)

-- | @'fwd' n@ instructs the Bit Machine to advance the active read frame's cursor by 'n' cells.
fwd :: Int -> MachineCodeK
fwd i k = Fix (Fwd i k)

-- | @'bwd' n@ instructs the Bit Machine to move the active read frame's cursor backwards by 'n' cells.
bwd :: Int -> MachineCodeK
bwd i k = Fix (Bwd i k)

-- | @'newFrame' n@ instructs the Bit Machine to push a new write frame of size 'n' onto the write frame stack.
newFrame :: Int -> MachineCodeK
newFrame i k = Fix (NewFrame i k)

-- | 'moveFrame' instructs the Bit Machine to pop a frame off the write frame stack and push it onto the read frame stack while reseting that frame's cursor to the beginning of the frame.
moveFrame :: MachineCodeK
moveFrame k = Fix (MoveFrame k)

-- | 'dropFrame' instructs the Bit Machine to pop a frame off the read frame stack.
dropFrame :: MachineCodeK
dropFrame k = Fix (DropFrame k)

-- | @p '|||' q@ instructs the Bit Machine to deterministically choose between two programs by reading the value under the active read frame's cursor.
-- If the value read is '0' then 'p' is executed.
-- If the value read is '1' then 'q' is executed.
(|||) :: MachineCodeK -> MachineCodeK -> MachineCodeK
x ||| y = \k -> Fix (Read (x k) (y k))

-- | @'bump' i p@ temporarily advances the active read frame's cursor by @i@ cells and executes @p@ before moving the cursor back.
--
-- It is intended that @p@ return the read frame stack back to its original configuration after execution; however, this is not enforced by 'bump'.
--
-- @'bump' i p = 'fwd' i . p . 'bwd' i@
bump :: Int -> MachineCodeK -> MachineCodeK
bump i p = fwd i . p . bwd i

-- | 'nop' is the empty program that does nothing.
nop :: MachineCodeK
nop k = k
