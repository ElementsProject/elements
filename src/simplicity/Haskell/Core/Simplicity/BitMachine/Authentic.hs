{-# LANGUAGE FlexibleContexts #-}
-- | This modules implements the Bit Machine according to its specification.
--
-- This @Authentic@ module properly tracks undefined values in the Bit Machine's cells and will properly crash when, for example, reading from undefined cells.
-- Other non-authentic implemenations of the Bit Machine might invoke undefined behavour when the Bit Machine crashes.
module Simplicity.BitMachine.Authentic
 ( runMachine
 , Stats(..)
 , instrumentMachine
 ) where

import Control.Monad ((>=>), guard, unless)
import Control.Monad.Fail (MonadFail)
import Control.Monad.Writer (MonadWriter, tell)
import Data.Functor.Fixedpoint (cata)
import Data.Monoid (Endo(..))
import Data.Vector ((//), (!?))
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as VM
import Lens.Family2 ((^.), to)

import Simplicity.BitMachine (Cell, MachineCodeF(..), MachineCode, Interpreter)

-- For the Bit Machine a frame is an array of Cell's and a cursor pointing at a position within the array.
data Frame = Frame { fData :: !(V.Vector Cell)
                   , fOffset :: !Int
                   }

-- Create a frame from a list of cells with the cursor initialized to the start of the frame.
fInit cells = Frame (V.fromList cells) 0

-- Create an empty frame of a given size with the cursor initialized to the start of the frame.
fNew n | 0 <= n = Frame (V.replicate n Nothing) 0

-- Reset a frame by moving the cursor from the end of the frame to the beginning of the frame.
-- This function fails if the input frame doesn't have its cursor at the end of the frame.
fReset fm = unless (fOffset fm == length (fData fm)) (fail "fReset: offset not at end of frame")
         >> return (fm {fOffset = 0})

-- Return the value of the cell under the frame's cursor.
-- This function fails if the cursor is at the end of the frame.
fRead fr = maybe (fail "fRead: offset out of range") return (fData fr !? fOffset fr)

-- Return an array of 'n' cells starting from the frame's cursor.
-- The function fails if there are not enough cells in the frame.
fSlice n = to go
 where
  go (Frame dt os) | os + n <= V.length dt = return $ V.slice os n dt
                   | otherwise = fail "fSlice: slice too large"

-- Write a Cell to a frame at the frame's cursor and advance the frame's cursor by 1.
-- This function fails if the cursor is at the end of the frame.
fWrite v (Frame dt os) | os < V.length dt = return $ Frame dt' os'
                       | otherwise = fail "fWrite: data too large"
 where
  dt' = dt // [(os, v)]
  os' = os+1

-- Write a vector of Cells to a frame starting at the frame's cursor and advance the frame's cursor by the length of the written data.
-- This function fails if there isn't sufficent room in the frame to write the data.
fFill v (Frame dt os) | os + n <= V.length dt = return $ Frame dt' os'
 where
  n = V.length v
  dt' = V.modify go dt
   where
    go mv = V.copy (VM.slice os n mv) v
  os' = os + n

-- Move a frame's cursor by 'n' cells.
-- If 'n' is positive the cursor moves forward and if 'n' negative the cursor moves backward.
-- This function fails if the cursors would end up past the end of the frame or past the beginning of the frame.
fMove n (Frame dt os) | 0 <= os' && os' <= length dt = return $ Frame dt os'
                      | otherwise = fail "fMove: index out of range"
 where
  os' = os+n

-- Returns the number of cells in the frame.
fSize (Frame dt _) = V.length dt

-- The active frames are the frames at the top of the read frame stack and the write frame stack.
data Active = Active { activeReadFrame :: !Frame
                     , activeWriteFrame :: !Frame
                     }

-- Two lenses that access the active read and write frames.
rf f x = (\y -> x { activeReadFrame = y }) <$> f (activeReadFrame x)
wf f x = (\y -> x { activeWriteFrame = y }) <$> f (activeWriteFrame x)

-- The state of the Bit Machine consists of the inactive read and write frames, and the active frames.
data State = State { inactiveReadFrames :: [Frame]
                   , activeFrames :: !Active
                   , inactiveWriteFrames :: [Frame]
                   }
-- A lens that accesses the active frames of a state.
act f x = (\y -> x { activeFrames = y }) <$> f (activeFrames x)

-- A state transformation that turns one state into another with possible side effects (such as crashing).
-- MachineCode instructions are interpreted as these State transformations.
type StateTrans m = State -> m State

-- Below are functions used in 'runMachineF' to implement the instructions for the Bit Machine.
abort :: MonadFail m => StateTrans m
abort _ = fail "explicit abort"

copy :: MonadFail m => Int -> StateTrans m
copy n st = do
  v <- st^.act.rf.fSlice n
  (act.wf) (fFill v) st

newFrame :: MonadFail m => Int -> StateTrans m
newFrame n (State irf (Active rf wf) iwf) = do
  unless (0 <= n) (fail "newFrame: negative size")
  return $ State irf (Active rf (fNew n)) (wf:iwf)

moveFrame :: MonadFail m => StateTrans m
moveFrame (State irf (Active rf wf) (iwf0:iwf)) = do
  nrf <- fReset wf
  return $ State (rf:irf) (Active nrf iwf0) iwf
moveFrame _ = fail "moveFrame: empty write frame stack"

dropFrame (State (irf0:irf) (Active _ wf) iwf) =
  return $ State irf (Active irf0 wf) iwf
dropFrame _ = fail "dropFrame: empty read frame stack"

-- 'runMachineF' is a MachineCode algebra that implements the bit machine.
-- 'runMachine' calls this algebra to recursively evaluate 'MachineCode'. 
runMachineF :: MonadFail m => MachineCodeF (StateTrans m) -> StateTrans m
runMachineF End = return
runMachineF Abort = abort
runMachineF (Write b k) = (act.wf) (fWrite (Just b)) >=> k
runMachineF (Copy n k) | 0 <= n = copy n >=> k
                       | otherwise = \_ -> fail "runMachineF Copy: negative index"
runMachineF (Skip n k) | 0 <= n = (act.wf) (fMove n) >=> k
                       | otherwise = \_ -> fail "runMachineF Skip: negative index"
runMachineF (Fwd n k) | 0 <= n = (act.rf) (fMove n) >=> k
                      | otherwise = \_ -> fail "runMachineF Fwd: negative index"
runMachineF (Bwd n k) | 0 <= n = (act.rf) (fMove (-n)) >=> k
                      | otherwise = \_ -> fail "runMachineF Bwd: negative index"
runMachineF (NewFrame n k) = newFrame n >=> k
runMachineF (MoveFrame k) = moveFrame >=> k
runMachineF (DropFrame k) = dropFrame >=> k
runMachineF (Read k0 k1) = \st -> do
  v <- fRead (st^.act.rf)
  b <- maybe (fail "runMachine Read: cell value undefined") return v
  if b then k1 st else k0 st

-- Create an inital state from the inital data for the read frame and the size of the write frame.
initialState :: [Cell] -> Int -> State
initialState input outLength = State [] (Active (fInit input) (fNew outLength)) []

-- Extract the write frame's data which contains the output of the Bit Machine.
finalState :: MonadFail m => State -> m [Cell]
finalState (State [] (Active _ output) []) = return $ V.toList (fData output)
finalState _ = fail "finalState: invalid final state"

-- | The implemenation of the authentic Bit Machine.
--
-- Given 'MachineCode', creates an 'Interpreter'.
-- The 'Interpreter' expects an inital state specified by the data for the initial read frame and the size of the initial write frame.
-- The 'Interpreter' returns the final data on the write frame.
runMachine :: MonadFail m => MachineCode -> Interpreter m
runMachine code input outputSize = cata runMachineF code (initialState input outputSize)
                               >>= finalState

-- These functions are used to insturment the Bit Machine and calculate the computations resources used during execution.
actReadFrameSize :: State -> Int
actReadFrameSize st = fSize (st^.act.rf)

actWriteFrameSize :: State -> Int
actWriteFrameSize st = fSize (st^.act.wf)

inactReadFrameSizes :: State -> [Int]
inactReadFrameSizes st = fSize <$> inactiveReadFrames st

inactWriteFrameSizes :: State -> [Int]
inactWriteFrameSizes st = fSize <$> inactiveWriteFrames st

-- | A collection of statistics about computation resources used during execution of the Bit Machine.
data Stats = Stats { memSize :: !Int   -- ^ Maximum total number of 'Cell's occuring during execution
                   , stackSize :: !Int -- ^ Maximum total number of frames occuring during execution
                   } deriving Show

instance Semigroup Stats where
  (<>) = mappend

-- The monoid instance for statistics combine intermediate execution profiles of the Bit Machine's state.
instance Monoid Stats where
  mempty = Stats { memSize = 0
                 , stackSize = 0
                 }
  a `mappend` b = Stats { memSize = max (memSize a) (memSize b)
                        , stackSize = max (stackSize a) (stackSize b)
                        }

-- This function computes the memory statistics of a snapshot of the Bit Machine's state.
profile :: State -> Stats
profile st = Stats { memSize = sum readStackStats + sum writeStackStats + actReadFrameSize st + actWriteFrameSize st
                   , stackSize = length readStackStats + length writeStackStats
                   }
 where
  readStackStats = inactReadFrameSizes st
  writeStackStats = inactWriteFrameSizes st

-- A state transformation that doesn't tranform the state but results in a side effect that emits the statistics of the current state.
instrument st = tell [profile st] >> return st

-- | An instrumented version of the authentic Bit Machine.
--
-- 'intrumentMachine' behaves as 'runMachine' but also profiles the execution returning 'Stats' about computation resources used during execution.
instrumentMachine :: (MonadWriter [Stats] m, MonadFail m) => MachineCode -> Interpreter m
instrumentMachine code input outputSize = interpreter (initialState input outputSize)
                                      >>= finalState
 where
  -- add an instrumentation step at the beginning of the runMachineF algebra.
  instrumentMachineF f = instrument >=> runMachineF f
  -- run the modified algebra and add a final instrumentation step to the result.
  interpreter = cata instrumentMachineF code >=> instrument
