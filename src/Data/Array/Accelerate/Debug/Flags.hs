{-# LANGUAGE CPP                      #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE TypeOperators            #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-unused-imports     #-}
#if __GLASGOW_HASKELL__ >= 800
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}
#endif
-- |
-- Module      : Data.Array.Accelerate.Debug.Flags
-- Copyright   : [2008..2019] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Option parsing for debug flags
--

module Data.Array.Accelerate.Debug.Flags (

  Value,
  unfolding_use_threshold,
  max_simplifier_iterations,
  getValue,
  setValue,

  Flag(..),
  seq_sharing, acc_sharing, exp_sharing, array_fusion, simplify, flush_cache, force_recomp,
  fast_math, debug, verbose, dump_phases, dump_sharing, dump_fusion,
  dump_simpl_stats, dump_simpl_iterations, dump_vectorisation, dump_dot,
  dump_simpl_dot, dump_gc, dump_gc_stats, dump_cc, dump_ld, dump_asm, dump_exec,
  dump_sched,

  getFlag,
  setFlag, setFlags,
  clearFlag, clearFlags,

  when,
  unless,

  __cmd_line_flags,

) where


import Data.Bits
import Data.Int
import Data.Word
import Foreign.Ptr
import Foreign.Storable

import Control.Monad.IO.Class                                       ( MonadIO, liftIO )
import qualified Control.Monad                                      as M

newtype Flag  = Flag  Int
newtype Value = Value (Ptr Int)   -- of type HsInt in flags.c

-- We aren't using a "real" enum so that we can make use of the unused top
-- bits for other configuration options, not controlled by the command line
-- flags.
--
instance Enum Flag where
  toEnum            = Flag
  fromEnum (Flag x) = x

instance Show Flag where
  show (Flag x) =
    case x of
      0  -> "seq-sharing"
      1  -> "acc-sharing"
      2  -> "exp-sharing"
      3  -> "fusion"
      4  -> "simplify"
      5  -> "fast-math"
      6  -> "flush_cache"
      7  -> "force-recomp"
      8  -> "debug"
      9  -> "verbose"
      10 -> "dump-phases"
      11 -> "dump-sharing"
      12 -> "dump-fusion"
      13 -> "dump-simpl_stats"
      14 -> "dump-simpl_iterations"
      15 -> "dump-vectorisation"
      16 -> "dump-dot"
      17 -> "dump-simpl_dot"
      18 -> "dump-gc"
      19 -> "dump-gc_stats"
      20 -> "dump-cc"
      21 -> "dump-ld"
      22 -> "dump-asm"
      23 -> "dump-exec"
      24 -> "dump-sched"
      _  -> show x

-- | Conditional execution of a monadic debugging expression.
--
-- This does nothing unless the program is compiled in debug mode.
--
{-# INLINEABLE when #-}
when :: MonadIO m => Flag -> m () -> m ()
#if ACCELERATE_DEBUG
when f action = do
  yes <- liftIO $ getFlag f
  M.when yes action
#else
when _ _ = return ()
#endif


-- | The opposite of 'when'.
--
-- This does nothing unless the program is compiled in debug mode.
--
{-# INLINEABLE unless #-}
unless :: MonadIO m => Flag -> m () -> m ()
#ifdef ACCELERATE_DEBUG
unless f action = do
  yes <- liftIO $ getFlag f
  M.unless yes action
#else
unless _ _ = return ()
#endif


setValue   :: Value -> Int -> IO ()
setValue (Value f) v = poke f v

getValue   :: Value -> IO Int
getValue (Value f) = peek f

getFlag    :: Flag -> IO Bool
getFlag (Flag i) = do
  flags  <- peek __cmd_line_flags
  return $! testBit flags i

setFlag    :: Flag -> IO ()
setFlag (Flag i) = do
  flags <- peek __cmd_line_flags
  poke __cmd_line_flags (setBit flags i)

clearFlag  :: Flag -> IO ()
clearFlag (Flag i) = do
  flags <- peek __cmd_line_flags
  poke __cmd_line_flags (clearBit flags i)

setFlags   :: [Flag] -> IO ()
setFlags = mapM_ setFlag

clearFlags :: [Flag] -> IO ()
clearFlags = mapM_ clearFlag

-- notEnabled :: a
-- notEnabled = error $ unlines [ "Data.Array.Accelerate: Debugging options are disabled."
--                              , "Reinstall package 'accelerate' with '-fdebug' to enable them." ]


-- Import the underlying flag variables. These are defined in the file
-- cbits/flags.h as a bitfield and initialised at program initialisation.
--
-- SEE: [layout of command line options bitfield]
--
foreign import ccall "&__cmd_line_flags" __cmd_line_flags :: Ptr Word32

-- These @-f<blah>=INT@ values are used by the compiler
--
foreign import ccall "&__unfolding_use_threshold"   unfolding_use_threshold   :: Value  -- the magic cut-off figure for inlining
foreign import ccall "&__max_simplifier_iterations" max_simplifier_iterations :: Value  -- maximum number of scalar simplification passes

-- These @-f<blah>@ flags can be reversed with @-fno-<blah>@
--
seq_sharing           = Flag  0 -- recover sharing of sequence expressions
acc_sharing           = Flag  1 -- recover sharing of array computations
exp_sharing           = Flag  2 -- recover sharing of scalar expressions
array_fusion          = Flag  3 -- fuse array expressions
simplify              = Flag  4 -- simplify scalar expressions
fast_math             = Flag  5 -- delete persistent compilation cache(s)
flush_cache           = Flag  6 -- force recompilation of array programs
force_recomp          = Flag  7 -- use faster, less precise math library operations

-- These debugging flags are disable by default and are enabled with @-d<blah>@
--
debug                 = Flag  8 -- compile code with debugging symbols (-g)
verbose               = Flag  9 -- be very chatty
dump_phases           = Flag 10 -- print information about each phase of the compiler
dump_sharing          = Flag 11 -- sharing recovery phase
dump_fusion           = Flag 12 -- array fusion phase
dump_simpl_stats      = Flag 13 -- statistics form fusion/simplification
dump_simpl_iterations = Flag 14 -- output from each simplifier iteration
dump_vectorisation    = Flag 15 -- output from the vectoriser
dump_dot              = Flag 16 -- generate dot output of the program
dump_simpl_dot        = Flag 17 -- generate simplified dot output
dump_gc               = Flag 18 -- trace garbage collector
dump_gc_stats         = Flag 19 -- print final GC statistics
dump_cc               = Flag 20 -- trace code generation & compilation
dump_ld               = Flag 21 -- trace runtime linker
dump_asm              = Flag 22 -- trace assembler
dump_exec             = Flag 23 -- trace execution
dump_sched            = Flag 24 -- trace scheduler

