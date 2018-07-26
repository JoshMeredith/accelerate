{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE CPP                  #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UnboxedTuples        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Array.Data
-- Copyright   : [2008..2017] Manuel M T Chakravarty, Gabriele Keller
--               [2009..2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module fixes the concrete representation of Accelerate arrays.  We
-- allocate all arrays using pinned memory to enable safe direct-access by
-- non-Haskell code in multi-threaded code.  In particular, we can safely pass
-- pointers to an array's payload to foreign code.
--

module Data.Array.Accelerate.Array.Data (

  -- * Array operations and representations
  ArrayElt(..), ArrayData, MutableArrayData, runArrayData,
  ArrayEltR(..), GArrayData(..),

  -- * Array tuple operations
  fstArrayData, sndArrayData, pairArrayData,

  -- * Type macros
  HTYPE_INT, HTYPE_WORD, HTYPE_LONG, HTYPE_UNSIGNED_LONG, HTYPE_CCHAR,

  -- * Allocator internals
  registerForeignPtrAllocator,

) where

-- friends
import Data.Array.Accelerate.Array.Unique
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.Debug.Flags
import Data.Array.Accelerate.Debug.Monitoring
import Data.Array.Accelerate.Debug.Trace

-- standard libraries
import Control.Applicative
import Control.Monad
import Control.Monad.Primitive
import Data.Bits
import Data.Char
import Data.IORef
import Data.Maybe
import Data.Primitive.ByteArray
import Data.Typeable                                                ( Typeable )
import Foreign.ForeignPtr
import Foreign.Ptr
import Foreign.Storable
import Language.Haskell.TH
import System.IO.Unsafe
import Text.Printf
import Prelude

import GHC.Ptr                                                      ( Ptr(..) )
import GHC.TypeLits                                                 ( KnownNat, natVal' )
import GHC.Base                                                     ( Int(..), IO(..), Proxy#, proxy#, unsafeCoerce#, newAlignedPinnedByteArray#, byteArrayContents#, copyAddrToByteArray#, copyByteArrayToAddr# )
import GHC.ForeignPtr                                               ( ForeignPtr(..), ForeignPtrContents(..) )


-- Determine the underlying type of a Haskell CLong or CULong.
--
$( runQ [d| type HTYPE_INT = $(
              case finiteBitSize (undefined::Int) of
                32 -> [t| Int32 |]
                64 -> [t| Int64 |]
                _  -> error "I don't know what architecture I am" ) |] )

$( runQ [d| type HTYPE_WORD = $(
              case finiteBitSize (undefined::Word) of
                32 -> [t| Word32 |]
                64 -> [t| Word64 |]
                _  -> error "I don't know what architecture I am" ) |] )

$( runQ [d| type HTYPE_LONG = $(
              case finiteBitSize (undefined::CLong) of
                32 -> [t| Int32 |]
                64 -> [t| Int64 |]
                _  -> error "I don't know what architecture I am" ) |] )

$( runQ [d| type HTYPE_UNSIGNED_LONG = $(
              case finiteBitSize (undefined::CULong) of
                32 -> [t| Word32 |]
                64 -> [t| Word64 |]
                _  -> error "I don't know what architecture I am" ) |] )

$( runQ [d| type HTYPE_CCHAR = $(
              case isSigned (undefined::CChar) of
                True  -> [t| Int8  |]
                False -> [t| Word8 |] ) |] )


-- Array representation
-- --------------------

-- |Immutable array representation
--
type ArrayData e = MutableArrayData e

-- |Mutable array representation
--
type MutableArrayData e = GArrayData UniqueArray e

-- Array representation in dependence on the element type, but abstracting
-- over the basic array type (in particular, abstracting over mutability)
--
data family GArrayData :: (* -> *) -> * -> *
data instance GArrayData ba ()        = AD_Unit
data instance GArrayData ba Int       = AD_Int     (ba Int)
data instance GArrayData ba Int8      = AD_Int8    (ba Int8)
data instance GArrayData ba Int16     = AD_Int16   (ba Int16)
data instance GArrayData ba Int32     = AD_Int32   (ba Int32)
data instance GArrayData ba Int64     = AD_Int64   (ba Int64)
data instance GArrayData ba Word      = AD_Word    (ba Word)
data instance GArrayData ba Word8     = AD_Word8   (ba Word8)
data instance GArrayData ba Word16    = AD_Word16  (ba Word16)
data instance GArrayData ba Word32    = AD_Word32  (ba Word32)
data instance GArrayData ba Word64    = AD_Word64  (ba Word64)
data instance GArrayData ba CShort    = AD_CShort  (ba Int16)
data instance GArrayData ba CUShort   = AD_CUShort (ba Word16)
data instance GArrayData ba CInt      = AD_CInt    (ba Int32)
data instance GArrayData ba CUInt     = AD_CUInt   (ba Word32)
data instance GArrayData ba CLong     = AD_CLong   (ba HTYPE_LONG)
data instance GArrayData ba CULong    = AD_CULong  (ba HTYPE_UNSIGNED_LONG)
data instance GArrayData ba CLLong    = AD_CLLong  (ba Int64)
data instance GArrayData ba CULLong   = AD_CULLong (ba Word64)
data instance GArrayData ba Half      = AD_Half    (ba Half)
data instance GArrayData ba Float     = AD_Float   (ba Float)
data instance GArrayData ba Double    = AD_Double  (ba Double)
data instance GArrayData ba CFloat    = AD_CFloat  (ba Float)
data instance GArrayData ba CDouble   = AD_CDouble (ba Double)
data instance GArrayData ba Bool      = AD_Bool    (ba Word8)
data instance GArrayData ba Char      = AD_Char    (ba Char)
data instance GArrayData ba CChar     = AD_CChar   (ba HTYPE_CCHAR)
data instance GArrayData ba CSChar    = AD_CSChar  (ba Int8)
data instance GArrayData ba CUChar    = AD_CUChar  (ba Word8)
data instance GArrayData ba (Vec n a) = AD_Vec     (GArrayData ba a)
data instance GArrayData ba (a, b)    = AD_Pair    (GArrayData ba a) (GArrayData ba b)

deriving instance Typeable GArrayData


-- | GADT to reify the 'ArrayElt' class.
--
data ArrayEltR a where
  ArrayEltRunit    :: ArrayEltR ()
  ArrayEltRint     :: ArrayEltR Int
  ArrayEltRint8    :: ArrayEltR Int8
  ArrayEltRint16   :: ArrayEltR Int16
  ArrayEltRint32   :: ArrayEltR Int32
  ArrayEltRint64   :: ArrayEltR Int64
  ArrayEltRword    :: ArrayEltR Word
  ArrayEltRword8   :: ArrayEltR Word8
  ArrayEltRword16  :: ArrayEltR Word16
  ArrayEltRword32  :: ArrayEltR Word32
  ArrayEltRword64  :: ArrayEltR Word64
  ArrayEltRcshort  :: ArrayEltR CShort
  ArrayEltRcushort :: ArrayEltR CUShort
  ArrayEltRcint    :: ArrayEltR CInt
  ArrayEltRcuint   :: ArrayEltR CUInt
  ArrayEltRclong   :: ArrayEltR CLong
  ArrayEltRculong  :: ArrayEltR CULong
  ArrayEltRcllong  :: ArrayEltR CLLong
  ArrayEltRcullong :: ArrayEltR CULLong
  ArrayEltRhalf    :: ArrayEltR Half
  ArrayEltRfloat   :: ArrayEltR Float
  ArrayEltRdouble  :: ArrayEltR Double
  ArrayEltRcfloat  :: ArrayEltR CFloat
  ArrayEltRcdouble :: ArrayEltR CDouble
  ArrayEltRbool    :: ArrayEltR Bool
  ArrayEltRchar    :: ArrayEltR Char
  ArrayEltRcchar   :: ArrayEltR CChar
  ArrayEltRcschar  :: ArrayEltR CSChar
  ArrayEltRcuchar  :: ArrayEltR CUChar
  ArrayEltRvec     :: ArrayEltR a -> ArrayEltR (Vec n a)  -- not restrictive enough
  ArrayEltRpair    :: ArrayEltR a -> ArrayEltR b -> ArrayEltR (a,b)

-- Array operations
-- ----------------
--
-- TLM: do we need to INLINE these functions to get good performance interfacing
--      to external libraries, especially Repa?

class ArrayElt e where
  type ArrayPtrs e
  arrayElt               :: ArrayEltR e
  --
  unsafeIndexArrayData   :: ArrayData e -> Int -> e
  ptrsOfArrayData        :: ArrayData e -> ArrayPtrs e
  touchArrayData         :: ArrayData e -> IO ()
  --
  newArrayData           :: Int -> IO (MutableArrayData e)
  unsafeReadArrayData    :: MutableArrayData e -> Int      -> IO e
  unsafeWriteArrayData   :: MutableArrayData e -> Int -> e -> IO ()
  unsafeFreezeArrayData  :: MutableArrayData e -> IO (ArrayData e)
  ptrsOfMutableArrayData :: MutableArrayData e -> IO (ArrayPtrs e)
  --
  {-# INLINE unsafeFreezeArrayData  #-}
  {-# INLINE ptrsOfMutableArrayData #-}
  unsafeFreezeArrayData  = return
  ptrsOfMutableArrayData = return . ptrsOfArrayData

instance ArrayElt () where
  type ArrayPtrs () = ()
  arrayElt          = ArrayEltRunit
  {-# INLINE newArrayData         #-}
  {-# INLINE ptrsOfArrayData      #-}
  {-# INLINE touchArrayData       #-}
  {-# INLINE unsafeIndexArrayData #-}
  {-# INLINE unsafeReadArrayData  #-}
  {-# INLINE unsafeWriteArrayData #-}
  newArrayData !_                    = return AD_Unit
  ptrsOfArrayData      AD_Unit       = ()
  touchArrayData       AD_Unit       = return ()
  unsafeIndexArrayData AD_Unit !_    = ()
  unsafeReadArrayData  AD_Unit !_    = return ()
  unsafeWriteArrayData AD_Unit !_ () = return ()

-- Bool arrays are stored as arrays of bytes. While this is memory inefficient,
-- it is better suited to parallel backends than a packed bit-vector
-- representation.
--
instance ArrayElt Bool where
  type ArrayPtrs Bool = Ptr Word8
  arrayElt            = ArrayEltRbool
  {-# INLINE newArrayData         #-}
  {-# INLINE ptrsOfArrayData      #-}
  {-# INLINE touchArrayData       #-}
  {-# INLINE unsafeIndexArrayData #-}
  {-# INLINE unsafeReadArrayData  #-}
  {-# INLINE unsafeWriteArrayData #-}
  newArrayData size                     = AD_Bool <$> newArrayData' size
  ptrsOfArrayData      (AD_Bool ba)     = unsafeUniqueArrayPtr ba
  touchArrayData       (AD_Bool ba)     = touchUniqueArray ba
  unsafeIndexArrayData (AD_Bool ba) i   = toBool  $! unsafeIndexArray ba i
  unsafeReadArrayData  (AD_Bool ba) i   = toBool <$> unsafeReadArray ba i
  unsafeWriteArrayData (AD_Bool ba) i e = unsafeWriteArray ba i (fromBool e)

instance (KnownNat n, ArrayElt a, ArrayPtrs a ~ Ptr e, Storable e) => ArrayElt (Vec n a) where
  type ArrayPtrs (Vec n a) = ArrayPtrs a
  arrayElt                 = ArrayEltRvec arrayElt
  {-# INLINE newArrayData         #-}
  {-# INLINE ptrsOfArrayData      #-}
  {-# INLINE touchArrayData       #-}
  {-# INLINE unsafeIndexArrayData #-}
  {-# INLINE unsafeReadArrayData  #-}
  {-# INLINE unsafeWriteArrayData #-}
  newArrayData size           = AD_Vec <$> newArrayData (fromIntegral (natVal' (proxy# :: Proxy# n)) * size)
  ptrsOfArrayData (AD_Vec ba) = ptrsOfArrayData ba
  touchArrayData  (AD_Vec ba) = touchArrayData ba
  unsafeIndexArrayData vec ix = unsafePerformIO $! unsafeReadArrayData vec ix
  --
  unsafeReadArrayData (AD_Vec ba) ix = do
    let n                   = fromIntegral (natVal' (proxy# :: Proxy# n))
        !bytes@(I# bytes#)  = n * sizeOf (undefined :: e)
        !(Ptr addr#)        = ptrsOfArrayData ba `plusPtr` (ix * bytes)
    --
    mba@(MutableByteArray mba#) <- newByteArray (n * bytes)
    primitive_ (copyAddrToByteArray# addr# mba# 0# bytes#)
    ByteArray ba# <- unsafeFreezeByteArray mba
    return $! Vec ba#
  --
  unsafeWriteArrayData (AD_Vec ba) ix (Vec ba#) =
    let n                   = fromIntegral (natVal' (proxy# :: Proxy# n))
        !bytes@(I# bytes#)  = n * sizeOf (undefined :: e)
        !(Ptr addr#)        = ptrsOfArrayData ba `plusPtr` (ix * bytes)
    in
    primitive_ (copyByteArrayToAddr# ba# 0# addr# bytes#)

instance (ArrayElt a, ArrayElt b) => ArrayElt (a, b) where
  type ArrayPtrs (a, b) = (ArrayPtrs a, ArrayPtrs b)
  arrayElt              = ArrayEltRpair arrayElt arrayElt
  {-# INLINE newArrayData           #-}
  {-# INLINE ptrsOfArrayData        #-}
  {-# INLINE ptrsOfMutableArrayData #-}
  {-# INLINE touchArrayData         #-}
  {-# INLINE unsafeFreezeArrayData  #-}
  {-# INLINE unsafeIndexArrayData   #-}
  {-# INLINE unsafeReadArrayData    #-}
  {-# INLINE unsafeWriteArrayData   #-}
  newArrayData size                             = AD_Pair <$> newArrayData size <*> newArrayData size
  touchArrayData         (AD_Pair a b)          = touchArrayData a >> touchArrayData b
  ptrsOfArrayData        (AD_Pair a b)          = (ptrsOfArrayData a, ptrsOfArrayData b)
  ptrsOfMutableArrayData (AD_Pair a b)          = (,) <$> ptrsOfMutableArrayData a <*> ptrsOfMutableArrayData b
  unsafeReadArrayData    (AD_Pair a b) i        = (,) <$> unsafeReadArrayData a i <*> unsafeReadArrayData b i
  unsafeIndexArrayData   (AD_Pair a b) i        = (unsafeIndexArrayData a i, unsafeIndexArrayData b i)
  unsafeWriteArrayData   (AD_Pair a b) i (x, y) = unsafeWriteArrayData a i x >> unsafeWriteArrayData b i y
  unsafeFreezeArrayData  (AD_Pair a b)          = AD_Pair <$> unsafeFreezeArrayData a <*> unsafeFreezeArrayData b


-- Array tuple operations
-- ----------------------

{-# INLINE fstArrayData #-}
fstArrayData :: ArrayData (a, b) -> ArrayData a
fstArrayData (AD_Pair x _) = x

{-# INLINE sndArrayData #-}
sndArrayData :: ArrayData (a, b) -> ArrayData b
sndArrayData (AD_Pair _ y) = y

{-# INLINE pairArrayData #-}
pairArrayData :: ArrayData a -> ArrayData b -> ArrayData (a, b)
pairArrayData = AD_Pair


-- Auxiliary functions
-- -------------------

{-# INLINE toBool #-}
toBool :: Word8 -> Bool
toBool 0 = False
toBool _ = True

{-# INLINE fromBool #-}
fromBool :: Bool -> Word8
fromBool True  = 1
fromBool False = 0

-- | Safe combination of creating and fast freezing of array data.
--
{-# INLINE runArrayData #-}
runArrayData
    :: IO (MutableArrayData e, e)
    -> (ArrayData e, e)
runArrayData st = unsafePerformIO $ do
  (mad, r) <- st
  return (mad, r)

-- Returns the element of an immutable array at the specified index. This does
-- no bounds checking.
--
{-# INLINE unsafeIndexArray #-}
unsafeIndexArray :: Storable e => UniqueArray e -> Int -> e
unsafeIndexArray ua i =
  unsafePerformIO $! unsafeReadArray ua i

-- Read an element from a mutable array at the given index. This does no bounds
-- checking.
--
{-# INLINE unsafeReadArray #-}
unsafeReadArray :: Storable e => UniqueArray e -> Int -> IO e
unsafeReadArray ua i =
  withUniqueArrayPtr ua $ \ptr -> peekElemOff ptr i

-- Write an element into a mutable array at the given index. This does no bounds
-- checking.
--
{-# INLINE unsafeWriteArray #-}
unsafeWriteArray :: Storable e => UniqueArray e -> Int -> e -> IO ()
unsafeWriteArray ua i e =
  withUniqueArrayPtr ua $ \ptr -> pokeElemOff ptr i e

-- Allocate a new array with enough storage to hold the given number of
-- elements.
--
-- The array is uninitialised and, in particular, allocated lazily. The latter
-- is important because it means that for backends that have discrete memory
-- spaces (e.g. GPUs), we will not increase host memory pressure simply to track
-- intermediate arrays that contain meaningful data only on the device.
--
{-# INLINE newArrayData' #-}
newArrayData' :: forall e. Storable e => Int -> IO (UniqueArray e)
newArrayData' !size
  = $internalCheck "newArrayData" "size must be >= 0" (size >= 0)
  $ newUniqueArray <=< unsafeInterleaveIO $ do
      let bytes = size * sizeOf (undefined :: e)
      new <- readIORef __mallocForeignPtrBytes
      ptr <- new bytes
      traceIO dump_gc $ printf "gc: allocated new host array (size=%d, ptr=%s)" bytes (show ptr)
      didAllocateBytesLocal (fromIntegral bytes)
      return (castForeignPtr ptr)

-- | Register the given function as the callback to use to allocate new array
-- data on the host containing the specified number of bytes. The returned array
-- must be pinned (with respect to Haskell's GC), so that it can be passed to
-- foreign code.
--
registerForeignPtrAllocator
    :: (Int -> IO (ForeignPtr Word8))
    -> IO ()
registerForeignPtrAllocator new = do
  traceIO dump_gc "registering new array allocator"
  atomicWriteIORef __mallocForeignPtrBytes new

{-# NOINLINE __mallocForeignPtrBytes #-}
__mallocForeignPtrBytes :: IORef (Int -> IO (ForeignPtr Word8))
__mallocForeignPtrBytes = unsafePerformIO $! newIORef mallocPlainForeignPtrBytesAligned

-- | Allocate the given number of bytes with 16-byte alignment. This is
-- essential for SIMD instructions.
--
-- Additionally, we return a plain ForeignPtr, which unlike a regular ForeignPtr
-- created with 'mallocForeignPtr' carries no finalisers. It is an error to try
-- to add a finaliser to the plain ForeignPtr. For our purposes this is fine,
-- since in Accelerate finalisers are handled using Lifetime
--
{-# INLINE mallocPlainForeignPtrBytesAligned #-}
mallocPlainForeignPtrBytesAligned :: Int -> IO (ForeignPtr a)
mallocPlainForeignPtrBytesAligned (I# size) = IO $ \s ->
  case newAlignedPinnedByteArray# size 16# s of
    (# s', mbarr# #) -> (# s', ForeignPtr (byteArrayContents# (unsafeCoerce# mbarr#)) (PlainPtr mbarr#) #)


-- Instances
-- ---------
--
$(runQ $ do
    let
        integralTypes :: [(Name, Maybe Name)]
        integralTypes =
          [ (''Int,     Nothing)
          , (''Int8,    Nothing)
          , (''Int16,   Nothing)
          , (''Int32,   Nothing)
          , (''Int64,   Nothing)
          , (''Word,    Nothing)
          , (''Word8,   Nothing)
          , (''Word16,  Nothing)
          , (''Word32,  Nothing)
          , (''Word64,  Nothing)
          , (''CShort,  Just ''Int16)
          , (''CUShort, Just ''Word16)
          , (''CInt,    Just ''Int32)
          , (''CUInt,   Just ''Word32)
          , (''CLong,   Just ''HTYPE_LONG)
          , (''CULong,  Just ''HTYPE_UNSIGNED_LONG)
          , (''CLLong,  Just ''Int64)
          , (''CULLong, Just ''Word64)
          ]

        floatingTypes :: [(Name, Maybe Name)]
        floatingTypes =
          [ (''Half,    Nothing)
          , (''Float,   Nothing)
          , (''Double,  Nothing)
          , (''CFloat,  Just ''Float)
          , (''CDouble, Just ''Double)
          ]

        nonNumTypes :: [(Name, Maybe Name)]
        nonNumTypes =
          [ (''Char,   Nothing)             -- wide characters are 4-bytes
          , (''CChar,  Just ''HTYPE_CCHAR)
          , (''CSChar, Just ''Int8)
          , (''CUChar, Just ''Word8)
          ]

        allTypes :: [(Name, Maybe Name)]
        allTypes = integralTypes ++ floatingTypes ++ nonNumTypes

        mkArrayElt :: Name -> Maybe Name -> Q [Dec]
        mkArrayElt name mrep =
          let
              simple  = isNothing mrep
              --
              n       = nameBase name
              t       = conT name
              r       = conT (fromMaybe name mrep)
              con     = conE (mkName ("AD_" ++ n))
              pat     = conP (mkName ("AD_" ++ n)) [varP (mkName "ba")]
              --
              wrap
                | simple    = varE (mkName "id")
                | otherwise = conE (mkName n)
              --
              unwrap
                | simple    = varP (mkName "e")
                | otherwise = conP (mkName n) [varP (mkName "e")]
          in
          [d| instance ArrayElt $t where
                type ArrayPtrs $t = Ptr $r
                arrayElt = $(conE (mkName ("ArrayEltR" ++ map toLower n)))
                {-# INLINE newArrayData         #-}
                {-# INLINE ptrsOfArrayData      #-}
                {-# INLINE touchArrayData       #-}
                {-# INLINE unsafeIndexArrayData #-}
                {-# INLINE unsafeReadArrayData  #-}
                {-# INLINE unsafeWriteArrayData #-}
                newArrayData size                   = $con <$> newArrayData' size
                ptrsOfArrayData      $pat           = unsafeUniqueArrayPtr ba
                touchArrayData       $pat           = touchUniqueArray ba
                unsafeIndexArrayData $pat i         = $wrap  $! unsafeIndexArray ba i
                unsafeReadArrayData  $pat i         = $wrap <$> unsafeReadArray  ba i
                unsafeWriteArrayData $pat i $unwrap = unsafeWriteArray ba i e
            |]
    --
    concat <$> mapM (uncurry mkArrayElt) allTypes
 )

