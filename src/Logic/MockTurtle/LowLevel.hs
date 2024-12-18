-- This FFI pattern cribbed from https://luctielen.com/posts/calling_cpp_from_haskell/, credit to Luc Tielen

module Logic.MockTurtle.LowLevel where

import Control.Exception (mask_)
import Foreign
import Foreign.C

data XAGWrap

data XAGBuilderWrap

data XAGReaderWrap

foreign import ccall unsafe "xag_alloc"
  allocXAGWrap :: IO (Ptr XAGWrap)

foreign import ccall unsafe "&xag_free"
  freeXAGWrap :: FunPtr (Ptr XAGWrap -> IO ())

foreign import ccall unsafe "xag_optimize"
  xagOptimize :: Ptr XAGWrap -> IO ()

allocForeignXAGWrap :: IO (ForeignPtr XAGWrap)
allocForeignXAGWrap = mask_ $ newForeignPtr freeXAGWrap =<< allocXAGWrap

foreign import ccall unsafe "xag_builder_alloc"
  allocXAGBuilderWrap :: Ptr XAGWrap -> IO (Ptr XAGBuilderWrap)

foreign import ccall unsafe "&xag_builder_free"
  freeXAGBuilderWrap :: FunPtr (Ptr XAGBuilderWrap -> IO ())

allocForeignXAGBuilderWrap :: Ptr XAGWrap -> IO (ForeignPtr XAGBuilderWrap)
allocForeignXAGBuilderWrap xagP = mask_ $ newForeignPtr freeXAGBuilderWrap =<< allocXAGBuilderWrap xagP

foreign import ccall unsafe "xag_builder_create_pi"
  xagBuilderWrapCreatePI :: Ptr XAGBuilderWrap -> CInt -> IO ()

foreign import ccall unsafe "xag_builder_create_const"
  xagBuilderWrapCreateConst :: Ptr XAGBuilderWrap -> CInt -> CBool -> IO ()

foreign import ccall unsafe "xag_builder_create_not"
  xagBuilderWrapCreateNot :: Ptr XAGBuilderWrap -> CInt -> CInt -> IO ()

foreign import ccall unsafe "xag_builder_create_xor"
  xagBuilderWrapCreateXor :: Ptr XAGBuilderWrap -> CInt -> CInt -> CInt -> IO ()

foreign import ccall unsafe "xag_builder_create_and"
  xagBuilderWrapCreateAnd :: Ptr XAGBuilderWrap -> CInt -> CInt -> CInt -> IO ()

foreign import ccall unsafe "xag_builder_create_po"
  xagBuilderWrapCreatePO :: Ptr XAGBuilderWrap -> CInt -> IO ()

foreign import ccall unsafe "xag_reader_alloc"
  allocXAGReaderWrap :: Ptr XAGWrap -> IO (Ptr XAGReaderWrap)

foreign import ccall unsafe "&xag_reader_free"
  freeXAGReaderWrap :: FunPtr (Ptr XAGReaderWrap -> IO ())

allocForeignXAGReaderWrap :: Ptr XAGWrap -> IO (ForeignPtr XAGReaderWrap)
allocForeignXAGReaderWrap xagP = mask_ $ newForeignPtr freeXAGReaderWrap =<< allocXAGReaderWrap xagP

foreign import ccall unsafe "xag_reader_get_num_pis"
  xagReaderGetNumPIs :: Ptr XAGReaderWrap -> IO CInt

foreign import ccall unsafe "xag_reader_get_num_nodes"
  xagReaderGetNumNodes :: Ptr XAGReaderWrap -> IO CInt

foreign import ccall unsafe "xag_reader_get_num_pos"
  xagReaderGetNumPOs :: Ptr XAGReaderWrap -> IO CInt

-- Return is nodeID; nodeID < 0 means end
foreign import ccall unsafe "xag_reader_read_next_pi"
  xagReaderReadNextPI :: Ptr XAGReaderWrap -> IO CInt

xagReaderNodeTypeConstFalse :: CInt
xagReaderNodeTypeConstFalse = 0

xagReaderNodeTypeConstTrue :: CInt
xagReaderNodeTypeConstTrue = 1

xagReaderNodeTypeNot :: CInt
xagReaderNodeTypeNot = 2

xagReaderNodeTypeXor :: CInt
xagReaderNodeTypeXor = 3

xagReaderNodeTypeAnd :: CInt
xagReaderNodeTypeAnd = 4

-- Param is array of 3 CInt: type, xID, yID
-- Return is nodeID; nodeID < 0 means end
foreign import ccall unsafe "xag_reader_read_next_node"
  xagReaderReadNextNode :: Ptr XAGReaderWrap -> Ptr CInt -> IO CInt

-- Return is nodeID; nodeID < 0 means end
foreign import ccall unsafe "xag_reader_read_next_po"
  xagReaderReadNextPO :: Ptr XAGReaderWrap -> IO CInt
