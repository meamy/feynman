{-# LANGUAGE DeriveGeneric, ImportQualifiedPost #-}

module Logic.MockTurtle (XAG.Graph (..), optimize) where

import Foreign (Ptr, peekArray, withForeignPtr, fromBool)
import Foreign.Marshal (allocaArray)
import GHC.IO (unsafePerformIO)
import Logic.MockTurtle.LowLevel
import Logic.MockTurtle.XAG qualified as XAG

-- Don't worry about inlining or CSE in this use of unsafePerformIO -- there
-- really should be no visible side-effects in this use, so strange behaviour,
-- repetition or elimination, in how the call to optimize is made is actually
-- okay, maybe even desirable.

-- It might be possible for some/all of these FFI calls not to depend on the IO
-- monad, but using the IO monad and containing it within a call to
-- unsafePerformIO does ensure the expected ordering. DO NOT NEST
-- unsafePerformIO calls however, or at least be very careful about it: once
-- you create an XAGWrap, all calls involving that particular XAGWrap should be
-- made within the same IO to ensure proper ordering!

-- About that: the place ordering is likely to go very sideways is if the build
-- and read steps aren't properly ordered with respect to each other. Because
-- Ptr XAGWrap doesn't change throughout the build process, Haskell has no
-- visibility into the state changes and could just decide to start reading as
-- soon as the thing is allocated, without ever even doing the build. It's the
-- same Ptr, right? That's where the IO usage saves our butts.

-- As long as we are done the whole process before we get back from
-- unsafePerformIO, though, we should be fine.

optimize :: XAG.Graph -> XAG.Graph
optimize g =
  unsafePerformIO
    ( do
        mtxagFP <- allocForeignXAGWrap
        withForeignPtr
          mtxagFP
          ( \mtxag -> do
              buildMTXAG g mtxag
              xagOptimize mtxag
              readMTXAG mtxag
          )
    )

buildMTXAG :: XAG.Graph -> Ptr XAGWrap -> IO ()
buildMTXAG g mtxag = do
  builder <- allocForeignXAGBuilderWrap mtxag
  withForeignPtr builder doBuild
  where
    doBuild :: Ptr XAGBuilderWrap -> IO ()
    doBuild b = do
      mapM_ (buildInput b) (XAG.inputIDs g)
      mapM_ (buildNode b) (XAG.nodes g)
      mapM_ (buildOutput b) (XAG.outputIDs g)

    buildOutput :: Ptr XAGBuilderWrap -> Int -> IO ()
    buildOutput b nID = xagBuilderWrapCreatePO b (fromIntegral nID)

    buildNode :: Ptr XAGBuilderWrap -> XAG.Node -> IO ()
    buildNode b (XAG.Const nID v) =
      xagBuilderWrapCreateConst b (fromIntegral nID) (fromBool v)
    buildNode b (XAG.Not nID xID) =
      xagBuilderWrapCreateNot b (fromIntegral nID) (fromIntegral xID)
    buildNode b (XAG.Xor nID xID yID) =
      xagBuilderWrapCreateXor b (fromIntegral nID) (fromIntegral xID) (fromIntegral yID)
    buildNode b (XAG.And nID xID yID) =
      xagBuilderWrapCreateAnd b (fromIntegral nID) (fromIntegral xID) (fromIntegral yID)

    buildInput :: Ptr XAGBuilderWrap -> Int -> IO ()
    buildInput b nID = xagBuilderWrapCreatePI b (fromIntegral nID)

readMTXAG :: Ptr XAGWrap -> IO XAG.Graph
readMTXAG mtxag = do
  reader <- allocForeignXAGReaderWrap mtxag
  (pis, nodes, pos) <- withForeignPtr reader doRead
  return $ XAG.Graph nodes pis pos
  where
    doRead :: Ptr XAGReaderWrap -> IO ([Int], [XAG.Node], [Int])
    doRead r = do
      pis <- readPIs r
      gates <- allocaArray 3 (readNodes r)
      pos <- readPOs r
      return (pis, gates, pos)

    readPIs r = do
      piID <- xagReaderReadNextPI r
      if piID < 0
        then return []
        else
          ( do
              remain <- readPIs r
              return $ fromIntegral piID : remain
          )

    readNodes r buf = do
      nID <- xagReaderReadNextNode r buf
      if nID < 0
        then return []
        else
          ( do
              vals <- peekArray 3 buf
              remain <- readNodes r buf
              return $ nodeFromBuf (fromIntegral nID) (head vals) (map fromIntegral (tail vals)) : remain
          )
      where
        nodeFromBuf nID t _
          | t == xagReaderNodeTypeConstFalse = XAG.Const nID False
          | t == xagReaderNodeTypeConstTrue = XAG.Const nID True
        nodeFromBuf nID t (xID : _)
          | t == xagReaderNodeTypeNot = XAG.Not nID xID
        nodeFromBuf nID t (xID : yID : _)
          | t == xagReaderNodeTypeXor = XAG.Xor nID xID yID
          | t == xagReaderNodeTypeAnd = XAG.And nID xID yID
        nodeFromBuf _ _ _ = undefined

    readPOs r = do
      poID <- xagReaderReadNextPO r
      if poID < 0
        then return []
        else
          ( do
              remain <- readPOs r
              return $ fromIntegral poID : remain
          )
