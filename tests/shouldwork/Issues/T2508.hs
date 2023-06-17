{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module T2508 where

import Clash.Explicit.Prelude
import qualified Prelude as P

import Control.Exception (AssertionFailed(..), throwIO)
import Control.Monad (when)
import Data.List (sort)
import System.Environment (getArgs)
import System.FilePath ((</>))
import System.FilePath.Glob (globDir1)

accum :: Unsigned 64 -> Unsigned 64 -> (Unsigned 64, Unsigned 64)
accum s i = (s + i, s)
{-# NOINLINE accum #-}

topEntity ::
  Clock System ->
  Reset System ->
  Enable System ->
  Signal System (Unsigned 64) ->
  Signal System (Unsigned 64)
topEntity clk rst ena = mealy clk rst ena accum 0
{-# OPAQUE topEntity #-}

mainVHDL :: IO ()
mainVHDL = do
  [topDir] <- getArgs

  -- 'bbWrapper' should get its own file, so we expect two: one for 'topEntity',
  -- one for 'bbWrapper'.
  --
  -- XXX: Naming doesn't make sense. 'topEntity1' should be called 'bbWrapper'.
  let hdlDir = topDir </> show 'topEntity
  actual0 <- sort <$> globDir1 "*.vhdl" hdlDir
  let
    actual1 = P.map (P.drop (P.length hdlDir + 1)) actual0
    expected = ["T2508_topEntity_types.vhdl", "mealy_accum.vhdl", "topEntity.vhdl"]
  when
    (actual1 /= expected)
    (throwIO $ AssertionFailed $ "Expected " <> show expected <> " got " <> show actual1)

  pure ()
