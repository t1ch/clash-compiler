{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module T2361 where

import Clash.Explicit.Prelude

data T = T !(Signed 32) deriving (Generic, NFDataX)

topEntity ::
  Clock System ->
  Enable System ->
  Signal System T ->
  Signal System T
topEntity clk ena t = delay clk ena (T 1) t
