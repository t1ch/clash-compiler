{-|
  Copyright   :  (C) 2023, Google LLC
  License     :  BSD2 (see the file LICENSE)
  Maintainer  :  QBayLogic B.V. <devops@qbaylogic.com>
-}
{-# LANGUAGE RecordWildCards #-}

module Clash.Cores.Xilinx.Xpm.Cdc.Handshake
  ( xpmCdcHandshake
  , XpmCdcHandshakeConfig(..)
  , xpmCdcHandshakeWith
  ) where

import Clash.Explicit.Prelude

import GHC.Stack (HasCallStack)

import Clash.Cores.Xilinx.Xpm.Cdc.Handshake.Internal (xpmCdcHandshake#)

-- | Synchronizes data from the source clock domain to the destination. For this
-- to function correctly, a full handshake must be completed before another data
-- transfer is initiated. The handshake is considered completed when both sides
-- have acknowledged the transfer and the handshake signals have been reset.
--
-- By default, it uses four synchronization stages in both source and
-- destination domains, and auto-detects whether to use initial values for the
-- synchronization registers. Use 'xpmCdcHandshakeWith' to change these
-- settings. For more information see [PG382](https://docs.xilinx.com/r/en-US/pg382-xpm-cdc-generator/XPM_CDC_HANDSHAKE).
--
-- __N.B.__: In order to simulate initial values, both the source and destination
--           domain need to support them. If the source and destination domain
--           disagree on this property, use of this function will fail to
--           simulate and translate to HDL. You can explicitly set it using
--           'xpmCdcHandshakeWith'.
xpmCdcHandshake ::
  forall a src dst.
  ( 1 <= BitSize a, BitSize a <= 1024
  , KnownDomain src
  , KnownDomain dst
  , BitPack a
  , NFDataX a
  , HasCallStack
  ) =>
  Clock src ->
  Clock dst ->
  -- | Word to synchronize to destination domain. This value should not change
  -- when @src_send@ is asserted.
  "src_in" ::: Signal src a ->

  -- | Assertion of this signal allows the @src_in@ bus to be synchronized to the
  -- destination clock domain. This signal should only be asserted when @src_rcv@
  -- is deasserted, indicating that the previous data transfer is complete. This
  -- signal should only be deasserted once @src_rcv@ is asserted, acknowledging
  -- that the @src_in@ has been received by the destination logic.
  "src_send" ::: Signal src Bool ->

  -- | Asserting this signal indicates that data on @dest_out@ has been captured
  -- by the destination logic. This signal should be deasserted once @dest_req@ is
  -- deasserted, completing the handshake on the destination clock domain and
  -- indicating that the destination logic is ready for a new data transfer.
  "dst_ack" ::: Signal dst Bool ->

  -- | @dest_req@ indicates that @dest_out@ contains valid data. It can be
  -- acknowledges by asserting @dst_ack@. @src_rcv@ indicates that the destination
  -- domain has acknowledged a data transfer.
  ( "dest_out" ::: Signal dst a
  , "dest_req" ::: Signal dst Bool
  , "src_rcv"  ::: Signal src Bool
  )
xpmCdcHandshake = xpmCdcHandshakeWith XpmCdcHandshakeConfig{..}
 where
  srcStages = d4
  dstStages = d4
  initialValues =
    case (initBehavior @src, initBehavior @dst) of
      (SDefined, SDefined) -> True
      (SUnknown, SUnknown) -> False
      _ -> clashCompileError $ "xpmCdcHandshake: domains need to agree on initial value "
                            <> "behavior. To set initial value usage explicitly, "
                            <> "consider using 'xpmCdcHandshakeWith'."
{-# INLINE xpmCdcHandshake #-}

-- | Configuration for 'xpmCdcHandshakeWith'
data XpmCdcHandshakeConfig srcStages dstStages = XpmCdcHandshakeConfig
  { -- | Number of synchronization stages in the source domain
    srcStages :: SNat srcStages

    -- | Number of synchronization stages in the destination domain
  , dstStages :: SNat dstStages

    -- | Initialize registers used within the primitive to /0/. Note that
    -- 'xpmCdcHandshake' will set this to 'True' if both domains support initial
    -- values, to 'False' if neither domain does, and will otherwise emit an
    -- error.
    --
    -- This value is ignored in Clash simulation on domains configured to not
    -- support initial values.
  , initialValues :: Bool
  }

-- | Like 'xpmCdcHandshake', but with a configurable number of stages, initial values,
-- and registered input. Also see 'XpmCdcHandshakeConfig'.
xpmCdcHandshakeWith ::
  forall srcStages dstStages a src dst.
  ( 2 <= srcStages, srcStages <= 10
  , 2 <= dstStages, dstStages <= 10
  , 1 <= BitSize a, BitSize a <= 1024
  , KnownDomain src
  , KnownDomain dst
  , BitPack a
  , NFDataX a
  , HasCallStack
  ) =>
  XpmCdcHandshakeConfig srcStages dstStages ->
  Clock src ->
  Clock dst ->

  -- | Word to synchronize to destination domain. This value should not change
  -- when @src_send@ is asserted.
  "src_in" ::: Signal src a ->

  -- | Assertion of this signal allows the @src_in@ bus to be synchronized to the
  -- destination clock domain. This signal should only be asserted when @src_rcv@
  -- is deasserted, indicating that the previous data transfer is complete. This
  -- signal should only be deasserted once @src_rcv@ is asserted, acknowledging
  -- that the @src_in@ has been received by the destination logic.
  "src_send" ::: Signal src Bool ->

  -- | Asserting this signal indicates that data on @dest_out@ has been captured
  -- by the destination logic. This signal should be deasserted once @dest_req@ is
  -- deasserted, completing the handshake on the destination clock domain and
  -- indicating that the destination logic is ready for a new data transfer.
  "dst_ack" ::: Signal dst Bool ->

  -- | @dest_req@ indicates that @dest_out@ contains valid data. It can be
  -- acknowledges by asserting @dst_ack@. @src_rcv@ indicates that the destination
  -- domain has acknowledged a data transfer.
  ( "dest_out" ::: Signal dst a
  , "dest_req" ::: Signal dst Bool
  , "src_rcv"  ::: Signal src Bool
  )
xpmCdcHandshakeWith XpmCdcHandshakeConfig{..} =
  xpmCdcHandshake# initialValues srcStages dstStages
{-# INLINE xpmCdcHandshakeWith #-}
