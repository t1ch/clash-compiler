{-# LANGUAGE CPP #-}

module ExpWithGhcCF where
import Clash.Prelude
import Clash.Explicit.Testbench
import qualified Exp

-- Constant folded topEntity (GHC/TemplateHaskell)
expected = $(lift (map pack Exp.expectedOutputs))

-- Constant folded (?) topEntity (Clash)
topEntity = Exp.topEntity
-- See: https://github.com/clash-lang/clash-compiler/pull/2511
{-# CLASH_OPAQUE topEntity #-}

testBench :: Signal System Bool
testBench = done
  where
    testInput      = stimuliGenerator clk rst Exp.testInput
    expectedOutput = outputVerifierBitVector' clk rst expected
    done           = expectedOutput ((pack . topEntity) <$> testInput)
    clk            = tbSystemClockGen (not <$> done)
    rst            = systemResetGen
