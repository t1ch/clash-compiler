{-|
Copyright  :  (C) 2013-2016, University of Twente,
                  2016-2017, Myrtle Software Ltd,
                  2017     , Google Inc.,
                  2021-2022, QBayLogic B.V.,
                  2022     , Google Inc.,
License    :  BSD2 (see the file LICENSE)
Maintainer :  QBayLogic B.V. <devops@qbaylogic.com>

Block RAM primitives

= Using RAMs #usingrams#

We will show a rather elaborate example on how you can, and why you might want
to use block RAMs. We will build a \"small\" CPU + Memory + Program ROM where we
will slowly evolve to using block RAMs. Note that the code is /not/ meant as a
de-facto standard on how to do CPU design in Clash.

We start with the definition of the Instructions, Register names and machine
codes:

@
{\-\# LANGUAGE RecordWildCards, TupleSections, DeriveAnyClass \#-\}

module CPU where

import Clash.Explicit.Prelude

type InstrAddr = Unsigned 8
type MemAddr   = Unsigned 5
type Value     = Signed 8

data Instruction
  = Compute Operator Reg Reg Reg
  | Branch Reg Value
  | Jump Value
  | Load MemAddr Reg
  | Store Reg MemAddr
  | Nop
  deriving (Eq, Show, Generic, NFDataX)

data Reg
  = Zero
  | PC
  | RegA
  | RegB
  | RegC
  | RegD
  | RegE
  deriving (Eq, Show, Enum, Generic, NFDataX)

data Operator = Add | Sub | Incr | Imm | CmpGt
  deriving (Eq, Show, Generic, NFDataX)

data MachCode
  = MachCode
  { inputX  :: Reg
  , inputY  :: Reg
  , result  :: Reg
  , aluCode :: Operator
  , ldReg   :: Reg
  , rdAddr  :: MemAddr
  , wrAddrM :: Maybe MemAddr
  , jmpM    :: Maybe Value
  }

nullCode =
  MachCode
    { inputX = Zero
    , inputY = Zero
    , result = Zero
    , aluCode = Imm
    , ldReg = Zero
    , rdAddr = 0
    , wrAddrM = Nothing
    , jmpM = Nothing
    }
@

Next we define the CPU and its ALU:

@
cpu
  :: Vec 7 Value          -- ^ Register bank
  -> (Value,Instruction)  -- ^ (Memory output, Current instruction)
  -> ( Vec 7 Value
     , (MemAddr, Maybe (MemAddr,Value), InstrAddr)
     )
cpu regbank (memOut, instr) =
  (regbank', (rdAddr, (,aluOut) '<$>' wrAddrM, bitCoerce ipntr))
 where
  -- Current instruction pointer
  ipntr = regbank 'Clash.Sized.Vector.!!' PC

  -- Decoder
  (MachCode {..}) = case instr of
    Compute op rx ry res -> nullCode {inputX=rx,inputY=ry,result=res,aluCode=op}
    Branch cr a          -> nullCode {inputX=cr,jmpM=Just a}
    Jump a               -> nullCode {aluCode=Incr,jmpM=Just a}
    Load a r             -> nullCode {ldReg=r,rdAddr=a}
    Store r a            -> nullCode {inputX=r,wrAddrM=Just a}
    Nop                  -> nullCode

  -- ALU
  regX   = regbank 'Clash.Sized.Vector.!!' inputX
  regY   = regbank 'Clash.Sized.Vector.!!' inputY
  aluOut = alu aluCode regX regY

  -- next instruction
  nextPC =
    case jmpM of
      Just a | aluOut /= 0 -> ipntr + a
      _                    -> ipntr + 1

  -- update registers
  regbank' = 'Clash.Sized.Vector.replace' Zero   0
           $ 'Clash.Sized.Vector.replace' PC     nextPC
           $ 'Clash.Sized.Vector.replace' result aluOut
           $ 'Clash.Sized.Vector.replace' ldReg  memOut
           $ regbank

alu Add   x y = x + y
alu Sub   x y = x - y
alu Incr  x _ = x + 1
alu Imm   x _ = x
alu CmpGt x y = if x > y then 1 else 0
@

We initially create a memory out of simple registers:

@
dataMem
  :: KnownDomain dom
  => Clock dom
  -> Reset dom
  -> Enable dom
  -> Signal dom MemAddr
  -- ^ Read address
  -> Signal dom (Maybe (MemAddr,Value))
  -- ^ (write address, data in)
  -> Signal dom Value
  -- ^ data out
dataMem clk rst en rd wrM =
  'Clash.Explicit.Mealy.mealy' clk rst en dataMemT ('Clash.Sized.Vector.replicate' d32 0) (bundle (rd,wrM))
 where
  dataMemT mem (rd,wrM) = (mem',dout)
    where
      dout = mem 'Clash.Sized.Vector.!!' rd
      mem' =
        case wrM of
          Just (wr,din) -> 'Clash.Sized.Vector.replace' wr din mem
          _             -> mem
@

And then connect everything:

@
system
  :: ( KnownDomain dom
     , KnownNat n )
  => Vec n Instruction
  -> Clock dom
  -> Reset dom
  -> Enable dom
  -> Signal dom Value
system instrs clk rst en = memOut
 where
  memOut = dataMem clk rst en rdAddr dout
  (rdAddr,dout,ipntr) = 'Clash.Explicit.Mealy.mealyB' clk rst en cpu ('Clash.Sized.Vector.replicate' d7 0) (memOut,instr)
  instr  = 'Clash.Explicit.Prelude.asyncRom' instrs '<$>' ipntr
@

Create a simple program that calculates the GCD of 4 and 6:

@
-- Compute GCD of 4 and 6
prog = -- 0 := 4
       Compute Incr Zero RegA RegA :>
       replicate d3 (Compute Incr RegA Zero RegA) ++
       Store RegA 0 :>
       -- 1 := 6
       Compute Incr Zero RegA RegA :>
       replicate d5 (Compute Incr RegA Zero RegA) ++
       Store RegA 1 :>
       -- A := 4
       Load 0 RegA :>
       -- B := 6
       Load 1 RegB :>
       -- start
       Compute CmpGt RegA RegB RegC :>
       Branch RegC 4 :>
       Compute CmpGt RegB RegA RegC :>
       Branch RegC 4 :>
       Jump 5 :>
       -- (a > b)
       Compute Sub RegA RegB RegA :>
       Jump (-6) :>
       -- (b > a)
       Compute Sub RegB RegA RegB :>
       Jump (-8) :>
       -- end
       Store RegA 2 :>
       Load 2 RegC :>
       Nil
@

And test our system:

@
>>> sampleN 32 $ system prog systemClockGen resetGen enableGen
[0,0,0,0,0,0,4,4,4,4,4,4,4,4,6,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,2]

@

to see that our system indeed calculates that the GCD of 6 and 4 is 2.

=== Improvement 1: using @asyncRam@

As you can see, it's fairly straightforward to build a memory using registers
and read ('Clash.Sized.Vector.!!') and write ('Clash.Sized.Vector.replace')
logic. This might however not result in the most efficient hardware structure,
especially when building an ASIC.

Instead it is preferable to use the 'Clash.Prelude.RAM.asyncRam' function which
has the potential to be translated to a more efficient structure:

@
system2
  :: ( KnownDomain dom
     , KnownNat n )
  => Vec n Instruction
  -> Clock dom
  -> Reset dom
  -> Enable dom
  -> Signal dom Value
system2 instrs clk rst en = memOut
 where
  memOut = 'Clash.Explicit.RAM.asyncRam' clk clk en d32 rdAddr dout
  (rdAddr,dout,ipntr) = 'Clash.Explicit.Prelude.mealyB' clk rst en cpu ('Clash.Sized.Vector.replicate' d7 0) (memOut,instr)
  instr  = 'Clash.Prelude.ROM.asyncRom' instrs '<$>' ipntr
@

Again, we can simulate our system and see that it works. This time however,
we need to disregard the first few output samples, because the initial content of an
'Clash.Prelude.RAM.asyncRam' is /undefined/, and consequently, the first few
output samples are also /undefined/. We use the utility function
'Clash.XException.printX' to conveniently filter out the undefinedness and
replace it with the string @\"undefined\"@ in the first few leading outputs.

@
>>> printX $ sampleN 32 $ system2 prog systemClockGen resetGen enableGen
[undefined,undefined,undefined,undefined,undefined,undefined,4,4,4,4,4,4,4,4,6,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,2]

@

=== Improvement 2: using @blockRam@

Finally we get to using 'blockRam'. On FPGAs, 'Clash.Prelude.RAM.asyncRam' will
be implemented in terms of LUTs, and therefore take up logic resources. FPGAs
also have large(r) memory structures called /block RAMs/, which are preferred,
especially as the memories we need for our application get bigger. The
'blockRam' function will be translated to such a /block RAM/.

One important aspect of block RAMs is that they have a /synchronous/ read port,
meaning unlike an 'Clash.Prelude.RAM.asyncRam', the result of a read command
given at time @t@ is output at time @t + 1@.

For us that means we need to change the design of our CPU. Right now, upon a
load instruction we generate a read address for the memory, and the value at
that read address is immediately available to be put in the register bank. We
will be using a block RAM, so the value is delayed until the next cycle. Thus,
we will also need to delay the register address to which the memory address is
loaded:

@
cpu2
  :: (Vec 7 Value,Reg)    -- ^ (Register bank, Load reg addr)
  -> (Value,Instruction)  -- ^ (Memory output, Current instruction)
  -> ( (Vec 7 Value, Reg)
     , (MemAddr, Maybe (MemAddr,Value), InstrAddr)
     )
cpu2 (regbank, ldRegD) (memOut, instr) =
  ((regbank', ldRegD'), (rdAddr, (,aluOut) '<$>' wrAddrM, bitCoerce ipntr))
 where
  -- Current instruction pointer
  ipntr = regbank 'Clash.Sized.Vector.!!' PC

  -- Decoder
  (MachCode {..}) = case instr of
    Compute op rx ry res -> nullCode {inputX=rx,inputY=ry,result=res,aluCode=op}
    Branch cr a          -> nullCode {inputX=cr,jmpM=Just a}
    Jump a               -> nullCode {aluCode=Incr,jmpM=Just a}
    Load a r             -> nullCode {ldReg=r,rdAddr=a}
    Store r a            -> nullCode {inputX=r,wrAddrM=Just a}
    Nop                  -> nullCode

  -- ALU
  regX   = regbank 'Clash.Sized.Vector.!!' inputX
  regY   = regbank 'Clash.Sized.Vector.!!' inputY
  aluOut = alu aluCode regX regY

  -- next instruction
  nextPC =
    case jmpM of
      Just a | aluOut /= 0 -> ipntr + a
      _                    -> ipntr + 1

  -- update registers
  ldRegD'  = ldReg  -- Delay the ldReg by 1 cycle
  regbank' = 'Clash.Sized.Vector.replace' Zero   0
           $ 'Clash.Sized.Vector.replace' PC     nextPC
           $ 'Clash.Sized.Vector.replace' result aluOut
           $ 'Clash.Sized.Vector.replace' ldRegD memOut
           $ regbank
@

We can now finally instantiate our system with a 'blockRam':

@
system3
  :: ( KnownDomain dom
     , KnownNat n )
  => Vec n Instruction
  -> Clock dom
  -> Reset dom
  -> Enable dom
  -> Signal dom Value
system3 instrs clk rst en = memOut
 where
  memOut = 'blockRam' clk en (replicate d32 0) rdAddr dout
  (rdAddr,dout,ipntr) = 'Clash.Explicit.Prelude.mealyB' clk rst en cpu2 (('Clash.Sized.Vector.replicate' d7 0),Zero) (memOut,instr)
  instr  = 'Clash.Explicit.Prelude.asyncRom' instrs '<$>' ipntr
@

We are, however, not done. We will also need to update our program. The reason
being that values that we try to load in our registers won't be loaded into the
register until the next cycle. This is a problem when the next instruction
immediately depends on this memory value. In our example, this was only the case
when we loaded the value @6@, which was stored at address @1@, into @RegB@.
Our updated program is thus:

@
prog2 = -- 0 := 4
       Compute Incr Zero RegA RegA :>
       replicate d3 (Compute Incr RegA Zero RegA) ++
       Store RegA 0 :>
       -- 1 := 6
       Compute Incr Zero RegA RegA :>
       replicate d5 (Compute Incr RegA Zero RegA) ++
       Store RegA 1 :>
       -- A := 4
       Load 0 RegA :>
       -- B := 6
       Load 1 RegB :>
       Nop :> -- Extra NOP
       -- start
       Compute CmpGt RegA RegB RegC :>
       Branch RegC 4 :>
       Compute CmpGt RegB RegA RegC :>
       Branch RegC 4 :>
       Jump 5 :>
       -- (a > b)
       Compute Sub RegA RegB RegA :>
       Jump (-6) :>
       -- (b > a)
       Compute Sub RegB RegA RegB :>
       Jump (-8) :>
       -- end
       Store RegA 2 :>
       Load 2 RegC :>
       Nil
@

When we simulate our system we see that it works. This time again,
we need to disregard the first sample, because the initial output of a
'blockRam' is /undefined/. We use the utility function 'Clash.XException.printX'
to conveniently filter out the undefinedness and replace it with the string @\"undefined\"@.

@
>>> printX $ sampleN 34 $ system3 prog2 systemClockGen resetGen enableGen
[undefined,0,0,0,0,0,0,4,4,4,4,4,4,4,4,6,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,2]

@

This concludes the short introduction to using 'blockRam'.

-}

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE ViewPatterns #-}

{-# LANGUAGE Trustworthy #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin=GHC.TypeLits.Extra.Solver #-}
{-# OPTIONS_GHC -fplugin=GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}
{-# OPTIONS_HADDOCK show-extensions #-}

-- In the blackbox definitions of 'trueDualPortBlockRam#' we bind a 'Vec', which
-- GHC doesn't recognize as being complete (though it will throw a type error if
-- the left and right side of the pattern match disagree on their types).
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

-- See [Note: eta port names for trueDualPortBlockRam]
{-# OPTIONS_GHC -fno-do-lambda-eta-expansion #-}

-- See: https://github.com/clash-lang/clash-compiler/commit/721fcfa9198925661cd836668705f817bddaae3c
-- as to why we need this.
{-# OPTIONS_GHC -fno-cpr-anal #-}

module Clash.Explicit.BlockRam
  ( -- * Block RAM synchronized to an arbitrary clock
    blockRam
  , blockRamPow2
  , blockRamU
  , blockRam1
  , ResetStrategy(..)
    -- ** Read/write conflict resolution
  , readNew
    -- * True dual-port block RAM
    -- $tdpbram
  , trueDualPortBlockRam
  , trueDualPortBlockRamBe
  , RamOp(..)
    -- * Internal
  , blockRam#
  , blockRamU#
  , blockRam1#
  , trueDualPortBlockRam#
  , writeRam
  , byteMaskToBitMask
  )
where

import           Clash.HaskellPrelude

import           Control.Exception      (catch, throw)
import           Control.Monad          (forM_)
import           Control.Monad.ST       (ST, runST)
import           Control.Monad.ST.Unsafe (unsafeInterleaveST, unsafeIOToST, unsafeSTToIO)
import           Data.Array.MArray      (newListArray)
import           Data.Constraint        (Dict(..))
import qualified Data.List              as L
import           Data.Maybe             (isJust, fromMaybe)
import           Data.Proxy             (Proxy(..))
import           GHC.Arr
  (STArray, unsafeReadSTArray, unsafeWriteSTArray)
import           Data.Bits              (shiftL, (.|.), (.&.), complement)
import qualified Data.Sequence          as Seq
import           Data.Sequence          (Seq)
import           Data.String.Interpolate(__i)
import           GHC.Generics           (Generic)
import           GHC.Stack              (HasCallStack, withFrozenCallStack)
import           GHC.TypeLits           (KnownNat, type (^), type (<=), type (*))
import           GHC.TypeLits.Extra     (type DivRU)
import           Unsafe.Coerce          (unsafeCoerce)

import           Clash.Annotations.Primitive
  (Primitive(InlineYamlPrimitive), HDL(..), hasBlackBox)
import           Clash.Class.BitPack    (BitPack(BitSize, pack, unpack))
import           Clash.Class.Resize     (Resize(resize))
import           Clash.Class.Num        (SaturationMode(SatBound), satSucc)
import           Clash.Explicit.Signal  (KnownDomain, Enable, register, fromEnable)
import           Clash.Signal.Internal
  (Clock(..), Reset, Signal (..), ClockAB (..), invertReset, (.&&.), mux,
   clockTicks)
import           Clash.Promoted.Nat     (SNat(..), natToNum)
import           Clash.Signal.Bundle    (unbundle, bundle)
import           Clash.Sized.BitVector  (BitVector)
import           Clash.Sized.Internal.BitVector (BitVector(BV))
import           Clash.Sized.Unsigned   (Unsigned)
import           Clash.Sized.Index      (Index)
import           Clash.Sized.Vector     (Vec, replicate, iterateI)
import qualified Clash.Sized.Vector     as CV
import           Clash.Sized.Vector     (Vec((:>), Nil))
import           Clash.XException
  (maybeIsX, NFDataX(deepErrorX), defaultSeqX, fromJustX, undefined,
   XException (..), seqX, isX, errorX)

{- $tdpbram
A true dual-port block RAM has two fully independent, fully functional access
ports: port A and port B. Either port can do both RAM reads and writes. These
two ports can even be on distinct clock domains, but the memory itself is shared
between the ports. This also makes a true dual-port block RAM suitable as a
component in a domain crossing circuit (but it needs additional logic for it to
be safe, see e.g. 'Clash.Explicit.Synchronizer.asyncFIFOSynchronizer').

A version with implicit clocks can be found in "Clash.Prelude.BlockRam".
-}

-- start benchmark only
-- import GHC.Arr (listArray, unsafeThawSTArray)
-- end benchmark only

{- $setup
>>> import Clash.Explicit.Prelude as C
>>> import qualified Data.Foldable as F
>>> import Data.Word (Word16)
>>> import Clash.Sized.BitVector (bLit)
>>> :set -XDataKinds -XRecordWildCards -XTupleSections -XDeriveAnyClass -XDeriveGeneric
>>> :set -XOverloadedLists -XTemplateHaskell -XNumericUnderscores
>>> type InstrAddr = Unsigned 8
>>> type MemAddr = Unsigned 5
>>> type Value = Signed 8
>>> :{
data Reg
  = Zero
  | PC
  | RegA
  | RegB
  | RegC
  | RegD
  | RegE
  deriving (Eq,Show,Enum,C.Generic,NFDataX)
:}

>>> :{
data Operator = Add | Sub | Incr | Imm | CmpGt
  deriving (Eq, Show, Generic, NFDataX)
:}

>>> :{
data Instruction
  = Compute Operator Reg Reg Reg
  | Branch Reg Value
  | Jump Value
  | Load MemAddr Reg
  | Store Reg MemAddr
  | Nop
  deriving (Eq, Show, Generic, NFDataX)
:}

>>> :{
data MachCode
  = MachCode
  { inputX  :: Reg
  , inputY  :: Reg
  , result  :: Reg
  , aluCode :: Operator
  , ldReg   :: Reg
  , rdAddr  :: MemAddr
  , wrAddrM :: Maybe MemAddr
  , jmpM    :: Maybe Value
  }
:}

>>> :{
nullCode = MachCode { inputX = Zero, inputY = Zero, result = Zero, aluCode = Imm
                    , ldReg = Zero, rdAddr = 0, wrAddrM = Nothing
                    , jmpM = Nothing
                    }
:}

>>> :{
alu Add   x y = x + y
alu Sub   x y = x - y
alu Incr  x _ = x + 1
alu Imm   x _ = x
alu CmpGt x y = if x > y then 1 else 0
:}

>>> :{
let cpu :: Vec 7 Value          -- ^ Register bank
        -> (Value,Instruction)  -- ^ (Memory output, Current instruction)
        -> ( Vec 7 Value
           , (MemAddr,Maybe (MemAddr,Value),InstrAddr)
           )
    cpu regbank (memOut,instr) = (regbank',(rdAddr,(,aluOut) <$> wrAddrM,bitCoerce ipntr))
      where
        -- Current instruction pointer
        ipntr = regbank C.!! PC
        -- Decoder
        (MachCode {..}) = case instr of
          Compute op rx ry res -> nullCode {inputX=rx,inputY=ry,result=res,aluCode=op}
          Branch cr a          -> nullCode {inputX=cr,jmpM=Just a}
          Jump a               -> nullCode {aluCode=Incr,jmpM=Just a}
          Load a r             -> nullCode {ldReg=r,rdAddr=a}
          Store r a            -> nullCode {inputX=r,wrAddrM=Just a}
          Nop                  -> nullCode
        -- ALU
        regX   = regbank C.!! inputX
        regY   = regbank C.!! inputY
        aluOut = alu aluCode regX regY
        -- next instruction
        nextPC = case jmpM of
                   Just a | aluOut /= 0 -> ipntr + a
                   _                    -> ipntr + 1
        -- update registers
        regbank' = replace Zero   0
                 $ replace PC     nextPC
                 $ replace result aluOut
                 $ replace ldReg  memOut
                 $ regbank
:}

>>> :{
let dataMem
      :: KnownDomain dom
      => Clock  dom
      -> Reset  dom
      -> Enable dom
      -> Signal dom MemAddr
      -> Signal dom (Maybe (MemAddr,Value))
      -> Signal dom Value
    dataMem clk rst en rd wrM = mealy clk rst en dataMemT (C.replicate d32 0) (bundle (rd,wrM))
      where
        dataMemT mem (rd,wrM) = (mem',dout)
          where
            dout = mem C.!! rd
            mem' = case wrM of
                     Just (wr,din) -> replace wr din mem
                     Nothing       -> mem
:}

>>> :{
let system
      :: ( KnownDomain dom
         , KnownNat n )
      => Vec n Instruction
      -> Clock dom
      -> Reset dom
      -> Enable dom
      -> Signal dom Value
    system instrs clk rst en = memOut
      where
        memOut = dataMem clk rst en rdAddr dout
        (rdAddr,dout,ipntr) = mealyB clk rst en cpu (C.replicate d7 0) (memOut,instr)
        instr  = asyncRom instrs <$> ipntr
:}

>>> :{
-- Compute GCD of 4 and 6
prog = -- 0 := 4
       Compute Incr Zero RegA RegA :>
       C.replicate d3 (Compute Incr RegA Zero RegA) C.++
       Store RegA 0 :>
       -- 1 := 6
       Compute Incr Zero RegA RegA :>
       C.replicate d5 (Compute Incr RegA Zero RegA) C.++
       Store RegA 1 :>
       -- A := 4
       Load 0 RegA :>
       -- B := 6
       Load 1 RegB :>
       -- start
       Compute CmpGt RegA RegB RegC :>
       Branch RegC 4 :>
       Compute CmpGt RegB RegA RegC :>
       Branch RegC 4 :>
       Jump 5 :>
       -- (a > b)
       Compute Sub RegA RegB RegA :>
       Jump (-6) :>
       -- (b > a)
       Compute Sub RegB RegA RegB :>
       Jump (-8) :>
       -- end
       Store RegA 2 :>
       Load 2 RegC :>
       Nil
:}

>>> :{
let system2
      :: ( KnownDomain dom
         , KnownNat n )
      => Vec n Instruction
      -> Clock dom
      -> Reset dom
      -> Enable dom
      -> Signal dom Value
    system2 instrs clk rst en = memOut
      where
        memOut = asyncRam clk clk en d32 rdAddr dout
        (rdAddr,dout,ipntr) = mealyB clk rst en cpu (C.replicate d7 0) (memOut,instr)
        instr  = asyncRom instrs <$> ipntr
:}

>>> :{
let cpu2 :: (Vec 7 Value,Reg)    -- ^ (Register bank, Load reg addr)
         -> (Value,Instruction)  -- ^ (Memory output, Current instruction)
         -> ( (Vec 7 Value,Reg)
            , (MemAddr,Maybe (MemAddr,Value),InstrAddr)
            )
    cpu2 (regbank,ldRegD) (memOut,instr) = ((regbank',ldRegD'),(rdAddr,(,aluOut) <$> wrAddrM,bitCoerce ipntr))
      where
        -- Current instruction pointer
        ipntr = regbank C.!! PC
        -- Decoder
        (MachCode {..}) = case instr of
          Compute op rx ry res -> nullCode {inputX=rx,inputY=ry,result=res,aluCode=op}
          Branch cr a          -> nullCode {inputX=cr,jmpM=Just a}
          Jump a               -> nullCode {aluCode=Incr,jmpM=Just a}
          Load a r             -> nullCode {ldReg=r,rdAddr=a}
          Store r a            -> nullCode {inputX=r,wrAddrM=Just a}
          Nop                  -> nullCode
        -- ALU
        regX   = regbank C.!! inputX
        regY   = regbank C.!! inputY
        aluOut = alu aluCode regX regY
        -- next instruction
        nextPC = case jmpM of
                   Just a | aluOut /= 0 -> ipntr + a
                   _                    -> ipntr + 1
        -- update registers
        ldRegD'  = ldReg -- Delay the ldReg by 1 cycle
        regbank' = replace Zero   0
                 $ replace PC     nextPC
                 $ replace result aluOut
                 $ replace ldRegD memOut
                 $ regbank
:}

>>> :{
let system3
      :: ( KnownDomain dom
         , KnownNat n )
      => Vec n Instruction
      -> Clock dom
      -> Reset dom
      -> Enable dom
      -> Signal dom Value
    system3 instrs clk rst en = memOut
      where
        memOut = blockRam clk en (C.replicate d32 0) rdAddr dout
        (rdAddr,dout,ipntr) = mealyB clk rst en cpu2 ((C.replicate d7 0),Zero) (memOut,instr)
        instr  = asyncRom instrs <$> ipntr
:}

>>> :{
prog2 = -- 0 := 4
       Compute Incr Zero RegA RegA :>
       C.replicate d3 (Compute Incr RegA Zero RegA) C.++
       Store RegA 0 :>
       -- 1 := 6
       Compute Incr Zero RegA RegA :>
       C.replicate d5 (Compute Incr RegA Zero RegA) C.++
       Store RegA 1 :>
       -- A := 4
       Load 0 RegA :>
       -- B := 6
       Load 1 RegB :>
       Nop :> -- Extra NOP
       -- start
       Compute CmpGt RegA RegB RegC :>
       Branch RegC 4 :>
       Compute CmpGt RegB RegA RegC :>
       Branch RegC 4 :>
       Jump 5 :>
       -- (a > b)
       Compute Sub RegA RegB RegA :>
       Jump (-6) :>
       -- (b > a)
       Compute Sub RegB RegA RegB :>
       Jump (-8) :>
       -- end
       Store RegA 2 :>
       Load 2 RegC :>
       Nil
:}

-}

-- | Create a block RAM with space for @n@ elements
--
-- * __NB__: Read value is delayed by 1 cycle
-- * __NB__: Initial output value is /undefined/, reading it will throw an
-- 'XException'
--
-- === See also:
--
-- * See "Clash.Explicit.BlockRam#usingrams" for more information on how to use a
-- block RAM.
-- * Use the adapter 'readNew' for obtaining write-before-read semantics like
-- this: @'readNew' clk rst en ('blockRam' clk inits) rd wrM@.
-- * A large 'Vec' for the initial content may be too inefficient, depending
-- on how it is constructed. See 'Clash.Explicit.BlockRam.File.blockRamFile' and
-- 'Clash.Explicit.BlockRam.Blob.blockRamBlob' for different approaches that
-- scale well.
--
-- === __Example__
-- @
-- bram40
--   :: 'Clock'  dom
--   -> 'Enable'  dom
--   -> 'Signal' dom ('Unsigned' 6)
--   -> 'Signal' dom (Maybe ('Unsigned' 6, 'Clash.Sized.BitVector.Bit'))
--   -> 'Signal' dom 'Clash.Sized.BitVector.Bit'
-- bram40 clk en = 'blockRam' clk en ('Clash.Sized.Vector.replicate' d40 1)
-- @
blockRam
  :: ( KnownDomain dom
     , HasCallStack
     , NFDataX a
     , Enum addr
     , NFDataX addr )
  => Clock dom
  -- ^ 'Clock' to synchronize to
  -> Enable dom
  -- ^ 'Enable' line
  -> Vec n a
  -- ^ Initial content of the BRAM, also determines the size, @n@, of the BRAM
   --
   -- __NB__: __MUST__ be a constant
  -> Signal dom addr
  -- ^ Read address @r@
  -> Signal dom (Maybe (addr, a))
  -- ^ (write address @w@, value to write)
  -> Signal dom a
  -- ^ Value of the BRAM at address @r@ from the previous clock cycle
blockRam = \clk gen content rd wrM ->
  let en       = isJust <$> wrM
      (wr,din) = unbundle (fromJustX <$> wrM)
  in  withFrozenCallStack
      (blockRam# clk gen content (fromEnum <$> rd) en (fromEnum <$> wr) din)
{-# INLINE blockRam #-}

-- | Create a block RAM with space for 2^@n@ elements
--
-- * __NB__: Read value is delayed by 1 cycle
-- * __NB__: Initial output value is /undefined/, reading it will throw an
-- 'XException'
--
-- === See also:
--
-- * See "Clash.Prelude.BlockRam#usingrams" for more information on how to use a
-- block RAM.
-- * Use the adapter 'readNew' for obtaining write-before-read semantics like
-- this: @'readNew' clk rst en ('blockRamPow2' clk inits) rd wrM@.
-- * A large 'Vec' for the initial content may be too inefficient, depending
-- on how it is constructed. See 'Clash.Explicit.BlockRam.File.blockRamFilePow2'
-- and 'Clash.Explicit.BlockRam.Blob.blockRamBlobPow2' for different approaches
-- that scale well.
--
-- === __Example__
-- @
-- bram32
--   :: 'Clock' dom
--   -> 'Enable' dom
--   -> 'Signal' dom ('Unsigned' 5)
--   -> 'Signal' dom (Maybe ('Unsigned' 5, 'Clash.Sized.BitVector.Bit'))
--   -> 'Signal' dom 'Clash.Sized.BitVector.Bit'
-- bram32 clk en = 'blockRamPow2' clk en ('Clash.Sized.Vector.replicate' d32 1)
-- @
blockRamPow2
  :: ( KnownDomain dom
     , HasCallStack
     , NFDataX a
     , KnownNat n )
  => Clock dom
  -- ^ 'Clock' to synchronize to
  -> Enable dom
  -- ^ 'Enable' line
  -> Vec (2^n) a
  -- ^ Initial content of the BRAM
  --
  -- __NB__: __MUST__ be a constant
  -> Signal dom (Unsigned n)
  -- ^ Read address @r@
  -> Signal dom (Maybe (Unsigned n, a))
  -- ^ (Write address @w@, value to write)
  -> Signal dom a
  -- ^ Value of the BRAM at address @r@ from the previous clock cycle
blockRamPow2 = \clk en cnt rd wrM -> withFrozenCallStack
  (blockRam clk en cnt rd wrM)
{-# INLINE blockRamPow2 #-}

data ResetStrategy (r :: Bool) where
  ClearOnReset :: ResetStrategy 'True
  NoClearOnReset :: ResetStrategy 'False

-- | A version of 'blockRam' that has no default values set. May be cleared to
-- an arbitrary state using a reset function.
blockRamU
   :: forall n dom a r addr
   . ( KnownDomain dom
     , HasCallStack
     , NFDataX a
     , Enum addr
     , NFDataX addr
     , 1 <= n )
  => Clock dom
  -- ^ 'Clock' to synchronize to
  -> Reset dom
  -- ^ 'Reset' line. This needs to be asserted for at least /n/ cycles in order
  -- for the BRAM to be reset to its initial state.
  -> Enable dom
  -- ^ 'Enable' line
  -> ResetStrategy r
  -- ^ Whether to clear BRAM on asserted reset ('ClearOnReset') or
  -- not ('NoClearOnReset'). The reset needs to be asserted for at least /n/
  -- cycles to clear the BRAM.
  -> SNat n
  -- ^ Number of elements in BRAM
  -> (Index n -> a)
  -- ^ If applicable (see 'ResetStrategy' argument), reset BRAM using this function
  -> Signal dom addr
  -- ^ Read address @r@
  -> Signal dom (Maybe (addr, a))
  -- ^ (write address @w@, value to write)
  -> Signal dom a
  -- ^ Value of the BRAM at address @r@ from the previous clock cycle
blockRamU clk rst0 en rstStrategy n@SNat initF rd0 mw0 =
  case rstStrategy of
    ClearOnReset ->
      -- Use reset infrastructure
      blockRamU# clk en n rd1 we1 wa1 w1
    NoClearOnReset ->
      -- Ignore reset infrastructure, pass values unchanged
      blockRamU# clk en n
        (fromEnum <$> rd0)
        we0
        (fromEnum <$> wa0)
        w0
 where
  rstBool = register clk rst0 en True (pure False)
  rstInv = invertReset rst0

  waCounter :: Signal dom (Index n)
  waCounter = register clk rstInv en 0 (satSucc SatBound <$> waCounter)

  wa0 = fst . fromJustX <$> mw0
  w0  = snd . fromJustX <$> mw0
  we0 = isJust <$> mw0

  rd1 = mux rstBool 0 (fromEnum <$> rd0)
  we1 = mux rstBool (pure True) we0
  wa1 = mux rstBool (fromInteger . toInteger <$> waCounter) (fromEnum <$> wa0)
  w1  = mux rstBool (initF <$> waCounter) w0

-- | blockRAMU primitive
blockRamU#
  :: forall n dom a
   . ( KnownDomain dom
     , HasCallStack
     , NFDataX a )
  => Clock dom
  -- ^ 'Clock' to synchronize to
  -> Enable dom
  -- ^ 'Enable' line
  -> SNat n
  -- ^ Number of elements in BRAM
  -> Signal dom Int
  -- ^ Read address @r@
  -> Signal dom Bool
  -- ^ Write enable
  -> Signal dom Int
  -- ^ Write address @w@
  -> Signal dom a
  -- ^ Value to write (at address @w@)
  -> Signal dom a
  -- ^ Value of the BRAM at address @r@ from the previous clock cycle
blockRamU# clk en SNat =
  -- TODO: Generalize to single BRAM primitive taking an initialization function
  blockRam#
    clk
    en
    (CV.map
      (\i -> deepErrorX $ "Initial value at index " <> show i <> " undefined.")
      (iterateI @n succ (0 :: Int)))
{-# NOINLINE blockRamU# #-}
{-# ANN blockRamU# hasBlackBox #-}

-- | A version of 'blockRam' that is initialized with the same value on all
-- memory positions
blockRam1
   :: forall n dom a r addr
   . ( KnownDomain dom
     , HasCallStack
     , NFDataX a
     , Enum addr
     , NFDataX addr
     , 1 <= n )
  => Clock dom
  -- ^ 'Clock' to synchronize to
  -> Reset dom
  -- ^ 'Reset' line. This needs to be asserted for at least /n/ cycles in order
  -- for the BRAM to be reset to its initial state.
  -> Enable dom
  -- ^ 'Enable' line
  -> ResetStrategy r
  -- ^ Whether to clear BRAM on asserted reset ('ClearOnReset') or
  -- not ('NoClearOnReset'). The reset needs to be asserted for at least /n/
  -- cycles to clear the BRAM.
  -> SNat n
  -- ^ Number of elements in BRAM
  -> a
  -- ^ Initial content of the BRAM (replicated /n/ times)
  -> Signal dom addr
  -- ^ Read address @r@
  -> Signal dom (Maybe (addr, a))
  -- ^ (write address @w@, value to write)
  -> Signal dom a
  -- ^ Value of the BRAM at address @r@ from the previous clock cycle
blockRam1 clk rst0 en rstStrategy n@SNat a rd0 mw0 =
  case rstStrategy of
    ClearOnReset ->
      -- Use reset infrastructure
      blockRam1# clk en n a rd1 we1 wa1 w1
    NoClearOnReset ->
      -- Ignore reset infrastructure, pass values unchanged
      blockRam1# clk en n a
        (fromEnum <$> rd0)
        we0
        (fromEnum <$> wa0)
        w0
 where
  rstBool = register clk rst0 en True (pure False)
  rstInv = invertReset rst0

  waCounter :: Signal dom (Index n)
  waCounter = register clk rstInv en 0 (satSucc SatBound <$> waCounter)

  wa0 = fst . fromJustX <$> mw0
  w0  = snd . fromJustX <$> mw0
  we0 = isJust <$> mw0

  rd1 = mux rstBool 0 (fromEnum <$> rd0)
  we1 = mux rstBool (pure True) we0
  wa1 = mux rstBool (fromInteger . toInteger <$> waCounter) (fromEnum <$> wa0)
  w1  = mux rstBool (pure a) w0

-- | blockRAM1 primitive
blockRam1#
  :: forall n dom a
   . ( KnownDomain dom
     , HasCallStack
     , NFDataX a )
  => Clock dom
  -- ^ 'Clock' to synchronize to
  -> Enable dom
  -- ^ 'Enable' line
  -> SNat n
  -- ^ Number of elements in BRAM
  -> a
  -- ^ Initial content of the BRAM (replicated /n/ times)
  -> Signal dom Int
  -- ^ Read address @r@
  -> Signal dom Bool
  -- ^ Write enable
  -> Signal dom Int
  -- ^ Write address @w@
  -> Signal dom a
  -- ^ Value to write (at address @w@)
  -> Signal dom a
  -- ^ Value of the BRAM at address @r@ from the previous clock cycle
blockRam1# clk en n a =
  -- TODO: Generalize to single BRAM primitive taking an initialization function
  blockRam# clk en (replicate n a)
{-# NOINLINE blockRam1# #-}
{-# ANN blockRam1# hasBlackBox #-}

-- | blockRAM primitive
blockRam#
  :: forall dom a n
   . ( KnownDomain dom
     , HasCallStack
     , NFDataX a )
  => Clock dom
  -- ^ 'Clock' to synchronize to
  -> Enable dom
  -- ^ 'Enable' line
  -> Vec n a
  -- ^ Initial content of the BRAM, also determines the size, @n@, of the BRAM
  --
  -- __NB__: __MUST__ be a constant
  -> Signal dom Int
  -- ^ Read address @r@
  -> Signal dom Bool
  -- ^ Write enable
  -> Signal dom Int
  -- ^ Write address @w@
  -> Signal dom a
  -- ^ Value to write (at address @w@)
  -> Signal dom a
  -- ^ Value of the BRAM at address @r@ from the previous clock cycle
blockRam# (Clock _ Nothing) gen content = \rd wen waS wd -> runST $ do
  ramStart <- newListArray (0,szI-1) contentL
  -- start benchmark only
  -- ramStart <- unsafeThawSTArray ramArr
  -- end benchmark only
  go
    ramStart
    (withFrozenCallStack (deepErrorX "blockRam: intial value undefined"))
    (fromEnable gen)
    rd
    (fromEnable gen .&&. wen)
    waS
    wd
 where
  contentL = unsafeCoerce content :: [a]
  szI = L.length contentL
  -- start benchmark only
  -- ramArr = listArray (0,szI-1) contentL
  -- end benchmark only

  go :: STArray s Int a -> a -> Signal dom Bool -> Signal dom Int
     -> Signal dom Bool -> Signal dom Int -> Signal dom a
     -> ST s (Signal dom a)
  go !ram o ret@(~(re :- res)) rt@(~(r :- rs)) et@(~(e :- en)) wt@(~(w :- wr)) dt@(~(d :- din)) = do
    o `seqX` (o :-) <$> (ret `seq` rt `seq` et `seq` wt `seq` dt `seq`
      unsafeInterleaveST
        (do o' <- unsafeIOToST
                    (catch (if re then unsafeSTToIO (ram `safeAt` r) else pure o)
                    (\err@XException {} -> pure (throw err)))
            d `defaultSeqX` upd ram e (fromEnum w) d
            go ram o' res rs en wr din))

  upd :: STArray s Int a -> Bool -> Int -> a -> ST s ()
  upd ram we waddr d = case maybeIsX we of
    Nothing -> case maybeIsX waddr of
      Nothing -> -- Put the XException from `waddr` as the value in all
                 -- locations of `ram`.
                 forM_ [0..(szI-1)] (\i -> unsafeWriteSTArray ram i (seq waddr d))
      Just wa -> -- Put the XException from `we` as the value at address
                 -- `waddr`.
                 safeUpdate wa (seq we d) ram
    Just True -> case maybeIsX waddr of
      Nothing -> -- Put the XException from `waddr` as the value in all
                 -- locations of `ram`.
                 forM_ [0..(szI-1)] (\i -> unsafeWriteSTArray ram i (seq waddr d))
      Just wa -> safeUpdate wa d ram
    _ -> return ()

  safeAt :: HasCallStack => STArray s Int a -> Int -> ST s a
  safeAt s i =
    if (0 <= i) && (i < szI) then
      unsafeReadSTArray s i
    else pure $
      withFrozenCallStack
        (deepErrorX ("blockRam: read address " <> show i <>
                     " not in range [0.." <> show szI <> ")"))
  {-# INLINE safeAt #-}

  safeUpdate :: HasCallStack => Int -> a -> STArray s Int a -> ST s ()
  safeUpdate i a s =
    if (0 <= i) && (i < szI) then
      unsafeWriteSTArray s i a
    else
      let d = withFrozenCallStack
                (deepErrorX ("blockRam: write address " <> show i <>
                             " not in range [0.." <> show szI <> ")"))
       in forM_ [0..(szI-1)] (\j -> unsafeWriteSTArray s j d)
  {-# INLINE safeUpdate #-}
blockRam# _ _ _ = error "blockRam#: dynamic clocks not supported"
{-# ANN blockRam# hasBlackBox #-}
{-# NOINLINE blockRam# #-}

-- | Create a read-after-write block RAM from a read-before-write one
readNew
  :: ( KnownDomain dom
     , NFDataX a
     , Eq addr )
  => Clock dom
  -> Reset dom
  -> Enable dom
  -> (Signal dom addr -> Signal dom (Maybe (addr, a)) -> Signal dom a)
  -- ^ The BRAM component
  -> Signal dom addr
  -- ^ Read address @r@
  -> Signal dom (Maybe (addr, a))
  -- ^ (Write address @w@, value to write)
  -> Signal dom a
  -- ^ Value of the BRAM at address @r@ from the previous clock cycle
readNew clk rst en ram rdAddr wrM = mux wasSame wasWritten $ ram rdAddr wrM
  where readNewT rd (Just (wr, wrdata)) = (wr == rd, wrdata)
        readNewT _  Nothing             = (False   , undefined)

        (wasSame,wasWritten) =
          unbundle (register clk rst en (False, undefined)
                             (readNewT <$> rdAddr <*> wrM))

-- | Port operation
data RamOp n a
  = RamRead (Index n)
  -- ^ Read from address
  | RamWrite (Index n) a
  -- ^ Write data to address
  | RamNoOp
  -- ^ No operation
  deriving (Generic, NFDataX, Show)

{-# INLINE trueDualPortBlockRam #-}
-- | Produces vendor-agnostic HDL that will be inferred as a true dual-port
-- block RAM
--
-- Any value that is being written on a particular port is also the
-- value that will be read on that port, i.e. the same-port read/write behavior
-- is: WriteFirst. For mixed-port read/write, when port A writes to the address
-- port B reads from, the output of port B is undefined, and vice versa.
trueDualPortBlockRam ::
  forall nAddrs domA domB a .
  ( HasCallStack
  , KnownNat nAddrs
  , KnownDomain domA
  , KnownDomain domB
  , NFDataX a
  , BitPack a
  )
  => Clock domA
  -- ^ Clock for port A
  -> Clock domB
  -- ^ Clock for port B
  -> Signal domA (RamOp nAddrs a)
  -- ^ RAM operation for port A
  -> Signal domB (RamOp nAddrs a)
  -- ^ RAM operation for port B
  -> (Signal domA a, Signal domB a)
  -- ^ Outputs data on /next/ cycle. When writing, the data written
  -- will be echoed. When reading, the read data is returned.
trueDualPortBlockRam = \clkA clkB opA opB ->
  trueDualPortBlockRamWrapper
    -- Disable write enables
    False

    -- Port A
    clkA (isOp <$> opA) (toByteMask <$> opA) (ramOpAddr <$> opA)
    (fromJustX . ramOpWriteVal <$> opA)

    -- Port B
    clkB (isOp <$> opB) (toByteMask <$> opB) (ramOpAddr <$> opB)
    (fromJustX . ramOpWriteVal <$> opB)
 where
  ramOpAddr :: RamOp n a -> Index n
  ramOpAddr (RamRead addr)    = addr
  ramOpAddr (RamWrite addr _) = addr
  ramOpAddr RamNoOp           = errorX "Address for No operation undefined"

  toByteMask :: Bounded b => RamOp n a -> b
  toByteMask (RamWrite {}) = maxBound
  toByteMask _             = minBound

  ramOpWriteVal :: RamOp n a -> Maybe a
  ramOpWriteVal (RamWrite _ val) = Just val
  ramOpWriteVal _                = Nothing

  isOp :: RamOp n a -> Bool
  isOp RamNoOp = False
  isOp _       = True

-- | Port operation
data BeRamOp nAddrs nBytes
  = BeRamRead (Index nAddrs)
  -- ^ Read from address
  | BeRamWrite (Index nAddrs) (BitVector nBytes) (BitVector (nBytes * 8))
  -- ^ Write data to address
  | BeRamNoOp
  -- ^ No operation
  deriving (Generic, NFDataX, Show)


-- | Postulates that multiplying some number /a/ by some constant /b/, and
-- subsequently dividing that result by /b/ equals /a/.
cancelMulDiv :: forall a b . (1 <= b) => Proxy a -> Proxy b -> Dict (DivRU (b * a) b ~ a)
cancelMulDiv Proxy Proxy = unsafeCoerce (Dict :: Dict (a ~ a))

-- | Produces vendor-agnostic HDL that will be inferred as a true dual-port
-- block RAM with write byte enables.
--
-- Any value that is being written on a particular port is also the
-- value that will be read on that port, i.e. the same-port read/write behavior
-- is: WriteFirst. For mixed-port read/write, when port A writes to the address
-- port B reads from, the output of port B is undefined, and vice versa.
{-# INLINE trueDualPortBlockRamBe #-}
trueDualPortBlockRamBe ::
  forall nAddrs nBytes domA domB .
  ( HasCallStack
  , KnownNat nAddrs
  , KnownNat nBytes
  , KnownDomain domA
  , KnownDomain domB
  , 1 <= nBytes
  )
  => Clock domA
  -- ^ Clock for port A
  -> Clock domB
  -- ^ Clock for port B
  -> Signal domA (BeRamOp nAddrs nBytes)
  -- ^ RAM operation for port A
  -> Signal domB (BeRamOp nAddrs nBytes)
  -- ^ RAM operation for port B
  -> ( Signal domA (BitVector (8 * nBytes))
     , Signal domB (BitVector (8 * nBytes)) )
  -- ^ Outputs data on /next/ cycle. When writing, the data written
  -- will be echoed. When reading, the read data is returned.
trueDualPortBlockRamBe = \clkA clkB opA opB ->
  case cancelMulDiv @nBytes @8 Proxy Proxy of
    Dict ->
      trueDualPortBlockRamWrapper
        -- Enable write enables
        True

        -- Port A
        clkA (isOp <$> opA) (toByteMask <$> opA) (ramOpAddr <$> opA)
        (fromJustX . ramOpWriteVal <$> opA)

        -- Port B
        clkB (isOp <$> opB) (toByteMask <$> opB) (ramOpAddr <$> opB)
        (fromJustX . ramOpWriteVal <$> opB)
 where
  ramOpAddr :: BeRamOp nAddrs nBytes -> Index nAddrs
  ramOpAddr (BeRamRead addr)      = addr
  ramOpAddr (BeRamWrite addr _ _) = addr
  ramOpAddr BeRamNoOp             = errorX "Address for No operation undefined"

  toByteMask :: BeRamOp nAddrs nBytes -> BitVector nBytes
  toByteMask (BeRamWrite _ mask _) = mask
  toByteMask _                     = 0

  ramOpWriteVal :: BeRamOp nAddrs nBytes -> Maybe (BitVector (8 * nBytes))
  ramOpWriteVal (BeRamWrite _ _ val) = Just val
  ramOpWriteVal _                  = Nothing

  isOp :: BeRamOp nAddrs nBytes -> Bool
  isOp BeRamNoOp = False
  isOp _         = True

toMaybeX :: a -> MaybeX a
toMaybeX a =
  case isX a of
    Left _ -> IsX
    Right _ -> IsDefined a

data MaybeX a = IsX | IsDefined !a

data Conflict = Conflict
  { cfRWA     :: !(MaybeX Bool) -- ^ Read/Write conflict for output A
  , cfRWB     :: !(MaybeX Bool) -- ^ Read/Write conflict for output B
  , cfWW      :: !(MaybeX Bool) -- ^ Write/Write conflict
  , cfAddress :: !(MaybeX Int) }

-- | Clone each bit in a mask 8 times.
--
-- >>> byteMaskToBitMask (0b01 :: BitVector 2)
-- 0b0000_0000_1111_1111
--
byteMaskToBitMask :: KnownNat n => BitVector n -> BitVector (8 * n)
byteMaskToBitMask = pack . CV.map go . unpack
 where
  go :: Bool -> BitVector 8
  go True = maxBound
  go False = 0

-- | Write to a RAM and account for undefined values in the address, byte enable,
-- and data to write. Return read after write value.
--
-- >>> let write byteEna addr dat = showX (F.toList (snd (writeRam d2 byteEna addr dat [10, 20 :: Word16])))
-- >>> doWrite = 0b11
-- >>> dontWrite = 0b00
-- >>> write dontWrite 0 30
-- "[10,20]"
-- >>> write doWrite 0 30
-- "[30,20]"
-- >>> write (errorX "X") 0 30
-- "[undefined,20]"
-- >>> write dontWrite (errorX "X") 30
-- "[10,20]"
-- >>> write doWrite (errorX "X") 30
-- "[undefined,undefined]"
-- >>> write doWrite 0 (errorX "X")
-- "[undefined,20]"
--
-- Examples using byte enables:
--
-- >>> write 0b11 0 30
-- "[30,20]"
-- >>> write 0b01 0 30
-- "[30,20]"
-- >>> write 0b10 0 30
-- "[10,20]"
-- >>> write 0b00 0 30
-- "[10,20]"
--
-- Byte enables can also be partially undefined:
--
-- >>> let writeBv dat byteEna = F.toList (snd (writeRam d2 byteEna 0 dat [10, 20 :: BitVector 16]))
-- >>> writeBv 0b1010_1010_1010_1010 $(bLit "11")
-- [0b1010_1010_1010_1010,0b0000_0000_0001_0100]
-- >>> writeBv 0b1010_1010_1010_1010 $(bLit "1.")
-- [0b1010_1010_.0.0_.0.0,0b0000_0000_0001_0100]
-- >>> writeBv 0b1010_1010_1010_1010 $(bLit ".1")
-- [0b.0.0_.0.0_1010_1010,0b0000_0000_0001_0100]
-- >>> writeBv 0b1010_1010_1010_1010 $(bLit "..")
-- [0b...._...._...._....,0b0000_0000_0001_0100]
-- >>> writeBv 0b1010_1010_1010_1010 (errorX "X")
-- [0b...._...._...._....,0b0000_0000_0001_0100]
--
writeRam ::
  forall nAddrs a nBytes .
  ( NFDataX a
  , BitPack a
  , KnownNat nBytes
  , nBytes ~ DivRU (BitSize a) 8
  ) =>
  SNat nAddrs ->
  -- | Byte enable
  BitVector nBytes ->
  -- | Address
  Int ->
  -- | Data to write
  a ->
  -- | Memory to write to
  Seq a ->
  -- | (Read after write value, new memory)
  (Maybe a, Seq a)
writeRam nAddrs@SNat byteEnable addr dat mem
  -- Fully undefined enable and address
  | Left enaMsg <- enableUndefined
  , Left addrMsg <- addrUndefined
  = let msg = "Unknown enable and address" <>
              "\nWrite enable error message: " <> enaMsg <>
              "\nAddress error message: " <> addrMsg
      in ( Just (deepErrorX msg)
        , Seq.fromFunction (natToNum @nAddrs)
                            (unknownEnableAndAddr enaMsg addrMsg) )

  -- Fully undefined enable
  | Left enaMsg <- enableUndefined
  = let msg = "Write enable unknown; position" <> show addr <>
              "\nWrite enable error message: " <> enaMsg
      in writeRam nAddrs maxBound addr (deepErrorX msg) mem

  -- Undefined address, full byte enable or byte enable partially undefined
  | Left addrMsg <- addrUndefined
  , not disable
  = ( Just (deepErrorX "Unknown address")
    , Seq.fromFunction (natToNum @nAddrs) (unknownAddr addrMsg) )

  -- Read, byte enable fully defined and zero
  | disable
  = (Nothing, mem)

  -- Write full word, byte enable fully defined and max bound
  | enable
  , not disable
  = (Just dat, Seq.update addr dat mem)

  -- Write with a partially undefined and/or partially unset byte enable mask
  | otherwise
  = let
      goAdjust :: a -> a
      goAdjust oldDat =
        let
          -- Note the resize here: this will be a no-op if @BitSize a@ is divisible
          -- by 8. This means that this logic only works properly if this condition
          -- is actually met. Wrappers of 'trueDualPortBlockRam#' should ensure
          -- this.
          bitEnable = resize (byteMaskToBitMask byteEnable)

          -- .&. and .|. will take care of any undefined bits in 'byteEnable'
          datBv = pack dat .&. bitEnable
          oldDatBv = pack oldDat .&. complement bitEnable
          newDatBv = datBv .|. oldDatBv
        in
          unpack newDatBv
    in
      (Just dat, Seq.adjust' goAdjust addr mem)

 where
  enableUndefined = isX byteEnable
  enable = isDefinedMaxBound byteEnable
  disable = isDefinedMinBound byteEnable
  addrUndefined = isX addr

  maxBoundMask = (1 `shiftL` natToNum @nBytes) - 1

  isDefinedMaxBound :: forall n. KnownNat n => BitVector n -> Bool
  isDefinedMaxBound (BV 0 n) = n == maxBoundMask
  isDefinedMaxBound _        = False

  isDefinedMinBound :: forall n. KnownNat n => BitVector n -> Bool
  isDefinedMinBound (BV 0 0) = True
  isDefinedMinBound _        = False

  unknownEnableAndAddr :: String -> String -> Int -> a
  unknownEnableAndAddr enaMsg addrMsg n =
    deepErrorX ("Write enable and address unknown; position " <> show n <>
                "\nWrite enable error message: " <> enaMsg <>
                "\nAddress error message: " <> addrMsg)

  unknownAddr :: String -> Int -> a
  unknownAddr msg n =
    deepErrorX ("Write enabled, but address unknown; position " <> show n <>
                "\nAddress error message: " <> msg)

-- [Note: eta port names for trueDualPortBlockRam]
--
-- By naming all the arguments and setting the -fno-do-lambda-eta-expansion GHC
-- option for this module, the generated HDL also contains names based on the
-- argument names used here. This greatly improves readability of the HDL.

-- [Note: true dual-port blockRAM separate architecture]
--
-- A multi-clock true dual-port block RAM is only inferred from the generated HDL
-- when it lives in its own Verilog module / VHDL architecture. Add any other
-- logic to the module / architecture, and synthesis will no longer infer a
-- multi-clock true dual-port block RAM. This wrapper pushes the primitive out
-- into its own module / architecture.
trueDualPortBlockRamWrapper byteEnables clkA enA byteEnaA addrA datA clkB enB byteEnaB addrB datB =
  trueDualPortBlockRam#     byteEnables clkA enA byteEnaA addrA datA clkB enB byteEnaB addrB datB
{-# NOINLINE trueDualPortBlockRamWrapper #-}

{-# NOINLINE trueDualPortBlockRam# #-}
{-# ANN trueDualPortBlockRam# hasBlackBox #-}
{-# ANN trueDualPortBlockRam# (
  let
    bbName = show 'trueDualPortBlockRam#
    (   _hasCallStack
     :> knownNatAddrs
     :> _knownDomainA
     :> _knownDomainB
     :> _nfdataX
     :> _bitpack
     :> knownNatNBytes
     :> _nBytes
     :> byteEnables

     :> clockA
     :> enaA
     :> byteEnaA
     :> addrA
     :> datA

     :> clockB
     :> enaB
     :> byteEnaB
     :> addrB
     :> datB

     :> Nil
     ) = CV.indicesI @19

    (   symBlockName
     :> symDoutA
     :> symDoutB
     :> Nil
     ) = CV.indicesI @3
  in
    InlineYamlPrimitive [VHDL] [__i|
    BlackBox:
      name: "#{bbName}"
      kind: Declaration
      template: |-
        -- trueDualPortBlockRam begin
        ~GENSYM[~RESULT_trueDualPortBlockRam][#{symBlockName}] : block
          -- Shared memory
          type mem_type is array ( ~LIT[#{knownNatAddrs}]-1 downto 0 ) of ~TYP[#{datA}];
          constant all_ones : std_logic_vector(~LIT[#{knownNatNBytes}]-1 downto 0) := (others => '1');
          shared variable mem : mem_type;
          signal ~GENSYM[a_dout][#{symDoutA}] : ~TYP[#{datA}];
          signal ~GENSYM[b_dout][#{symDoutB}] : ~TYP[#{datB}];
        begin

          -- Port A
          process(~ARG[#{clockA}])
          begin
              if(rising_edge(~ARG[#{clockA}])) then
                    if(~ARG[#{enaA}]) then
                      ~IF~LIT[#{byteEnables}]~THEN
                      for i in 0 to ~LIT[#{knownNatNBytes}] - 1 loop
                        if ~ARG[#{byteEnaA}](i) = '1' then
                          mem(~IF~SIZE[~TYP[#{addrA}]]~THENto_integer(~ARG[#{addrA}])~ELSE0~FI)((i + 1) * 8 - 1 downto i * 8) := ~ARG[#{datA}]((i + 1) * 8 - 1 downto i * 8);
                        end if;
                      end loop;
                      ~ELSE
                      if(~ARG[#{byteEnaA}] = all_ones) then
                          mem(~IF~SIZE[~TYP[#{addrA}]]~THENto_integer(~ARG[#{addrA}])~ELSE0~FI) := ~ARG[#{datA}];
                      end if;
                      ~FI
                      ~SYM[#{symDoutA}] <= mem(~IF~SIZE[~TYP[#{addrA}]]~THENto_integer(~ARG[#{addrA}])~ELSE0~FI);
                  end if;
              end if;
          end process;

          -- Port B
          process(~ARG[#{clockB}])
          begin
              if(rising_edge(~ARG[#{clockB}])) then
                  if(~ARG[#{enaB}]) then
                      ~IF~LIT[#{byteEnables}]~THEN
                      for i in 0 to ~LIT[#{knownNatNBytes}] - 1 loop
                        if ~ARG[#{byteEnaB}](i) = '1' then
                          mem(~IF~SIZE[~TYP[#{addrB}]]~THENto_integer(~ARG[#{addrB}])~ELSE0~FI)((i + 1) * 8 - 1 downto i * 8) := ~ARG[#{datB}]((i + 1) * 8 - 1 downto i * 8);
                        end if;
                      end loop;
                      ~ELSE
                      if(~ARG[#{byteEnaB}] = all_ones) then
                          mem(~IF~SIZE[~TYP[#{addrB}]]~THENto_integer(~ARG[#{addrB}])~ELSE0~FI) := ~ARG[#{datB}];
                      end if;
                      ~FI
                      ~SYM[#{symDoutB}] <= mem(~IF~SIZE[~TYP[#{addrB}]]~THENto_integer(~ARG[#{addrB}])~ELSE0~FI);
                  end if;
              end if;
          end process;

          ~RESULT <= (~SYM[#{symDoutA}], ~SYM[#{symDoutB}]);
        end block;
        -- end trueDualPortBlockRam
|]) #-}
{-# ANN trueDualPortBlockRam# (
  let
    bbName = show 'trueDualPortBlockRam#
    (   _hasCallStack
     :> knownNatAddrs
     :> knownDomainA
     :> knownDomainB
     :> _nfdataX
     :> _bitpack
     :> knownNatNBytes
     :> _nBytes
     :> byteEnables

     :> clockA
     :> enaA
     :> byteEnaA
     :> addrA
     :> datA

     :> clockB
     :> enaB
     :> byteEnaB
     :> addrB
     :> datB

     :> Nil
     ) = CV.indicesI @19

    (   symMemName
     :> symAllOnes
     :> symDoutA
     :> symDoutB
     :> Nil
     ) = CV.indicesI @4
  in
    InlineYamlPrimitive [SystemVerilog] [__i|
    BlackBox:
      name: "#{bbName}"
      kind: Declaration
      template: |-
        // trueDualPortBlockRam begin
        // Shared memory
        logic [~SIZE[~TYP[#{datA}]]-1:0] ~GENSYM[mem][#{symMemName}] [~LIT[#{knownNatAddrs}]-1:0];
        logic [~LIT[#{knownNatNBytes}]-1:0] ~GENSYM[all_ones][#{symAllOnes}];
        assign ~SYM[#{symAllOnes}] = {~LIT[#{knownNatNBytes}]{1'b1}};

        ~SIGD[~GENSYM[data_slow][#{symDoutA}]][#{datA}];
        ~SIGD[~GENSYM[data_fast][#{symDoutB}]][#{datB}];

        // Port A
        always @(~IF~ACTIVEEDGE[Rising][#{knownDomainA}]~THENposedge~ELSEnegedge~FI ~ARG[#{clockA}]) begin
            if(~ARG[#{enaA}]) begin
                ~SYM[#{symDoutA}] <= ~SYM[#{symMemName}][~IF~SIZE[~TYP[#{addrA}]]~THEN~ARG[#{addrA}]~ELSE0~FI];
                ~IF~LIT[#{byteEnables}]~THEN
                for(i=0; i<~LIT[#{knownNatNBytes}]; i=i+1) begin
                  if(~ARG[#{byteEnaA}][i]) begin
                    ~SYM[#{symMemName}][~IF~SIZE[~TYP[#{addrA}]]~THEN~ARG[#{addrA}]~ELSE0~FI][i*8 +: 8] <= ~ARG[#{datA}][i*8 +: 8];
                    ~SYM[#{symDoutA}] <= ~ARG[#{datA}];
                  end
                end
                ~ELSE
                if(~ARG[#{byteEnaA}] == ~SYM[#{symAllOnes}]) begin
                    ~SYM[#{symMemName}][~IF~SIZE[~TYP[#{addrA}]]~THEN~ARG[#{addrA}]~ELSE0~FI] <= ~ARG[#{datA}];
                    ~SYM[#{symDoutA}] <= ~ARG[#{datA}];
                end
                ~FI
            end
        end

        // Port B
        always @(~IF~ACTIVEEDGE[Rising][#{knownDomainB}]~THENposedge~ELSEnegedge~FI ~ARG[#{clockB}]) begin
            if(~ARG[#{enaB}]) begin
                ~SYM[#{symDoutB}] <= ~SYM[#{symMemName}][~IF~SIZE[~TYP[#{addrB}]]~THEN~ARG[#{addrB}]~ELSE0~FI];
                ~IF~LIT[#{byteEnables}]~THEN
                for(i=0; i<~LIT[#{knownNatNBytes}]; i=i+1) begin
                  if(~ARG[#{byteEnaB}][i]) begin
                    ~SYM[#{symMemName}][~IF~SIZE[~TYP[#{addrB}]]~THEN~ARG[#{addrB}]~ELSE0~FI][i*8 +: 8] <= ~ARG[#{datB}][i*8 +: 8];
                    ~SYM[#{symDoutB}] <= ~ARG[#{datB}];
                  end
                end
                ~ELSE
                if(~ARG[#{byteEnaB}] == ~SYM[#{symAllOnes}]) begin
                    ~SYM[#{symDoutB}] <= ~ARG[#{datB}];
                    ~SYM[#{symMemName}][~IF~SIZE[~TYP[#{addrB}]]~THEN~ARG[#{addrB}]~ELSE0~FI] <= ~ARG[#{datB}];
                end
                ~FI
            end
        end

        assign ~RESULT = {~SYM[#{symDoutA}], ~SYM[#{symDoutB}]};
        // end trueDualPortBlockRam
|]) #-}
{-# ANN trueDualPortBlockRam# (
  let
    bbName = show 'trueDualPortBlockRam#
    (   _hasCallStack
     :> knownNatAddrs
     :> knownDomainA
     :> knownDomainB
     :> _nfdataX
     :> _bitpack
     :> knownNatNBytes
     :> _nBytes
     :> byteEnables

     :> clockA
     :> enaA
     :> byteEnaA
     :> addrA
     :> datA

     :> clockB
     :> enaB
     :> byteEnaB
     :> addrB
     :> datB

     :> Nil
     ) = CV.indicesI @19

    (   symMemName
     :> symAllOnes
     :> symDoutA
     :> symDoutB
     :> Nil
     ) = CV.indicesI @4
  in
    InlineYamlPrimitive [Verilog] [__i|
    BlackBox:
      name: "#{bbName}"
      kind: Declaration
      template: |-
        // trueDualPortBlockRam begin
        // Shared memory
        reg [~SIZE[~TYP[#{datA}]]-1:0] ~GENSYM[mem][#{symMemName}] [~LIT[#{knownNatAddrs}]-1:0];

        wire [~LIT[#{knownNatNBytes}]-1:0] ~GENSYM[all_ones][#{symAllOnes}];
        assign ~SYM[#{symAllOnes}] = {~LIT[#{knownNatNBytes}]{1'b1}};

        reg ~SIGD[~GENSYM[data_slow][#{symDoutA}]][#{datA}];
        reg ~SIGD[~GENSYM[data_fast][#{symDoutB}]][#{datB}];

        // Port A
        always @(~IF~ACTIVEEDGE[Rising][#{knownDomainA}]~THENposedge~ELSEnegedge~FI ~ARG[#{clockA}]) begin
            if(~ARG[#{enaA}]) begin
                ~SYM[#{symDoutA}] <= ~SYM[#{symMemName}][~IF~SIZE[~TYP[#{addrA}]]~THEN~ARG[#{addrA}]~ELSE0~FI];
                ~IF~LIT[#{byteEnables}]~THEN
                for(i=0; i<~LIT[#{knownNatNBytes}]; i=i+1) begin
                  if(~ARG[#{byteEnaA}][i]) begin
                    ~SYM[#{symMemName}][~IF~SIZE[~TYP[#{addrA}]]~THEN~ARG[#{addrA}]~ELSE0~FI][i*8 +: 8] <= ~ARG[#{datA}][i*8 +: 8];
                    ~SYM[#{symDoutA}] <= ~ARG[#{datA}];
                  end
                end
                ~ELSE
                if(~ARG[#{byteEnaA}] == ~SYM[#{symAllOnes}]) begin
                    ~SYM[#{symMemName}][~IF~SIZE[~TYP[#{addrA}]]~THEN~ARG[#{addrA}]~ELSE0~FI] <= ~ARG[#{datA}];
                    ~SYM[#{symDoutA}] <= ~ARG[#{datA}];
                end
                ~FI
            end
        end

        // Port B
        always @(~IF~ACTIVEEDGE[Rising][#{knownDomainB}]~THENposedge~ELSEnegedge~FI ~ARG[#{clockB}]) begin
            if(~ARG[#{enaB}]) begin
                ~SYM[#{symDoutB}] <= ~SYM[#{symMemName}][~IF~SIZE[~TYP[#{addrB}]]~THEN~ARG[#{addrB}]~ELSE0~FI];
                ~IF~LIT[#{byteEnables}]~THEN
                for(i=0; i<~LIT[#{knownNatNBytes}]; i=i+1) begin
                  if(~ARG[#{byteEnaB}][i]) begin
                    ~SYM[#{symMemName}][~IF~SIZE[~TYP[#{addrB}]]~THEN~ARG[#{addrB}]~ELSE0~FI][i*8 +: 8] <= ~ARG[#{datB}][i*8 +: 8];
                    ~SYM[#{symDoutB}] <= ~ARG[#{datB}];
                  end
                end
                ~ELSE
                if(~ARG[#{byteEnaB}] == ~SYM[#{symAllOnes}]) begin
                    ~SYM[#{symDoutB}] <= ~ARG[#{datB}];
                    ~SYM[#{symMemName}][~IF~SIZE[~TYP[#{addrB}]]~THEN~ARG[#{addrB}]~ELSE0~FI] <= ~ARG[#{datB}];
                end
                ~FI
            end
        end

        assign ~RESULT = {~SYM[#{symDoutA}], ~SYM[#{symDoutB}]};

        // end trueDualPortBlockRam
|]) #-}
-- | Haskell model/primitive for 'trueDualPortBlockRam'.
--
trueDualPortBlockRam#, trueDualPortBlockRamWrapper ::
  forall nAddrs domB domA a nBytes .
  ( HasCallStack
  , KnownNat nAddrs
  , KnownDomain domA
  , KnownDomain domB
  , NFDataX a
  , BitPack a
  , KnownNat nBytes -- XXX: Can be inferred at call-site. Why not here?
  , nBytes ~ DivRU (BitSize a) 8
  ) =>
  -- | Enable byte enables? (only used in the blackbox)
  Bool ->

  Clock domA ->
  -- | Enable
  Signal domA Bool ->
  -- | Write byte enable
  Signal domA (BitVector nBytes) ->
  -- | Address
  Signal domA (Index nAddrs) ->
  -- | Write data
  Signal domA a ->

  Clock domB ->
  -- | Enable
  Signal domB Bool ->
  -- | Write byte enable
  Signal domB (BitVector nBytes) ->
  -- | Address
  Signal domB (Index nAddrs) ->
  -- | Write data
  Signal domB a ->

  (Signal domA a, Signal domB a)
trueDualPortBlockRam# !_ clkA enA byteEnaA addrA datA clkB enB byteEnaB addrB datB =
  ( startA :- outA
  , startB :- outB )
 where
  (outA, outB) =
    go
      (Seq.fromFunction (natToNum @nAddrs) initElement)
      (clockTicks clkA clkB)
      (bundle (enA, byteEnaA, fromIntegral <$> addrA, datA))
      (bundle (enB, byteEnaB, fromIntegral <$> addrB, datB))
      startA startB

  startA = deepErrorX $ "trueDualPortBlockRam: Port A: First value undefined"
  startB = deepErrorX $ "trueDualPortBlockRam: Port B: First value undefined"

  initElement :: Int -> a
  initElement n =
    deepErrorX ("Unknown initial element; position " <> show n)


  getConflict :: Bool -> Bool -> BitVector nBytes -> Int -> BitVector nBytes -> Int -> Maybe Conflict
  getConflict enA_ enB_ wenA addrA_ wenB addrB_ =
    -- If port A or port B is writing on (potentially!) the same address,
    -- there's a conflict
    if sameAddr then Just conflict else Nothing
   where
    wenAX = toMaybeX (wenA == maxBound)
    wenBX = toMaybeX (wenB == maxBound)

    mergeX IsX b = b
    mergeX a IsX = a
    mergeX (IsDefined a) (IsDefined b) = IsDefined (a && b)

    conflict = Conflict
      { cfRWA     = if enB_ then wenBX else IsDefined False
      , cfRWB     = if enA_ then wenAX else IsDefined False
      , cfWW      = if enA_ && enB_ then mergeX wenAX wenBX else IsDefined False
      , cfAddress = toMaybeX addrA_ }

    sameAddr =
      case (isX addrA_, isX addrB_) of
        (Left _, _) -> True
        (_, Left _) -> True
        _           -> addrA_ == addrB_

  go ::
    Seq a ->
    [ClockAB] ->
    Signal domA (Bool, BitVector nBytes, Int, a) ->
    Signal domB (Bool, BitVector nBytes, Int, a) ->
    a -> a ->
    (Signal domA a, Signal domB a)
  go _ [] _ _ =
    error "trueDualPortBlockRamModel#.go: `ticks` should have been an infinite list"
  go ram0 (tick:ticks) as0 bs0 =
    case tick of
      ClockA -> goA
      ClockB -> goB
      ClockAB -> goBoth
   where
    (enA_, byteEnaA_, addrA_, datA_) :- as1 = as0
    (enB_, byteEnaB_, addrB_, datB_) :- bs1 = bs0

    goBoth prevA prevB = outA2 `seqX` outB2 `seqX` (outA2 :- as2, outB2 :- bs2)
     where
      conflict = getConflict enA_ enB_ byteEnaA_ addrA_ byteEnaB_ addrB_

      (datA1_,datB1_) = case conflict of
        Just Conflict{cfWW=IsDefined True} ->
          ( deepErrorX "trueDualPortBlockRam: conflicting write/write queries"
          , deepErrorX "trueDualPortBlockRam: conflicting write/write queries" )
        Just Conflict{cfWW=IsX} ->
          ( deepErrorX "trueDualPortBlockRam: conflicting write/write queries"
          , deepErrorX "trueDualPortBlockRam: conflicting write/write queries" )
        _ -> (datA_,datB_)

      (wroteA,ram1) = writeRam (SNat @nAddrs) byteEnaA_ addrA_ datA1_ ram0
      (wroteB,ram2) = writeRam (SNat @nAddrs) byteEnaB_ addrB_ datB1_ ram1

      outA1 = case conflict of
        Just Conflict{cfRWA=IsDefined True} ->
          deepErrorX "trueDualPortBlockRam: conflicting read/write queries"
        Just Conflict{cfRWA=IsX} ->
          deepErrorX "trueDualPortBlockRam: conflicting read/write queries"
        _ -> fromMaybe (ram0 `Seq.index` addrA_) wroteA

      outB1 = case conflict of
        Just Conflict{cfRWB=IsDefined True} ->
          deepErrorX "trueDualPortBlockRam: conflicting read/write queries"
        Just Conflict{cfRWB=IsX} ->
          deepErrorX "trueDualPortBlockRam: conflicting read/write queries"
        _ -> fromMaybe (ram0 `Seq.index` addrB_) wroteB

      outA2 = if enA_ then outA1 else prevA
      outB2 = if enB_ then outB1 else prevB
      (as2,bs2) = go ram2 ticks as1 bs1 outA2 outB2

    goA _ prevB | enA_ = out0 `seqX` (out0 :- as2, bs2)
     where
      (wrote, !ram1) = writeRam (SNat @nAddrs) byteEnaA_ addrA_ datA_ ram0
      out0 = fromMaybe (ram1 `Seq.index` addrA_) wrote
      (as2, bs2) = go ram1 ticks as1 bs0 out0 prevB

    goA prevA prevB = (prevA :- as2, bs2)
      where
        (as2,bs2) = go ram0 ticks as1 bs0 prevA prevB

    goB prevA _ | enB_ = out0 `seqX` (as2, out0 :- bs2)
     where
      (wrote, !ram1) = writeRam (SNat @nAddrs) byteEnaB_ addrB_ datB_ ram0
      out0 = fromMaybe (ram1 `Seq.index` addrB_) wrote
      (as2, bs2) = go ram1 ticks as0 bs1 prevA out0

    goB prevA prevB = (as2, prevB :- bs2)
     where
       (as2,bs2) = go ram0 ticks as0 bs1 prevA prevB
