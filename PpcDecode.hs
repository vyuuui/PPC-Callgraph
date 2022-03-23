module PpcDecode
( PpcCode(..)
, decodeWord
, mapOffset
) where

import Data.Bits (shiftL, (.&.), (.|.))
import Data.Word


data PpcCode
    = Branch Word32  -- Unconditional branch to rel, either local or forwarding
    | BranchCond Word32  -- Conditional branch to rel, typically local
    | BranchLink Word32  -- Unconditional branch to rel, with return
    | BranchCondLink Word32  -- Condition branch to rel, with return
    | BranchLr  -- Unconditional branch to LR
    | BranchCtr  -- Unconditional branch to CTR
    | OtherInstruction


mapOffset :: (Word32 -> Word32) -> PpcCode -> PpcCode
mapOffset f (Branch v) = Branch $ f v
mapOffset f (BranchCond v) = BranchCond $ f v
mapOffset f (BranchLink v) = BranchLink $ f v
mapOffset f (BranchCondLink v) = BranchCondLink $ f v
mapOffset _ x = x

opcodeMask :: Word32
opcodeMask = 0xfc000000

lrFlagMask :: Word32
lrFlagMask = 0x00000001

branchCondOp :: Word32
branchCondOp = 0x40000000

branchRegOp :: Word32
branchRegOp = 0x4c000000

branchOp :: Word32
branchOp = 0x48000000

-- Bx [op=6|LI=24|AA=1|LK=1]
bOffsetMask :: Word32
bOffsetMask = 0x03fffffc

-- Sign extend branch/link offset
bOffsetExtended :: Word32 -> Word32
bOffsetExtended offset
    | offset .&. 0x02000000 /= 0 = offset .|. 0xfc000000
    | otherwise                  = offset

-- BCx [op=6|BO=5|BI=5|BD=14|AA=1|LK=1]
bcOffsetMask :: Word32
bcOffsetMask = 0x0000fffc

-- Sign extend branch BCx/BCLx offset
bcOffsetExtended :: Word32 -> Word32
bcOffsetExtended offset
    | offset .&. 0x00008000 /= 0 = offset .|. 0xffff0000
    | otherwise                  = offset

-- BCLRx or BCCTRx
bRegFuncMask :: Word32
bRegFuncMask = 0x000001fe

bcctrFunc :: Word32
bcctrFunc = 528 `shiftL` 1

bclrFunc :: Word32
bclrFunc = 16 `shiftL` 1

bRegBoAlways :: Word32
bRegBoAlways = 0x02800000

decodeWord :: Word32 -> PpcCode
decodeWord instWord
    | opcode == branchOp     = if lrEnabled
                               then BranchLink $ bOffsetExtended bOffset
                               else Branch $ bOffsetExtended bOffset
    | opcode == branchCondOp = if lrEnabled
                               then BranchCondLink $ bcOffsetExtended bcOffset
                               else BranchCond $ bcOffsetExtended bcOffset
    | opcode == branchRegOp  = decodeBranchReg instWord
    | otherwise              = OtherInstruction
  where
    opcode = instWord .&. opcodeMask
    bOffset = instWord .&. bOffsetMask
    bcOffset = instWord .&. bcOffsetMask
    lrEnabled = (instWord .&. lrFlagMask) == lrFlagMask
    decodeBranchReg instWord
        | func == bclrFunc && bo == bRegBoAlways  = BranchLr
        | func == bcctrFunc && bo == bRegBoAlways = BranchCtr
        | otherwise                               = OtherInstruction
      where
        func = instWord .&. bRegFuncMask
        bo = instWord .&. bRegBoAlways
