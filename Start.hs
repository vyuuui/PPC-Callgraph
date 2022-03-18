import Control.Monad
import Data.Word
import Data.Bits
import qualified Data.Binary.Get as BG
import qualified Data.ByteString.Lazy as BS
import qualified Data.Map as M
import System.IO
import Data.Ix (inRange)

type VAddr = Word32

type SubroutineMap = M.Map VAddr Callgraph
data Callgraph = Node VAddr [VAddr]

data DolSection
    = TextSection { start :: !Word32, memStart :: !VAddr, size :: !Word32 }
    | DataSection { start :: !Word32, memStart :: !VAddr, size :: !Word32 }
      deriving (Show)

memEnd :: DolSection -> Word32
memEnd sect = memStart sect + size sect - 1

data DolHeader = DolHeader { sections :: [DolSection], entryPoint :: !VAddr } deriving (Show)

data VirtualMapping = VirtualMapping { header :: DolHeader, rawData :: BS.ByteString }

{-
   Get the file location of a virtual address, given its virtual mapping
   Returns nothing if the virtual address is an invalid mapping
-}
getFileMapping :: VirtualMapping -> VAddr -> Maybe Word32
getFileMapping vContext addr = foldr findSection Nothing (sections $ header vContext)
  where
    findSection sect acc
      | inRange (memStart sect, memEnd sect) addr = Just $ addr - memStart sect + start sect
      | otherwise                                 = acc

data GekkoInst
    = Branch VAddr  -- Unconditional branch to rel, either local or forwarding
    | BranchCond VAddr  -- Conditional branch to rel, typically local
    | BranchLink VAddr  -- Unconditional branch to rel, with return
    | BranchCondLink VAddr -- Condition branch to rel, with return
    | BranchLr  -- Unconditional branch to LR
    | BranchCtr  -- Unconditional branch to CTR
    | OtherInstruction
      deriving (Show)

getTextSection :: Int -> BG.Get DolSection
getTextSection num = do
    BG.skip $ num * 4
    start <- BG.getWord32be
    BG.skip 0x44
    memStart <- BG.getWord32be
    BG.skip 0x44
    size <- BG.getWord32be
    return $! TextSection start memStart size

getDataSection :: Int -> BG.Get DolSection
getDataSection num = do
    BG.skip $ num * 4 + 0x1c
    start <- BG.getWord32be
    BG.skip 0x44
    memStart <- BG.getWord32be
    BG.skip 0x44
    size <- BG.getWord32be
    return $! DataSection start memStart size

getAllSections :: Int -> (Int -> BG.Get DolSection) -> BS.ByteString -> [DolSection]
getAllSections num getter bs = foldr parseSection [] getters
  where
    getters = map getter [0..(num - 1)]
    parseSection :: BG.Get DolSection -> [DolSection] -> [DolSection]
    parseSection g acc
        | start sect /= 0 = sect : acc
        | otherwise         = acc
      where sect = BG.runGet g bs

readSections :: BS.ByteString -> [DolSection]
readSections bs = getAllSections 7 getTextSection bs ++ getAllSections 11 getDataSection bs

readEntry :: BS.ByteString -> Word32
readEntry = BG.runGet $ BG.skip 0xe0 >> BG.getWord32be

readHeader :: BS.ByteString -> DolHeader
readHeader bs = DolHeader (readSections bs) (readEntry bs)



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

bOffsetExtended :: Word32 -> Word32
bOffsetExtended offset
    | offset .&. 0x02000000 /= 0 = offset .|. 0xfc000000
    | otherwise                  = offset

-- BCx [op=6|BO=5|BI=5|BD=14|AA=1|LK=1]
bcOffsetMask :: Word32
bcOffsetMask = 0x0000fffc

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

decodeAddress :: VirtualMapping -> VAddr -> Maybe GekkoInst
decodeAddress vContext addr = do
    fileOff <- getFileMapping vContext addr
    let instWord = BG.runGet (BG.skip (fromIntegral fileOff) >> BG.getWord32be) (rawData vContext)
     in return $ decodeInstruction instWord
  where
    decodeInstruction instWord
        | opcode == branchOp     = if lrEnabled
                                   then BranchLink $ addr + bOffsetExtended bOffset
                                   else Branch $ addr + bOffsetExtended bOffset
        | opcode == branchCondOp = if lrEnabled
                                   then BranchCondLink $ addr + bcOffsetExtended bcOffset
                                   else BranchCond $ addr + bcOffsetExtended bcOffset
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

-- generateCallgraph :: BS.ByteString -> DolHeader -> VAddr -> Callgraph
-- generateCallgraph bs hdr analStart =

{-
generate callgraph: given a start address, scan downwards
- if instruction is BL    -> toss into child analysis stack
- if instruction is B     -> follow to relative location
- if instruction is Bc    -> toss into current analysis stack
- if instruction is BLR   -> termiante analysis, pop from (current, child) analysis stack
- if instruction is BCTR  -> terminate analysis, pop from (current, child) analysis stack
- otherwise               -> expand coverage region
We can ignore B(c)?(LR|CTR)L? and follow to next instruction, as they conditionally lead to an unknown location
if both analysis stacks are empty, terminate and spit out graph
-}

main = do
    -- dolFile <- openFile "default_mp2.dol" ReadMode
    dolContents <- BS.readFile "default_mp2.dol"
    let mapping = VirtualMapping (readHeader dolContents) dolContents
     in print $ decodeAddress mapping 0x8030e09c

