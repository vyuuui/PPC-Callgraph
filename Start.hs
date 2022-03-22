import Control.Monad
import Control.Monad.State
import Data.Word
import Data.Bits
import Data.List
import Numeric (showHex)
import qualified Data.Binary.Get as BG
import qualified Data.ByteString.Lazy as BS
import qualified Data.Map as M
import qualified Data.Set as S
import System.IO
import Data.Ix (inRange)
import qualified IntervalTree as IT

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

type VAddr = Word32

data SubroutineNode = Node VAddr [VAddr]
type SubroutineGraph = M.Map VAddr SubroutineNode
type AnalysisStack = [VAddr]

data DolSection
    = TextSection { start :: !Word32, memStart :: !VAddr, size :: !Word32 }
    | DataSection { start :: !Word32, memStart :: !VAddr, size :: !Word32 }
      deriving (Show)

memEnd :: DolSection -> Word32
memEnd sect = memStart sect + size sect - 1

physEnd :: DolSection -> Word32
physEnd sect = start sect + size sect - 1

data DolHeader = DolHeader { sections :: [DolSection], entryPoint :: !VAddr } deriving (Show)

data VirtualMapping = VirtualMapping { header :: DolHeader, rawData :: BS.ByteString }

{-
   Get the file location of a virtual address, given its virtual mapping
   Returns nothing if the virtual address is an invalid mapping
-}
convertMapping
    :: VirtualMapping
    -> (DolSection -> Word32)
    -> (DolSection -> Word32)
    -> (DolSection -> Word32)
    -> Word32
    -> Maybe Word32

convertMapping mapping ibegin iend obegin conv = foldr findSection Nothing (sections $ header mapping)
  where
    findSection sect acc
        | inRange (ibegin sect, iend sect) conv = Just $ conv - ibegin sect + obegin sect
        | otherwise                             = acc

toPhysAddr :: VirtualMapping -> VAddr -> Maybe Word32
toPhysAddr mapping = convertMapping mapping memStart memEnd start

toVirtAddr :: VirtualMapping -> Word32 -> Maybe VAddr
toVirtAddr mapping = convertMapping mapping start physEnd memStart

getWord :: BS.ByteString -> Word32 -> Word32
getWord bs addr = BG.runGet (BG.skip (fromIntegral addr) >> BG.getWord32be) bs

data GekkoCode
    = Branch VAddr  -- Unconditional branch to rel, either local or forwarding
    | BranchCond VAddr  -- Conditional branch to rel, typically local
    | BranchLink VAddr  -- Unconditional branch to rel, with return
    | BranchCondLink VAddr -- Condition branch to rel, with return
    | BranchLr  -- Unconditional branch to LR
    | BranchCtr  -- Unconditional branch to CTR
    | OtherInstruction
      deriving (Show)

data Instruction = Instruction { phys :: VAddr, virt :: Word32, code :: GekkoCode }

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

decodeInstruction :: VAddr -> Word32 -> Word32 -> Instruction
decodeInstruction vAddr pAddr instWord
    | opcode == branchOp     = if lrEnabled
                               then Instruction vAddr pAddr $ BranchLink $ vAddr + bOffsetExtended bOffset
                               else Instruction vAddr pAddr $ Branch $ vAddr + bOffsetExtended bOffset
    | opcode == branchCondOp = if lrEnabled
                               then Instruction vAddr pAddr $ BranchCondLink $ vAddr + bcOffsetExtended bcOffset
                               else Instruction vAddr pAddr $ BranchCond $ vAddr + bcOffsetExtended bcOffset
    | opcode == branchRegOp  = decodeBranchReg instWord
    | otherwise              = Instruction vAddr pAddr OtherInstruction
  where
    opcode = instWord .&. opcodeMask
    bOffset = instWord .&. bOffsetMask
    bcOffset = instWord .&. bcOffsetMask
    lrEnabled = (instWord .&. lrFlagMask) == lrFlagMask
    decodeBranchReg instWord
        | func == bclrFunc && bo == bRegBoAlways  = Instruction vAddr pAddr BranchLr
        | func == bcctrFunc && bo == bRegBoAlways = Instruction vAddr pAddr BranchCtr
        | otherwise                               = Instruction vAddr pAddr OtherInstruction
      where
        func = instWord .&. bRegFuncMask
        bo = instWord .&. bRegBoAlways

type AnalysisState = State AnalysisContext
data AnalysisContext = AnalysisContext
    { graph :: SubroutineGraph
    , localStack :: AnalysisStack
    , subStack :: AnalysisStack
    , coverage :: IT.IntervalNode Word32  -- Reported in physical locations, not virtual
    , mapping :: VirtualMapping
    }

whileM :: Monad m => (a -> Bool) -> (a -> m a) -> a -> m a
whileM pred iter val
    | pred val  = iter val >>= \v -> whileM pred iter v
    | otherwise = return val

-- Reports a list of calls within a subroutine chunk
data SubChunkInfo = SubChunkInfo
    { chunkJumps :: [VAddr]
    , chunkCalls :: [VAddr]
    , chunkVirtRegion :: IT.Interval VAddr
    , chunkPhysRegion :: IT.Interval Word32
    }

instance Show SubChunkInfo where
    show info = intercalate "\n" $ fmap ($ "\t") stringFns
      where
        cjSep x = "chunkJumps:"
        ccSep x = "chunkCalls:"
        crSep x = "chunkPhysRegion:"
        showRegion :: IT.Interval Word32 -> [ShowS]
        showRegion (l, r) = [showHex l, showHex r]
        stringFns = [cjSep] ++ fmap showHex (chunkJumps info) ++ [ccSep] ++ fmap showHex (chunkCalls info) ++ [crSep] ++ showRegion (chunkPhysRegion info)

parseSubroutineChunkDriver :: VAddr -> VirtualMapping -> Maybe SubChunkInfo
parseSubroutineChunkDriver vStart mapping =
    toPhysAddr mapping vStart >>= \pStart ->
    return $ parseSubroutineChunk vStart pStart (maxBound :: Word32) (rawData mapping)

parseSubroutineChunk :: Word32 -> VAddr -> Word32 -> BS.ByteString -> SubChunkInfo
parseSubroutineChunk vStart pStart pEnd mem =
    (foldl' parseSingleInst (SubChunkInfo [] [] (vStart, vStart) (pStart, pStart)) . takeWhile continueParse) instructions
  where 
    instructions = [decodeInstruction v p $ getWord mem p
                   | (v, p) <- zip (iterate (+4) vStart) (iterate (+4) pStart)]

    continueParse :: Instruction -> Bool
    continueParse (Instruction _ pAddr code) = (pAddr < pEnd) && continueInst code

    continueInst :: GekkoCode -> Bool
    continueInst (Branch _) = False
    continueInst BranchLr = False
    continueInst BranchCtr = False
    continueInst _ = True

    parseSingleInst :: SubChunkInfo -> Instruction -> SubChunkInfo
    parseSingleInst (SubChunkInfo jmpList callList viv piv) (Instruction vAddr pAddr (BranchCond target)) =
        SubChunkInfo (target:jmpList) callList (expandInterval viv) (expandInterval piv)
    parseSingleInst (SubChunkInfo jmpList callList viv piv) (Instruction vAddr pAddr (BranchLink target)) =
        SubChunkInfo jmpList (target:callList) (expandInterval viv) (expandInterval piv)
    parseSingleInst (SubChunkInfo jmpList callList viv piv) (Instruction vAddr pAddr (BranchCondLink target)) =
        SubChunkInfo jmpList (target:callList) (expandInterval viv) (expandInterval piv)
    parseSingleInst (SubChunkInfo jmpList callList viv piv) (Instruction vAddr pAddr _) =
        SubChunkInfo jmpList callList (expandInterval viv) (expandInterval piv)

    expandInterval :: IT.Interval Word32 -> IT.Interval Word32
    expandInterval (l, r) = (l, r + 4)



data SubInfo = SubInfo { subJumps :: S.Set VAddr, subCalls :: S.Set VAddr, subCoverage :: IT.IntervalNode Word32 }
instance Show SubInfo where
    show info = sjSep ++ S.foldr' hexAndNewline (scSep ++ S.foldr' hexAndNewline "" (subCalls info)) (subJumps info)
      where
        sjSep = "\nsubJumps:"
        scSep = "\nsubCalls:"
        hexAndNewline = (fmap . fmap) ("\n\t" ++) showHex

accrueChunk :: SubInfo -> SubChunkInfo -> SubInfo
accrueChunk (SubInfo jmps calls ivt) (SubChunkInfo jmps' calls' viv piv) =
    SubInfo (S.union jmps (S.fromList jmps')) (S.union calls (S.fromList calls')) (IT.insert ivt piv)

addInterval :: SubInfo -> IT.Interval Word32 -> SubInfo
addInterval (SubInfo jmps calls ivt) iv = SubInfo jmps calls $ IT.insert ivt iv

parseFullSubroutineDriver :: VAddr -> VirtualMapping -> Maybe SubInfo
parseFullSubroutineDriver vStart mapping =
    toPhysAddr mapping vStart >>= \pStart ->
    return $ parseFullSubroutine vStart pStart mapping

parseFullSubroutine :: VAddr -> Word32 -> VirtualMapping -> SubInfo
parseFullSubroutine vStart pStart mapping =
    until (null . subJumps) (\info -> S.foldl' parseJump info $ subJumps info) initialInfo
  where
    -- TODO: Use coverage tree from AnalysisContext
    initialInfo = SubInfo (S.fromList jmps) (S.fromList calls) (IT.singleton piv)
      where
        (SubChunkInfo jmps calls viv piv) = parseSubroutineChunk vStart pStart (maxBound :: Word32) (rawData mapping)

    -- Parse a jump, removing the jump from the set
    parseJump :: SubInfo -> VAddr -> SubInfo
    parseJump (SubInfo jmps calls ivt) vStart = case toPhysAddr mapping vStart of
        Nothing       -> infoSubStart
        (Just pStart) -> if IT.query ivt pStart
                         then infoSubStart
                         else parseChunk infoSubStart vStart pStart
      where
        infoSubStart = SubInfo (S.delete vStart jmps) calls ivt

    parseChunk :: SubInfo -> VAddr -> Word32 -> SubInfo
    parseChunk info vStart pStart
        | overlapped = accrueChunk info chunk
        | otherwise  = addLastInst (accrueChunk info chunk) chunk
      where
        overlapped = IT.query (subCoverage info) (snd $ chunkPhysRegion chunk)
        pEnd = IT.nearestAbove (subCoverage info) pStart
        chunk = parseSubroutineChunk vStart pStart pEnd (rawData mapping)
        addLastInst info'@(SubInfo j c ivt) (SubChunkInfo _ _ (_, vr) (_, pr)) =
            case inst of
              (Branch target) -> SubInfo (S.insert target j) c ivt
              _               -> info'
          where
            inst = code $ decodeInstruction vr pr $ getWord (rawData mapping) pr

generateCallgraph :: VAddr -> VirtualMapping -> Maybe SubroutineGraph
generateCallgraph mapping analStart = do
    physAddr <- toPhysAddr mapping analStart
    let traversal = [getWord (rawData mapping) x | x <- [physAddr, physAddr + 4..]]
     in Nothing


main = do
    -- dolFile <- openFile "default_mp2.dol" ReadMode
    dolContents <- BS.readFile "default_mp2.dol"
    let mapping = VirtualMapping (readHeader dolContents) dolContents
     in print $ parseFullSubroutineDriver 0x8030da5c mapping

