module PpcAnalyze
( PpcInst(..)
, SubChunkInfo(..)
, SubInfo(..)
, SubroutineGraph
, parseFullSubroutineDriver
, parseSubroutineChunkDriver
, generateCallgraph
) where


import Control.Monad
import qualified Data.ByteString.Lazy as BS
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Word
import DolParse
import PpcDecode
import qualified IntervalTree as IT
import Numeric (showHex)


type SubroutineGraph = M.Map Word32 [Word32]

data PpcInst = PpcInst { virt :: Word32, phys :: Word32, code :: PpcCode }

data SubChunkInfo = SubChunkInfo
    { chunkJumps :: [Word32]
    , chunkCalls :: [Word32]
    , chunkVirtRegion :: IT.Interval Word32
    , chunkPhysRegion :: IT.Interval Word32
    }

data SubInfo = SubInfo
    { subJumps :: S.Set Word32
    , subCalls :: S.Set Word32
    , subCoverage :: IT.IntervalNode Word32
    , subStart :: Word32
    }

data GraphContext = GraphContext { pendingCalls :: S.Set Word32, subGraph :: SubroutineGraph }


instance Show SubChunkInfo where
    show info = L.intercalate "\n" $ fmap ($ "\t") stringFns
      where
        cjSep x = "chunkJumps:"
        ccSep x = "chunkCalls:"
        crSep x = "chunkPhysRegion:"
        showRegion :: IT.Interval Word32 -> [ShowS]
        showRegion (l, r) = [showHex l, showHex r]
        stringFns = [cjSep] ++ fmap showHex (chunkJumps info) ++ [ccSep] ++ fmap showHex (chunkCalls info) ++ [crSep] ++ showRegion (chunkPhysRegion info)

instance Show SubInfo where
    show info = ssSep ++ showHex (subStart info) (sjSep ++ S.foldr' hexAndNewline (scSep ++ S.foldr' hexAndNewline "" (subCalls info)) (subJumps info))
      where
        ssSep = "\nsubStart:"
        sjSep = "\nsubJumps:"
        scSep = "\nsubCalls:"
        hexAndNewline = (fmap . fmap) ("\n\t" ++) showHex


accrueChunk :: SubInfo -> SubChunkInfo -> SubInfo
accrueChunk (SubInfo jmps calls ivt subAddr) (SubChunkInfo jmps' calls' viv piv) =
    SubInfo (S.union jmps (S.fromList jmps')) (S.union calls (S.fromList calls')) (IT.insert ivt piv) subAddr

accrueSub :: GraphContext -> SubInfo -> GraphContext
accrueSub (GraphContext calls graph) (SubInfo _ subCalls _ subStart) =
    GraphContext (S.union calls subCalls) (M.insert subStart (S.toList subCalls) graph)

addInterval :: SubInfo -> IT.Interval Word32 -> SubInfo
addInterval (SubInfo jmps calls ivt subStart) iv = SubInfo jmps calls (IT.insert ivt iv) subStart

decodeInstruction :: Word32 -> Word32 -> Word32 -> PpcInst
decodeInstruction vStart pStart instWord = PpcInst vStart pStart $ mapOffset (+vStart) $ decodeWord instWord

-- | Reports a list of calls within a subroutine chunk
parseSubroutineChunk :: Word32 -> Word32 -> Word32 -> BS.ByteString -> SubChunkInfo
parseSubroutineChunk vStart pStart pEnd mem =
    (L.foldl' parseSingleInst (SubChunkInfo [] [] (vStart, vStart) (pStart, pStart)) . takeWhile continueParse) instructions
  where 
    instructions = [decodeInstruction v p $ getWord mem p
                   | (v, p) <- zip (iterate (+4) vStart) (iterate (+4) pStart)]

    continueParse :: PpcInst -> Bool
    continueParse (PpcInst _ pAddr code) = (pAddr < pEnd) && continueInst code

    continueInst :: PpcCode -> Bool
    continueInst (Branch _) = False
    continueInst BranchLr = False
    continueInst BranchCtr = False
    continueInst _ = True

    parseSingleInst :: SubChunkInfo -> PpcInst -> SubChunkInfo
    parseSingleInst (SubChunkInfo jmpList callList viv piv) (PpcInst vAddr pAddr (BranchCond target)) =
        SubChunkInfo (target:jmpList) callList (expandInterval viv) (expandInterval piv)
    parseSingleInst (SubChunkInfo jmpList callList viv piv) (PpcInst vAddr pAddr (BranchLink target)) =
        SubChunkInfo jmpList (target:callList) (expandInterval viv) (expandInterval piv)
    parseSingleInst (SubChunkInfo jmpList callList viv piv) (PpcInst vAddr pAddr (BranchCondLink target)) =
        SubChunkInfo jmpList (target:callList) (expandInterval viv) (expandInterval piv)
    parseSingleInst (SubChunkInfo jmpList callList viv piv) (PpcInst vAddr pAddr _) =
        SubChunkInfo jmpList callList (expandInterval viv) (expandInterval piv)

    expandInterval :: IT.Interval Word32 -> IT.Interval Word32
    expandInterval (l, r) = (l, r + 4)

parseFullSubroutine :: Word32 -> Word32 -> VirtualMapping -> SubInfo
parseFullSubroutine vStart pStart mapping =
    until (null . subJumps) (\info -> S.foldl' parseJump info $ subJumps info) initialInfo
  where
    initialInfo = SubInfo (S.fromList jmps) (S.fromList calls) (IT.singleton piv) vStart
      where
        (SubChunkInfo jmps calls viv piv) = parseSubroutineChunk vStart pStart (maxBound :: Word32) (rawData mapping)

    -- | Parse only if both unvisited and a valid virtual address
    parseJump :: SubInfo -> Word32 -> SubInfo
    parseJump (SubInfo jmps calls ivt subAddr) vTarget = case toPhysAddr mapping vTarget of
        Nothing        -> infoSubStart
        (Just pTarget) -> if IT.query ivt pTarget
                          then infoSubStart
                          else parseChunk infoSubStart vTarget pTarget
      where
        infoSubStart = SubInfo (S.delete vTarget jmps) calls ivt subAddr

    -- | Workhorse to parse a chunk of assembly, updating a folding SubInfo with the chunk
    parseChunk :: SubInfo -> Word32 -> Word32 -> SubInfo
    parseChunk info vStart pStart
        | overlapped = accrueChunk info chunk
        | otherwise  = addLastInst (accrueChunk info chunk) chunk
      where
        overlapped = IT.query (subCoverage info) (snd $ chunkPhysRegion chunk)
        pEnd = IT.nearestAbove (subCoverage info) pStart
        chunk = parseSubroutineChunk vStart pStart pEnd (rawData mapping)
        addLastInst info'@(SubInfo j c ivt subAddr) (SubChunkInfo _ _ (_, vr) (_, pr)) =
            case inst of
              (Branch target) -> SubInfo (S.insert target j) c ivt subAddr
              _               -> info'
          where
            inst = code $ decodeInstruction vr pr $ getWord (rawData mapping) pr

generateCallgraph :: Word32 -> VirtualMapping -> SubroutineGraph
generateCallgraph vStart mapping =
    subGraph $ until (null . pendingCalls) (\context -> S.foldl' parseCall context $ pendingCalls context) (GraphContext (S.singleton vStart) M.empty)
  where
    parseCall :: GraphContext -> Word32 -> GraphContext
    parseCall (GraphContext calls graph) vStart = case toPhysAddr mapping vStart of
        Nothing       -> contextSubStart
        (Just pStart) -> if M.member vStart graph
                         then contextSubStart
                         else accrueSub contextSubStart (parseFullSubroutine vStart pStart mapping)
      where
        contextSubStart = GraphContext (S.delete vStart calls) graph


parseSubroutineChunkDriver :: Word32 -> VirtualMapping -> Maybe SubChunkInfo
parseSubroutineChunkDriver vStart mapping =
    toPhysAddr mapping vStart >>= \pStart ->
    return $ parseSubroutineChunk vStart pStart (maxBound :: Word32) (rawData mapping)

parseFullSubroutineDriver :: Word32 -> VirtualMapping -> Maybe SubInfo
parseFullSubroutineDriver vStart mapping =
    toPhysAddr mapping vStart >>= \pStart ->
    return $ parseFullSubroutine vStart pStart mapping
