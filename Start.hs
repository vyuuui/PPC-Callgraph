import System.IO
import Control.Monad.State
import Data.Word
import Data.List
import Data.Maybe
import qualified Data.ByteString.Lazy as BS
import qualified Data.ByteString.Lazy.Char8 as BSC
import qualified Data.Map as M
import qualified Data.Set as S
import qualified IntervalTree as IT
import Numeric (showHex, readHex)

import PpcAnalyze
import DolParse


type SymbolMap = M.Map Word32 BSC.ByteString
type SymbolicatedGraph = M.Map BSC.ByteString [BSC.ByteString]


showGraph :: SubroutineGraph -> String
showGraph graph =
    unlines $ map formatNode (M.toList graph)
  where
    hexAndNewline :: Word32 -> String -> String
    hexAndNewline = (fmap . fmap) ("\n    sub_" ++) showHex

    formatNode :: (Word32, [Word32]) -> String
    formatNode (addr, links) = "sub_" ++ showHex addr (":" ++ foldr hexAndNewline "" links)

showSymGraph :: SymbolicatedGraph -> String
showSymGraph graph =
    unlines $ map formatNode (M.toList graph)
  where
    unpackPrepend :: BSC.ByteString -> String -> String
    unpackPrepend x a = "\n    " ++ BSC.unpack x ++ a

    formatNode :: (BSC.ByteString, [BSC.ByteString]) -> String
    formatNode (name, links) = BSC.unpack name ++ ":" ++ foldr unpackPrepend "" links

processSymMap :: String -> String -> IO ()
processSymMap path outPath = do
    mapContents <- fmap (fmap BSC.words . BSC.lines) (BSC.readFile path)
    let contents2 = filter isFunction mapContents
    fdOut <- openFile outPath WriteMode
    mapM_ (writeFixedLine fdOut) contents2
    hClose fdOut
  where
    isFunction :: [BSC.ByteString] -> Bool
    isFunction a = (length a == 5) && (a !! 1 /= BSC.pack "00000000") && (a !! 3 == BSC.pack "0")

    writeFixedLine :: Handle -> [BSC.ByteString] -> IO ()
    writeFixedLine fdOut line = do
        BSC.hPutStr fdOut (line !! 2)
        hPutStr fdOut " "
        BSC.hPutStr fdOut (line !! 4)
        hPutStr fdOut "\n"


loadSymMap :: String -> IO SymbolMap
loadSymMap path = do
    mapContents <- fmap (fmap (BSC.break (==' ')) . BSC.lines) (BSC.readFile path)
    let parsed = map (\(addr, name) -> (fst $ head $ readHex $ BSC.unpack addr, BSC.drop 1 name))
                     (filter (not . BSC.null . snd) mapContents)
    return $ M.fromList parsed

symbolicateGraph :: SymbolMap -> SubroutineGraph -> SymbolicatedGraph
symbolicateGraph syms graph = M.mapKeys getSymbolName $ M.map (map getSymbolName) graph
  where
    getSymbolName addr = case M.lookup addr syms of
        Just str -> str
        Nothing  -> BSC.pack $ "sub_" ++ showHex addr ""

outputDot :: SymbolicatedGraph -> String -> IO ()
outputDot graph path = do
    fdOut <- openFile path WriteMode
    hPutStr fdOut "digraph subroutines {\n"
    let nodeNameMap = fst $ M.foldrWithKey (\k e (mp, ix) -> (M.insert k ix mp, ix + 1)) (M.empty, 0) graph
    M.foldrWithKey (outputNodeDefinition fdOut) (return ()) nodeNameMap
    M.foldrWithKey (outputNodeLinks fdOut nodeNameMap) (return 0) graph
    hPutStr fdOut "}"
    hClose fdOut
  where
    -- | output fd -> foldrWithKey args: node name -> node index -> IO env
    outputNodeDefinition :: Handle -> BSC.ByteString -> Int -> IO () -> IO ()
    outputNodeDefinition fdOut name index env = do
        hPutStr fdOut ("  node_" ++ show index ++ " [label=\"" ++ BSC.unpack name ++ "\"];\n")
        env

    -- | output fd -> name to node# -> foldrWithKey args: source node name -> target node names -> IO env
    outputNodeLinks
        :: Handle
        -> M.Map BSC.ByteString Int
        -> BSC.ByteString
        -> [BSC.ByteString]
        -> IO Int
        -> IO Int
    outputNodeLinks fdOut nodeNameMap _ links env = do
        idx <- env
        foldr (outputSingleLink fdOut nodeNameMap idx) (return ()) links
        return $ idx + 1
     where
        -- | output fd -> name to node# -> source node# -> foldr args: target node name -> IO env
        outputSingleLink
            :: Handle
            -> M.Map BSC.ByteString Int
            -> Int
            -> BSC.ByteString
            -> IO ()
            -> IO ()
        outputSingleLink fdOut nodeNameMap sidx name env = do
            let tidx = M.lookup name nodeNameMap
            when (isJust tidx)
                 (hPutStr fdOut $ "  node_" ++ show sidx ++ " -> node_" ++ show (fromJust tidx) ++ ";\n")
            env

main = do
    symMap <- loadSymMap "mp1_demangled.map"
    dolContents <- BS.readFile "default.dol"
    let mapping = VirtualMapping (readHeader dolContents) dolContents
    outputDot (symbolicateGraph symMap $ generateCallgraph 0x80018770 mapping) "dot_res.dot"

