import Control.Monad.State
import Data.Word
import Data.List
import qualified Data.ByteString.Lazy as BS
import qualified Data.Map as M
import qualified Data.Set as S
import qualified IntervalTree as IT
import Numeric (showHex)

import PpcAnalyze
import DolParse


showGraph :: SubroutineGraph -> String
showGraph graph = intercalate "\n" $ map (\(a, c) -> "sub_" ++ (showHex a $ if null c then "\n  No calls" else " -- calls:" ++ foldr hexAndNewline "" c)) (M.toList graph)
  where
    hexAndNewline = (fmap . fmap) ("\n  sub_" ++) showHex


main = do
    dolContents <- BS.readFile "default_mp2.dol"
    let mapping = VirtualMapping (readHeader dolContents) dolContents
     in putStr $ showGraph $ generateCallgraph 0x8030da5c mapping

