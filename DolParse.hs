module DolParse
( DolSection(..)
, DolHeader(..)
, VirtualMapping(..)
, toPhysAddr
, toVirtAddr
, getWord
, readHeader
) where


import Control.Monad
import qualified Data.Binary.Get as BG
import qualified Data.ByteString.Lazy as BS
import Data.Ix (inRange)
import Data.Word


data DolSection
    = TextSection { start :: !Word32, memStart :: !Word32, size :: !Word32 }
    | DataSection { start :: !Word32, memStart :: !Word32, size :: !Word32 }

data DolHeader = DolHeader { sections :: [DolSection], entryPoint :: !Word32 }

data VirtualMapping = VirtualMapping { header :: DolHeader, rawData :: BS.ByteString }


memEnd :: DolSection -> Word32
memEnd sect = memStart sect + size sect - 1

physEnd :: DolSection -> Word32
physEnd sect = start sect + size sect - 1

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

toPhysAddr :: VirtualMapping -> Word32 -> Maybe Word32
toPhysAddr mapping = convertMapping mapping memStart memEnd start

toVirtAddr :: VirtualMapping -> Word32 -> Maybe Word32
toVirtAddr mapping = convertMapping mapping start physEnd memStart

getWord :: BS.ByteString -> Word32 -> Word32
getWord bs addr = BG.runGet (BG.skip (fromIntegral addr) >> BG.getWord32be) bs

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
