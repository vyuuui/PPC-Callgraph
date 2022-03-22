module IntervalTree
( insert
, query
, nearestAbove
, null
, singleton
, Interval
, IntervalNode
) where

import Data.Ix (inRange, Ix)
import Prelude hiding (null, singleton)

type Interval a = (a, a)

data IntervalNode a = Leaf (Interval a) | Node (Interval a) (IntervalNode a) (IntervalNode a) | Null
    deriving (Show)

null :: (Ix a) => IntervalNode a
null = Null

singleton :: (Ix a) => Interval a -> IntervalNode a
singleton = Leaf

insert :: (Ix a) => IntervalNode a -> Interval a -> IntervalNode a
insert Null insIv = Leaf insIv
insert (Leaf iv@(l, r)) insIv@(il, _)
    | il < l    = Node iv (Leaf insIv) Null
    | otherwise = Node iv Null (Leaf insIv)
insert (Node iv@(l, r) lc rc) insIv@(il, _)
    | il < l    = Node iv (insert lc insIv) rc
    | otherwise = Node iv lc (insert rc insIv)

query :: (Ix a) => IntervalNode a -> a -> Bool
query Null _ = False
query (Leaf iv) v = inRange iv v
query (Node iv@(l, _) lc rc) v
    | inRange iv v = True
    | v < l        = query lc v
    | otherwise    = query rc v

{- Precondition: point is not within interval tree -}
nearestAbove :: (Ix a, Bounded a) => IntervalNode a -> a -> a
nearestAbove Null _ = maxBound
nearestAbove (Leaf iv@(l, _)) v
    | v < l        = l
    | otherwise    = maxBound
nearestAbove (Node iv@(l, _) lc rc) v
    | v < l     = min l $ nearestAbove lc v
    | otherwise = nearestAbove rc v
