module TestLiquidZ3 where

import Data.Set

{-@ measure toList :: Set a -> [a] @-}

{-@ threeSet :: {x:Set Int | len (toList x) == 3} @-}
threeSet :: Set Int
threeSet = singleton 1 `union` singleton 2 `union` singleton 3
