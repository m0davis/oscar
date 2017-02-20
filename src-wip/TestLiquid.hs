{-@ LIQUID "--notermination" @-}

module TestLiquid where

-- import Prelude hiding (lookup)
import Data.Map

{-
data Free f a = Pure a | Free (f (Free f a))

oneForFree :: Free [] Int
oneForFree = Free [Pure 1]

recQux :: Int -> [a] -> Int
recQux _ [] = -1
recQux 0 xs = length xs
recQux i xs = recQux (i - 1) xs

recFoo :: Free [] Int -> [Int] -> Bool
recFoo (Free (x:xs)) ys = recFoo x ys
recFoo (Pure x) ys = False

{- nonEmptyString1 :: {s:String | len s > 0} @-}
nonEmptyString1 :: String
nonEmptyString1 = ['a']


{- nonEmptyString2 :: {s:String | len s > 0} @-}
nonEmptyString2 :: String
nonEmptyString2 = "a"
-}

{-@ embed Data.Map.Map as Map_t @-}

---------------------------------------------------------------------------------------
-- | Logical Map Operators: Interpreted "natively" by the SMT solver ------------------
---------------------------------------------------------------------------------------

{-@ measure Map_select :: forall k v. Data.Map.Map k v -> k -> v @-}

{-@ measure Map_store  :: forall k v. Data.Map.Map k v -> k -> v -> Data.Map.Map k v @-}

{-@ measure Map_size   :: forall k v. Data.Map.Map k v -> Int @-}


{-@ insert :: Ord k => k:k -> v:v -> m:Data.Map.Map k v -> {n:Data.Map.Map k v | n = Map_store m k v} @-}

{-@ Data.Map.lookup :: Ord k => k:k -> m:Data.Map.Map k v -> Maybe {v:v | v = Map_select m k} @-}

{-@ (!)    :: Ord k => m:Data.Map.Map k v -> k:k -> {v:v | v = Map_select m k} @-}

{- myMap1 :: {m:Map Int String | (Map_size m) >= 0 } @-}
myMap1 :: Map Int String
myMap1 = empty


myMap2 :: Map Int String
myMap2 = insert 0 "" empty

bad :: String
bad = myMap1 ! 1

