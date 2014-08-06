{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}

module Main where

data DataType = C1 | C2
    deriving (Show)

foo :: * -> C2
foo c1 = C2

main :: IO ()
main = print $ foo (C1)
