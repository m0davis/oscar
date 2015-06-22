{-# LANGUAGE UnicodeSyntax #-}
module Main where

import Control.Monad
import Data.Char
import Text.Printf
import Data.Monoid

main ∷ IO ()
main = do
    mapM_ showAndTell [1..0x30000]

data Ͱ

(᭝) = undefined

-- (ᤷ) = undefined

(÷) :: Int -> Int -> Bool
(÷) = undefined

ƽ :: Int -> Int -> Bool
ƽ = undefined

showAndTell ∷ Int → IO ()
showAndTell i = do
    if getAny (mconcat [Any $ (snd $ kinds !! (p - 1)) c | p ← [1..5]]) then
        printf "%c%c%c%c%c %04x %c\n"
               (kq 1)
               (kq 2)
               (kq 3)
               (kq 4)
               (kq 5)
               i i
      else return ()
  where
    c = chr i
    kq p = if snd k c then fst k
                      else ' '
      where
        k = kinds !! (p - 1)

kinds ∷ [(Char, Char → Bool)]
kinds = [(,) 'U' isUpper
        ,(,) 'l' isLower
        ,(,) 'M' isMark
        ,(,) 'P' isPunctuation
        ,(,) 'S' isSymbol
        ]

