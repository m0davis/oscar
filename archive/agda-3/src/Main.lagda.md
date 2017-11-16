
It's possible to do things in Agda!

```agda
module Main where

open import IO
open import Data.Unit
open import Data.List
open import Data.Colist
open import Coinduction
import IO.Primitive as Prim
open import Data.Colist
open import Agda.Builtin.Coinduction

open import Agda.Builtin.IO public using () renaming (IO to IIO)
open import Foreign.Haskell
open import Agda.Primitive
open import Agda.Builtin.Char

say-hello : IO ⊤
say-hello = putStrLn "Hello, World!"

main = run say-hello
```
