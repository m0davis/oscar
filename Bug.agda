module Bug where

open import Data.AVL using (Tree; empty)
open import Data.Vec using (Vec)
open import Data.String using (String)
open import Relation.Binary using (StrictTotalOrder)
open import Data.Nat.Properties using (strictTotalOrder)

empty' : Tree (Vec String)
       (StrictTotalOrder.isStrictTotalOrder strictTotalOrder)
empty' = empty (Vec String) {!!}
