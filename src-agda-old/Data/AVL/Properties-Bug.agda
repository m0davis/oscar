open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module Data.AVL.Properties-Bug
  {k v ℓ}
  {Key : Set k} (Value : Key → Set v)
  {_<_ : Rel Key ℓ}
  (isStrictTotalOrder : IsStrictTotalOrder P._≡_ _<_) where

open import Data.AVL Value isStrictTotalOrder using ( module Extended-key )
open Extended-key

okay : ∀ ( a⁺ : Key⁺ )
         ( b c : Key )
         ( a⁺<b : a⁺ <⁺ [ b ] )
         ( b<c : [ b ] <⁺ [ c ] )
       → a⁺ <⁺ [ c ]
okay a⁺ b c a⁺<b b<c = trans⁺ a⁺ a⁺<b b<c

not-okay : ∀ ( a : Key )
             ( b c : Key )
             ( a<b : [ a ] <⁺ [ b ] )
             ( b<c : [ b ] <⁺ [ c ] )
           → [ a ] <⁺ [ c ]
not-okay a b c a<b b<c = trans⁺ [ a ] a<b b<c

okay-again : ∀ ( a : Key )
               ( b c : Key )
               ( a<b : [ a ] <⁺ [ b ] )
               ( b<c : [ b ] <⁺ [ c ] )
             → [ a ] <⁺ [ c ]
okay-again a b c a<b b<c = trans⁺ [ a ] { m = [ b ] } { u = [ c ] } a<b b<c
