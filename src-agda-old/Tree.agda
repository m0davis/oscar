open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)
 
module Tree { 𝑼⟨Key⟩ 𝑼⟨Value⟩ 𝑼⟨<ᵏ⟩ : Level }
            { Key : Set 𝑼⟨Key⟩ }
            ( Value : Set 𝑼⟨Value⟩ )
            { _<ᵏ_ : Rel Key 𝑼⟨<ᵏ⟩ }
            ( isStrictTotalOrder : IsStrictTotalOrder _≡_ _<ᵏ_ )
  where
 
  open import Data.List.Base
  open import Data.AVL (λ _ → Value) isStrictTotalOrder hiding ( module Indexed ) public
  open import Data.AVL.Properties (λ _ → Value) isStrictTotalOrder hiding ( module Indexed ) public

  module Indexed where
    import Data.AVL
    open Data.AVL.Indexed (λ _ → Value) isStrictTotalOrder public
    import Data.AVL.Properties
    open Data.AVL.Properties.Indexed (λ _ → Value) isStrictTotalOrder public
    -- open Indexed public
    -- open import Data.AVL.Properties (λ _ → Value) isStrictTotalOrder using ( module Data.AVL.Properties.Indexed public
  
  open import Function
  open import Data.Product
 
  keys : Tree → List Key
  keys = Data.List.Base.map proj₁ ∘ toList

  elems : Tree → List Value
  elems = Data.List.Base.map proj₂ ∘ toList
