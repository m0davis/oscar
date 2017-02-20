module Map where

open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Tree

open module Map-Type { 𝑼⟨Key⟩ 𝑼⟨Value⟩ 𝑼⟨<ᵏ⟩ : Level }
           ( Key : Set 𝑼⟨Key⟩ )
           ( Value : Set 𝑼⟨Value⟩ )
           { _<ᵏ_ : Rel Key 𝑼⟨<ᵏ⟩ }
           ⦃ isStrictTotalOrder : IsStrictTotalOrder _≡_ _<ᵏ_ ⦄ = Tree Value isStrictTotalOrder public using () renaming ( Tree to Map )

open module Map-Functions { 𝑼⟨Key⟩ 𝑼⟨Value⟩ 𝑼⟨<ᵏ⟩ : Level }
           { Key : Set 𝑼⟨Key⟩ }
           { Value : Set 𝑼⟨Value⟩ }
           { _<ᵏ_ : Rel Key 𝑼⟨<ᵏ⟩ }
           ⦃ isStrictTotalOrder : IsStrictTotalOrder _≡_ _<ᵏ_ ⦄ = Tree Value isStrictTotalOrder public hiding ( Tree )

