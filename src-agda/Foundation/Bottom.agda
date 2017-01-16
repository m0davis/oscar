
module Foundation.Bottom where

open import Foundation.Primitive

record IsBottom {ℓ⊥} (⊥ : Set ℓ⊥) a : ℞ ⟰ a ⊔ ℓ⊥ where
  field
    ⊥-elim : ⊥ → {A : Set a} → A

open IsBottom ⦃ … ⦄ public

record Bottom ℓ⊥ a : ℞₁ a ⊔ ℓ⊥ where
  field
    ⊥ : Set ℓ⊥
    ⦃ isBottom ⦄ : IsBottom ⊥ a

open Bottom ⦃ … ⦄ public
