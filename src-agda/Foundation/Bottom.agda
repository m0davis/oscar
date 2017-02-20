
module Foundation.Bottom where

open import Foundation.Primitive

record IsBottom {ℓ-⊥} (⊥ : Set ℓ-⊥) ℓ-elim : ℞ ⟰ ℓ-elim ⊔ ℓ-⊥ where
  field
    ⊥-elim : ⊥ → {A : Set ℓ-elim} → A

open IsBottom ⦃ … ⦄ public

record Bottom ℓ-⊥ ℓ-elim : ℞₁ ℓ-elim ⊔ ℓ-⊥ where
  field
    ⊥ : Set ℓ-⊥
    instance ⦃ isBottom ⦄ : IsBottom ⊥ ℓ-elim

  ¬_ : ∀ {a} → Set a → ℞ a ⊔ ℓ-⊥
  ¬_ p = p → ⊥

open Bottom ⦃ … ⦄ public
