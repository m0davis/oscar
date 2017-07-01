
module Oscar.ClassBug where

open import Oscar.Prelude

record Equivalence₂
  {a} {A : Ø a} {b}
    (B : A → A → Ø b)
    c
  : Ø a ∙̂ b ∙̂ ↑̂ c where
    infix 4 _≈_
    field
      _≈_ : ∀ {x y} → B x y → B x y → Ø c

open Equivalence₂ ⦃ … ⦄ public

module _
  {a₂} {A₂ : Ø a₂} {b₂}
    (B₂ : A₂ → A₂ → Ø b₂)
    c₂
  where
  record Commutativity : Ø a₂ ∙̂ b₂ ∙̂ ↑̂ c₂ where
    field
      ⦃ ⌶Equivalence₂ ⦄ : Equivalence₂ B₂ c₂
      special : ∀ {x y} (f : B₂ x y) → f ≈ f

open Commutativity ⦃ … ⦄ public
