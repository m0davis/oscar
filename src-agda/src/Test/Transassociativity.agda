
module Test.Transassociativity where

open import Oscar.Prelude
open import Oscar.Class.Transitivity
open import Oscar.Class.Transassociativity
open import Oscar.Data.Proposequality

test-transassociativity-≡ : ∀
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  ⦃ _ : [𝓣ransassociativity] _∼_ Proposequality ⦄
  ⦃ _ : 𝓣ransitivity _∼_ ⦄
  ⦃ _ : 𝓣ransassociativity _∼_ Proposequality ⦄
  → ∀ {w x y z} (f : w ∼ x) (g : x ∼ y) (h : y ∼ z) → (h ∙ g) ∙ f ≡ h ∙ g ∙ f
test-transassociativity-≡ f g h rewrite transassociativity {_∼̇_ = Proposequality} f g h = ∅ -- transassociativity
