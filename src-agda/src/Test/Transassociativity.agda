
open import Everything

module Test.Transassociativity where

test-transassociativity-≡ : ∀
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  ⦃ _ : Transitivity.class _∼_ ⦄
  ⦃ _ : Transassociativity!.class _∼_ Proposequality ⦄
  → ∀ {w x y z} (f : w ∼ x) (g : x ∼ y) (h : y ∼ z) → (h ∙ g) ∙ f ≡ h ∙ g ∙ f
test-transassociativity-≡ f g h rewrite transassociativity![ Proposequality ] f g h = ∅ -- transassociativity
