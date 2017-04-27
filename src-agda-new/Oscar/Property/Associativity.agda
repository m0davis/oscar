
module Oscar.Property.Associativity where

open import Oscar.Level

record Associativity
  {𝔬} {⋆ : Set 𝔬}
  {𝔪} {_⇒_ : ⋆ → ⋆ → Set 𝔪}
  (_∙_ : ∀ {y z} → y ⇒ z → ∀ {x} → x ⇒ y → x ⇒ z)
  {𝔮} (_≤_ : ∀ {x y} → x ⇒ y → x ⇒ y → Set 𝔮)
  : Set (𝔬 ⊔ 𝔪 ⊔ 𝔮) where
  field
    associativity : ∀ {w x} (f : w ⇒ x) {y} (g : x ⇒ y) {z} (h : y ⇒ z) → ((h ∙ g) ∙ f) ≤ (h ∙ (g ∙ f))

open Associativity ⦃ … ⦄ public

association : ∀
  {𝔬} {⋆ : Set 𝔬}
  {𝔪} {_⇒_ : ⋆ → ⋆ → Set 𝔪}
  (_∙_ : ∀ {y z} → y ⇒ z → ∀ {x} → x ⇒ y → x ⇒ z)
  {𝔮} (_≤_ : ∀ {x y} → x ⇒ y → x ⇒ y → Set 𝔮)
  ⦃ _ : Associativity _∙_ _≤_ ⦄
  → ∀ {w x} (f : w ⇒ x) {y} (g : x ⇒ y) {z} (h : y ⇒ z) → ((h ∙ g) ∙ f) ≤ (h ∙ (g ∙ f))
association _∙_ _≤_ = associativity {_∙_ = _∙_} {_≤_ = _≤_}
