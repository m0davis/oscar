
module Oscar.Relation where

open import Oscar.Level

_⟨_⟩→_ : ∀ {a} {A : Set a} {b} → A → (A → Set b) → A → Set b
m ⟨ B ⟩→ n = B m → B n

Transitive : ∀ {a} {A : Set a} {b} (B : A → A → Set b) → Set (a ⊔ b)
Transitive B = ∀ {y z} → B y z → ∀ {x} → B x y → B x z

module _ {𝔬} {⋆ : Set 𝔬} {𝔪} {_↦_ : ⋆ → ⋆ → Set 𝔪} (_∙_ : Transitive _↦_) {𝔮} (_≞_ : ∀ {x} {y} → x ↦ y → x ↦ y → Set 𝔮) where

  Extensional : Set (𝔬 ⊔ 𝔪 ⊔ 𝔮)
  Extensional =
    ∀ {x y} {f₁ f₂ : x ↦ y}
    → f₁ ≞ f₂ → ∀ {z} {g₁ g₂ : y ↦ z}
    → g₁ ≞ g₂
    → (g₁ ∙ f₁) ≞ (g₂ ∙ f₂)

  Associative : Set (𝔬 ⊔ 𝔪 ⊔ 𝔮)
  Associative =
    ∀ {w x}
      (f : w ↦ x)
    {y}
      (g : x ↦ y)
    {z}
      (h : y ↦ z)
    → ((h ∙ g) ∙ f) ≞ (h ∙ (g ∙ f))
