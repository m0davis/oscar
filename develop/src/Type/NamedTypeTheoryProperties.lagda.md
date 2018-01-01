
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.NamedTypeTheoryProperties where

open import Type.Prelude

open import Type.A2
open import Type.NamedA2
open import Type.NamedVariable
open import Type.NamedContext alphabet
open import Type.NamedExpression alphabet
open import Type.NamedTypeTheory
```

```agda
≝-project₁ : ∀ {Γ : Context} {x y A} → Γ ⊢ x ≝ y ∶ A → Γ ⊢ x ∶ A
≝-project₂ : ∀ {Γ : Context} {x y A} → Γ ⊢ x ≝ y ∶ A → Γ ⊢ y ∶ A

≝-project₁ (≝-reflexivity Γ⊢x∶A) = Γ⊢x∶A
≝-project₁ (≝-symmetry Γ⊢y≝x∶A) = ≝-project₂ Γ⊢y≝x∶A
≝-project₁ (≝-transitivity Γ⊢x≝⋆∶A _) = ≝-project₁ Γ⊢x≝⋆∶A
≝-project₁ (≝-subst Γ⊢x≝y∶B Γ⊢B≝A∶𝒰) = ≝-subst (≝-project₁ Γ⊢x≝y∶B) Γ⊢B≝A∶𝒰
≝-project₁ (ΠI x₁) = ΠI (≝-project₁ x₁)
≝-project₁ (ΠE x₁ x₂ x₃ x₄) = ΠE (ΠI x₁) x₂ x₄
≝-project₁ (ΠU x₂ x₃) = x₂
≝-project₁ (ΣI x₁ x₂ x₃) = {!!}
≝-project₁ (ΣE x₁ x₂ x₃ x₄ x₅ x₆) = {!!}
≝-project₁ (+Iˡ x x₁ x₂) = {!!}
≝-project₁ (+Iʳ x x₁ x₂) = {!!}
≝-project₁ (+Eˡ x₁ x₂ x₃ x₄ x₅ x₆) = {!!}
≝-project₁ (+Eʳ x₁ x₂ x₃ x₄ x₅ x₆) = {!!}
≝-project₁ (𝟙E x x₁ x₂) = {!!}
≝-project₁ (ℕIˢ x₁) = {!!}
≝-project₁ (ℕEᶻ x x₁ x₂ x₃) = {!!}
≝-project₁ (ℕEˢ x x₁ x₂ x₃ x₄ x₅) = {!!}
≝-project₁ (=I x₁) = {!!}
≝-project₁ (=E x₁ x₂ x₃ x₄ x₅) = {!!}

≝-project₂ (≝-reflexivity x₁) = {!!}
≝-project₂ (≝-symmetry x₁) = {!!}
≝-project₂ (≝-transitivity x₁ x₂) = {!!}
≝-project₂ (≝-subst x₁ x₂) = {!!}
≝-project₂ (ΠI x₁) = ΠI (≝-project₂ x₁)
≝-project₂ (ΠE x₁ x₂ x₃ x₄) = {!!}
≝-project₂ (ΠU x₂ x₃) = ΠI (ΠE {!!} (var (ctx-EXT {!!} x₃) zero refl refl) refl)
≝-project₂ (ΣI x₁ x₂ x₃) = {!!}
≝-project₂ (ΣE x₁ x₂ x₃ x₄ x₅ x₆) = {!!}
≝-project₂ (+Iˡ x x₁ x₂) = {!!}
≝-project₂ (+Iʳ x x₁ x₂) = {!!}
≝-project₂ (+Eˡ x₁ x₂ x₃ x₄ x₅ x₆) = {!!}
≝-project₂ (+Eʳ x₁ x₂ x₃ x₄ x₅ x₆) = {!!}
≝-project₂ (𝟙E x x₁ x₂) = {!!}
≝-project₂ (ℕIˢ x₁) = {!!}
≝-project₂ (ℕEᶻ x x₁ x₂ x₃) = {!!}
≝-project₂ (ℕEˢ x x₁ x₂ x₃ x₄ x₅) = {!!}
≝-project₂ (=I x₁) = {!!}
≝-project₂ (=E x₁ x₂ x₃ x₄ x₅) = {!!}
```
