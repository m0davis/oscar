
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.DeBruijnTypeTheoryProperties where

open import Type.Prelude

open import Type.A2
open import Type.DeBruijnA2
open import Type.DeBruijnVariable
open import Type.DeBruijnContext alphabet
open import Type.DeBruijnExpression alphabet
open import Type.DeBruijnTypeTheory
```

```agda
≝-project₁ : ∀ {N} {Γ : Context N} {x y A} → Γ ⊢ x ≝ y ∶ A → Γ ⊢ x ∶ A
≝-project₂ : ∀ {N} {Γ : Context N} {x y A} → Γ ⊢ x ≝ y ∶ A → Γ ⊢ y ∶ A

≝-project₁ (≝-reflexivity Γ⊢x∶A) = Γ⊢x∶A
≝-project₁ (≝-symmetry Γ⊢y≝x∶A) = ≝-project₂ Γ⊢y≝x∶A
≝-project₁ (≝-transitivity Γ⊢x≝⋆∶A _) = ≝-project₁ Γ⊢x≝⋆∶A
≝-project₁ (≝-type-substitution Γ⊢x≝y∶B Γ⊢B≝A∶𝒰) = ≝-type-substitution (≝-project₁ Γ⊢x≝y∶B) Γ⊢B≝A∶𝒰
≝-project₁ (ΠU _ A B Γ⊢f∶ΠF) = Γ⊢f∶ΠF
≝-project₁ (ΠI ℓ ⊢A t) = ΠI _ ⊢A (≝-project₁ t)
≝-project₁ (ΣI ⊢A x t t₁) = {!!}
≝-project₁ (+Iˡ t) = {!!}
≝-project₁ (+Iʳ t) = {!!}
≝-project₁ (ℕIˢ t) = {!!}
≝-project₁ (=I t) = {!!}
≝-project₁ (ΠE ⊢A x x₁) = {!!}
≝-project₁ (ΣE ⊢ΠAB x ⊢A ⊢B x₁ x₂ x₃) = {!!}
≝-project₁ (+LE ⊢+FAB x ⊢A x₁ ⊢B x₂ x₃) = {!!}
≝-project₁ (+RE x x₁ x₂) = {!!}
≝-project₁ (𝟙E x) = {!!}
≝-project₁ (ℕEᶻ x x₁) = {!!}
≝-project₁ (ℕEˢ x x₁ x₂) = {!!}
≝-project₁ (=E x x₁) = {!!}

≝-project₂ (≝-reflexivity x₁) = {!!}
≝-project₂ (≝-symmetry x₁) = {!!}
≝-project₂ (≝-transitivity x₁ x₂) = {!!}
≝-project₂ (≝-type-substitution x₁ x₂) = {!!}
≝-project₂ (ΠU f A B x) = ΠI {!!} {!!} (ΠE (weakenExpressionFrom 0 A) (weakenExpressionFrom 1 B) {!!} (Vble {!!} refl) {!!})
≝-project₂ (ΠI ℓ x x₁) = {!!}
≝-project₂ (ΣI ⊢A x x₁ x₂) = {!!}
≝-project₂ (+Iˡ x₁) = {!!}
≝-project₂ (+Iʳ x₁) = {!!}
≝-project₂ (ℕIˢ x₁) = {!!}
≝-project₂ (=I x₁) = {!!}
≝-project₂ (ΠE ⊢A x x₁) = {!!}
≝-project₂ (ΣE ⊢ΠAB x ⊢A ⊢B x₁ x₂ x₃) = {!!}
≝-project₂ (+LE ⊢+FAB x ⊢A x₁ ⊢B x₂ x₃) = {!!}
≝-project₂ (+RE x x₁ x₂) = {!!}
≝-project₂ (𝟙E x) = {!!}
≝-project₂ (ℕEᶻ x x₁) = {!!}
≝-project₂ (ℕEˢ x x₁ x₂) = {!!}
≝-project₂ (=E x x₁) = {!!}
```
