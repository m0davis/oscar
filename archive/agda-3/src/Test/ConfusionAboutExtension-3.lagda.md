Many (maybe all) of the `Constraint`s may be removed.

```agda
open import Oscar.Class
open import Oscar.Class.Transitivity
open import Oscar.Data.Proposequality
open import Oscar.Data.Constraint
open import Oscar.Prelude

module Test.ConfusionAboutExtension-3 where

module Transextensionality
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  (transitivity : Transitivity.type _∼_)
  (let _∙_ : FlipTransitivity.type _∼_
       _∙_ g f = transitivity f g)
  = ℭLASS (𝔒 ,, _∼_ ,, (λ {x y} → _∼̇_ {x} {y}) , λ {x y z} → transitivity {x} {y} {z})
          (∀ {x y z} {f₁ f₂ : x ∼ y} {g₁ g₂ : y ∼ z} → f₁ ∼̇ f₂ → g₁ ∼̇ g₂ → g₁ ∙ f₁ ∼̇ g₂ ∙ f₂)

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  (_↦_ : Transitivity.type _∼_)
  ⦃ _ : Constraint (𝔒 ,, _∼_ ,, (λ {x y} → _∼̇_ {x} {y}) , λ {x y z} → _↦_ {x} {y} {z}) ⦄
  where
  record IsPrecategory : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where
    constructor ∁
    field
      ⦃ `𝓣ransextensionality ⦄ : Transextensionality.class _∼_ _∼̇_ _↦_

module _ {𝔬} {𝔒 : Ø 𝔬} where

  instance

    𝓣ransitivityProposequality : Transitivity.class Proposequality⟦ 𝔒 ⟧
    𝓣ransitivityProposequality .⋆ ∅ y∼z = y∼z

Transextensionality--Morphism=Proposequality : ∀
  {a} {A : Ø a}
  {m} {_⊸_ : A → A → Ø m}
  {transitivity : Transitivity.type _⊸_}
  ⦃ _ : Constraint (A ,, _⊸_ ,, λ {x y z} → transitivity {x} {y} {z}) ⦄
  → Transextensionality.class _⊸_ Proposequality transitivity
Transextensionality--Morphism=Proposequality .⋆ ∅ ∅ = ∅

module _
  {a} {A : Ø a} ⦃ _ : Constraint A ⦄
  where

  Transextensionality--Object=Proposequality,Morphism=Proposequality : Transextensionality.class Proposequality⟦ A ⟧ Proposequality transitivity
  Transextensionality--Object=Proposequality,Morphism=Proposequality .⋆ ∅ ∅ = ∅

module _
  {a} {A : Ø a}
  where

  module _ where
    instance _ = Transextensionality--Morphism=Proposequality
    test-1 : Transextensionality.class Proposequality⟦ A ⟧ (Proposequality) transitivity
    test-1 = !
    use-1 : Transextensionality.type Proposequality⟦ A ⟧ (Proposequality) transitivity
    use-1 = Transextensionality.method Proposequality⟦ A ⟧ (Proposequality) transitivity -- Transextensionality.method _ _ _

  module _ where
    instance _ = Transextensionality--Object=Proposequality,Morphism=Proposequality
    test-2 : Transextensionality.class Proposequality⟦ A ⟧ (Proposequality) transitivity
    test-2 = !
    use-2 : Transextensionality.type Proposequality⟦ A ⟧ (Proposequality) transitivity
    use-2 = Transextensionality.method _ _ _

  module _ where
    instance _ = Transextensionality--Morphism=Proposequality
    instance _ = Transextensionality--Object=Proposequality,Morphism=Proposequality
    test-3 : Transextensionality.class Proposequality⟦ A ⟧ (Proposequality) transitivity
    test-3 = !
```
