```agda
open import Oscar.Class
open import Oscar.Class.Transitivity
open import Oscar.Data.Proposequality
open import Oscar.Data.Constraint
open import Oscar.Prelude

module Test.ConfusionAboutExtension-2 where

module Transextensionality
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  (transitivity : Transitivity.type _∼_)
  (let _∙_ : FlipTransitivity.type _∼_
       _∙_ g f = transitivity f g)
  = ℭLASS (𝔒 ,, _∼_ ,, (λ {x y} → _∼̇_ {x} {y}) , λ {x y z} → transitivity {x} {y} {z}) -- FIXME what other possibilities work here?
          (∀ {x y z} {f₁ f₂ : x ∼ y} {g₁ g₂ : y ∼ z} → f₁ ∼̇ f₂ → g₁ ∼̇ g₂ → g₁ ∙ f₁ ∼̇ g₂ ∙ f₂)

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  (_↦_ : Transitivity.type _∼_)
  where
  record IsPrecategory : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where
    constructor ∁
    field
      ⦃ `𝓣ransextensionality ⦄ : Transextensionality.class _∼_ _∼̇_ _↦_
      -- ⦃ `𝓣ransassociativity ⦄ : Transassociativity.class _∼_ _∼̇_ _↦_

module _ {𝔬} {𝔒 : Ø 𝔬} where

  instance

    𝓣ransitivityProposequality : Transitivity.class Proposequality⟦ 𝔒 ⟧
    𝓣ransitivityProposequality .⋆ ∅ y∼z = y∼z

instance

    𝓣ransextensionality⋆Proposequality : ∀
      {a} {A : Ø a}
      {m} {_⊸_ : A → A → Ø m}
      {transitivity : Transitivity.type _⊸_}
      ⦃ _ : Constraint (_⊸_ ,, λ {x y z} → transitivity {x} {y} {z}) ⦄
      → Transextensionality.class _⊸_ Proposequality transitivity
    𝓣ransextensionality⋆Proposequality .⋆ ∅ ∅ = ∅

module _
  {a} {A : Ø a}
  where

  instance

    𝓣ransextensionalityProposequalityProposequality : Transextensionality.class Proposequality⟦ A ⟧ Proposequality transitivity
    -- 𝓣ransextensionalityProposequalityProposequality = 𝓣ransextensionality⋆Proposequality -- using this instead avoids the below-mentioned errors
    𝓣ransextensionalityProposequalityProposequality .⋆ ∅ ∅ = ∅

module _
  {a} {A : Ø a}
  where

  testme : Transextensionality.class Proposequality⟦ A ⟧ (Proposequality) transitivity
  testme = ! -- errors

  instance

    IsPrecategoryExtension : IsPrecategory Proposequality⟦ A ⟧ Proposequality transitivity
    IsPrecategoryExtension .IsPrecategory.`𝓣ransextensionality = ! -- FIXME I'd like to use instance search to find this instance, but this errors b/c of
    -- IsPrecategoryExtension .IsPrecategory.`𝓣ransassociativity = magic
```
