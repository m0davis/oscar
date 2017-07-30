
open import Oscar.Prelude
open import Oscar.Class.HasEquivalence
open import Oscar.Class.Reflexivity
open import Oscar.Class.Surjectextensivity
open import Oscar.Data.Proposequality

module Oscar.Class.Factsurj3 where

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔞̈ 𝔞̇ ℓ̇}
  (𝔄̈ : π̂² 𝔞̈ 𝔄)
  (𝔄̇ : π̂ 𝔞̇ 𝔄)
  ⦃ _ : 𝓡eflexivity 𝔄̈ ⦄
  ⦃ _ : 𝓢urjectextensivity 𝔄̈ 𝔄̇ ⦄
  ⦃ _ : ∀ {x} → HasEquivalence (𝔄̇ x) ℓ̇ ⦄
  where
  [𝓯actsurj3] : Wrap (∀ {a} (ȧ : 𝔄̇ a) → _)
  [𝓯actsurj3] .π₀ ȧ = ȧ ≈ ε[ 𝔄̈ ] ◃ ȧ

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔞̇} {𝔄̇ : 𝔄 → Ø 𝔞̇} {ℓ}
  (type : Wrap (∀ {a} (ȧ : 𝔄̇ a) → Ø ℓ))
  where
  𝒻actsurj3 = ∀ {a} {b : 𝔄̇ a} → π₀ type b
  module _
    𝔯
    where
    record [ℱactsurj3] : Ø 𝔞 ∙̂ 𝔞̇ ∙̂ ↑̂ 𝔯 ∙̂ ↑̂ ℓ where
      constructor ∁
      field
        _∼ᵣ_ : π̂² 𝔯 𝔄
        ⦃ ⌶Reflexivity ⦄ : 𝓡eflexivity _∼ᵣ_
        ⦃ ⌶Surjectextensivity ⦄ : 𝓢urjectextensivity _∼ᵣ_ 𝔄̇
        ⦃ ⌶HasEquivalence ⦄ : ∀ {x} → HasEquivalence (𝔄̇ x) ℓ
        ⦃ ⌶CorrectFactsurj3 ⦄ : ([𝓯actsurj3] _∼ᵣ_ 𝔄̇) ≡ type
  module _
    {𝔯}
    ⦃ _ : [ℱactsurj3] 𝔯 ⦄
    where
    record ℱactsurj3 : Ø 𝔞 ∙̂ 𝔞̇ ∙̂ ℓ where
      field factsurj3 : 𝒻actsurj3

open ℱactsurj3 ⦃ … ⦄ public

module _
  {ℓ} {𝔞} {𝔄 : Ø 𝔞} {𝔟} (𝔅 : 𝔄 → Ø 𝔟)
  {𝔯} (_∼ᵣ_ : π̂² 𝔯 𝔄)
  ⦃ _ : 𝓡eflexivity _∼ᵣ_ ⦄
  ⦃ _ : 𝓢urjectextensivity _∼ᵣ_ 𝔅 ⦄
  ⦃ _ : ∀ {x} → HasEquivalence (𝔅 x) ℓ ⦄
  where
  𝓯actsurj3 = 𝒻actsurj3 ([𝓯actsurj3] _∼ᵣ_ 𝔅)
  [𝓕actsurj3] = [ℱactsurj3] ([𝓯actsurj3] _∼ᵣ_ 𝔅)
  𝓕actsurj3 = ℱactsurj3 ([𝓯actsurj3] _∼ᵣ_ 𝔅)
