
open import Oscar.Prelude
open import Oscar.Class.HasEquivalence
open import Oscar.Class.Reflexivity
open import Oscar.Class.Surjectextensivity
open import Oscar.Data.Proposequality

module Oscar.Class.Factsurj3 where

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔞̈ 𝔞̇ 𝔞̇̈}
  (𝔄̇ : π̂ 𝔞̇ 𝔄)
  (𝔄̈ : π̂² 𝔞̈ 𝔄)
  (ε̈ : 𝓻eflexivity 𝔄̈)
  (_◃′_ : 𝓼urjectextensivity 𝔄̈ 𝔄̇)
  (let infix 18 _◃′_
       _◃′_ = _◃′_)
  (𝔄̇̈ : ∀̇ π̂² 𝔞̇̈ 𝔄̇)
  (let infix 4 _≈_
       _≈_ = 𝔄̇̈)
  where
  [𝒻actsurj3] : Ṗroperty 𝔞̇̈ 𝔄̇
  [𝒻actsurj3] .π₀ 𝒶̇ = 𝒶̇ ≈ ε̈ ◃′ 𝒶̇

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔞̇} {𝔄̇ : 𝔄 → Ø 𝔞̇} {𝔞̇̈}
  ([𝔄̇̇] : Ṗroperty 𝔞̇̈ 𝔄̇)
  where
  𝒻actsurj3 = ∀ {𝒶} {𝒶̇ : 𝔄̇ 𝒶} → π₀ [𝔄̇̇] 𝒶̇
  module _
    𝔞̈
    where
    record [ℱactsurj3] : Ø 𝔞 ∙̂ 𝔞̇ ∙̂ ↑̂ 𝔞̈ ∙̂ ↑̂ 𝔞̇̈ where
      constructor ∁
      field
        𝔄̈ : π̂² 𝔞̈ 𝔄
        ε̈ : 𝓻eflexivity 𝔄̈
        _◃_ : 𝓼urjectextensivity 𝔄̈ 𝔄̇
        𝔄̇̈ : ∀̇ π̂² 𝔞̇̈ 𝔄̇
        ⦃ ⌶CorrectFactsurj3 ⦄ : [𝒻actsurj3] 𝔄̇ 𝔄̈ ε̈ _◃_ 𝔄̇̈ ≡ [𝔄̇̇]
    record ℱactsurj3 ⦃ _ : [ℱactsurj3] ⦄ : Ø 𝔞 ∙̂ 𝔞̇ ∙̂ 𝔞̇̈ where
      field factsurj3 : 𝒻actsurj3

open ℱactsurj3 ⦃ … ⦄ public

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔞̇} (𝔄̇ : 𝔄 → Ø 𝔞̇)
  {𝔞̈} (𝔄̈ : π̂² 𝔞̈ 𝔄)
  (ε̈ : 𝓻eflexivity 𝔄̈)
  (_◃_ : 𝓼urjectextensivity 𝔄̈ 𝔄̇)
  {𝔞̇̈} (𝔄̇̈ : ∀̇ π̂² 𝔞̇̈ 𝔄̇)
  where
  𝓯actsurj3 = 𝒻actsurj3 ([𝒻actsurj3] 𝔄̇ 𝔄̈ ε̈ _◃_ 𝔄̇̈)
  [𝓕actsurj3] = [ℱactsurj3] ([𝒻actsurj3] 𝔄̇ 𝔄̈ ε̈ _◃_ 𝔄̇̈) 𝔞̈
  𝓕actsurj3 = ℱactsurj3 ([𝒻actsurj3] 𝔄̇ 𝔄̈ ε̈ _◃_ 𝔄̇̈) 𝔞̈
