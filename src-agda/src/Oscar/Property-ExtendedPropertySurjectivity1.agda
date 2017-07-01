--{-# OPTIONS --show-implicit #-}
{-# OPTIONS --postfix-projections #-}
--{-# OPTIONS -v30 #-}
{-# OPTIONS --rewriting #-}
module Oscar.Property-ExtendedPropertySurjectivity1 where

open import Oscar.Prelude
open import Oscar.Class

Arrow : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} (𝔄 : 𝔛 → Ø 𝔞)
  {𝔟} (𝔅 : 𝔛 → Ø 𝔟)
  → 𝔛 → 𝔛
  → Ø 𝔞 ∙̂ 𝔟
Arrow 𝔄 𝔅 x y = 𝔄 x → 𝔅 y

Extension : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) → 𝔒 → 𝔒 → Ø 𝔭
Extension 𝔓 m n = 𝔓 m → 𝔓 n

Property : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} (𝔒 : 𝔛 → Ø 𝔬)
  ℓ
  → Ø 𝔵 ∙̂ 𝔬 ∙̂ ↑̂ ℓ
Property 𝔒 ℓ = ∀ {x} → 𝔒 x → Ø ℓ

Extended : ∀
    {𝔞} {𝔄 : Ø 𝔞}
    {𝔟} {𝔅 : Ø 𝔟}
    {ℓ} (_≈_ : 𝔅 → 𝔅 → Ø ℓ)
    → (𝔄 → 𝔅) → (𝔄 → 𝔅)
    → Ø 𝔞 ∙̂ ℓ
Extended _≈_ = λ f g → ∀ x → f x ≈ g x

ExtendedProperty : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} (𝔒 : 𝔛 → Ø 𝔬)
  ℓ
  {ℓ̇} (_↦_ : ∀ {x} → 𝔒 x → 𝔒 x → Ø ℓ̇)
  → Ø 𝔵 ∙̂ 𝔬 ∙̂ ↑̂ ℓ ∙̂ ℓ̇
ExtendedProperty 𝔒 ℓ _↦_ = Σ (Property 𝔒 ℓ) (λ P → ∀ {x} {f g : 𝔒 x} → f ↦ g → P f → P g)

ArrowsourceExtendedProperty :
  ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔬₁} (𝔒₁ : 𝔛 → Ø 𝔬₁)
    {𝔬₂} (𝔒₂ : 𝔛 → Ø 𝔬₂)
    ℓ
    → (x : 𝔛) → ∀
      {ℓ̇} (_↦_ : ∀ {y} → Arrow 𝔒₁ 𝔒₂ x y → Arrow 𝔒₁ 𝔒₂ x y → Ø ℓ̇) → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ ∙̂ ℓ̇
ArrowsourceExtendedProperty 𝔒₁ 𝔒₂ ℓ x _↦_ = ExtendedProperty (Arrow 𝔒₁ 𝔒₂ x) ℓ _↦_

-- FunctorSubstitunctionProposextensequalityExtensionTermProposextensequality
module _
  {𝔬} {𝔒 : Ø 𝔬}
  where
  instance
    𝓢urjectionIdentity : 𝓢urjection 𝔒 𝔒
    𝓢urjectionIdentity .𝓢urjection.surjection = ¡

instance
 postulate
  ExtendedPropertySurjectivity : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔒₁ : 𝔛 → Ø 𝔞}
    {𝔟} {𝔒₂ : 𝔛 → Ø 𝔟}
    {ℓ : Ł}
    {ℓ̇} {_↦_ : ∀ {x} → 𝔒₂ x → 𝔒₂ x → Ø ℓ̇}
    -- ⦃ _ : [𝓢urjectivity] (Arrow 𝔒₁ 𝔒₂) (Extension 𝔒₂) ⦄
    -- ⦃ _ : 𝓢urjectivity (Arrow 𝔒₁ 𝔒₂) (Extension 𝔒₂) ⦄
    -- ⦃ _ : [𝓢urjextensionality] (Arrow 𝔒₁ 𝔒₂) (Extended _↦_) (Extension 𝔒₂) (Extended _↦_) ⦄
    -- ⦃ _ : 𝓢urjextensionality (Arrow 𝔒₁ 𝔒₂) (Extended _↦_) (Extension 𝔒₂) (Extended _↦_) ⦄
    ⦃ _ : [𝓢urjectivity] (Arrow 𝔒₁ 𝔒₂) (Extension $ λ v → ArrowsourceExtendedProperty 𝔒₁ 𝔒₂ ℓ v (Extended _↦_)) ⦄
    → 𝓢urjectivity (Arrow 𝔒₁ 𝔒₂) (Extension $ λ v → ArrowsourceExtendedProperty 𝔒₁ 𝔒₂ ℓ v (Extended _↦_))
  -- ExtendedPropertySurjectivity .𝓢urjectivity.surjectivity f P = (λ g → π₀ P (surjectivity g ∘ f)) , (λ f≐g Pf'◇f → π₁ P (surjextensionality f≐g ∘ f) Pf'◇f)

module TestExtendedPropertyFunctions
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} {𝔒₁ : 𝔛 → Ø 𝔞}
  {𝔟} {𝔒₂ : 𝔛 → Ø 𝔟}
  {ℓ}
  {ℓ̇} (_↦_ : ∀ {x} → 𝔒₂ x → 𝔒₂ x → Ø ℓ̇)
  -- ⦃ _ : [𝓢urjectivity] (Arrow 𝔒₁ 𝔒₂) (Extension 𝔒₂) ⦄
  -- ⦃ _ : 𝓢urjectivity (Arrow 𝔒₁ 𝔒₂) (Extension 𝔒₂) ⦄
  -- ⦃ _ : [𝓢urjextensionality] (Arrow 𝔒₁ 𝔒₂) (Extended _↦_) (Extension 𝔒₂) (Extended _↦_) ⦄
  -- ⦃ _ : 𝓢urjextensionality (Arrow 𝔒₁ 𝔒₂) (Extended _↦_) (Extension 𝔒₂) (Extended _↦_) ⦄
  ⦃ _ : [𝓢urjectivity] (Arrow 𝔒₁ 𝔒₂) (Extension $ λ v → ArrowsourceExtendedProperty 𝔒₁ 𝔒₂ ℓ v (Extended _↦_)) ⦄
  where

  works : ∀ {x y} → ArrowsourceExtendedProperty 𝔒₁ 𝔒₂ ℓ x (Extended _↦_) → Arrow 𝔒₁ 𝔒₂ x y → ArrowsourceExtendedProperty 𝔒₁ 𝔒₂ ℓ y (Extended _↦_)
  works P f = § ⦃ r = ExtendedPropertySurjectivity {_↦_ = _↦_} ⦄ f $ P

  fails : ∀ {x y} → ArrowsourceExtendedProperty 𝔒₁ 𝔒₂ ℓ x (Extended _↦_) → Arrow 𝔒₁ 𝔒₂ x y → ArrowsourceExtendedProperty 𝔒₁ 𝔒₂ ℓ y (Extended _↦_)
  fails P f = § f $ P
