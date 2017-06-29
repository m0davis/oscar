{-# OPTIONS --show-implicit #-}
module Oscar.Property-ExtendedPropertySurjectivity2 where

open import Oscar.Prelude using (Σ; _$_)

module _
  {𝔒₁ : Set}
  (_∼₁_ : 𝔒₁ → 𝔒₁ → Set)
  (_∼₂_ : 𝔒₁ → 𝔒₁ → Set₁)
  where
  record [𝓢urjectivity] : Set where
    no-eta-equality
  record 𝓢urjectivity ⦃ _ : [𝓢urjectivity] ⦄ : Set₁ where
    field
      surjectivity : ∀ {x y} → x ∼₁ y → x ∼₂ y

open 𝓢urjectivity ⦃ … ⦄ public

Arrow : ∀
  {𝔛 : Set}
  (𝔄 : 𝔛 → Set)
  (𝔅 : 𝔛 → Set)
  → 𝔛 → 𝔛
  → Set
Arrow 𝔄 𝔅 x y = 𝔄 x → 𝔅 y

Extension : ∀ {𝔒 : Set} (𝔓 : 𝔒 → Set₁) → 𝔒 → 𝔒 → Set₁
Extension 𝔓 m n = 𝔓 m → 𝔓 n

Property : ∀
  {𝔛 : Set}
  (𝔒 : 𝔛 → Set)
  → Set₁
--Property 𝔒 = ∀ {x} → 𝔒 x → Set
Property 𝔒 = ∀ x → 𝔒 x → Set

Extended :
    {𝔄 : Set}
    {𝔅 : Set}
    (_≈_ : 𝔅 → 𝔅 → Set)
    → (𝔄 → 𝔅) → (𝔄 → 𝔅)
    → Set
Extended _≈_ = λ f g → ∀ x → f x ≈ g x

ExtendedProperty : ∀
  {𝔛 : Set}
  (𝔒 : 𝔛 → Set)
  (R : ∀ {x} → 𝔒 x → 𝔒 x → Set)
  → Set₁
ExtendedProperty 𝔒 R = Σ (Property 𝔒) (λ P → ∀ x (f g : 𝔒 x) → R f g → P _ f → P _ g)
-- ExtendedProperty 𝔒 _↦_ = Σ (Property 𝔒) (λ P → ∀ {x} {f g : 𝔒 x} → f ↦ g → P f → P g)

postulate 𝔛 : Set
postulate 𝔒₁ : 𝔛 → Set
postulate 𝔒₂ : 𝔛 → Set

ExtendedPropertyArrow :
--  {𝔛 : Set}
--  (𝔒₁ : 𝔛 → Set)
--  (𝔒₂ : 𝔛 → Set) →
  (x : 𝔛) → ∀
    (R : ∀ {y} → Arrow 𝔒₁ 𝔒₂ x y → Arrow 𝔒₁ 𝔒₂ x y → Set) → Set₁
ExtendedPropertyArrow {-𝔒₁ 𝔒₂-} x R = ExtendedProperty (Arrow 𝔒₁ 𝔒₂ x) R

record SType (S : ∀ {x} → 𝔒₂ x → 𝔒₂ x → Set) : Set where
  no-eta-equality

instance
  postulate
    ExtendedPropertySurjectivity : ∀
      {S : ∀ {x} → 𝔒₂ x → 𝔒₂ x → Set}
      ⦃ _ : SType S ⦄
      ⦃ xi : [𝓢urjectivity] (Arrow 𝔒₁ 𝔒₂) (Extension $ λ v → ExtendedPropertyArrow {-𝔒₁ 𝔒₂-} v (Extended S)) ⦄
      → 𝓢urjectivity (Arrow 𝔒₁ 𝔒₂) (Extension $ λ v → ExtendedPropertyArrow {-𝔒₁ 𝔒₂-} v (Extended S))

module _
  (R : ∀ {x} → 𝔒₂ x → 𝔒₂ x → Set)
  ⦃ _ : SType R ⦄
  ⦃ xi : [𝓢urjectivity] (Arrow 𝔒₁ 𝔒₂) (Extension $ λ v → ExtendedPropertyArrow {-𝔒₁ 𝔒₂-} v (Extended R)) ⦄
  where

  works : ∀ {x y} → Arrow 𝔒₁ 𝔒₂ x y → ExtendedPropertyArrow {-𝔒₁ 𝔒₂-} x (Extended R) → ExtendedPropertyArrow {-𝔒₁ 𝔒₂-} y (Extended R)
  works {x} {y} f P = surjectivity {𝔒₁ = 𝔛} {_∼₁_ = Arrow 𝔒₁ 𝔒₂} {_∼₂_ = Extension $
                                                          (λ v →
                                                             ExtendedPropertyArrow {-(λ z → 𝔒₁ z) (λ z → 𝔒₂ z)-} v
                                                             (λ {xx} → Extended (R {xx})))} ⦃ xi ⦄ ⦃ ExtendedPropertySurjectivity {S = R} ⦄ {x} {y} f P

  fails : ∀ {x y} → Arrow 𝔒₁ 𝔒₂ x y → ExtendedPropertyArrow {-𝔒₁ 𝔒₂-} x (Extended R) → ExtendedPropertyArrow {-𝔒₁ 𝔒₂-} y (Extended R)
  fails {x} {y} f P = surjectivity {𝔒₁ = 𝔛} {_∼₁_ = Arrow 𝔒₁ 𝔒₂} {_∼₂_ = Extension $
                                                          (λ v →
                                                             ExtendedPropertyArrow {-(λ z → 𝔒₁ z) (λ z → 𝔒₂ z)-} v
                                                             (λ {xx} → Extended (R {xx})))} ⦃ xi ⦄ {x} {y} f $ P
