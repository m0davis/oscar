
module Oscar.Property-NoInstanceBug where

open import Oscar.Prelude using (Ø₀; Ø_; _∙̂_; ↑̂_)

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

ArrowsourceProperty : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬₁} (𝔒₁ : 𝔛 → Ø 𝔬₁)
  {𝔬₂} (𝔒₂ : 𝔛 → Ø 𝔬₂)
  ℓ
  → 𝔛
  → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ
ArrowsourceProperty 𝔒₁ 𝔒₂ ℓ x = Property (Arrow 𝔒₁ 𝔒₂ x) ℓ

record 𝓢urjection
  {𝔬₁} (𝔒₁ : Ø 𝔬₁)
  {𝔬₂} (𝔒₂ : Ø 𝔬₂)
  : Ø 𝔬₁ ∙̂ 𝔬₂ where
  field surjection : 𝔒₁ → 𝔒₂

open 𝓢urjection ⦃ … ⦄ public

record 𝓢urjectivity'
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {𝔬₂} (𝔒₂ : 𝔒₁ → Ø 𝔬₂)
  : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ 𝔬₂ where
  field
    surjectivity' : ∀ {x y} → x ∼₁ y → 𝔒₂ x → 𝔒₂ y

open 𝓢urjectivity' ⦃ … ⦄ public

record [𝓢urjectivity]
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  : Ø₀ where
  no-eta-equality

record 𝓢urjectivity
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄ ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄ : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ where
  field
    surjectivity : ∀ {x y} → x ∼₁ y → surjection x ∼₂ surjection y

open 𝓢urjectivity ⦃ … ⦄ public

instance

  toSurj : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    ⦃ _ : [𝓢urjectivity] _∼₁_ (Extension 𝔒₂) ⦄
    ⦃ _ : 𝓢urjectivity _∼₁_ (Extension 𝔒₂) ⦃ record { surjection = λ x → x } ⦄ ⦄
    → 𝓢urjectivity' _∼₁_ 𝔒₂
  toSurj {{_}} {{r}} .𝓢urjectivity'.surjectivity' = surjectivity {{r = r}}

module _
  {𝔬} {𝔒 : Ø 𝔬}
  where
  instance
    𝓢urjectionIdentity : 𝓢urjection 𝔒 𝔒
    𝓢urjectionIdentity .𝓢urjection.surjection = λ x → x

postulate
  instance
    PropertySurjectivity : ∀
      {𝔵} {𝔛 : Ø 𝔵}
      {𝔞} {𝔒₁ : 𝔛 → Ø 𝔞}
      {𝔟} {𝔒₂ : 𝔛 → Ø 𝔟}
      {ℓ}
      ⦃ _ : [𝓢urjectivity] (Arrow 𝔒₁ 𝔒₂) (Extension (ArrowsourceProperty 𝔒₁ 𝔒₂ ℓ)) ⦄
      → 𝓢urjectivity (Arrow 𝔒₁ 𝔒₂) (Extension (ArrowsourceProperty 𝔒₁ 𝔒₂ ℓ))

module TestPropertyFunctions
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} {𝔒₁ : 𝔛 → Ø 𝔞}
  {𝔟} {𝔒₂ : 𝔛 → Ø 𝔟}
  {ℓ}
  ⦃ _ : [𝓢urjectivity] (Arrow 𝔒₁ 𝔒₂) (Extension (ArrowsourceProperty 𝔒₁ 𝔒₂ ℓ)) ⦄
  where

  works : ∀ {x y} → ArrowsourceProperty 𝔒₁ 𝔒₂ ℓ x → Arrow 𝔒₁ 𝔒₂ x y → ArrowsourceProperty 𝔒₁ 𝔒₂ ℓ y
  works P f = surjectivity' ⦃ r = toSurj ⦄ f P

  fails : ∀ {x y} → ArrowsourceProperty 𝔒₁ 𝔒₂ ℓ x → Arrow 𝔒₁ 𝔒₂ x y → ArrowsourceProperty 𝔒₁ 𝔒₂ ℓ y
  fails P f = surjectivity' f P
