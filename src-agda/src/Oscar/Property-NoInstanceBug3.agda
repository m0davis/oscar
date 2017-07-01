
module Oscar.Property-NoInstanceBug3 where

open import Oscar.Prelude using (Ø₀; Ø_; _∙̂_; ↑̂_)

Extension : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) → 𝔒 → 𝔒 → Ø 𝔭
Extension 𝔓 m n = 𝔓 m → 𝔓 n

ExtensionProperty : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬₁} (𝔒₁ : 𝔛 → Ø 𝔬₁)
  ℓ
  → 𝔛
  → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ ↑̂ ℓ
ExtensionProperty 𝔒₁ ℓ x = ∀ {y} → Extension 𝔒₁ x y → Ø ℓ

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
  {𝔯₂} (_∼₂_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₂)
  : Ø₀ where
  no-eta-equality

record 𝓢urjectivity
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {𝔯₂} (_∼₂_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₂)
  ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄ : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ 𝔯₂ where
  field
    surjectivity : ∀ {x y} → x ∼₁ y → x ∼₂ y

open 𝓢urjectivity ⦃ … ⦄ public

instance

  toSurj : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    ⦃ _ : [𝓢urjectivity] _∼₁_ (Extension 𝔒₂) ⦄
    ⦃ _ : 𝓢urjectivity _∼₁_ (Extension 𝔒₂) ⦄
    → 𝓢urjectivity' _∼₁_ 𝔒₂
  toSurj {{_}} {{r}} .𝓢urjectivity'.surjectivity' = surjectivity {{r = r}}

module TestPropertyFunctions
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} {𝔒₁ : 𝔛 → Ø 𝔞}
  {ℓ}
  ⦃ _ : [𝓢urjectivity] (Extension 𝔒₁) (Extension (ExtensionProperty 𝔒₁ ℓ)) ⦄
  ⦃ _ : 𝓢urjectivity (Extension 𝔒₁) (Extension (ExtensionProperty 𝔒₁ ℓ)) ⦄
  ⦃ toSurj' : 𝓢urjectivity' (Extension 𝔒₁) ((ExtensionProperty 𝔒₁ ℓ)) ⦄
  where

  works : ∀ {x y} → ExtensionProperty 𝔒₁ ℓ x → Extension 𝔒₁ x y → ExtensionProperty 𝔒₁ ℓ y
  works P f = surjectivity' ⦃ r = toSurj' ⦄ f P

  fails : ∀ {x y} → ExtensionProperty 𝔒₁ ℓ x → Extension 𝔒₁ x y → ExtensionProperty 𝔒₁ ℓ y
  fails P f = surjectivity' f P
