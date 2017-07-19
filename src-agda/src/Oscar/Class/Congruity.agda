
open import Oscar.Prelude

module Oscar.Class.Congruity where

module _ where

  module _
    {ℓ} (_∼_ : ∀ {𝔬} {𝔒 : Ø 𝔬} → 𝔒 → 𝔒 → Ø ℓ)
    𝔵 𝔶
    where
    𝓬ongruity = ∀ {𝔛 : Ø 𝔵} {𝔜 : Ø 𝔶} {x₁ x₂} (f : 𝔛 → 𝔜) → x₁ ∼ x₂ → f x₁ ∼ f x₂
    record 𝓒ongruity : Ø ℓ ∙̂ ↑̂ (𝔵 ∙̂ 𝔶) where
      field congruity : 𝓬ongruity

  open 𝓒ongruity ⦃ … ⦄ public

  module _
    {ℓ} (_∼_ : ∀ {𝔬} {𝔒 : Ø 𝔬} → 𝔒 → 𝔒 → Ø ℓ)
    {𝔵 𝔶} (𝔛 : Ø 𝔵) (𝔜 : Ø 𝔶)
    where
    𝓬ongruity' = ∀ {x₁ x₂} (f : 𝔛 → 𝔜) → x₁ ∼ x₂ → f x₁ ∼ f x₂
    record 𝓒ongruity' : Ø ℓ ∙̂ ↑̂ (𝔵 ∙̂ 𝔶) where
      field congruity' : 𝓬ongruity'

  open 𝓒ongruity' ⦃ … ⦄ public

  module _
    {ℓ} {𝔬} (_∼_ : ∀ {𝔒 : Ø 𝔬} → 𝔒 → 𝔒 → Ø ℓ)
    (𝔛 𝔜 : Ø 𝔬)
    where
    𝓬ongruity'' = ∀ {x₁ x₂} (f : 𝔛 → 𝔜) → x₁ ∼ x₂ → f x₁ ∼ f x₂
    record 𝓒ongruity'' : Ø ℓ ∙̂ 𝔬 where
      field congruity'' : 𝓬ongruity''

  open 𝓒ongruity'' ⦃ … ⦄ public

-- a functional replacement of 𝓒ongruity₂ (but note the additional requirement of 𝓣ransitivity)
congruity2 : ∀ {ℓ} {_∼_ : ∀ {x} {X : Ø x} → X → X → Ø ℓ}
    {𝔵 𝔶 𝔷}
    ⦃ _ : 𝓒ongruity _∼_ 𝔵 (𝔶 ∙̂ 𝔷) ⦄
    ⦃ _ : 𝓒ongruity _∼_ (𝔶 ∙̂ 𝔷) 𝔷 ⦄
    ⦃ _ : 𝓒ongruity _∼_ 𝔶 (𝔵 ∙̂ 𝔷) ⦄
    ⦃ _ : 𝓒ongruity _∼_ (𝔵 ∙̂ 𝔷) 𝔷 ⦄
    ⦃ _ : ∀ {x} {X : Ø x} → 𝓣ransitivity (_∼_ {X = X}) ⦄
    → ∀ {𝔛 : Ø 𝔵} {𝔜 : Ø 𝔶} {ℨ : Ø 𝔷} {x₁ x₂} {y₁ y₂} (f : 𝔛 → 𝔜 → ℨ) → x₁ ∼ x₂ → y₁ ∼ y₂ → f x₁ y₁ ∼ f x₂ y₂
congruity2 {𝔛 = 𝔛}{𝔜}{ℨ}{x₁}{x₂}{y₁}{y₂} f x₁∼x₂ y₁∼y₂ =
  let fx1=fx2 = congruity f x₁∼x₂ in
  let g2 = λ (fx : 𝔜 → ℨ) → fx y₂ in
  let fx1y2=fx2y2 = congruity g2 fx1=fx2 in
  let e = flip f in
  let ey1=ey2 = congruity e y₁∼y₂ in
  let h1 = λ (ex : 𝔛 → ℨ) → ex x₁ in
  let fx1y1=fx1y2 = congruity h1 ey1=ey2 in
  transitivity fx1y1=fx1y2 fx1y2=fx2y2

module _ where

  record 𝓒ongruity₂
    {ℓ} (_∼_ : ∀ {x} {X : Ø x} → X → X → Ø ℓ)
    𝔵 𝔶 𝔷
    : Ø ℓ ∙̂ ↑̂ (𝔵 ∙̂ 𝔶 ∙̂ 𝔷) where
    field congruity₂ : ∀ {𝔛 : Ø 𝔵} {𝔜 : Ø 𝔶} {ℨ : Ø 𝔷} {x₁ x₂} {y₁ y₂} (f : 𝔛 → 𝔜 → ℨ) → x₁ ∼ x₂ → y₁ ∼ y₂ → f x₁ y₁ ∼ f x₂ y₂

  open 𝓒ongruity₂ ⦃ … ⦄ public

module _ where

  module _
    𝔬 𝔭
    {ℓ} (_∼̇_ : ∀ {⋆ : Ø 𝔬} {⋆̇ : ⋆ → Ø 𝔭} → ((𝓞 : ⋆) → ⋆̇ 𝓞) → ((𝓞 : ⋆) → ⋆̇ 𝓞) → Ø ℓ)
    (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
    where
    record 𝓒̇ongruity : Ø ↑̂ (𝔬 ∙̂ 𝔭) ∙̂ ℓ where
      field ċongruity : ∀ {⋆ : Ø 𝔬} {⋆̇ : ⋆ → Ø 𝔭} {f₁ f₂ : (𝓞 : ⋆) → ⋆̇ 𝓞} (G : ∀ {𝓞 : ⋆} → ⋆̇ 𝓞 → ⋆̇ 𝓞) → f₁ ∼̇ f₂ → G ∘ f₁ ∼̇ G ∘ f₂

  open 𝓒̇ongruity ⦃ … ⦄ public
