{-# OPTIONS --show-implicit #-}
{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}
module Oscar.Class where

open import Oscar.Prelude
open import Oscar.Data using (_≡_; Proposequality; ∅)
open import Oscar.Class.Reflexivity public
open import Oscar.Class.Transitivity public
open import Oscar.Class.Congruity public
open import Oscar.Class.Symmetrical public
open import Oscar.Class.Symmetry public
open import Oscar.Class.IsEquivalence public
open import Oscar.Class.Setoid public
open import Oscar.Class.Transextensionality public
open import Oscar.Class.Transassociativity public
-- FIXME this won't work due to cyclic dependency: open import Oscar.Class.Surjection

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  where
  record IsPrecategory : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where
    constructor ∁
    field
      overlap ⦃ `𝓣ransitivity ⦄ : 𝓣ransitivity _∼_
      overlap ⦃ `[𝓣ransextensionality] ⦄ : [𝓣ransextensionality] _∼_ _∼̇_
      overlap ⦃ `[𝓣ransassociativity] ⦄ : [𝓣ransassociativity] _∼_ _∼̇_
      ⦃ `𝓣ransextensionality ⦄ : 𝓣ransextensionality _∼_ _∼̇_
      ⦃ `𝓣ransassociativity ⦄ : 𝓣ransassociativity _∼_ _∼̇_

record Precategory 𝔬 𝔯 ℓ : Ø ↑̂ (𝔬 ∙̂ 𝔯 ∙̂ ℓ) where
  constructor ∁
  infix 4 _∼̇_
  field
    {𝔒} : Ø 𝔬
    _∼_ : 𝔒 → 𝔒 → Ø 𝔯
    _∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ
    ⦃ `IsPrecategory ⦄ : IsPrecategory _∼_ _∼̇_

module _ where

  module _
    {𝔬₁} (𝔒₁ : Ø 𝔬₁)
    {𝔬₂} (𝔒₂ : Ø 𝔬₂)
    where
    module _
      where
      𝓼urjection = 𝔒₁ → 𝔒₂
      record 𝓢urjection : Ø 𝔬₁ ∙̂ 𝔬₂ where
        constructor ∁
        field surjection : 𝓼urjection
  open 𝓢urjection ⦃ … ⦄ public

  surjection[_] : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} (𝔒₂ : Ø 𝔬₂)
    ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
    → 𝓼urjection 𝔒₁ 𝔒₂
  surjection[ _ ] = surjection

module _ where

  module _
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {𝔬₂} (𝔒₂ : 𝔒₁ → Ø 𝔬₂)
    where
    module _
      where
      𝓼urjectextensivity = ∀ {x y} → x ∼₁ y → 𝔒₂ x → 𝔒₂ y
      record 𝓢urjectextensivity : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ 𝔬₂ where
        field
          surjectextensivity : 𝓼urjectextensivity
        infixr 10 surjectextensivity
        syntax surjectextensivity σ τ = σ ◃ τ
        surjectextensivity!syntax = surjectextensivity
        infixl 10 surjectextensivity!syntax
        syntax surjectextensivity!syntax rxy px = px ● rxy

  open 𝓢urjectextensivity ⦃ … ⦄ public

  surjectextensivity[]syntax : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
    {𝔬₂} (𝔒₂ : 𝔒₁ → Ø 𝔬₂)
    ⦃ _ : 𝓢urjectextensivity _∼₁_ 𝔒₂ ⦄
    → 𝓼urjectextensivity _∼₁_ 𝔒₂
  surjectextensivity[]syntax _ = surjectextensivity

  syntax surjectextensivity[]syntax 𝔒₂ x∼y fx = x∼y ◃[ 𝔒₂ ] fx

  module _
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    where
    record [𝓢urjectivity] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
      where
      𝓼urjectivity = ∀ {x y} → x ∼₁ y → surjection x ∼₂ surjection y
      record 𝓢urjectivity ⦃ _ : [𝓢urjectivity] ⦄ : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ where
        field
          surjectivity : 𝓼urjectivity

  private

    module projection where
      open 𝓢urjectivity ⦃ … ⦄ public

      surjectivity[_] : ∀
        {𝔬₁} {𝔒₁ : Ø 𝔬₁}
        {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
        {𝔬₂} {𝔒₂ : Ø 𝔬₂}
        {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
        ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
        ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
        ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
        → 𝓼urjectivity _∼₁_ _∼₂_
      surjectivity[ _ ] = surjectivity

      surjectivity⟦_/_⟧ : ∀
        {𝔬₁} {𝔒₁ : Ø 𝔬₁}
        {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
        {𝔬₂} {𝔒₂ : Ø 𝔬₂}
        {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
        (surjection : 𝔒₁ → 𝔒₂)
        (let instance _ : 𝓢urjection 𝔒₁ 𝔒₂
                      _ = ∁ surjection)
        ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
        ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
        → 𝓼urjectivity _∼₁_ _∼₂_
      surjectivity⟦_/_⟧ {𝔒₁ = 𝔒₁} {𝔒₂ = 𝔒₂} _ surjection =
        let instance _ : 𝓢urjection 𝔒₁ 𝔒₂
                     _ = ∁ surjection
        in surjectivity

      open import Oscar.Data

      ≡-surjectivity⟦_⟧ : ∀
        {𝔬₁} {𝔒₁ : Ø 𝔬₁}
        {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
        {𝔬₂} {𝔒₂ : Ø 𝔬₂}
        (surjection : 𝔒₁ → 𝔒₂)
        (let instance _ : 𝓢urjection 𝔒₁ 𝔒₂
                      _ = ∁ surjection)
        ⦃ _ : [𝓢urjectivity] _∼₁_ Proposequality⟦ 𝔒₂ ⟧ ⦄
        ⦃ _ : 𝓢urjectivity _∼₁_ _≡_ ⦄
        → 𝓼urjectivity _∼₁_ _≡_
      ≡-surjectivity⟦_⟧ {𝔒₁ = 𝔒₁} {𝔒₂ = 𝔒₂} surjection =
        let instance _ : 𝓢urjection 𝔒₁ 𝔒₂
                     _ = ∁ surjection
        in surjectivity

  module _ where
    open projection public

  module _ where
    open projection public using () renaming (surjectivity to §; surjectivity[_] to §[_])
    -- TODO rename § to ⟦_⟧?

  module _ where -- TODO move to another file

    open import Oscar.Data

    instance

      toSurj' : ∀
        {𝔬₁} {𝔒₁ : Ø 𝔬₁}
        {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
        {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
        ⦃ _ : [𝓢urjectivity] _∼₁_ (Extension 𝔒₂) ⦄
        ⦃ _ : 𝓢urjectivity _∼₁_ (Extension 𝔒₂) ⦃ record { surjection = ¡ } ⦄ ⦄
        → 𝓢urjectextensivity _∼₁_ 𝔒₂
      toSurj' {{_}} {{x₂}} .𝓢urjectextensivity.surjectextensivity = § {{r = x₂}}

module _ where

  module _
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂) (let infix 4 _∼̇₂_ ; _∼̇₂_ = _∼̇₂_)
    where
    record [𝓢urjtranscommutativity] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
      ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
      ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
      ⦃ _ : 𝓣ransitivity _∼₁_ ⦄
      ⦃ _ : 𝓣ransitivity _∼₂_ ⦄
      where
      𝓼urjtranscommutativity = ∀ {x y z} (f : x ∼₁ y) (g : y ∼₁ z) → surjectivity (g ∙ f) ∼̇₂ surjectivity g ∙ surjectivity f
      record 𝓢urjtranscommutativity ⦃ _ : [𝓢urjtranscommutativity] ⦄ : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂ where
        field
          surjtranscommutativity : 𝓼urjtranscommutativity
        syntax surjtranscommutativity f g = g ⟪∙⟫ f

  private

    module projection where

      open 𝓢urjtranscommutativity ⦃ … ⦄ public

      surjtranscommutativity[_] : ∀
        {𝔬₁} {𝔒₁ : Ø 𝔬₁}
        {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
        {𝔬₂} {𝔒₂ : Ø 𝔬₂}
        {𝔯₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
        {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
        ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
        ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
        ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
        ⦃ _ : 𝓣ransitivity _∼₁_ ⦄
        ⦃ _ : 𝓣ransitivity _∼₂_ ⦄
        ⦃ _ : [𝓢urjtranscommutativity] _∼₁_ _∼₂_ _∼̇₂_ ⦄
        ⦃ _ : 𝓢urjtranscommutativity _∼₁_ _∼₂_ _∼̇₂_ ⦄
        → 𝓼urjtranscommutativity _∼₁_ _∼₂_ _∼̇₂_
      surjtranscommutativity[ _ ] = surjtranscommutativity

      ⟪∙⟫-surjtranscommutativity[]-syntax = surjtranscommutativity[_]
      syntax ⟪∙⟫-surjtranscommutativity[]-syntax t f g = g ⟪∙⟫[ t ] f

  open projection public



module _ where

  module _
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {ℓ₁} (_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁)
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    where
    record [𝓢urjextensionality] : Ø 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
      ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
      ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
      where
      𝓼urjextensionality = ∀ {x y} {f₁ f₂ : x ∼₁ y} → f₁ ∼̇₁ f₂ → surjectivity f₁ ∼̇₂ surjectivity f₂
      record 𝓢urjextensionality ⦃ _ : [𝓢urjextensionality] ⦄ : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ ℓ₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂ where field surjextensionality : 𝓼urjextensionality

  private

    module projection where

      open 𝓢urjextensionality ⦃ … ⦄ public

      surjextensionality[_] : ∀
        {𝔬₁} {𝔒₁ : Ø 𝔬₁}
        {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
        {ℓ₁} {_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁}
        {𝔬₂} {𝔒₂ : Ø 𝔬₂}
        {𝔯₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
        {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
        ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
        ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
        ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
        ⦃ _ : [𝓢urjextensionality] _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_ ⦄
        ⦃ _ : 𝓢urjextensionality _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_ ⦄
        → 𝓼urjextensionality _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_
      surjextensionality[ _ ] = surjextensionality

  open projection public

  module _ where
    open projection public using () renaming (surjextensionality to ⟪_⟫)
    ⟪⟫-surjextensionality[]-syntax = surjextensionality[_]
    syntax ⟪⟫-surjextensionality[]-syntax t x = ⟪ x ⟫[ t ]

module _ where

  module _
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {ℓ₁} (_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁)
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    where
    record IsPrefunctor : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ ℓ₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂ where
      constructor ∁
      field
        overlap ⦃ `IsPrecategory₁ ⦄ : IsPrecategory _∼₁_ _∼̇₁_
        overlap ⦃ `IsPrecategory₂ ⦄ : IsPrecategory _∼₂_ _∼̇₂_
        overlap ⦃ `𝓢urjection ⦄ : 𝓢urjection 𝔒₁ 𝔒₂
        overlap ⦃ `[𝓢urjectivity] ⦄ : [𝓢urjectivity] _∼₁_ _∼₂_
        overlap ⦃ `[𝓢urjtranscommutativity] ⦄ : [𝓢urjtranscommutativity] _∼₁_ _∼₂_ _∼̇₂_
        overlap ⦃ `[𝓢urjextensionality] ⦄ : [𝓢urjextensionality] _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_
        overlap ⦃ `𝓢urjectivity ⦄ : 𝓢urjectivity _∼₁_ _∼₂_
        overlap ⦃ `𝓢urjtranscommutativity ⦄ : 𝓢urjtranscommutativity _∼₁_ _∼₂_ _∼̇₂_
        ⦃ `𝓢urjextensionality ⦄ : 𝓢urjextensionality _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_

record Prefunctor 𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂ : Ø ↑̂ (𝔬₁ ∙̂ 𝔯₁ ∙̂ ℓ₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂) where
  constructor ∁
  field
    {𝔒₁} : Ø 𝔬₁
    _∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁
    _∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁
    {𝔒₂} : Ø 𝔬₂
    _∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂
    _∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂
    ⦃ `IsPrefunctor ⦄ : IsPrefunctor _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_

module _ where

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
    where
    record [𝓣ransleftidentity] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓡eflexivity _∼_ ⦄
      ⦃ _ : 𝓣ransitivity _∼_ ⦄
      where
      𝓽ransleftidentity = ∀ {x y} {f : x ∼ y} → ε ∙ f ∼̇ f
      record 𝓣ransleftidentity ⦃ _ : [𝓣ransleftidentity] ⦄ : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where field transleftidentity : 𝓽ransleftidentity
  open 𝓣ransleftidentity ⦃ … ⦄ public

  transleftidentity[_] : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
    {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ)
    ⦃ _ : 𝓡eflexivity _∼_ ⦄
    ⦃ _ : 𝓣ransitivity _∼_ ⦄
    ⦃ _ : [𝓣ransleftidentity] _∼_ _∼̇_ ⦄
    ⦃ _ : 𝓣ransleftidentity _∼_ _∼̇_ ⦄
    → 𝓽ransleftidentity _∼_ _∼̇_
  transleftidentity[ _ ] = transleftidentity

module _ where

  open import Oscar.Data

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔣} (F : 𝔒 → Ø 𝔣)
    {𝔱} (T : {x : 𝔒} → F x → 𝔒 → Ø 𝔱)
    (let _∼_ : ∀ x y → Ø 𝔣 ∙̂ 𝔱
         _∼_ = λ x y → (f : F x) → T f y)
    where
    record [≡̇-𝓣ransleftidentity] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓡eflexivity _∼_ ⦄
      ⦃ _ : 𝓣ransitivity _∼_ ⦄
      where
      ≡̇-𝓽ransleftidentity = ∀ {x y} {f : x ∼ y} → ε ∙ f ≡̇ f
      record ≡̇-𝓣ransleftidentity ⦃ _ : [≡̇-𝓣ransleftidentity] ⦄ : Ø 𝔬 ∙̂ 𝔣 ∙̂ 𝔱 where field ≡̇-transleftidentity : ≡̇-𝓽ransleftidentity
  open ≡̇-𝓣ransleftidentity ⦃ … ⦄ public

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔣} {F : 𝔒 → Ø 𝔣}
    {𝔱} {T : {x : 𝔒} → F x → 𝔒 → Ø 𝔱}
    (let _∼_ : ∀ x y → Ø 𝔣 ∙̂ 𝔱
         _∼_ = λ x y → (f : F x) → T f y)
    where
    instance
      `[≡̇-𝓣ransleftidentity] :
        ⦃ _ : [𝓣ransleftidentity] _∼_ _≡̇_ ⦄
        → [≡̇-𝓣ransleftidentity] F T
      `[≡̇-𝓣ransleftidentity] = ∁

      `≡̇-𝓣ransleftidentity :
        ⦃ _ : [𝓣ransleftidentity] _∼_ _≡̇_ ⦄
        ⦃ _ : 𝓡eflexivity _∼_ ⦄
        ⦃ _ : 𝓣ransitivity _∼_ ⦄
        ⦃ _ : 𝓣ransleftidentity _∼_ _≡̇_ ⦄
        → ≡̇-𝓣ransleftidentity F T
      `≡̇-𝓣ransleftidentity .≡̇-𝓣ransleftidentity.≡̇-transleftidentity = transleftidentity

module _ where

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
    where
    record [𝓣ransrightidentity] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓡eflexivity _∼_ ⦄
      ⦃ _ : 𝓣ransitivity _∼_ ⦄
      where
      𝓽ransrightidentity = ∀ {x y} {f : x ∼ y} → f ∙ ε ∼̇ f
      record 𝓣ransrightidentity ⦃ _ : [𝓣ransrightidentity] ⦄ : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where field transrightidentity : 𝓽ransrightidentity
  open 𝓣ransrightidentity ⦃ … ⦄ public

  transrightidentity[_] : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
    {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ)
    ⦃ _ : 𝓡eflexivity _∼_ ⦄
    ⦃ _ : 𝓣ransitivity _∼_ ⦄
    ⦃ _ : [𝓣ransrightidentity] _∼_ _∼̇_ ⦄
    ⦃ _ : 𝓣ransrightidentity _∼_ _∼̇_ ⦄
    → 𝓽ransrightidentity _∼_ _∼̇_
  transrightidentity[ _ ] = transrightidentity

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  where
  record IsCategory : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where
    constructor ∁
    field
      ⦃ `IsPrecategory ⦄ : IsPrecategory _∼_ _∼̇_
      overlap ⦃ `[𝓣ransleftidentity] ⦄ : [𝓣ransleftidentity] _∼_ _∼̇_
      overlap ⦃ `[𝓣ransrightidentity] ⦄ : [𝓣ransrightidentity] _∼_ _∼̇_
      overlap ⦃ `𝓡eflexivity ⦄ : 𝓡eflexivity _∼_
      ⦃ `𝓣ransleftidentity ⦄ : 𝓣ransleftidentity _∼_ _∼̇_
      ⦃ `𝓣ransrightidentity ⦄ : 𝓣ransrightidentity _∼_ _∼̇_

record Category 𝔬 𝔯 ℓ : Ø ↑̂ (𝔬 ∙̂ 𝔯 ∙̂ ℓ) where
  constructor ∁
  infix 4 _∼̇_
  field
    {𝔒} : Ø 𝔬
    _∼_ : 𝔒 → 𝔒 → Ø 𝔯
    _∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ
    ⦃ `IsCategory ⦄ : IsCategory _∼_ _∼̇_

module _ where

  module _
    {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂ ℓ₂}
    {𝔒₁ : Ø 𝔬₁}
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {𝔒₂ : Ø 𝔬₂}
    (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
    ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
    ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₁_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₂_ ⦄
    where
    [𝓈urjidentity] = λ x → surjectivity (ε[ _∼₁_ ] {x}) ∼̇₂ ε

  record [𝒮urjidentity]
    {𝔬₁} {𝔒₁ : Ø 𝔬₁} {ℓ₂} (𝔓 : 𝔒₁ → Ø ℓ₂)
    𝔯₁ 𝔬₂ 𝔯₂
    : Ø 𝔬₁ ∙̂ ↑̂ (𝔯₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂) where
    constructor ∁
    field
      _∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁
      {𝔒₂} : Ø 𝔬₂
      _∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂
      _∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂
      ⦃ `𝓢urjection     ⦄ : 𝓢urjection 𝔒₁ 𝔒₂
      ⦃ `[𝓢urjectivity] ⦄ : [𝓢urjectivity] _∼₁_ _∼₂_
      ⦃ `𝓢urjectivity   ⦄ : 𝓢urjectivity _∼₁_ _∼₂_
      ⦃ `𝓡eflexivity₁   ⦄ : 𝓡eflexivity _∼₁_
      ⦃ `𝓡eflexivity₂   ⦄ : 𝓡eflexivity _∼₂_
      ⦃ `Proposequality[𝓈urjidentity] ⦄ : [𝓈urjidentity] _∼₁_ _∼₂_ _∼̇₂_ ≡ 𝔓

  [𝓢urjidentity] : ∀
    {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂ ℓ₂}
    {𝔒₁ : Ø 𝔬₁}
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {𝔒₂ : Ø 𝔬₂}
    (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
    ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
    ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₁_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₂_ ⦄
    𝔯₁ 𝔬₂ 𝔯₂
    → Ø 𝔬₁ ∙̂ ↑̂ (𝔯₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂)
  [𝓢urjidentity] _∼₁_ _∼₂_ _∼̇₂_ = [𝒮urjidentity] ([𝓈urjidentity] _∼₁_ _∼₂_ _∼̇₂_)

  module _
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {ℓ₂}
    where
    module _
      (𝔓 : 𝔒₁ → Ø ℓ₂)
      where
      𝓈urjidentity = ∀ {x} → 𝔓 x

  module _
    {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂ ℓ₂}
    {𝔒₁ : Ø 𝔬₁}
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {𝔒₂ : Ø 𝔬₂}
    (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
    ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
    ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₁_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₂_ ⦄
    where
    𝓼urjidentity = 𝓈urjidentity ([𝓈urjidentity] _∼₁_ _∼₂_ _∼̇₂_)

  record 𝒮urjidentity
    {𝔬₁} {𝔒₁ : Ø 𝔬₁} {ℓ₂}
      (𝔓 : 𝔒₁ → Ø ℓ₂)
    {𝔯₁ 𝔬₂ 𝔯₂}
      ⦃ _ : [𝒮urjidentity] 𝔓 𝔯₁ 𝔬₂ 𝔯₂ ⦄
    : Ø 𝔬₁ ∙̂ ℓ₂ where
    field
      surjidentity : 𝓈urjidentity 𝔓
  open 𝒮urjidentity ⦃ … ⦄ public

  𝓢urjidentity : ∀
    {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂ ℓ₂}
    {𝔒₁ : Ø 𝔬₁}
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {𝔒₂ : Ø 𝔬₂}
    (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
    ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
    ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₁_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₂_ ⦄
    ⦃ _ : [𝓢urjidentity] _∼₁_ _∼₂_ _∼̇₂_ 𝔯₁ 𝔬₂ 𝔯₂ ⦄
    → Ø 𝔬₁ ∙̂ ℓ₂
  𝓢urjidentity _∼₁_ _∼₂_ _∼̇₂_ = 𝒮urjidentity ([𝓈urjidentity] _∼₁_ _∼₂_ _∼̇₂_)

  surjidentity[_,_] : ∀
    {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂ ℓ₂}
    {𝔒₁ : Ø 𝔬₁}
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {𝔒₂ : Ø 𝔬₂}
    {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
    (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
    ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
    ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₁_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₂_ ⦄
    ⦃ _ : [𝓢urjidentity] _∼₁_ _∼₂_ _∼̇₂_ 𝔯₁ 𝔬₂ 𝔯₂ ⦄
    ⦃ _ : 𝓢urjidentity _∼₁_ _∼₂_ _∼̇₂_ ⦄
    → 𝓼urjidentity _∼₁_ _∼₂_ _∼̇₂_
  surjidentity[ _ , _ ] = surjidentity

module _ where

  module _
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {ℓ₁} (_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁)
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    where
    record IsFunctor : Ø 𝔬₁ ∙̂ ↑̂ 𝔯₁ ∙̂ ℓ₁ ∙̂ ↑̂ (𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂) where
      constructor ∁
      field
        ⦃ `IsPrefunctor ⦄ : IsPrefunctor _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_
        overlap ⦃ `IsCategory₁ ⦄ : IsCategory _∼₁_ _∼̇₁_
        overlap ⦃ `IsCategory₂ ⦄ : IsCategory _∼₂_ _∼̇₂_
        overlap ⦃ `[𝒮urjidentity] ⦄ : [𝓢urjidentity] _∼₁_ _∼₂_ _∼̇₂_ 𝔯₁ 𝔬₂ 𝔯₂
        overlap ⦃ `𝒮urjidentity ⦄ : 𝓢urjidentity _∼₁_ _∼₂_ _∼̇₂_

record Functor 𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂ : Ø ↑̂ (𝔬₁ ∙̂ 𝔯₁ ∙̂ ℓ₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂) where
  constructor ∁
  field
    {𝔒₁} : Ø 𝔬₁
    _∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁
    _∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁
    {𝔒₂} : Ø 𝔬₂
    _∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂
    _∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂
    ⦃ `IsFunctor ⦄ : IsFunctor _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_
  open IsFunctor `IsFunctor public

module _ where

  module _ -- Arity=1
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} (𝔒₂ : 𝔒₁ → Ø 𝔬₂)
    where
    𝓲njection₁ = (x : 𝔒₁) → 𝔒₂ x
    record 𝓘njection₁ : Ø 𝔬₁ ∙̂ 𝔬₂ where field injection₁ : 𝓲njection₁
    open 𝓘njection₁ ⦃ … ⦄ public
    module _
      {ℓ₂} (_∼₂_ : ∀ {x₁ x₂} → 𝔒₂ x₁ → 𝔒₂ x₂ → Ø ℓ₂)
      {ℓ₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁)
      where
      record [𝓘njectivity₁] : Ø₀ where
        no-eta-equality
        constructor ∁
      module _
        ⦃ _ : 𝓘njection₁ ⦄
        where
        𝓲njectivity₁ = ∀ {x₁ x₂} → injection₁ x₁ ∼₂ injection₁ x₂ → x₁ ∼₁ x₂
        record 𝓘njectivity₁ ⦃ _ : [𝓘njectivity₁] ⦄ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ ℓ₁ ∙̂ ℓ₂ where field injectivity₁ : 𝓲njectivity₁
        open 𝓘njectivity₁ ⦃ … ⦄ public

  injectivity₁[_] : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    {ℓ₂} {_∼₂_ : ∀ {x₁ x₂} → 𝔒₂ x₁ → 𝔒₂ x₂ → Ø ℓ₂}
    {ℓ₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁)
    ⦃ _ : 𝓘njection₁ (λ (x : 𝔒₁) → 𝔒₂ x) ⦄
    ⦃ _ : [𝓘njectivity₁] (λ (x : 𝔒₁) → 𝔒₂ x) _∼₂_ _∼₁_ ⦄
    ⦃ _ : 𝓘njectivity₁ (λ (x : 𝔒₁) → 𝔒₂ x) _∼₂_ _∼₁_ ⦄
    → 𝓲njectivity₁ (λ (x : 𝔒₁) → 𝔒₂ x) _∼₂_ _∼₁_
  injectivity₁[ _ ] = injectivity₁

  module _ -- Arity=2
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    {𝔬₃} (𝔒₃ : ∀ x₁ → 𝔒₂ x₁ → Ø 𝔬₃)
    where
    𝓲njection₂ = ∀ x₁ → (x₂ : 𝔒₂ x₁) → 𝔒₃ _ x₂
    record 𝓘njection₂ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ where
      constructor ∁
      field injection₂ : 𝓲njection₂
    open 𝓘njection₂ ⦃ … ⦄ public
    module _ -- Fixed=0
      {ℓ₃} (_∼₃_ : ∀ {x₁ x₂} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} → 𝔒₃ _ y₁ → 𝔒₃ _ y₂ → Ø ℓ₃)
      where
      module _ -- Var=1
        {ℓ₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁)
        where
        record [𝓘njectivity₂,₀,₁] : Ø₀ where
          no-eta-equality
          constructor ∁
        module _
          ⦃ _ : 𝓘njection₂ ⦄
          where
          𝓲njectivity₂,₀,₁ = ∀ {x₁ x₂} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} → injection₂ _ y₁ ∼₃ injection₂ _ y₂ → x₁ ∼₁ x₂
          record 𝓘njectivity₂,₀,₁ ⦃ _ : [𝓘njectivity₂,₀,₁] ⦄ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ ℓ₁ ∙̂ ℓ₃ where field injectivity₂,₀,₁ : 𝓲njectivity₂,₀,₁
          open 𝓘njectivity₂,₀,₁ ⦃ … ⦄ public
      module _ -- Var=2
        {ℓ₂} (_∼₂_ : ∀ {x₁ x₂} → 𝔒₂ x₁ → 𝔒₂ x₂ → Ø ℓ₂)
        where
        record [𝓘njectivity₂,₀,₂] : Ø₀ where
          no-eta-equality
          constructor ∁
        module _
          ⦃ _ : 𝓘njection₂ ⦄
          where
          𝓲njectivity₂,₀,₂ = ∀ {x₁ x₂ : 𝔒₁} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} → injection₂ _ y₁ ∼₃ injection₂ _ y₂ → y₁ ∼₂ y₂
          record 𝓘njectivity₂,₀,₂ ⦃ _ : [𝓘njectivity₂,₀,₂] ⦄ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ ℓ₂ ∙̂ ℓ₃ where field injectivity₂,₀,₂ : 𝓲njectivity₂,₀,₂
          open 𝓘njectivity₂,₀,₂ ⦃ … ⦄ public
    module _ -- Fixed=1
      {ℓ₃} (_∼₃_ : ∀ {x} {y₁ y₂ : 𝔒₂ x} → 𝔒₃ _ y₁ → 𝔒₃ _ y₂ → Ø ℓ₃)
      {ℓ₂} (_∼₂_ : ∀ {x} → 𝔒₂ x → 𝔒₂ x → Ø ℓ₂)
      where
      record [𝓘njectivity₂,₁] : Ø₀ where
        no-eta-equality
        constructor ∁
      module _
        ⦃ _ : 𝓘njection₂ ⦄
        where
        𝓲njectivity₂,₁ = ∀ (x : 𝔒₁) {y₁ y₂ : 𝔒₂ x} → injection₂ _ y₁ ∼₃ injection₂ _ y₂ → y₁ ∼₂ y₂
        record 𝓘njectivity₂,₁ ⦃ _ : [𝓘njectivity₂,₁] ⦄ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ ℓ₂ ∙̂ ℓ₃ where field injectivity₂,₁ : 𝓲njectivity₂,₁
        open 𝓘njectivity₂,₁ ⦃ … ⦄ public

  injectivity₂,₀,₁[_] : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    {𝔬₃} {𝔒₃ : ∀ x₁ → 𝔒₂ x₁ → Ø 𝔬₃}
    {ℓ₃} {_∼₃_ : ∀ {x₁ x₂} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} → 𝔒₃ _ y₁ → 𝔒₃ _ y₂ → Ø ℓ₃}
    {ℓ₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁)
    ⦃ _ : 𝓘njection₂ 𝔒₃ ⦄
    ⦃ _ : [𝓘njectivity₂,₀,₁] 𝔒₃ _∼₃_ _∼₁_ ⦄
    ⦃ _ : 𝓘njectivity₂,₀,₁ 𝔒₃ _∼₃_ _∼₁_ ⦄
    → 𝓲njectivity₂,₀,₁ 𝔒₃ _∼₃_ _∼₁_
  injectivity₂,₀,₁[ _ ] = injectivity₂,₀,₁

  injectivity₂,₀,₂[_] : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    {𝔬₃} {𝔒₃ : ∀ x₁ → 𝔒₂ x₁ → Ø 𝔬₃}
    {ℓ₃} {_∼₃_ : ∀ {x₁ x₂} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} → 𝔒₃ _ y₁ → 𝔒₃ _ y₂ → Ø ℓ₃}
    {ℓ₂} (_∼₂_ : ∀ {x₁ x₂} → 𝔒₂ x₁ → 𝔒₂ x₂ → Ø ℓ₂)
    ⦃ _ : 𝓘njection₂ 𝔒₃ ⦄
    ⦃ _ : [𝓘njectivity₂,₀,₂] 𝔒₃ _∼₃_ _∼₂_ ⦄
    ⦃ _ : 𝓘njectivity₂,₀,₂ 𝔒₃ _∼₃_ _∼₂_ ⦄
    → 𝓲njectivity₂,₀,₂ 𝔒₃ _∼₃_ _∼₂_
  injectivity₂,₀,₂[ _ ] = injectivity₂,₀,₂

  injectivity₂,₁[_] : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    {𝔬₃} {𝔒₃ : ∀ x₁ → 𝔒₂ x₁ → Ø 𝔬₃}
    {ℓ₃} {_∼₃_ : ∀ {x} {y₁ y₂ : 𝔒₂ x} → 𝔒₃ _ y₁ → 𝔒₃ _ y₂ → Ø ℓ₃}
    {ℓ₂} (_∼₂_ : ∀ {x} → 𝔒₂ x → 𝔒₂ x → Ø ℓ₂)
    ⦃ _ : [𝓘njectivity₂,₁] 𝔒₃ _∼₃_ _∼₂_ ⦄
    ⦃ _ : 𝓘njection₂ 𝔒₃ ⦄
    ⦃ _ : 𝓘njectivity₂,₁ 𝔒₃ _∼₃_ _∼₂_ ⦄
    → 𝓲njectivity₂,₁ 𝔒₃ _∼₃_ _∼₂_
  injectivity₂,₁[ _ ] = injectivity₂,₁

  module _ -- Arity=3
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    {𝔬₃} {𝔒₃ : ∀ x₁ → 𝔒₂ x₁ → Ø 𝔬₃}
    {𝔬₄} (𝔒₄ : ∀ x₁ → (x₂ : 𝔒₂ x₁) → 𝔒₃ _ x₂ → Ø 𝔬₄)
    where
    𝓲njection₃ = ∀ x₁ → (x₂ : 𝔒₂ x₁) → (x₃ : 𝔒₃ _ x₂) → 𝔒₄ _ _ x₃
    record 𝓘njection₃ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ where
      constructor ∁
      field injection₃ : 𝓲njection₃
    open 𝓘njection₃ ⦃ … ⦄ public
    module _ -- Fixed=0
      {ℓ₄} (_∼₄_ : ∀ {x₁ x₂} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} {z₁ : 𝔒₃ _ y₁} {z₂ : 𝔒₃ _ y₂} → 𝔒₄ _ _ z₁ → 𝔒₄ _ _ z₂ → Ø ℓ₄)
      where
      module _ -- Var=1
        {ℓ₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁)
        where
        record [𝓘njectivity₃,₀,₁] : Ø₀ where
          no-eta-equality
          constructor ∁
        module _
          ⦃ _ : 𝓘njection₃ ⦄
          where
          𝓲njectivity₃,₀,₁ = ∀ {x₁ x₂} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} {z₁ : 𝔒₃ _ y₁} {z₂ : 𝔒₃ _ y₂} → injection₃ _ _ z₁ ∼₄ injection₃ _ _ z₂ → x₁ ∼₁ x₂
          record 𝓘njectivity₃,₀,₁ ⦃ _ : [𝓘njectivity₃,₀,₁] ⦄ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ ℓ₁ ∙̂ ℓ₄ where field injectivity₃,₀,₁ : 𝓲njectivity₃,₀,₁
          open 𝓘njectivity₃,₀,₁ ⦃ … ⦄ public
      module _ -- Var=2
        {ℓ₂} (_∼₂_ : ∀ {x₁ x₂} → 𝔒₂ x₁ → 𝔒₂ x₂ → Ø ℓ₂)
        where
        record [𝓘njectivity₃,₀,₂] : Ø₀ where
          no-eta-equality
          constructor ∁
        module _
          ⦃ _ : 𝓘njection₃ ⦄
          where
          𝓲njectivity₃,₀,₂ = ∀ {x₁ x₂ : 𝔒₁} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} {z₁ : 𝔒₃ _ y₁} {z₂ : 𝔒₃ _ y₂} → injection₃ _ _ z₁ ∼₄ injection₃ _ _ z₂ → y₁ ∼₂ y₂
          record 𝓘njectivity₃,₀,₂ ⦃ _ : [𝓘njectivity₃,₀,₂] ⦄ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ ℓ₂ ∙̂ ℓ₄ where field injectivity₃,₀,₂ : 𝓲njectivity₃,₀,₂
          open 𝓘njectivity₃,₀,₂ ⦃ … ⦄ public

  injectivity₃,₀,₁[_] : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    {𝔬₃} {𝔒₃ : ∀ x₁ → 𝔒₂ x₁ → Ø 𝔬₃}
    {𝔬₄} {𝔒₄ : ∀ x₁ → (x₂ : 𝔒₂ x₁) → 𝔒₃ _ x₂ → Ø 𝔬₄}
    {ℓ₄} {_∼₄_ : ∀ {x₁ x₂} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} {z₁ : 𝔒₃ _ y₁} {z₂ : 𝔒₃ _ y₂} → 𝔒₄ _ _ z₁ → 𝔒₄ _ _ z₂ → Ø ℓ₄}
    {ℓ₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁)
    ⦃ _ : [𝓘njectivity₃,₀,₁] 𝔒₄ _∼₄_ _∼₁_ ⦄
    ⦃ _ : 𝓘njection₃ 𝔒₄ ⦄
    ⦃ _ : 𝓘njectivity₃,₀,₁ 𝔒₄ _∼₄_ _∼₁_ ⦄
    → 𝓲njectivity₃,₀,₁ 𝔒₄ _∼₄_ _∼₁_
  injectivity₃,₀,₁[ _ ] = injectivity₃,₀,₁

  injectivity₃,₀,₂[_] : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    {𝔬₃} {𝔒₃ : ∀ x₁ → 𝔒₂ x₁ → Ø 𝔬₃}
    {𝔬₄} {𝔒₄ : ∀ x₁ → (x₂ : 𝔒₂ x₁) → 𝔒₃ _ x₂ → Ø 𝔬₄}
    {ℓ₄} {_∼₄_ : ∀ {x₁ x₂} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} {z₁ : 𝔒₃ _ y₁} {z₂ : 𝔒₃ _ y₂} → 𝔒₄ _ _ z₁ → 𝔒₄ _ _ z₂ → Ø ℓ₄}
    {ℓ₂} (_∼₂_ : ∀ {x₁ x₂} → 𝔒₂ x₁ → 𝔒₂ x₂ → Ø ℓ₂)
    ⦃ _ : [𝓘njectivity₃,₀,₂] 𝔒₄ _∼₄_ _∼₂_ ⦄
    ⦃ _ : 𝓘njection₃ 𝔒₄ ⦄
    ⦃ _ : 𝓘njectivity₃,₀,₂ 𝔒₄ _∼₄_ _∼₂_ ⦄
    → 𝓲njectivity₃,₀,₂ 𝔒₄ _∼₄_ _∼₂_
  injectivity₃,₀,₂[ _ ] = injectivity₃,₀,₂

module _ where

  module _
    {𝔬} (𝔒 : Ø 𝔬)
    where
    𝓼uccessor₀ = 𝔒 → 𝔒
    record 𝓢uccessor₀ : Ø 𝔬 where
      field
        successor₀ : 𝓼uccessor₀

      instance

        `𝓘njection₁ : 𝓘njection₁ (λ (_ : 𝔒) → 𝔒)
        `𝓘njection₁ .𝓘njection₁.injection₁ = successor₀

  open 𝓢uccessor₀ ⦃ … ⦄ public using (successor₀)
  open 𝓢uccessor₀ ⦃ … ⦄ public using () renaming (successor₀ to ⇑₀)

  module _
    {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
    where
    record [𝓢uccessor₁] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓢uccessor₀ 𝔒 ⦄
      where
      𝓼uccessor₁ = ∀ {m} → 𝔓 m → 𝔓 (⇑₀ m)
      record 𝓢uccessor₁ ⦃ _ : [𝓢uccessor₁] ⦄ : Ø 𝔬 ∙̂ 𝔭 where
        field
          successor₁ : 𝓼uccessor₁

        instance

          `𝓘njection₁ : ∀ {m} → 𝓘njection₁ (λ (_ : 𝔓 m) → 𝔓 (⇑₀ m))
          `𝓘njection₁ {m} .𝓘njection₁.injection₁ = successor₁

          `𝓘njection₂ : 𝓘njection₂ (λ (m : 𝔒) (n : 𝔓 m) → 𝔓 (⇑₀ m))
          `𝓘njection₂ .𝓘njection₂.injection₂ = λ _ → successor₁

  open 𝓢uccessor₁ ⦃ … ⦄ public using (successor₁)
  open 𝓢uccessor₁ ⦃ … ⦄ public using () renaming (successor₁ to ⇑₁)

  module _
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {ℓ₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁)
    {ℓ₂} (_∼₂_ : 𝔒₁ → 𝔒₁ → Ø ℓ₂)
    where
    𝓶ap = ∀ {x y} → x ∼₁ y → x ∼₂ y
    record 𝓜ap : Ø 𝔬₁ ∙̂ ℓ₁ ∙̂ ℓ₂ where field map : 𝓶ap
  open 𝓜ap ⦃ … ⦄ public

  module _
    (𝔉 : ∀ {𝔣} → Ø 𝔣 → Ø 𝔣)
    𝔬₁ 𝔬₂
    where
    𝓯map = ∀ {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂} (f : 𝔒₁ → 𝔒₂) → 𝔉 𝔒₁ → 𝔉 𝔒₂
    record 𝓕map : Ø ↑̂ (𝔬₁ ∙̂ 𝔬₂) where field fmap : 𝓯map
  open 𝓕map ⦃ … ⦄ public

  module _
    (𝔉 : ∀ {𝔣} → Ø 𝔣 → Ø 𝔣)
    𝔬₁ 𝔬₂
    where
    𝓪pply = ∀ {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂} → 𝔉 (𝔒₁ → 𝔒₂) → 𝔉 𝔒₁ → 𝔉 𝔒₂
    record 𝓐pply : Ø ↑̂ (𝔬₁ ∙̂ 𝔬₂) where
      infixl 4 apply
      field apply : 𝓪pply
      syntax apply f x = f <*> x
  open 𝓐pply ⦃ … ⦄ public

  _<*>_ = apply

  module _
    {𝔬 𝔣}
    (𝔉 : Ø 𝔬 → Ø 𝔣)
    where
    𝓹ure = ∀ {𝔒 : Ø 𝔬} → 𝔒 → 𝔉 𝔒
    record 𝓟ure : Ø 𝔣 ∙̂ ↑̂ 𝔬 where
      field pure : 𝓹ure
  open 𝓟ure ⦃ … ⦄ public

  module _
    (𝔉 : ∀ {𝔣} → Ø 𝔣 → Ø 𝔣)
    𝔬₁ 𝔬₂
    where
    𝓫ind = ∀ {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂} → 𝔉 𝔒₁ → (𝔒₁ → 𝔉 𝔒₂) → 𝔉 𝔒₂
    record 𝓑ind : Ø ↑̂ (𝔬₁ ∙̂ 𝔬₂) where
      infixl 6 bind
      field bind : 𝓫ind
      syntax bind m f = f =<< m
    open 𝓑ind ⦃ … ⦄ public

  module _
    {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
    where
    record [𝓣hin] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓢uccessor₀ X ⦄
      where
      𝔱hin : ∀ (m : X) → A (⇑₀ m) → B m → Ø b
      𝔱hin m = λ _ _ → B (⇑₀ m)
      𝓽hin = ∀ {m : X} → A (⇑₀ m) → B m → B (⇑₀ m)
      record 𝓣hin ⦃ _ : [𝓣hin] ⦄ : Ø x ∙̂ a ∙̂ b where
        field
          thin : 𝓽hin
        instance `𝓘njection₂ : ∀ {m} → 𝓘njection₂ (𝔱hin m)
        `𝓘njection₂ = ∁ thin
  open 𝓣hin ⦃ … ⦄ public

  module _
    {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
    where
    record [𝓣hick] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓢uccessor₀ X ⦄
      where
      𝓽hick = ∀ {m} → A m → B (⇑₀ m) → B m
      record 𝓣hick ⦃ _ : [𝓣hick] ⦄ : Ø x ∙̂ a ∙̂ b where field thick : 𝓽hick
  open 𝓣hick ⦃ … ⦄ public

  module _
    {x} {X : Ø x}
    {a} (A : X → Ø a)
    {b} (B : X → Ø b)
    {ℓ} (_≈_ : ∀ {x} → B x → B x → Ø ℓ)
    where
    record [𝓣hick/thin=1] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓢uccessor₀ X ⦄
      ⦃ _ : [𝓢uccessor₁] A ⦄
      ⦃ _ : 𝓢uccessor₁ A ⦄
      ⦃ _ : [𝓣hin] A B ⦄
      ⦃ _ : 𝓣hin A B ⦄
      ⦃ _ : [𝓣hick] A B ⦄
      ⦃ _ : 𝓣hick A B ⦄
      where
      𝓽hick/thin=1 = ∀ {m} (x : A m) (y : B m) → thick x (thin (⇑₁ x) y) ≈ y
      record 𝓣hick/thin=1 : Ø x ∙̂ a ∙̂ b ∙̂ ℓ where field thick/thin=1 : 𝓽hick/thin=1
  open 𝓣hick/thin=1 ⦃ … ⦄ public

  module _
    {x} {X : Ø x}
    {a} (A : X → Ø a)
    {b} (B : X → Ø b)
    {c} (C : Ø b → Ø c)
    where
    record [𝓒heck] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓢uccessor₀ X ⦄
      where
      𝓬heck = ∀ {m} → A (⇑₀ m) → B (⇑₀ m) → C (B m)
      record 𝓒heck ⦃ _ : [𝓒heck] ⦄ : Ø x ∙̂ a ∙̂ b ∙̂ c where field check : 𝓬heck
  open 𝓒heck ⦃ … ⦄ public

  check[_] : ∀
    {x} {X : Ø x}
    {a} {A : X → Ø a}
    {b} {B : X → Ø b}
    {c} (C : Ø b → Ø c)
    ⦃ _ : [𝓒heck] A B C ⦄
    ⦃ _ : 𝓢uccessor₀ X ⦄
    ⦃ _ : 𝓒heck A B C ⦄
    → 𝓬heck A B C
  check[ _ ] = check

  module _
    {x} {X : Ø x}
    {a} (A : X → Ø a)
    {b} (B : X → Ø b)
    {c} (C : Ø b → Ø c)
    {ℓ} (_≈_ : ∀ {x} → C (B x) → C (B x) → Ø ℓ)
    where
    record [𝓒heck/thin=1] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓢uccessor₀ X ⦄
      ⦃ _ : [𝓣hin] A B ⦄
      ⦃ _ : 𝓣hin A B ⦄
      ⦃ _ : [𝓒heck] A B C ⦄
      ⦃ _ : 𝓒heck A B C ⦄
      ⦃ _ : 𝓟ure C ⦄
      where
      𝓬heck/thin=1 = ∀ {n} (x : A (⇑₀ n)) (y : B n) → check x (thin x y) ≈ pure y
      record 𝓒heck/thin=1 ⦃ _ : [𝓒heck/thin=1] ⦄ : Ø x ∙̂ a ∙̂ b ∙̂ c ∙̂ ℓ where field check/thin=1 : 𝓬heck/thin=1
  open 𝓒heck/thin=1 ⦃ … ⦄ public

  check/thin=1[_] : ∀
    {x} {X : Ø x}
    {a} {A : X → Ø a}
    {b} {B : X → Ø b}
    {c} {C : Ø b → Ø c}
    {ℓ} (_≈_ : ∀ {x} → C (B x) → C (B x) → Ø ℓ)
    ⦃ _ : 𝓢uccessor₀ X ⦄
    ⦃ _ : [𝓣hin] A B ⦄
    ⦃ _ : 𝓣hin A B ⦄
    ⦃ _ : [𝓒heck] A B C ⦄
    ⦃ _ : 𝓒heck A B C ⦄
    ⦃ _ : 𝓟ure C ⦄
    ⦃ _ : [𝓒heck/thin=1] A B C _≈_ ⦄
    ⦃ _ : 𝓒heck/thin=1 A B C _≈_ ⦄
    → 𝓬heck/thin=1 A B C _≈_
  check/thin=1[ _ ] = check/thin=1

  record IsThickandthin
    {x a b c ℓb ℓc}
    {X : Ø x}
    (A : X → Ø a)
    (B : X → Ø b)
    (_≈B_ : ∀ {x} → B x → B x → Ø ℓb)
    (C : Ø b → Ø c)
    (_≈C_ : ∀ {x} → C (B x) → C (B x) → Ø ℓc)
    : Ø x ∙̂ a ∙̂ ↑̂ b ∙̂ ℓb ∙̂ c ∙̂ ℓc where
    constructor ∁
    field
      overlap ⦃ `𝓢uccessor₀ ⦄ : 𝓢uccessor₀ X
      overlap ⦃ `[𝓢uccessor₁] ⦄ : [𝓢uccessor₁] A
      overlap ⦃ `𝓢uccessor₁ ⦄ : 𝓢uccessor₁ A
      overlap ⦃ `[𝓣hick] ⦄ : [𝓣hick] A B
      overlap ⦃ `𝓣hick ⦄ : 𝓣hick A B
      overlap ⦃ `[𝓣hin] ⦄ : [𝓣hin] A B
      overlap ⦃ `𝓣hin ⦄ : 𝓣hin A B
      overlap ⦃ `[𝓘njectivity₂,₁] ⦄ : ∀ {m} → [𝓘njectivity₂,₁] (𝔱hin A B m) _≈B_ _≈B_
      overlap ⦃ `𝓘njectivity₂,₁ ⦄   : ∀ {m} → 𝓘njectivity₂,₁ (𝔱hin A B m) _≈B_ _≈B_
      overlap ⦃ `[𝓒heck] ⦄ : [𝓒heck] A B C
      overlap ⦃ `𝓒heck ⦄ : 𝓒heck A B C
      overlap ⦃ `[𝓣hick/thin=1] ⦄ : [𝓣hick/thin=1] A B _≈B_
      overlap ⦃ `𝓣hick/thin=1 ⦄ : 𝓣hick/thin=1 A B _≈B_
      overlap ⦃ `[𝓒heck/thin=1] ⦄ : [𝓒heck/thin=1] A B C _≈C_
      overlap ⦃ `𝓟ure ⦄ : 𝓟ure C
      overlap ⦃ `𝓒heck/thin=1 ⦄ : 𝓒heck/thin=1 A B C _≈C_

  record Thickandthin x a b ℓb c ℓc : Ø ↑̂ (x ∙̂ a ∙̂ b ∙̂ ℓb ∙̂ c ∙̂ ℓc) where
    constructor ∁
    field
      {X} : Ø x
      A : X → Ø a
      B : X → Ø b
      _≈B_ : ∀ {x} → B x → B x → Ø ℓb
      C : Ø b → Ø c
      _≈C_ : ∀ {x} → C (B x) → C (B x) → Ø ℓc
      ⦃ `IsThickandthin ⦄ : IsThickandthin A B _≈B_ C _≈C_

  module Test-Thickandthin {x a b ℓb c ℓc} ⦃ _ : Thickandthin x a b ℓb c ℓc ⦄ where
    open Thickandthin ⦃ … ⦄

    test-thin : 𝓽hin A B
    test-thin = thin

    test-check/thin=1 : 𝓬heck/thin=1 A B C _≈C_
    test-check/thin=1 = check/thin=1

    test-injectivity : ∀ {m : X} {x : A (⇑₀ m)} → 𝓶ap (_≈B_ on thin x) _≈B_
    test-injectivity {x = x} = injectivity₂,₁ x

module _ where

  record HasEquivalence {𝔬} (𝔒 : Ø 𝔬) ℓ : Ø 𝔬 ∙̂ ↑̂ ℓ where
    constructor ∁

    field
      Equivalence : 𝔒 → 𝔒 → Ø ℓ
      ⦃ ⌶IsEquivalence ⦄ : IsEquivalence Equivalence
    infix 4 Equivalence

  open HasEquivalence ⦃ … ⦄ public
  open HasEquivalence ⦃ … ⦄ public using () renaming (Equivalence to _≈_)

  module _ where

    infix 4 ≈-syntax
    ≈-syntax : ∀ {𝔬} (𝔒 : Ø 𝔬) {ℓ} ⦃ _ : HasEquivalence 𝔒 ℓ ⦄ → 𝔒 → 𝔒 → Ø ℓ
    ≈-syntax _ = _≈_
    syntax ≈-syntax 𝔒 x y = x ≈[ 𝔒 ] y

module _ where

  open import Oscar.Data

  record IsDecidable {𝔬} (𝔒 : Ø 𝔬) : Ø 𝔬 where
    infix 4 _≟_
    field
      _≟_ : (x y : 𝔒) → Decidable (x ≡ y)

  open IsDecidable ⦃ … ⦄ public

module _ where

  record Properthing {𝔬} ℓ (𝔒 : Ø 𝔬) : Ø 𝔬 ∙̂ ↑̂ ℓ where
    infixr 15 _∧_
    field
      ➊ : 𝔒
      _∧_ : 𝔒 → 𝔒 → 𝔒
      ⦃ ⌶HasEquivalence ⦄ : HasEquivalence 𝔒 ℓ
      Nothing : 𝔒 → Ø ℓ
      fact2 : ∀ {P Q} → P ≈ Q → Nothing P → Nothing Q
      ∧-leftIdentity : ∀ P → ➊ ∧ P ≈ P

  open Properthing ⦃ … ⦄ public

module _ where

  record Exotransitivity
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} (𝔄 : 𝔛 → Ø 𝔞)
    {𝔟} (𝔅 : 𝔛 → 𝔛 → Ø 𝔟)
    : Ø 𝔵 ∙̂ 𝔞 ∙̂ 𝔟
    where
    field
      exotransitivity : ∀ {x y} → 𝔅 x y → 𝔄 x → 𝔄 y

module _ where

  module _
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} (𝔄 : 𝔛 → Ø 𝔞)
    {𝔟} (𝔅 : 𝔛 → Ø 𝔟)
    (let _∼_ = Arrow 𝔄 𝔅) (let infix 4 _∼_ ; _∼_ = _∼_)
    {ℓ̇} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ̇)
    ⦃ _ : 𝓣ransitivity _∼_ ⦄
    ⦃ _ : 𝓡eflexivity _∼_ ⦄
    ℓ
    where
    𝓹rop-id = ∀ {m n} {f : m ∼ n} (P : LeftExtensionṖroperty ℓ _∼_ _∼̇_ m)
              (let P₀ = π₀ (π₀ P)) → P₀ f → P₀ (ε ∙ f)
    record PropId : Ø 𝔵 ∙̂ 𝔞 ∙̂ 𝔟 ∙̂ ℓ̇ ∙̂ ↑̂ ℓ where field prop-id : 𝓹rop-id

  open PropId ⦃ … ⦄ public

module _ where

  record Amgu {𝔵} {X : Ø 𝔵} {𝔱} (T : X → Ø 𝔱) {𝔞} (A : X → Ø 𝔞) {𝔪} (M : Ø 𝔞 → Ø 𝔪) : Ø 𝔵 ∙̂ 𝔱 ∙̂ 𝔞 ∙̂ 𝔪 where
    field amgu : ∀ {x} → T x → T x → A x → M (A x)

  open Amgu ⦃ … ⦄ public

module _ where

  record [IsExtensionB]
    {a} {A : Ø a}
    {b} (B : A → Ø b)
    : Ø₀ where
    constructor ∁
    no-eta-equality

module _ where

  record [ExtensibleType]
      {𝔵} {𝔛 : Ø 𝔵}
      {𝔟} {𝔒₂ : 𝔛 → Ø 𝔟}
      {ℓ̇} (_↦_ : ∀ {x} → 𝔒₂ x → 𝔒₂ x → Ø ℓ̇)
      : Ø₀ where
    constructor ∁
    no-eta-equality

module _ where

  record [𝓢urjectextenscongruity]
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼ᵣ_ : π̂² 𝔯 𝔒)
    {𝔭} (𝔓 : π̂ 𝔭 𝔒)
    {ℓ} (_∼ₚ_ : ∀̇ π̂² ℓ 𝔓)
    : Ø₀ where
    no-eta-equality
    constructor ∁

  record 𝓢urjectextenscongruity
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼ᵣ_ : π̂² 𝔯 𝔒)
    {𝔭} (𝔓 : π̂ 𝔭 𝔒)
    {ℓ} (_∼ₚ_ : ∀̇ π̂² ℓ 𝔓)
    ⦃ _ : [𝓢urjectextenscongruity] _∼ᵣ_ 𝔓 _∼ₚ_ ⦄
    ⦃ _ : 𝓢urjectextensivity _∼ᵣ_ 𝔓 ⦄
    : Ø 𝔬 ∙̂ 𝔭 ∙̂ 𝔯 ∙̂ ℓ where
    field
      surjectextenscongruity : ∀
        {m n} {P Q : 𝔓 m} (f : m ∼ᵣ n) → P ∼ₚ Q → (f ◃ P) ∼ₚ (f ◃ Q)

  open 𝓢urjectextenscongruity ⦃ … ⦄ public

module _ where

  Refl4 : ∀ {𝔞} ℓ → Ø 𝔞 → Ø 𝔞 ∙̂ ↑̂ ℓ
  Refl4 ℓ 𝔄 = 𝔄 → 𝔄 → 𝔄 → 𝔄 → Ø ℓ

  𝓅roperfact1 : ∀ {𝔞} {𝔄 : Ø 𝔞} {ℓ} → Refl4 ℓ 𝔄 → Ø 𝔞 ∙̂ ℓ
  𝓅roperfact1 refl4 = ∀ s1 s2 t1 t2 → refl4 s1 s2 t1 t2

  [𝓹roperfact1] : ∀ {𝔞} {𝔄 : Ø 𝔞} {𝔟} {𝔅 : Ø 𝔟} {ℓ} ⦃ _ : Properthing ℓ 𝔅 ⦄ (_∼_ : 𝔄 → 𝔄 → 𝔅) (_⊛_ : 𝔄 → 𝔄 → 𝔄) → Refl4 ℓ 𝔄
  [𝓹roperfact1] _∼_ _⊛_ s1 s2 t1 t2 = let _∼_ = _∼_ ; infix 18 _∼_ in
    s1 ⊛ s2 ∼ t1 ⊛ t2 ≈ s1 ∼ t1 ∧ s2 ∼ t2

  module _
    {𝔞} {𝔄 : Ø 𝔞} ℓ (refl4 : Refl4 ℓ 𝔄)
    where
    record [𝒫roperfact1] 𝔟 : Ø 𝔞 ∙̂ ↑̂ 𝔟 ∙̂ ↑̂ ℓ where
      constructor ∁
      infix 18 _∼_
      field
        𝔅 : Ø 𝔟
        _∼_ : 𝔄 → 𝔄 → 𝔅
        ⦃ ⌶Properthing ⦄ : Properthing ℓ 𝔅
        _⊛_ : 𝔄 → 𝔄 → 𝔄
        ⦃ ⌶CorrectProp ⦄ : [𝓹roperfact1] _∼_ _⊛_ ≡ refl4

    record 𝒫roperfact1 {𝔟} ⦃ _ : [𝒫roperfact1] 𝔟 ⦄ : Ø 𝔞 ∙̂ ℓ where
      field properfact1 : 𝓅roperfact1 refl4

  open 𝒫roperfact1 ⦃ … ⦄ public

  module _
    {𝔞} {𝔄 : Ø 𝔞} {𝔟} {𝔅 : Ø 𝔟} (_∼_ : 𝔄 → 𝔄 → 𝔅) {ℓ} ⦃ _ : Properthing ℓ 𝔅 ⦄ (_⊛_ : 𝔄 → 𝔄 → 𝔄)
    where
    𝓹roperfact1 = 𝓅roperfact1 ([𝓹roperfact1] _∼_ _⊛_)
    [𝓟roperfact1] = [𝒫roperfact1] _ ([𝓹roperfact1] _∼_ _⊛_) 𝔟
    𝓟roperfact1 = 𝒫roperfact1 _ ([𝓹roperfact1] _∼_ _⊛_)

module _ where

  TYPE : ∀ {𝔞} {𝔄 : Ø 𝔞} {𝔟} ℓ → (𝔄 → Ø 𝔟) → Ø 𝔞 ∙̂ 𝔟 ∙̂ ↑̂ ℓ
  TYPE ℓ 𝔅 = ∀ {a} (B : 𝔅 a) → Ø ℓ

  𝒻actsurj3 : ∀ {𝔞} {𝔄 : Ø 𝔞} {𝔟} {𝔅 : 𝔄 → Ø 𝔟} {ℓ} → TYPE ℓ 𝔅 → Ø 𝔞 ∙̂ 𝔟 ∙̂ ℓ
  𝒻actsurj3 {𝔅 = B} C = ∀ {a} {b : B a} → C b

  [𝓯actsurj3] : ∀ {𝔞} {𝔄 : Ø 𝔞} {𝔯} {𝔟} {ℓ} (_∼ᵣ_ : π̂² 𝔯 𝔄) (B : π̂ 𝔟 𝔄) ⦃ _ : 𝓡eflexivity _∼ᵣ_ ⦄ ⦃ _ : 𝓢urjectextensivity _∼ᵣ_ B ⦄ ⦃ _ : ∀ {x} → HasEquivalence (B x) ℓ ⦄ → TYPE ℓ B
  [𝓯actsurj3] _∼ᵣ_ 𝔅 B = B ≈ ε[ _∼ᵣ_ ] ◃ B

  module _
    {ℓ} {𝔞} {𝔄 : Ø 𝔞} {𝔟} {𝔅 : 𝔄 → Ø 𝔟}
    (type : TYPE ℓ 𝔅)
    where
    record [𝐹actsurj3] 𝔯 : Ø 𝔞 ∙̂ 𝔟 ∙̂ ↑̂ 𝔯 ∙̂ ↑̂ ℓ where
      constructor ∁
      field
        _∼ᵣ_ : π̂² 𝔯 𝔄
        ⦃ ⌶Reflexivity ⦄ : 𝓡eflexivity _∼ᵣ_
        ⦃ ⌶Surjectextensivity ⦄ : 𝓢urjectextensivity _∼ᵣ_ 𝔅
        ⦃ ⌶HasEquivalence ⦄ : ∀ {x} → HasEquivalence (𝔅 x) ℓ
        ⦃ ⌶CorrectFactsurj3 ⦄ : (λ {a} → [𝓯actsurj3] _∼ᵣ_ 𝔅 {a}) ≡ type

    record 𝐹actsurj3 {𝔯} ⦃ _ : [𝐹actsurj3] 𝔯 ⦄ : Ø 𝔞 ∙̂ 𝔟 ∙̂ ℓ where
      field factsurj3 : 𝒻actsurj3 (λ {x} → type {x})

  open 𝐹actsurj3 ⦃ … ⦄ public

  module _
    {ℓ} {𝔞} {𝔄 : Ø 𝔞} {𝔟} (𝔅 : 𝔄 → Ø 𝔟)
    {𝔯} (_∼ᵣ_ : π̂² 𝔯 𝔄)
    ⦃ _ : 𝓡eflexivity _∼ᵣ_ ⦄
    ⦃ _ : 𝓢urjectextensivity _∼ᵣ_ 𝔅 ⦄
    ⦃ _ : ∀ {x} → HasEquivalence (𝔅 x) ℓ ⦄
    where
    𝓯actsurj3 = 𝒻actsurj3 (λ {x} → [𝓯actsurj3] _∼ᵣ_ 𝔅 {x})
    [𝓕actsurj3] = [𝐹actsurj3] (λ {x} → [𝓯actsurj3] _∼ᵣ_ 𝔅 {x})
    𝓕actsurj3 = 𝐹actsurj3 (λ {x} → [𝓯actsurj3] _∼ᵣ_ 𝔅 {x})

module _ where

  module _
    {𝔞} {𝔄 : Ø 𝔞}
    {𝔟} (𝔅 : 𝔄 → Ø 𝔟)
    {𝔠} (ℭ : 𝔄 → 𝔄 → Ø 𝔠)
    where
    𝓯actsurj4-act = ∀ {a₁ a₂} → ℭ a₁ a₂ → 𝔅 a₁ → 𝔅 a₂
    module _
      {𝔡} (𝔇 : ∀ {a} → 𝔅 a → Ø 𝔡)
      where
      record [𝓕actsurj4] : Ø 𝔞 ∙̂ 𝔠 ∙̂ 𝔟 where
        constructor ∁
        field
          act : 𝓯actsurj4-act
      module _
        (act : 𝓯actsurj4-act)
        where
        𝓯actsurj4 = ∀ {a₁ a₂} {b : 𝔅 a₁} (c : ℭ a₁ a₂) → 𝔇 b → 𝔇 (act c b)
      module _
        ⦃ ⌶[𝓕actsurj4] : [𝓕actsurj4] ⦄
        where
        open [𝓕actsurj4] ⌶[𝓕actsurj4]
        record 𝓕actsurj4 : Ø 𝔞 ∙̂ 𝔟 ∙̂ 𝔠 ∙̂ 𝔡 where
          field factsurj4 : 𝓯actsurj4 act

  open 𝓕actsurj4 ⦃ … ⦄ public

module _ where

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
    {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    {ℓ∼} (_≈̈_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ∼) (let _≈̈_ = _≈̈_ ; infix 4 _≈̈_)
    {ℓ𝔭} (_≈̇_ : ∀ {x} → 𝔓 x → 𝔓 x → Ø ℓ𝔭) (let _≈̇_ = _≈̇_ ; infix 4 _≈̇_)
    where
    record [𝓕actsurj6] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓢urjectextensivity _∼_ 𝔓 ⦄
      where
      record 𝓕actsurj6 ⦃ _ : [𝓕actsurj6] ⦄ : Ø 𝔬 ∙̂ 𝔭 ∙̂ 𝔯 ∙̂ ℓ∼ ∙̂ ℓ𝔭 where
        field factsurj6 : ∀ {m n} {f g : m ∼ n} (P : 𝔓 m) → f ≈̈ g → f ◃ P ≈̇ g ◃ P

  open 𝓕actsurj6 ⦃ … ⦄ public

open import Oscar.Data

instance

  [ExtensibleType]Proposequality : ∀ {a} {b} {A : Set a} {B : A → Set b} → [ExtensibleType] (λ {w} → Proposequality⟦ B w ⟧)
  [ExtensibleType]Proposequality = ∁

  [𝓢urjectivity]ArrowE : ∀ {ℓ} {a} {f} {t} {¶ : Set a} {Fin : ¶ → Set f} {Term : ¶ → Set t} → [𝓢urjectivity] (Arrow Fin Term) (Extension $ LeftExtensionṖroperty ℓ (Arrow Fin Term) _≡̇_)
  [𝓢urjectivity]ArrowE = ∁

  [𝓢urjectivity]LeftṖroperty : ∀ {ℓ} {a} {f} {¶ : Set a} {_↦_ : ¶ → ¶ → Set f} → [𝓢urjectivity] _↦_ (Extension $ LeftṖroperty ℓ _↦_)
  [𝓢urjectivity]LeftṖroperty = ∁

instance

  𝓢ymmetrical𝓢ymmetry : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {ℓ} {_∼_ : 𝔒 → 𝔒 → Ø ℓ}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
    → 𝓢ymmetrical 𝔒 (λ s t t' s' → s ∼ t → t' ∼ s')
  𝓢ymmetrical𝓢ymmetry .𝓢ymmetrical.symmetrical x y = symmetry
