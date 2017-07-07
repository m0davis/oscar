{-# OPTIONS --show-implicit #-}
{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}
module Oscar.Class where

open import Oscar.Prelude
open import Oscar.Data using (_≡_; Proposequality; ∅)

module IMPORT…Reflexivity where

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    where
    𝓻eflexivity = ∀ {x} → x ∼ x
    record 𝓡eflexivity : Ø 𝔬 ∙̂ 𝔯 where
      field
        reflexivity : 𝓻eflexivity

  private

    module projection where

      open 𝓡eflexivity ⦃ … ⦄ public using (reflexivity)

      reflexivity[_] : ∀
        {𝔬} {𝔒 : Ø 𝔬}
        {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
        ⦃ _ : 𝓡eflexivity _∼_ ⦄
        → 𝓻eflexivity _∼_
      reflexivity[ _ ] = reflexivity

  open projection public
  open projection public using () renaming (reflexivity to ε; reflexivity[_] to ε[_])

open IMPORT…Reflexivity public

module _ where

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    where
    𝓼ymmetry = ∀ {x y} → x ∼ y → y ∼ x
    record 𝓢ymmetry : Ø 𝔬 ∙̂ 𝔯 where field symmetry : 𝓼ymmetry

    record 𝓢ymmetryOpen : Ø 𝔬 ∙̂ 𝔯 where
      field
        symmetryOpen : ∀ x y → x ∼ y → y ∼ x
      syntax symmetryOpen x y eq = x ⟨∼ eq ∼⟩ y

  private

    module projection where

      open 𝓢ymmetry ⦃ … ⦄ public

      symmetry[_] : ∀
        {𝔬} {𝔒 : Ø 𝔬}
        {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
        ⦃ _ : 𝓢ymmetry _∼_ ⦄
        → 𝓼ymmetry _∼_
      symmetry[ _ ] = symmetry

  open projection public

  instance

    SymmetryOpenInstances : ∀
      {𝔬} {𝔒 : Ø 𝔬}
      {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
      ⦃ _ : 𝓢ymmetry _∼_ ⦄
      → 𝓢ymmetryOpen _∼_
    SymmetryOpenInstances .𝓢ymmetryOpen.symmetryOpen _ _ = symmetry

  open 𝓢ymmetryOpen ⦃ … ⦄ public

module _ where

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    where
    𝓽ransitivity = ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z

  record 𝓣ransitivity
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    : Ø 𝔬 ∙̂ 𝔯 where
    field transitivity : 𝓽ransitivity _∼_
    infixr 9 transitivity
    syntax transitivity f g = g ∙ f

  open 𝓣ransitivity ⦃ … ⦄ public

  transitivity[_] : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_⊸_ : 𝔒 → 𝔒 → Ø 𝔯)
    ⦃ _ : 𝓣ransitivity _⊸_ ⦄
    → 𝓽ransitivity _⊸_
  transitivity[ _ ] = transitivity

  infixr 9 ∙[]-syntax
  ∙[]-syntax = transitivity[_]
  syntax ∙[]-syntax _⊸_ f g = g ∙[ _⊸_ ] f

  open import Oscar.Data

  ≡̇-transitivity : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔭} {𝔓 : 𝔒 → Ø 𝔭}
    ⦃ _ : 𝓣ransitivity (Proposextensequality⟦ 𝔓 ⟧) ⦄
    → 𝓽ransitivity Proposextensequality⟦ 𝔓 ⟧
  ≡̇-transitivity = transitivity[ Proposextensequality ]

  infixr 9 ≡̇-transitivity
  syntax ≡̇-transitivity f g = g ≡̇-∙ f

  infixr 9 ≡̇-transitivity-syntax
  ≡̇-transitivity-syntax = ≡̇-transitivity
  syntax ≡̇-transitivity-syntax f g = g ⟨≡̇⟩ f

record IsEquivalence
  {𝔬} {𝔒 : Ø 𝔬}
  {ℓ} (_≈_ : 𝔒 → 𝔒 → Ø ℓ)
  : Ø 𝔬 ∙̂ ℓ where
  constructor ∁
  field
    ⦃ `𝓡eflexivity ⦄ : 𝓡eflexivity _≈_
    ⦃ `𝓢ymmetry ⦄ : 𝓢ymmetry _≈_
    ⦃ `𝓣ransitivity ⦄ : 𝓣ransitivity _≈_

module _ where

  record Setoid 𝔬 ℓ : Ø ↑̂ (𝔬 ∙̂ ℓ) where
    constructor ∁
    field
      {Object} : Ø 𝔬
      ObjectEquivalence : Object → Object → Ø ℓ
      ⦃ `IsEquivalence ⦄ : IsEquivalence ObjectEquivalence

module _ where

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
    where
    record [𝓣ransextensionality] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓣ransitivity _∼_ ⦄
      where
      𝓽ransextensionality = ∀ {x y z} {f₁ f₂ : x ∼ y} {g₁ g₂ : y ∼ z} → f₁ ∼̇ f₂ → g₁ ∼̇ g₂ → g₁ ∙ f₁ ∼̇ g₂ ∙ f₂
      record 𝓣ransextensionality ⦃ _ : [𝓣ransextensionality] ⦄ : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where
        field transextensionality : 𝓽ransextensionality
        syntax transextensionality f₁∼̇f₂ g₁∼̇g₂ = g₁∼̇g₂ ⟨∙⟩ f₁∼̇f₂
        infixr 19 transextensionality
  open 𝓣ransextensionality ⦃ … ⦄ public

module _ where

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
    where
    record [𝓣ransassociativity] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓣ransitivity _∼_ ⦄
      where
      𝓽ransassociativity = ∀ {w x y z} (f : w ∼ x) (g : x ∼ y) (h : y ∼ z) → (h ∙ g) ∙ f ∼̇ h ∙ g ∙ f
      record 𝓣ransassociativity ⦃ _ : [𝓣ransassociativity] ⦄ : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where
        field transassociativity : 𝓽ransassociativity
        syntax transassociativity f g h = h ⟨∙ g ⟨∙ f
  open 𝓣ransassociativity ⦃ … ⦄ public

  transassociativity[_] : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
    {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ)
    ⦃ _ : 𝓣ransitivity _∼_ ⦄
    ⦃ _ : [𝓣ransassociativity] _∼_ _∼̇_ ⦄
    ⦃ _ : 𝓣ransassociativity _∼_ _∼̇_ ⦄
    → 𝓽ransassociativity _∼_ _∼̇_
  transassociativity[ _ ] = transassociativity

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
      𝓼urjectivity' = ∀ {x y} → x ∼₁ y → 𝔒₂ x → 𝔒₂ y
      record 𝓢urjectivity' : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ 𝔬₂ where -- TODO rename
        field
          surjectivity' : 𝓼urjectivity'
        infixr 10 surjectivity'
        syntax surjectivity' σ τ = σ ◃ τ
        surjectivity'!syntax = surjectivity'
        infixl 10 surjectivity'!syntax
        syntax surjectivity'!syntax rxy px = px ● rxy

  open 𝓢urjectivity' ⦃ … ⦄ public hiding (surjectivity')
  open 𝓢urjectivity' ⦃ … ⦄ public using () renaming (surjectivity' to §')

  surjectivity'[]syntax : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
    {𝔬₂} (𝔒₂ : 𝔒₁ → Ø 𝔬₂)
    ⦃ _ : 𝓢urjectivity' _∼₁_ 𝔒₂ ⦄
    → 𝓼urjectivity' _∼₁_ 𝔒₂
  surjectivity'[]syntax _ = §'

  syntax surjectivity'[]syntax 𝔒₂ x∼y fx = x∼y ◃[ 𝔒₂ ] fx

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
        → 𝓢urjectivity' _∼₁_ 𝔒₂
      toSurj' {{_}} {{x₂}} .𝓢urjectivity'.surjectivity' = § {{r = x₂}}

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

  module _
    {ℓ} (_∼_ : ∀ {𝔬} {𝔒 : Ø 𝔬} → 𝔒 → 𝔒 → Ø ℓ)
    𝔵 𝔶
    where
    𝓬ongruity = ∀ {𝔛 : Ø 𝔵} {𝔜 : Ø 𝔶} {x₁ x₂} (f : 𝔛 → 𝔜) → x₁ ∼ x₂ → f x₁ ∼ f x₂
    record 𝓒ongruity : Ø ℓ ∙̂ ↑̂ (𝔵 ∙̂ 𝔶) where
      field congruity : 𝓬ongruity

  open 𝓒ongruity ⦃ … ⦄ public

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
    -- infix 4 Equivalence
    -- syntax Equivalence x y = x ≈ y

  open HasEquivalence ⦃ … ⦄ public

  module _ where

    infix 4 _≈_
    _≈_ : ∀ {𝔬} {𝔒 : Ø 𝔬} {ℓ} ⦃ _ : HasEquivalence 𝔒 ℓ ⦄ → 𝔒 → 𝔒 → Ø ℓ
    _≈_ = HasEquivalence.Equivalence !


module _ where

  open import Oscar.Data

  record IsDecidable {𝔬} (𝔒 : Ø 𝔬) : Ø 𝔬 where
    infix 4 _≟_
    field
      _≟_ : (x y : 𝔒) → Decidable (x ≡ y)

  open IsDecidable ⦃ … ⦄ public

module _ where

  record Properthing {𝔬} ℓ (𝔒 : Ø 𝔬) : Ø 𝔬 ∙̂ ↑̂ ℓ where
    field
      _∧_ : 𝔒 → 𝔒 → 𝔒
      _⇔_ : 𝔒 → 𝔒 → Ø ℓ
      ⦃ IsEquivalence⇔ ⦄ : IsEquivalence _⇔_
      Nothing : 𝔒 → Ø ℓ
      fact2 : ∀ {P Q} → P ⇔ Q → Nothing P → Nothing Q

  open Properthing ⦃ … ⦄ public

  ⇔syntax : ∀
    {𝔬} {ℓ} (𝔒 : Ø 𝔬)
    ⦃ _ : Properthing ℓ 𝔒 ⦄
    → 𝔒 → 𝔒 → Ø ℓ
  ⇔syntax _ = _⇔_

  syntax ⇔syntax 𝔒 P Q = P ⇔[ 𝔒 ] Q


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
              (let P₀ = π₀ P) → P₀ f → P₀ (ε ∙ f)
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


-- record HasËquivalence {𝔬} {𝔒 : Ø 𝔬} {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯) ℓ : Ø 𝔬 ∙̂ 𝔯 ∙̂ ↑̂ ℓ where
--   constructor ∁
--   field
--     Ëquivalence : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ
--     ⦃ ⌶IsEquivalence ⦄ : ∀ {x y} → IsEquivalence (Ëquivalence {x} {y})

-- module _ where

--   infix 4 _≈̈_
--   _≈̈_ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯} {ℓ} ⦃ _ : HasËquivalence _∼_ ℓ ⦄ → ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ
--   _≈̈_ = HasËquivalence.Ëquivalence !
