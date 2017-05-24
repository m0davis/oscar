--{-# OPTIONS --show-implicit #-}
{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}
module Oscar.Class where

open import Oscar.Prelude

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

module _ where

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    where
    𝓽ransitivity = ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z
    record 𝓣ransitivity : Ø 𝔬 ∙̂ 𝔯 where
      field transitivity : 𝓽ransitivity
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

record IsEquivalence
  {𝔬} {𝔒 : Ø 𝔬}
  {ℓ} (_≈_ : 𝔒 → 𝔒 → Ø ℓ)
  : Ø 𝔬 ∙̂ ℓ where
  field
    ⦃ `𝓡eflexivity ⦄ : 𝓡eflexivity _≈_
    ⦃ `𝓢ymmetry ⦄ : 𝓢ymmetry _≈_
    ⦃ `𝓣ransitivity ⦄ : 𝓣ransitivity _≈_

module _ where

  record Setoid 𝔬 ℓ : Ø ↑̂ (𝔬 ∙̂ ℓ) where
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
    record [𝓣ransextensionality] : Ø₀ where no-eta-equality
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
    record [𝓣ransassociativity] : Ø₀ where no-eta-equality
    module _
      ⦃ _ : 𝓣ransitivity _∼_ ⦄
      where
      𝓽ransassociativity = ∀ {w x y z} (f : w ∼ x) (g : x ∼ y) (h : y ∼ z) → (h ∙ g) ∙ f ∼̇ h ∙ g ∙ f
      record 𝓣ransassociativity ⦃ _ : [𝓣ransassociativity] ⦄ : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where
        field transassociativity : 𝓽ransassociativity
        syntax transassociativity f g h = h ⟨∙ g ⟨∙ f
  open 𝓣ransassociativity ⦃ … ⦄ public

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  where
  record IsPrecategory : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where
    field
      overlap ⦃ `𝓣ransitivity ⦄ : 𝓣ransitivity _∼_
      overlap ⦃ `[𝓣ransextensionality] ⦄ : [𝓣ransextensionality] _∼_ _∼̇_
      overlap ⦃ `[𝓣ransassociativity] ⦄ : [𝓣ransassociativity] _∼_ _∼̇_
      ⦃ `𝓣ransextensionality ⦄ : 𝓣ransextensionality _∼_ _∼̇_
      ⦃ `𝓣ransassociativity ⦄ : 𝓣ransassociativity _∼_ _∼̇_

record Precategory 𝔬 𝔯 ℓ : Ø ↑̂ (𝔬 ∙̂ 𝔯 ∙̂ ℓ) where
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
      record 𝓢urjection : Ø 𝔬₁ ∙̂ 𝔬₂ where field surjection : 𝓼urjection
  open 𝓢urjection ⦃ … ⦄ public

module _ where

  module _
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    where
    record [𝓢urjectivity] : Ø₀ where no-eta-equality
    module _
      ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
      where
      𝓼urjectivity = ∀ {x y} → x ∼₁ y → surjection x ∼₂ surjection y
      record 𝓢urjectivity ⦃ _ : [𝓢urjectivity] ⦄ : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ where field surjectivity : 𝓼urjectivity
  open 𝓢urjectivity ⦃ … ⦄ public

  module _ where

    surjectivity[_] : ∀
      {𝔬₁} {𝔒₁ : Ø 𝔬₁}
      {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
      {𝔬₂} {𝔒₂ : Ø 𝔬₂}
      {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
      ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
      ⦃ `[𝓢urjectivity] : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
      ⦃ `𝓢urjectivity : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
      → 𝓼urjectivity _∼₁_ _∼₂_
    surjectivity[ _ ] = surjectivity

module _ where

  module _
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂) (let infix 4 _∼̇₂_ ; _∼̇₂_ = _∼̇₂_)
    where
    record [𝓢urjtranscommutativity] : Ø₀ where no-eta-equality
    module _
      ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
      ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
      ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
      ⦃ _ : 𝓣ransitivity _∼₁_ ⦄
      ⦃ _ : 𝓣ransitivity _∼₂_ ⦄
      where
      𝓼urjtranscommutativity = ∀ {x y z} (f : x ∼₁ y) (g : y ∼₁ z) → surjectivity (g ∙ f) ∼̇₂ surjectivity g ∙ surjectivity f
      record 𝓢urjtranscommutativity ⦃ _ : [𝓢urjtranscommutativity] ⦄ : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂ where field surjtranscommutativity : 𝓼urjtranscommutativity
open 𝓢urjtranscommutativity ⦃ … ⦄ public

module _ where

  module _
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {ℓ₁} (_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁)
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    where
    record [𝓢urjextensionality] : Ø₀ where no-eta-equality
    module _
      ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
      ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
      ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
      where
      𝓼urjextensionality = ∀ {x y} {f₁ f₂ : x ∼₁ y} → f₁ ∼̇₁ f₂ → surjectivity f₁ ∼̇₂ surjectivity f₂
      record 𝓢urjextensionality ⦃ _ : [𝓢urjextensionality] ⦄ : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ ℓ₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂ where field surjextensionality : 𝓼urjextensionality
  open 𝓢urjextensionality ⦃ … ⦄ public

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
    record [𝓣ransleftidentity] : Ø₀ where no-eta-equality
    module _
      ⦃ _ : 𝓡eflexivity _∼_ ⦄
      ⦃ _ : 𝓣ransitivity _∼_ ⦄
      where
      𝓽ransleftidentity = ∀ {x y} {f : x ∼ y} → ε ∙ f ∼̇ f
      record 𝓣ransleftidentity ⦃ _ : [𝓣ransleftidentity] ⦄ : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where field transleftidentity : 𝓽ransleftidentity
  open 𝓣ransleftidentity ⦃ … ⦄ public

module _ where

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
    where
    record [𝓣ransrightidentity] : Ø₀ where no-eta-equality
    module _
      ⦃ _ : 𝓡eflexivity _∼_ ⦄
      ⦃ _ : 𝓣ransitivity _∼_ ⦄
      where
      𝓽ransrightidentity = ∀ {x y} {f : x ∼ y} → ε ∙ f ∼̇ f
      record 𝓣ransrightidentity ⦃ _ : [𝓣ransrightidentity] ⦄ : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where field transrightidentity : 𝓽ransrightidentity
  open 𝓣ransrightidentity ⦃ … ⦄ public


module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  where
  record IsCategory : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where
    field
      ⦃ `IsPrecategory ⦄ : IsPrecategory _∼_ _∼̇_
      overlap ⦃ `[𝓣ransleftidentity] ⦄ : [𝓣ransleftidentity] _∼_ _∼̇_
      overlap ⦃ `[𝓣ransrightidentity] ⦄ : [𝓣ransrightidentity] _∼_ _∼̇_
      overlap ⦃ `𝓡eflexivity ⦄ : 𝓡eflexivity _∼_
      ⦃ `𝓣ransleftidentity ⦄ : 𝓣ransleftidentity _∼_ _∼̇_
      ⦃ `𝓣ransrightidentity ⦄ : 𝓣ransrightidentity _∼_ _∼̇_

record Category 𝔬 𝔯 ℓ : Ø ↑̂ (𝔬 ∙̂ 𝔯 ∙̂ ℓ) where
  infix 4 _∼̇_
  field
    {𝔒} : Ø 𝔬
    _∼_ : 𝔒 → 𝔒 → Ø 𝔯
    _∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ
    ⦃ `IsCategory ⦄ : IsCategory _∼_ _∼̇_


module _ where

  module _
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    where
    record [𝓜apidentity] : Ø₀ where no-eta-equality
    module _
      ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
      ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
      ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
      ⦃ _ : 𝓡eflexivity _∼₁_ ⦄
      ⦃ _ : 𝓡eflexivity _∼₂_ ⦄
      where
      𝓶apidentity = ∀ {x} → surjectivity (ε[ _∼₁_ ] {x}) ∼̇₂ ε
      record 𝓜apidentity ⦃ _ : [𝓜apidentity] ⦄ : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂ where field mapidentity : 𝓶apidentity
  open 𝓜apidentity ⦃ … ⦄ public using (mapidentity)


module _ where

  module _
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {ℓ₁} (_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁)
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    where
    record IsFunctor : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ ℓ₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂ where
      field
        ⦃ `IsPrefunctor ⦄ : IsPrefunctor _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_
        overlap ⦃ `IsCategory₁ ⦄ : IsCategory _∼₁_ _∼̇₁_
        overlap ⦃ `IsCategory₂ ⦄ : IsCategory _∼₂_ _∼̇₂_
        overlap ⦃ `[𝓜apidentity] ⦄ : [𝓜apidentity] _∼₁_ _∼₂_ _∼̇₂_
        overlap ⦃ `𝓜apidentity ⦄ : 𝓜apidentity _∼₁_ _∼₂_ _∼̇₂_

record Functor 𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂ : Ø ↑̂ (𝔬₁ ∙̂ 𝔯₁ ∙̂ ℓ₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂) where
  field
    {𝔒₁} : Ø 𝔬₁
    _∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁
    _∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁
    {𝔒₂} : Ø 𝔬₂
    _∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂
    _∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂
    ⦃ `IsFunctor ⦄ : IsFunctor _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_

module Test1 where

  test-functor-transextensionality : ∀
    {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂}
    ⦃ functor : Functor 𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂ ⦄
    (open Functor functor)
    → 𝓽ransextensionality _∼₁_ _∼̇₁_
  test-functor-transextensionality = transextensionality

module Test2 where

  test-functor-transextensionality : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
    {ℓ₁} {_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁}
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔯₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
    {ℓ₂} {_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂}
    ⦃ _ : IsFunctor _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_ ⦄
    ⦃ _ : IsFunctor _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_ ⦄
    → 𝓽ransextensionality _∼₁_ _∼̇₁_
  test-functor-transextensionality = transextensionality

module Test3 where

  module _
    {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂}
    where
    postulate instance functor : Functor 𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂
    open Functor ⦃ … ⦄
    test : asInstance `IsFunctor $ 𝓽ransextensionality _∼₁_ _∼̇₁_
    test = asInstance `IsFunctor transextensionality -- -- Test1.test-functor-transextensionality

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

  module _
    {𝔬} (𝔒 : Ø 𝔬)
    where
    𝓼uccessor₀ = 𝔒 → 𝔒
    record 𝓢uccessor₀ : Ø 𝔬 where
      field
        successor₀ : 𝓼uccessor₀

  open 𝓢uccessor₀ ⦃ … ⦄ public using (successor₀)
  open 𝓢uccessor₀ ⦃ … ⦄ public renaming (successor₀ to ⇑₀)

  module _
    {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
    where
    record [𝓢uccessor₁] : Ø₀ where no-eta-equality
    module _
      ⦃ _ : 𝓢uccessor₀ 𝔒 ⦄
      where
      𝓼uccessor₁ = ∀ {m} → 𝔓 m → 𝔓 (⇑₀ m)
      record 𝓢uccessor₁ ⦃ _ : [𝓢uccessor₁] ⦄ : Ø 𝔬 ∙̂ 𝔭 where
        field
          successor₁ : 𝓼uccessor₁
  open 𝓢uccessor₁ ⦃ … ⦄ public using (successor₁)
  open 𝓢uccessor₁ ⦃ … ⦄ public using () renaming (successor₁ to ⇑₁)

  module _
    {𝔬₁} (𝔒₁ : Ø 𝔬₁)
    {𝔬₂} (𝔒₂ : 𝔒₁ → Ø 𝔬₂)
    where
    𝓲njection₁ = (x : 𝔒₁) → 𝔒₂ x
    record 𝓘njection₁ : Ø 𝔬₁ ∙̂ 𝔬₂ where
      field injection₁ : 𝓲njection₁
  open 𝓘njection₁ ⦃ … ⦄ public

  module _
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {ℓ₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁)
    {ℓ₂} (_∼₂_ : 𝔒₁ → 𝔒₁ → Ø ℓ₂)
    where
    𝓶ap = ∀ {x y} → x ∼₁ y → x ∼₂ y
    record 𝓜ap : Ø 𝔬₁ ∙̂ ℓ₁ ∙̂ ℓ₂ where field map : 𝓶ap
  open 𝓜ap ⦃ … ⦄ public

  module _
    {𝔬₁} (𝔒₁ : Ø 𝔬₁)
    {𝔬₂} (𝔒₂ : 𝔒₁ → Ø 𝔬₂)
    {ℓ₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁)
    {ℓ₂} (_∼₂_ : ∀ {x₁ x₂} → 𝔒₂ x₁ → 𝔒₂ x₂ → Ø ℓ₂)
    where
    record [𝓘njectivity₁] : Ø₀ where
      no-eta-equality
    module _
      ⦃ _ : 𝓘njection₁ 𝔒₁ 𝔒₂ ⦄
      where
      𝓲njectivity₁ = ∀ {x₁ x₂} → injection₁ x₁ ∼₂ injection₁ x₂ → x₁ ∼₁ x₂
      record 𝓘njectivity₁ ⦃ _ : [𝓘njectivity₁] ⦄ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ ℓ₁ ∙̂ ℓ₂ where field injectivity₁ : 𝓲njectivity₁
  open 𝓘njectivity₁ ⦃ … ⦄ public

  module _
    {𝔬₁} (𝔒₁ : Ø 𝔬₁)
    {𝔬₂} (𝔒₂ : 𝔒₁ → Ø 𝔬₂)
    {𝔬₃} (𝔒₃ : ∀ x₁ → 𝔒₂ x₁ → Ø 𝔬₃)
    where
    𝓲njection₂ = ∀ x₁ → (x₂ : 𝔒₂ x₁) → 𝔒₃ x₁ x₂
    record 𝓘njection₂ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ where field injection₂ : 𝓲njection₂
  open 𝓘njection₂ ⦃ … ⦄ public

  module _
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} (𝔒₂ : 𝔒₁ → Ø 𝔬₂)
    {𝔬₃} (𝔒₃ : ∀ x₁ → 𝔒₂ x₁ → Ø 𝔬₃)
    {ℓ₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁)
    {ℓ₂} (_∼₂_ : ∀ {x₁ x₂} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} → 𝔒₃ _ y₁ → 𝔒₃ _ y₂ → Ø ℓ₂)
    where
    record [𝓘njectivity₂] : Ø₀ where no-eta-equality
    module _
      ⦃ _ : 𝓘njection₂ 𝔒₁ 𝔒₂ 𝔒₃ ⦄
      where
      𝓲njectivity₂ = ∀ {x₁ y₁} {x₂ : 𝔒₂ x₁} {y₂ : 𝔒₂ y₁} → injection₂ x₁ x₂ ∼₂ injection₂ y₁ y₂ → x₁ ∼₁ y₁
      record 𝓘njectivity₂ ⦃ _ : [𝓘njectivity₂] ⦄ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ ℓ₁ ∙̂ ℓ₂ where field injectivity₂ : 𝓲njectivity₂
  open 𝓘njectivity₂ ⦃ … ⦄ public using (injectivity₂)

  module _
    {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
    where
    record [𝓣hin] : Ø₀ where no-eta-equality
    module _
      ⦃ _ : 𝓢uccessor₀ X ⦄
      where
      𝓽hin = ∀ {m : X} → A (⇑₀ m) → B m → B (⇑₀ m)
      record 𝓣hin ⦃ _ : [𝓣hin] ⦄ : Ø x ∙̂ a ∙̂ b where field thin : 𝓽hin
  open 𝓣hin ⦃ … ⦄ public
  {-# DISPLAY 𝓣hin.thin _ = thin #-}

  module _
    {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
    where
    record [𝓣hick] : Ø₀ where no-eta-equality
    module _
      ⦃ _ : 𝓢uccessor₀ X ⦄
      where
      𝓽hick = ∀ {m} → B (⇑₀ m) → A m → B m
      record 𝓣hick ⦃ _ : [𝓣hick] ⦄ : Ø x ∙̂ a ∙̂ b where field thick : 𝓽hick
  open 𝓣hick ⦃ … ⦄ public

  module _
    {x} {X : Ø x}
    {a} (A : X → Ø a)
    {b} (B : X → Ø b)
    {ℓ} (_≈_ : ∀ {x} → B x → B x → Ø ℓ)
    where
    record [𝓣hick∘thin=id] : Ø₀ where no-eta-equality
    module _
      ⦃ _ : 𝓢uccessor₀ X ⦄
      ⦃ _ : [𝓢uccessor₁] A ⦄
      ⦃ _ : 𝓢uccessor₁ A ⦄
      ⦃ _ : [𝓣hin] A B ⦄
      ⦃ _ : 𝓣hin A B ⦄
      ⦃ _ : [𝓣hick] A B ⦄
      ⦃ _ : 𝓣hick A B ⦄
      where
      𝓽hick∘thin=id = ∀ {m} (x : A m) (y : B m) → thick (thin (⇑₁ x) y) x ≈ y
      record 𝓣hick∘thin=id : Ø x ∙̂ a ∙̂ b ∙̂ ℓ where field thick∘thin=id : 𝓽hick∘thin=id
  open 𝓣hick∘thin=id ⦃ … ⦄ public

  module _
    {x} {X : Ø x}
    {a} (A : X → Ø a)
    {b} (B : X → Ø b)
    {e} (E? : Ø b → Ø e)
    where
    record [𝓒heck] : Ø₀ where no-eta-equality
    module _
      ⦃ _ : 𝓢uccessor₀ X ⦄
      where
      𝓬heck = ∀ {m} → A (⇑₀ m) → B (⇑₀ m) → E? (B m)
      record 𝓒heck ⦃ _ : [𝓒heck] ⦄ : Ø x ∙̂ a ∙̂ b ∙̂ e where field check : 𝓬heck
  open 𝓒heck ⦃ … ⦄ public

  module _
    {x} {X : Ø x}
    {b} (B : X → Ø b)
    {e} (E? : Ø b → Ø e)
    where
    𝓳ust = ∀ {x} → B x → E? (B x)
    record 𝓙ust : Ø x ∙̂ b ∙̂ e where
      field just : 𝓳ust
  open 𝓙ust ⦃ … ⦄ public

  module _
    {x} {X : Ø x}
    {a} (A : X → Ø a)
    {b} (B : X → Ø b)
    {ℓb} (_≈B_ : ∀ {x} → B x → B x → Ø ℓb)
    {e} (E? : Ø b → Ø e)
    {ℓe} (_≈E?_ : ∀ {A : Ø b} → E? A → E? A → Ø ℓe)
    where
    record [𝓣hin-check-id] : Ø₀ where no-eta-equality
    module _
      ⦃ _ : 𝓢uccessor₀ X ⦄
      ⦃ _ : [𝓣hin] A B ⦄
      ⦃ _ : 𝓣hin A B ⦄
      ⦃ _ : [𝓒heck] A B E? ⦄
      ⦃ _ : 𝓒heck A B E? ⦄
      ⦃ `𝓙ust : 𝓙ust B E? ⦄
      where
      𝓽hin-check-id = ∀ {m} (x : A (⇑₀ m)) y → ∀ (y' : B m) → thin x y' ≈B y → check x y ≈E? just y'
      record 𝓣hin-check-id ⦃ _ : [𝓣hin-check-id] ⦄ : Ø x ∙̂ a ∙̂ b ∙̂ ℓb ∙̂ e ∙̂ ℓe where field thin-check-id : 𝓽hin-check-id
  open 𝓣hin-check-id ⦃ … ⦄ public

  record IsThickandthin
    {x a b ℓb e ℓe}
    {X : Ø x}
    (A : X → Ø a)
    (B : X → Ø b)
    (_≈B_ : ∀ {x} → B x → B x → Ø ℓb)
    (E? : Ø b → Ø e)
    (_≈E?_ : ∀ {A : Ø b} → E? A → E? A → Ø ℓe)
    : Ø x ∙̂ a ∙̂ b ∙̂ ℓb ∙̂ e ∙̂ ℓe where
    field
      overlap ⦃ `𝓢uccessor₀ ⦄ : 𝓢uccessor₀ X
      overlap ⦃ `[𝓢uccessor₁] ⦄ : [𝓢uccessor₁] A
      overlap ⦃ `𝓢uccessor₁ ⦄ : 𝓢uccessor₁ A
      overlap ⦃ `[𝓣hick] ⦄ : [𝓣hick] A B
      overlap ⦃ `𝓣hick ⦄ : 𝓣hick A B
      overlap ⦃ `[𝓣hin] ⦄ : [𝓣hin] A B
      overlap ⦃ `𝓣hin ⦄ : 𝓣hin A B
      overlap ⦃ `𝓜ap ⦄ : ∀ {m : X} {x : A (⇑₀ m)} → 𝓜ap (_≈B_ on thin x) _≈B_
      overlap ⦃ `[𝓒heck] ⦄ : [𝓒heck] A B E?
      overlap ⦃ `𝓒heck ⦄ : 𝓒heck A B E?
      overlap ⦃ `[𝓣hick∘thin=id] ⦄ : [𝓣hick∘thin=id] A B _≈B_
      overlap ⦃ `𝓣hick∘thin=id ⦄ : 𝓣hick∘thin=id A B _≈B_
      overlap ⦃ `[𝓣hin-check-id] ⦄ : [𝓣hin-check-id] A B _≈B_ E? _≈E?_
      overlap ⦃ `𝓙ust ⦄ : 𝓙ust B E?
      ⦃ `𝓣hin-check-id ⦄ : 𝓣hin-check-id A B _≈B_ E? _≈E?_

  record Thickandthin x a b ℓb e ℓe : Ø ↑̂ (x ∙̂ a ∙̂ b ∙̂ ℓb ∙̂ e ∙̂ ℓe) where
    field
      {X} : Ø x
      A : X → Ø a
      B : X → Ø b
      _≈B_ : ∀ {x} → B x → B x → Ø ℓb
      E? : Ø b → Ø e
      _≈E?_ : ∀ {A : Ø b} → E? A → E? A → Ø ℓe
      ⦃ `IsThickandthin ⦄ : IsThickandthin A B _≈B_ E? _≈E?_

  module Test-Thickandthin {x a b ℓb e ℓe} ⦃ _ : Thickandthin x a b ℓb e ℓe ⦄ where
    open Thickandthin ⦃ … ⦄
    {-# DISPLAY Thickandthin._≈B_ _ = _≈B_ #-}
    {-# DISPLAY Thickandthin.B _ = B #-}

    test-thin : 𝓽hin A B
    test-thin = thin

    test-thin-check-id : 𝓽hin-check-id A B _≈B_ E? _≈E?_
    test-thin-check-id = thin-check-id

    test-map : ∀ {m : X} {x : A (⇑₀ m)} → 𝓶ap (_≈B_ on thin x) _≈B_
    test-map = map

module _ where

  record HasEquivalence {𝔬} (𝔒 : Ø 𝔬) ℓ : Ø 𝔬 ∙̂ ↑̂ ℓ where
    field
      Equivalence : 𝔒 → 𝔒 → Ø ℓ
      ⦃ ⌶IsEquivalence ⦄ : IsEquivalence Equivalence

  module _ where

    infix 4 _≈_
    _≈_ : ∀ {𝔬} {𝔒 : Ø 𝔬} {ℓ} ⦃ _ : HasEquivalence 𝔒 ℓ ⦄ → 𝔒 → 𝔒 → Ø ℓ
    _≈_ = HasEquivalence.Equivalence !



-- open import Oscar.Data

-- module _ where

--   module _ {𝔬} {𝔒 : Ø 𝔬} where

--     instance

--       𝓡eflexivity∁Proposequality : 𝓡eflexivity∁ Proposequality⟦ 𝔒 ⟧
--       𝓡eflexivity∁Proposequality .𝓡eflexivity∁.reflexivity = !

--       𝓢ymmetry∁Proposequality : 𝓢ymmetry∁ Proposequality⟦ 𝔒 ⟧
--       𝓢ymmetry∁Proposequality .𝓢ymmetry∁.symmetry ∅ = !

--       𝓣ransitivity∁Proposequality : 𝓣ransitivity∁ Proposequality⟦ 𝔒 ⟧
--       𝓣ransitivity∁Proposequality .𝓣ransitivity∁.transitivity ∅ = ¡

--       IsEquivalence∁Proposequality : IsEquivalence∁ Proposequality⟦ 𝔒 ⟧
--       IsEquivalence∁Proposequality .IsEquivalence∁.⌶𝓡eflexivity∁ = !
--       IsEquivalence∁Proposequality .IsEquivalence∁.⌶𝓢ymmetry∁ = !
--       IsEquivalence∁Proposequality .IsEquivalence∁.⌶𝓣ransitivity∁ = !

-- module _ where

--   module _ {𝔬} (𝔒 : Ø 𝔬) where

--     SetoidProposequality : Setoid _ _
--     Setoid.Object SetoidProposequality = _
--     Setoid.ObjectEquality SetoidProposequality = Proposequality⟦ 𝔒 ⟧

--   instance

--     𝓒ongruity∁Proposequality : ∀ {a b} → 𝓒ongruity∁ a b Proposequality
--     𝓒ongruity∁Proposequality .𝓒ongruity∁.congruity _ ∅ = !

--     𝓒ongruity₂∁Proposequality : ∀ {a b c} → 𝓒ongruity₂∁ a b c Proposequality
--     𝓒ongruity₂∁Proposequality .𝓒ongruity₂∁.congruity₂ _ ∅ ∅ = !

--     𝓣ransextensionality∁Proposequality : ∀
--       {a} {A : Ø a}
--       {m} {_⊸_ : A → A → Ø m}
--       ⦃ _ : 𝓣ransitivity∁ _⊸_ ⦄
--       → 𝓣ransextensionality∁ _⊸_ Proposequality
--     𝓣ransextensionality∁Proposequality .𝓣ransextensionality∁.⌶𝓣ransitivity∁ = !
--     𝓣ransextensionality∁Proposequality .𝓣ransextensionality∁.⌶𝓣ransextensionality/ .𝓣ransextensionality/.transextensionality = congruity₂ _

-- module _ where

--   module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} where

--     instance

--       𝓡eflexivity∁Proposextensequality : 𝓡eflexivity∁ Proposextensequality⟦ 𝔓 ⟧
--       𝓡eflexivity∁.reflexivity 𝓡eflexivity∁Proposextensequality _ = ∅

--       𝓢ymmetry∁Proposextensequality : 𝓢ymmetry∁ Proposextensequality⟦ 𝔓 ⟧
--       𝓢ymmetry∁.symmetry 𝓢ymmetry∁Proposextensequality f₁≡̇f₂ x rewrite f₁≡̇f₂ x = ∅

--       𝓣ransitivity∁Proposextensequality : 𝓣ransitivity∁ Proposextensequality⟦ 𝔓 ⟧
--       𝓣ransitivity∁.transitivity 𝓣ransitivity∁Proposextensequality f₁≡̇f₂ f₂≡̇f₃ x rewrite f₁≡̇f₂ x = f₂≡̇f₃ x

--       IsEquivalence∁Proposextensequality : IsEquivalence∁ Proposextensequality⟦ 𝔓 ⟧
--       IsEquivalence∁.⌶𝓡eflexivity∁ IsEquivalence∁Proposextensequality = !
--       IsEquivalence∁.⌶𝓢ymmetry∁ IsEquivalence∁Proposextensequality = !
--       IsEquivalence∁.⌶𝓣ransitivity∁ IsEquivalence∁Proposextensequality = !

--       𝓒̇ongruity∁Proposextensequality : ∀ {a b} → 𝓒̇ongruity∁ a b Proposextensequality
--       𝓒̇ongruity∁.ċongruity 𝓒̇ongruity∁Proposextensequality _ f≡̇g x rewrite f≡̇g x = ∅

-- module _ where

--   module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) where

--     SetoidProposextensequality : Setoid _ _
--     Setoid.Object SetoidProposextensequality = _
--     Setoid.ObjectEquality SetoidProposextensequality = Proposextensequality⟦ 𝔓 ⟧

-- module _ where

--   module _
--     {a}
--     where

--     instance

--       𝓡eflexivity∁Function : 𝓡eflexivity∁ Function⟦ a ⟧
--       𝓡eflexivity∁.reflexivity 𝓡eflexivity∁Function = ¡

--       𝓣ransitivity∁Function : 𝓣ransitivity∁ Function⟦ a ⟧
--       𝓣ransitivity∁.transitivity 𝓣ransitivity∁Function f g = g ∘ f

-- module _ where

--   module _
--     {a} {A : Ø a} {b} {B : A → Ø b}
--     where

--     instance

--       𝓡eflexivity∁Extension : 𝓡eflexivity∁ (Extension B)
--       𝓡eflexivity∁.reflexivity 𝓡eflexivity∁Extension = ¡

--       𝓣ransitivity∁Extension : 𝓣ransitivity∁ (Extension B)
--       𝓣ransitivity∁.transitivity 𝓣ransitivity∁Extension f g = g ∘ f

--       𝓣ransassociativity/Extension : 𝓣ransassociativity/ (Extension B) Proposextensequality
--       𝓣ransassociativity/Extension .𝓣ransassociativity/.transassociativity _ _ _ _ = !

--       𝓣ransassociativity∁Extension = 𝓣ransassociativity∁ (Extension B) Proposextensequality ∋ record {}

--       𝓣ransextensionality/Extensional : 𝓣ransextensionality/ (Extension B) Proposextensequality
--       𝓣ransextensionality/Extensional .𝓣ransextensionality/.transextensionality {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = g₁≡̇g₂ (f₂ x)

--       𝓣ransextensionality∁Extensional = 𝓣ransextensionality∁ (Extension B) Proposextensequality ∋ record {}

--       𝓣ransleftidentity/Extension : 𝓣ransleftidentity/ (Extension B) Proposextensequality
--       𝓣ransleftidentity/Extension .𝓣ransleftidentity/.transleftidentity _ = !

--       𝓣ransleftidentity∁Extension = 𝓣ransleftidentity∁ (Extension B) Proposextensequality ∋ record {}

--       𝓣ransrightidentity/Extension : 𝓣ransrightidentity/ (Extension B) Proposextensequality
--       𝓣ransrightidentity/Extension .𝓣ransrightidentity/.transrightidentity _ = !

--       𝓣ransrightidentity∁Extension = 𝓣ransrightidentity∁ (Extension B) Proposextensequality ∋ record {}

--       IsPrecategory∁Extension = IsPrecategory∁ (Extension B) Proposextensequality ∋ record {}

--       IsCategory/Extension : IsCategory/ (Extension B) Proposextensequality
--       IsCategory/Extension = record {}

--       IsCategory∁Extension = IsCategory∁ (Extension B) Proposextensequality ∋ record {}

--   module _
--     {a} {A : Ø a} {b} (B : A → Ø b)
--     where

--     PrecategoryExtension' = Precategory _ _ _ ∋ record { Object = _ ; Arrow = Extension B ; ArrowEquivalent = Proposextensequality }

--     PrecategoryExtension : Precategory _ _ _
--     PrecategoryExtension .Precategory.Object = _
--     PrecategoryExtension .Precategory.Arrow = Extension B
--     PrecategoryExtension .Precategory.ArrowEquivalent = Proposextensequality

--     CategoryExtension : Category _ _ _
--     CategoryExtension .Category.Object = _
--     CategoryExtension .Category.Arrow = Extension B
--     CategoryExtension .Category.ArrowEquivalent = Proposextensequality

-- record Substitunction⌶ {𝔭} (𝔓 : Ø 𝔭) : Ø₀ where
--   no-eta-equality

--   open Substitunction 𝔓
--   open Term 𝔓

--   private

--     mutual

--       𝓶apSubstitunctionExtensionTerm : 𝓶ap/ Substitunction (Extension Term) ¡
--       𝓶apSubstitunctionExtensionTerm σ (i x) = σ x
--       𝓶apSubstitunctionExtensionTerm σ leaf = leaf
--       𝓶apSubstitunctionExtensionTerm σ (τ₁ fork τ₂) = 𝓶apSubstitunctionExtensionTerm σ τ₁ fork 𝓶apSubstitunctionExtensionTerm σ τ₂
--       𝓶apSubstitunctionExtensionTerm σ (function p τs) = function p (𝓶apSubstitunctionExtensionTerms σ τs)

--       𝓶apSubstitunctionExtensionTerms : ∀ {N} → 𝓶ap/ Substitunction (Extension $ Terms N) ¡
--       𝓶apSubstitunctionExtensionTerms σ ∅ = ∅
--       𝓶apSubstitunctionExtensionTerms σ (τ , τs) = 𝓶apSubstitunctionExtensionTerm σ τ , 𝓶apSubstitunctionExtensionTerms σ τs

--   instance

--     𝓜ap/SubstitunctionExtensionTerm : 𝓜ap/ Substitunction (Extension Term) ¡
--     𝓜ap/SubstitunctionExtensionTerm .𝓜ap/.map = 𝓶apSubstitunctionExtensionTerm

--     𝓜ap∁SubstitunctionExtensionTerm = 𝓜ap∁ Substitunction (Extension Term) ∋ record { μ = ¡ }

--     𝓜ap/SubstitunctionExtensionTerms : ∀ {N} → 𝓜ap/ Substitunction (Extension $ Terms N) ¡
--     𝓜ap/SubstitunctionExtensionTerms .𝓜ap/.map = 𝓶apSubstitunctionExtensionTerms

--     𝓜ap∁SubstitunctionExtensionTerms = λ {N} → 𝓜ap∁ Substitunction (Extension $ Terms N) ∋ record { μ = ¡ }

--     𝓣ransitivity∁Substitunction : 𝓣ransitivity∁ Substitunction
--     𝓣ransitivity∁Substitunction .𝓣ransitivity∁.transitivity f g = map g ∘ f

--   private

--     mutual

--       𝓶apextensionalitySubstitunctionExtensionTerm : 𝓶apextensionality/ Substitunction Proposextensequality (Extension Term) Proposextensequality
--       𝓶apextensionalitySubstitunctionExtensionTerm p (i x) = p x
--       𝓶apextensionalitySubstitunctionExtensionTerm p leaf = ∅
--       𝓶apextensionalitySubstitunctionExtensionTerm p (s fork t) = congruity₂ _fork_ (𝓶apextensionalitySubstitunctionExtensionTerm p s) (𝓶apextensionalitySubstitunctionExtensionTerm p t)
--       𝓶apextensionalitySubstitunctionExtensionTerm p (function fn ts) = congruity (function fn) (𝓶apextensionalitySubstitunctionExtensionTerms p ts)

--       𝓶apextensionalitySubstitunctionExtensionTerms : ∀ {N} → 𝓶apextensionality/ Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality
--       𝓶apextensionalitySubstitunctionExtensionTerms p ∅ = ∅
--       𝓶apextensionalitySubstitunctionExtensionTerms p (t , ts) = congruity₂ _,_ (𝓶apextensionalitySubstitunctionExtensionTerm p t) (𝓶apextensionalitySubstitunctionExtensionTerms p ts)

--   instance

--     𝓜apextensionality/SubstitunctionExtensionTerm : 𝓜apextensionality/ Substitunction Proposextensequality (Extension Term) Proposextensequality
--     𝓜apextensionality/SubstitunctionExtensionTerm .𝓜apextensionality/.mapextensionality = 𝓶apextensionalitySubstitunctionExtensionTerm

--     𝓜apextensionality∁SubstitunctionExtensionTerm = 𝓜apextensionality∁ Substitunction Proposextensequality (Extension Term) Proposextensequality ∋ record {}

--     𝓜apextensionality/SubstitunctionExtensionTerms : ∀ {N} → 𝓜apextensionality/ Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality
--     𝓜apextensionality/SubstitunctionExtensionTerms .𝓜apextensionality/.mapextensionality = 𝓶apextensionalitySubstitunctionExtensionTerms

--     𝓜apextensionality∁SubstitunctionExtensionTerms = λ {N} → 𝓜apextensionality∁ Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality ∋ record {}

--   private

--     mutual

--       𝓶aptranscommutativitySubstitunctionExtensionTerm : 𝓶aptranscommutativity/ Substitunction (Extension Term) Proposextensequality
--       𝓶aptranscommutativitySubstitunctionExtensionTerm _ _ (i _) = !
--       𝓶aptranscommutativitySubstitunctionExtensionTerm _ _ leaf = !
--       𝓶aptranscommutativitySubstitunctionExtensionTerm _ _ (τ₁ fork τ₂) = congruity₂ _fork_ (𝓶aptranscommutativitySubstitunctionExtensionTerm _ _ τ₁) (𝓶aptranscommutativitySubstitunctionExtensionTerm _ _ τ₂)
--       𝓶aptranscommutativitySubstitunctionExtensionTerm f g (function fn ts) = congruity (function fn) (𝓶aptranscommutativitySubstitunctionExtensionTerms f g ts)

--       𝓶aptranscommutativitySubstitunctionExtensionTerms : ∀ {N} → 𝓶aptranscommutativity/ Substitunction (Extension $ Terms N) Proposextensequality
--       𝓶aptranscommutativitySubstitunctionExtensionTerms _ _ ∅ = !
--       𝓶aptranscommutativitySubstitunctionExtensionTerms _ _ (τ , τs) = congruity₂ _,_ (𝓶aptranscommutativitySubstitunctionExtensionTerm _ _ τ) (𝓶aptranscommutativitySubstitunctionExtensionTerms _ _ τs)

--   instance

--     𝓜aptranscommutativity/SubstitunctionExtensionTerm : 𝓜aptranscommutativity/ Substitunction (Extension Term) Proposextensequality
--     𝓜aptranscommutativity/SubstitunctionExtensionTerm .𝓜aptranscommutativity/.maptranscommutativity = 𝓶aptranscommutativitySubstitunctionExtensionTerm

--     𝓜aptranscommutativity∁SubstitunctionExtensionTerm = 𝓜aptranscommutativity∁ Substitunction (Extension Term) Proposextensequality ∋ record {}

--     𝓜aptranscommutativity/SubstitunctionExtensionTerms : ∀ {N} → 𝓜aptranscommutativity/ Substitunction (Extension $ Terms N) Proposextensequality
--     𝓜aptranscommutativity/SubstitunctionExtensionTerms {N} .𝓜aptranscommutativity/.maptranscommutativity = 𝓶aptranscommutativitySubstitunctionExtensionTerms

--     𝓜aptranscommutativity∁SubstitunctionExtensionTerms = λ {N} → 𝓜aptranscommutativity∁ Substitunction (Extension $ Terms N) Proposextensequality ∋ record {}

--   instance

--     𝓣ransassociativity/Substitunction : 𝓣ransassociativity/ Substitunction Proposextensequality
--     𝓣ransassociativity/Substitunction .𝓣ransassociativity/.transassociativity f g h = maptranscommutativity g h ∘ f

--     𝓣ransassociativity∁Substitunction = 𝓣ransassociativity∁ Substitunction Proposextensequality ∋ record {}

--     𝓣ransextensionality/Substitunction : 𝓣ransextensionality/ Substitunction Proposextensequality
--     𝓣ransextensionality/Substitunction .𝓣ransextensionality/.transextensionality {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = mapextensionality g₁≡̇g₂ $ f₂ x

--     𝓣ransextensionality∁Substitunction = 𝓣ransextensionality∁ Substitunction Proposextensequality ∋ record {}

--     IsPrecategory∁Substitunction = IsPrecategory∁ Substitunction Proposextensequality ∋ record {}

--   PrecategorySubstitunction = Precategory _ _ _ ∋ record { Object = _ ; Arrow = Substitunction ; ArrowEquivalent = Proposextensequality }

--   instance

--     IsPrefunctor∁SubstitunctionExtensionTerm = IsPrefunctor∁ Substitunction Proposextensequality (Extension Term) Proposextensequality ∋ record {}
--     IsPrefunctor∁SubstitunctionExtensionTerms = λ {N} → IsPrefunctor∁ Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality ∋ record {}

--   PrefunctorSubstitunctionExtensionTerm : Prefunctor _ _ _ _ _ _
--   PrefunctorSubstitunctionExtensionTerm .Prefunctor.Object₁ = _
--   PrefunctorSubstitunctionExtensionTerm .Prefunctor.Arrow₁ = Substitunction
--   PrefunctorSubstitunctionExtensionTerm .Prefunctor.ArrowEquivalent₁ = Proposextensequality
--   PrefunctorSubstitunctionExtensionTerm .Prefunctor.Object₂ = _
--   PrefunctorSubstitunctionExtensionTerm .Prefunctor.Arrow₂ = Extension Term
--   PrefunctorSubstitunctionExtensionTerm .Prefunctor.ArrowEquivalent₂ = Proposextensequality

--   PrefunctorSubstitunctionExtensionTerms : ¶ → Prefunctor _ _ _ _ _ _
--   PrefunctorSubstitunctionExtensionTerms _ .Prefunctor.Object₁ = _
--   PrefunctorSubstitunctionExtensionTerms _ .Prefunctor.Arrow₁ = Substitunction
--   PrefunctorSubstitunctionExtensionTerms _ .Prefunctor.ArrowEquivalent₁ = Proposextensequality
--   PrefunctorSubstitunctionExtensionTerms _ .Prefunctor.Object₂ = _
--   PrefunctorSubstitunctionExtensionTerms N .Prefunctor.Arrow₂ = Extension $ Terms N
--   PrefunctorSubstitunctionExtensionTerms _ .Prefunctor.ArrowEquivalent₂ = Proposextensequality

--   instance

--     𝓡eflexivity∁Substitunction : 𝓡eflexivity∁ Substitunction
--     𝓡eflexivity∁Substitunction .𝓡eflexivity∁.reflexivity = i

-- -- -- -- -- -- -- -- -- -- -- --   private

-- -- -- -- -- -- -- -- -- -- -- --     mutual

-- -- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerm : 𝓲dentity Substitunction (Extension Term) _ ¡
-- -- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerm (i x) = ∅
-- -- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerm leaf = ∅
-- -- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerm (s fork t) = congruity₂ _fork_ (𝓲dentitySubstitunctionExtensionTerm s) (𝓲dentitySubstitunctionExtensionTerm t)
-- -- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerm (function fn ts) = congruity (function fn) (𝓲dentitySubstitunctionExtensionTerms ts)

-- -- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerms : ∀ {N} → 𝓲dentity Substitunction (Extension $ Terms N) _ ¡
-- -- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerms ∅ = ∅
-- -- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerms (t , ts) = congruity₂ _,_ (𝓲dentitySubstitunctionExtensionTerm t) (𝓲dentitySubstitunctionExtensionTerms ts)

-- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- --     Identity!SubstitunctionExtensionTerm : Identity! Substitunction (Extension Term) _ ¡
-- -- -- -- -- -- -- -- -- -- -- --     Identity!.identity! Identity!SubstitunctionExtensionTerm = {!!} -- 𝓲dentitySubstitunctionExtensionTerm

-- -- -- -- -- -- -- -- -- -- -- --     Identity!SubstitunctionExtensionTerms : ∀ {N} → Identity! Substitunction (Extension $ Terms N) _ ¡
-- -- -- -- -- -- -- -- -- -- -- --     Identity!.identity! Identity!SubstitunctionExtensionTerms = {!!} -- 𝓲dentitySubstitunctionExtensionTerms

-- -- -- -- -- -- -- -- -- -- -- --     Identity?SubstitunctionExtensionTerm : Identity? Substitunction (Extension Term) _ ¡
-- -- -- -- -- -- -- -- -- -- -- --     Identity?.identity? Identity?SubstitunctionExtensionTerm = 𝓲dentitySubstitunctionExtensionTerm

-- -- -- -- -- -- -- -- -- -- -- --     Identity?SubstitunctionExtensionTerms : ∀ {N} → Identity? Substitunction (Extension $ Terms N) _ ¡
-- -- -- -- -- -- -- -- -- -- -- --     Identity?.identity? Identity?SubstitunctionExtensionTerms = 𝓲dentitySubstitunctionExtensionTerms

-- -- -- -- -- -- -- -- -- -- -- --     LeftIdentity!Substitunction : LeftIdentity! Substitunction _
-- -- -- -- -- -- -- -- -- -- -- --     LeftIdentity!.left-identity! LeftIdentity!Substitunction f x = ((Term _ → Proposequality (𝓶apSubstitunctionExtensionTerm i (f x)) (f x)) ∋ identity?) (f x) -- {!{!identity!!} ∘ f!}
-- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- --     IdentitySubstitunctionExtensionTerm : Identity Substitunction (Extension Term) _ ¡
-- -- -- -- -- -- -- -- -- -- -- --     Identity′.identity IdentitySubstitunctionExtensionTerm = 𝓲dentitySubstitunctionExtensionTerm

-- -- -- -- -- -- -- -- -- -- -- --     IdentitySubstitunctionExtensionTerms : ∀ {N} → Identity Substitunction (Extension $ Terms N) _ ¡
-- -- -- -- -- -- -- -- -- -- -- --     Identity′.identity IdentitySubstitunctionExtensionTerms = 𝓲dentitySubstitunctionExtensionTerms

-- -- -- -- -- -- -- -- -- -- -- --     LeftIdentitySubstitunction : LeftIdentity Substitunction _
-- -- -- -- -- -- -- -- -- -- -- --     LeftIdentity.left-identity LeftIdentitySubstitunction f = identity ∘ f

-- -- -- -- -- -- -- -- -- -- -- --     RightIdentitySubstitunction : RightIdentity Substitunction _
-- -- -- -- -- -- -- -- -- -- -- --     RightIdentity.right-identity RightIdentitySubstitunction _ _ = ∅

-- -- -- -- -- -- -- -- -- -- -- --     IsCategorySubstitunction : IsCategory Substitunction _
-- -- -- -- -- -- -- -- -- -- -- --     IsCategorySubstitunction = record {}

-- -- -- -- -- -- -- -- -- -- -- --     IsFunctorSubstitunctionExtensionTerm : IsFunctor Substitunction _ (Extension Term) _ ¡
-- -- -- -- -- -- -- -- -- -- -- --     IsFunctorSubstitunctionExtensionTerm = record {}

-- -- -- -- -- -- -- -- -- -- -- --     IsFunctorSubstitunctionExtensionTerms : ∀ {N} → IsFunctor Substitunction _ (Extension $ Terms N) _ ¡
-- -- -- -- -- -- -- -- -- -- -- --     IsFunctorSubstitunctionExtensionTerms = record {}

-- -- -- -- -- -- -- -- -- -- -- -- module SubstitunctionØ {𝔭} (𝔓 : Ø 𝔭) where

-- -- -- -- -- -- -- -- -- -- -- --   open Substitunction 𝔓
-- -- -- -- -- -- -- -- -- -- -- --   open Term 𝔓

-- -- -- -- -- -- -- -- -- -- -- --   open Substitunction⌶ (Substitunction⌶ 𝔓 ∋ record {})

-- -- -- -- -- -- -- -- -- -- -- --   SemigroupoidSubstitunction : Semigroupoid _ _ _
-- -- -- -- -- -- -- -- -- -- -- --   Semigroupoid.Object SemigroupoidSubstitunction = _
-- -- -- -- -- -- -- -- -- -- -- --   Semigroupoid.Morphism SemigroupoidSubstitunction = Substitunction

-- -- -- -- -- -- -- -- -- -- -- --   SemifunctorSubstitunctionExtensionTerm : Semifunctor _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- --   Semifunctor.Object₁ SemifunctorSubstitunctionExtensionTerm = _
-- -- -- -- -- -- -- -- -- -- -- --   Semifunctor.Morphism₁ SemifunctorSubstitunctionExtensionTerm = Substitunction
-- -- -- -- -- -- -- -- -- -- -- --   Semifunctor.Object₂ SemifunctorSubstitunctionExtensionTerm = _
-- -- -- -- -- -- -- -- -- -- -- --   Semifunctor.Morphism₂ SemifunctorSubstitunctionExtensionTerm = Extension Term
-- -- -- -- -- -- -- -- -- -- -- --   Semifunctor.μ SemifunctorSubstitunctionExtensionTerm = ¡

-- -- -- -- -- -- -- -- -- -- -- --   CategorySubstitunction : Category _ _ _
-- -- -- -- -- -- -- -- -- -- -- --   Category.Object CategorySubstitunction = _
-- -- -- -- -- -- -- -- -- -- -- --   Category.Morphism CategorySubstitunction = Substitunction

-- -- -- -- -- -- -- -- -- -- -- --   FunctorSubstitunctionExtensionTerm : Functor _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- --   Functor.Object₁ FunctorSubstitunctionExtensionTerm = _
-- -- -- -- -- -- -- -- -- -- -- --   Functor.Morphism₁ FunctorSubstitunctionExtensionTerm = Substitunction
-- -- -- -- -- -- -- -- -- -- -- --   Functor.Object₂ FunctorSubstitunctionExtensionTerm = _
-- -- -- -- -- -- -- -- -- -- -- --   Functor.Morphism₂ FunctorSubstitunctionExtensionTerm = Extension Term
-- -- -- -- -- -- -- -- -- -- -- --   Functor.μ FunctorSubstitunctionExtensionTerm = ¡

-- -- -- -- -- -- -- -- -- -- -- --   module _ (N : ¶) where

-- -- -- -- -- -- -- -- -- -- -- --     FunctorSubstitunctionExtensionTerms : Functor _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- --     Functor.Object₁ FunctorSubstitunctionExtensionTerms = _
-- -- -- -- -- -- -- -- -- -- -- --     Functor.Morphism₁ FunctorSubstitunctionExtensionTerms = Substitunction
-- -- -- -- -- -- -- -- -- -- -- --     Functor.Object₂ FunctorSubstitunctionExtensionTerms = _
-- -- -- -- -- -- -- -- -- -- -- --     Functor.Morphism₂ FunctorSubstitunctionExtensionTerms = Extension $ Terms N
-- -- -- -- -- -- -- -- -- -- -- --     Functor.μ FunctorSubstitunctionExtensionTerms = ¡

-- -- -- -- -- -- -- -- -- -- -- -- open SubstitunctionØ public

-- -- -- -- -- -- -- -- -- -- -- -- module AList⌶ {a} {A : Nat → Set a} where

-- -- -- -- -- -- -- -- -- -- -- --   private AList = Descender⟨ A ⟩

-- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- --     Reflexivity⌶AList : Reflexivity AList
-- -- -- -- -- -- -- -- -- -- -- --     Reflexivity.reflexivity Reflexivity⌶AList = ∅

-- -- -- -- -- -- -- -- -- -- -- --     Transitivity⌶AList : Transitivity AList
-- -- -- -- -- -- -- -- -- -- -- --     Contiguity.contiguity Transitivity⌶AList f ∅ = f
-- -- -- -- -- -- -- -- -- -- -- --     Contiguity.contiguity Transitivity⌶AList f (x , g) = x , contiguity f g

-- -- -- -- -- -- -- -- -- -- -- --     MorphismEquivalence⌶AList : MorphismEquivalence AList _
-- -- -- -- -- -- -- -- -- -- -- --     MorphismEquivalence.morphismEquivalence MorphismEquivalence⌶AList = Proposequality

-- -- -- -- -- -- -- -- -- -- -- --     Associativity⌶AList : Associativity AList _
-- -- -- -- -- -- -- -- -- -- -- --     Associativity.associativity Associativity⌶AList _ _ ∅ = ∅
-- -- -- -- -- -- -- -- -- -- -- --     Associativity.associativity Associativity⌶AList f g (x , h) = congruity (x ,_) $ associativity f g h

-- -- -- -- -- -- -- -- -- -- -- --     IsSemigroupoid⌶AList : IsSemigroupoid AList _
-- -- -- -- -- -- -- -- -- -- -- --     IsSemigroupoid⌶AList = record {}

-- -- -- -- -- -- -- -- -- -- -- --     LeftIdentity⌶AList : LeftIdentity AList _
-- -- -- -- -- -- -- -- -- -- -- --     LeftIdentity.left-identity LeftIdentity⌶AList _ = ∅

-- -- -- -- -- -- -- -- -- -- -- --     RightIdentity⌶AList : RightIdentity AList _
-- -- -- -- -- -- -- -- -- -- -- --     RightIdentity.right-identity RightIdentity⌶AList ∅ = ∅
-- -- -- -- -- -- -- -- -- -- -- --     RightIdentity.right-identity RightIdentity⌶AList (x , f) = congruity (x ,_) $ right-identity f

-- -- -- -- -- -- -- -- -- -- -- --     IsCategory⌶AList : IsCategory AList _
-- -- -- -- -- -- -- -- -- -- -- --     IsCategory⌶AList = record {}

-- -- -- -- -- -- -- -- -- -- -- -- module Substitist⌶ {𝔭} {𝔓 : Ø 𝔭} where

-- -- -- -- -- -- -- -- -- -- -- --   open Substitunction 𝔓
-- -- -- -- -- -- -- -- -- -- -- --   open Term 𝔓
-- -- -- -- -- -- -- -- -- -- -- --   open Substitist 𝔓
-- -- -- -- -- -- -- -- -- -- -- --   open Substitunction⌶ (Substitunction⌶ 𝔓 ∋ record {})

-- -- -- -- -- -- -- -- -- -- -- --   postulate
-- -- -- -- -- -- -- -- -- -- -- --     _for_ : ∀ {n} (t' : Term n) (x : Fin (↑ n)) -> Fin (↑ n) -> Term n

-- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- --     Map⌶Substitist,Substitunction : Map Substitist Substitunction
-- -- -- -- -- -- -- -- -- -- -- --     Map.map Map⌶Substitist,Substitunction ∅ = i
-- -- -- -- -- -- -- -- -- -- -- --     Map.map Map⌶Substitist,Substitunction ((x , t) , σ) = map σ ∙ (t for x)

-- -- -- -- -- -- -- -- -- -- -- -- module Fin⌶ where

-- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- --     Map⌶Maybe : ∀ {x} → Map {A = Ø x} (λ x y → x → y) (λ x y → Maybe x → Maybe y)
-- -- -- -- -- -- -- -- -- -- -- --     Map.map Map⌶Maybe f ∅ = ∅
-- -- -- -- -- -- -- -- -- -- -- --     Map.map Map⌶Maybe f (↑ x) = ↑ (f x)

-- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- --     Successor₀⌶¶ : Successor₀ ¶
-- -- -- -- -- -- -- -- -- -- -- --     Successor₀.⇑₀ Successor₀⌶¶ = ↑_

-- -- -- -- -- -- -- -- -- -- -- --     Principal₁Fin : Principal₁ Fin
-- -- -- -- -- -- -- -- -- -- -- --     Principal₁Fin = record {}

-- -- -- -- -- -- -- -- -- -- -- --     Successor₁⌶Fin : Successor₁ Fin
-- -- -- -- -- -- -- -- -- -- -- --     Successor₁.⇑₁ Successor₁⌶Fin = ↑_

-- -- -- -- -- -- -- -- -- -- -- --     Thin⌶Fin,Fin : Thin Fin Fin
-- -- -- -- -- -- -- -- -- -- -- --     Thin.thin Thin⌶Fin,Fin ∅ = ↑_
-- -- -- -- -- -- -- -- -- -- -- --     Thin.thin Thin⌶Fin,Fin (↑ x) ∅ = ∅
-- -- -- -- -- -- -- -- -- -- -- --     Thin.thin Thin⌶Fin,Fin (↑ x) (↑ y) = ↑ (thin x y)

-- -- -- -- -- -- -- -- -- -- -- --     Equivalence⌶Fin : ∀ {n} → Equivalence (Fin n) ∅̂
-- -- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶Fin = Proposequality

-- -- -- -- -- -- -- -- -- -- -- --     Equivalence⌶¶ : Equivalence ¶ ∅̂
-- -- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶¶ = Proposequality

-- -- -- -- -- -- -- -- -- -- -- --     pattern Fin↑ n = ¶⟨<_⟩.↑_ {n = n}

-- -- -- -- -- -- -- -- -- -- -- --     Injectivity₀⌶¶↑ : Injectivity₀ ¶.↑_ ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- --     Injectivity₀⌶¶↑ = {!!}

-- -- -- -- -- -- -- -- -- -- -- --     Injectivity₀⌶Fin↑ : ∀ {n} → Injectivity₀ (Fin↑ n) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- --     Injectivity₀.injectivity₀ (Injectivity₀⌶Fin↑ {n}) = {!!}

-- -- -- -- -- -- -- -- -- -- -- --     Injectivity₁⌶Fin↑ : Injectivity₁ Fin↑ ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- --     Injectivity₁.injectivity₁ Injectivity₁⌶Fin↑ = {!!}

-- -- -- -- -- -- -- -- -- -- -- --     Injectivity!⌶Fin↑ : Injectivity? Fin↑ ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- --     Injectivity!.injectivity! Injectivity!⌶Fin↑ = {!!}

-- -- -- -- -- -- -- -- -- -- -- --     Injectivity₁⌶ThinFin : ∀ {m} → Injectivity₁ (thin {A = Fin} {B = Fin} {m = m}) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- --     Injectivity₁.injectivity₁ (Injectivity₁⌶ThinFin {m}) (∅ {n = .m}) {x} {y} x₁ = injectivity₁[ Fin↑ ] _ x₁
-- -- -- -- -- -- -- -- -- -- -- --     Injectivity₁.injectivity₁ (Injectivity₁⌶ThinFin {m}) (↑_ {n = .m} w) {x} {y} x₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- --     Injectivity!⌶ThinFin : ∀ {m} → Injectivity? (thin {A = Fin} {B = Fin} {m = m}) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- --     Injectivity!.injectivity! (Injectivity!⌶ThinFin {m}) (∅ {n = .m}) {x} {y} x₁ = injectivity?[ Fin↑ ] _ x₁
-- -- -- -- -- -- -- -- -- -- -- --     Injectivity!.injectivity! (Injectivity!⌶ThinFin {m}) (↑_ {n = .m} w) {x} {y} x₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- --     Injectivity₂⌶ThinFin : ∀ {m} → Injectivity₂ (thin {A = Fin} {B = Fin} {m = m}) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- --     Injectivity₂.injectivity₂ (Injectivity₂⌶ThinFin {m}) (∅ {n = .m}) {x} {y} x₁ = injectivity₀[ Fin↑ m ] x₁
-- -- -- -- -- -- -- -- -- -- -- --     Injectivity₂.injectivity₂ (Injectivity₂⌶ThinFin {m}) (↑_ {n = .m} w) {x} {y} x₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective : ∀ {m} (x : Fin (↑ m)) {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective x eq = injectivity₂[ thin[ Fin ] ] x eq

-- -- -- -- -- -- -- -- -- -- -- --   -- injectivity₂[ thin[ Fin ] ] x eq
-- -- -- -- -- -- -- -- -- -- -- --   -- injectivity₁[ thin[ Fin ] ] x eq

-- -- -- -- -- -- -- -- -- -- -- --     -- ∀ {n} → Injectivity₁ (thin {A = Fin} {B = Fin} {m = n}) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- --     -- Injectivity₁⌶ThinFin = ?


-- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity₁.injectivity₁ (Injectivity₁⌶ThinFin {n}) (∅ {n = .n}) {x} {y} eq = injectivity![ (λ n → ¶⟨<_⟩.↑_ {n = n}) ] _ _ _ eq
-- -- -- -- -- -- -- -- -- -- -- -- --       -- injectivity₁⋆[ (λ {n} → ¶⟨<_⟩.↑_ {n}) ] eq -- injectivity₀[ ¶⟨<_⟩.↑_ {n = n} ] eq
-- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity₁.injectivity₁ (Injectivity₁⌶ThinFin {n}) (↑_ {n = .n} w) {x} {y} eq = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     InjThinFin : ∀ {m} {x : Fin (↑ m)} → INJ (thin[ Fin ] x) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     INJ.inj (InjThinFin {m} {∅ {n = .m}}) {x} {y} = INj (¶⟨<_⟩.↑_ {m}) ⦃ it ⦄ ⦃ it ⦄ ⦃ {!InjThinFin {m = m} {x = ∅}!} ⦄ {x} {y}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     INJ.inj (InjThinFin {m} {↑_ {n = .m} x}) {x₁} {y} = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective : ∀ {m} {x : Fin (↑ m)} {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective {m = m} {x = x} eq = INj2 (thin {A = Fin} {B = Fin}) {w = x} eq -- INj2 (thin[ Fin ]) {w = x} eq -- INj2 (thin {A = Fin} {B = Fin}) eq

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective2 : ∀ {m} {x : Fin (↑ m)} {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective2 {x = x} = test-thin-injective {x = x}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity⌶↑¶ : Injectivity ¶.↑_ ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity.injectivity Injectivity⌶↑¶ ∅ = ∅

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity⌶↑Fin : ∀ {n} → Injectivity {A = ¶⟨< n ⟩} {B = ¶⟨< ↑ n ⟩} ¶⟨<_⟩.↑_ ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity.injectivity (Injectivity⌶↑Fin {n}) {x} {.x} ∅ = ∅

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Injectivity⌶ThinFin : ∀ {m} {x : Fin (⇑₀ m)} → Injectivity (thin[ Fin ] x) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Injectivity.injectivity (Injectivity⌶ThinFin {m = m} {x = ∅}) e = injectivity {B = Fin (↑ m)} {f = ↑_ {n = m}} e -- injectivity {B = Fin m} {f = ↑_ {n = _}} e -- injectivity {f = ¶⟨<_⟩.↑_ {n = _}} ⦃ r = {!!} ⦄ {!e!} -- injectivity {f = ¶⟨<_⟩.↑_} e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       -- injectivity[ ¶⟨<_⟩.↑_ ] ⦃ e1 = ! ⦄ ⦃ e2 = Equivalence⌶Fin ⦄ ⦃ i1 = Injectivity⌶↑Fin ⦄ e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       -- injectivity[ ¶.↑_ ] e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Injectivity.injectivity (Injectivity⌶ThinFin {.(↑ _)} {↑_ {n = .(↑ n)} x}) {∅ {n = n}} {y} x₂ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Injectivity.injectivity (Injectivity⌶ThinFin {.(↑ _)} {↑_ {n = .(↑ n)} x}) {↑_ {n = n} x₁} {y} x₂ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective⌶Fin,Fin : ThinInjective Fin Fin ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective.iInjectivity ThinInjective⌶Fin,Fin {m} {x} = Injectivity⌶ThinFin {m} {x} -- Injectivity⌶ThinFin

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective : ∀ {m} {x : Fin (↑ m)} {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective {x = x} = thin-injective {B = Fin} { x = x }

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance I1 = Injectivity⌶ThinFin

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective' : ∀ {m} {x : Fin (↑ m)} {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective' {m} {x = x} eq = injectivity {A = Fin m} {B = Fin (↑ m)} {f = thin {A = Fin} {B = λ v → Fin v} x} ⦃ r = I1 {m} {{!!}} ⦄ eq --

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     InjectivityP⌶Fin : ∀ {m} {x : Fin m} → InjectivityP (¶⟨<_⟩.↑_ {n = m})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     InjectivityP.injectivityP (InjectivityP⌶Fin {m} {x}) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     InjectivityP⌶ThinFin : ∀ {m} {x : Fin (⇑₀ m)} → InjectivityP (thin[ Fin ] x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     InjectivityP.injectivityP (InjectivityP⌶ThinFin {m} {∅ {n = .m}}) {x} {y} x₂ = injectivityP x₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     InjectivityP.injectivityP (InjectivityP⌶ThinFin {m} {↑_ {n = .m} x}) {x₁} {y} x₂ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-fin-injective : ∀ {m} {y₁ y₂ : Fin m} → ¶⟨<_⟩.↑ y₁ ≋ ↑ y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-fin-injective {m} = injectivity {f = λ v → ¶⟨<_⟩.↑_ {m} v}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective⌶Fin,Fin : ThinInjective Fin Fin ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ∅} e = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ↑ x} {∅} {∅} _ = ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ↑ x} {∅} {↑ _} ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ↑ x} {↑ _} {∅} ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ↑ x} {↑ y₁} {↑ y₂} = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Thick⌶Fin,Fin : Thick Fin Fin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Thick.thick Thick⌶Fin,Fin = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickThinId⌶Fin,Fin : ThickThinId Fin Fin ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickThinId.thick∘thin=id ThickThinId⌶Fin,Fin = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Maybe*⌶ : ∀ {a} → Maybe* a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Maybe*.Maybe Maybe*⌶ = Maybe
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Maybe*.just Maybe*⌶ = ↑_

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Check⌶Fin,Fin : Check Fin Fin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin ∅ ∅ = ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin ∅ (↑ y) = ↑ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin {∅} (↑ ()) _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin {↑ _} (↑ x) ∅ = ↑ ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin {↑ _} (↑ x) (↑ y) = map ¶⟨<_⟩.↑_ $ check x y

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence⌶Maybe : ∀ {a} {A : Ø a} {ℓ} ⦃ _ : Equivalence A ℓ ⦄ → Equivalence (Maybe A) ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶Maybe ∅ ∅ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶Maybe ∅ (↑ x₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶Maybe (↑ x₁) ∅ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶Maybe (↑ x₁) (↑ x₂) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.⌶IsSetoid Equivalence⌶Maybe = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence⌶MaybeFin : ∀ {n} → Equivalence (Maybe (Fin n)) ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶MaybeFin = Proposequality

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinCheckId⌶Fin,Fin : ThinCheckId Fin Fin ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinCheckId.thin-check-id ThinCheckId⌶Fin,Fin x y y' x₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin⌶FinFin : ThickAndThin Fin Fin ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin⌶FinFin = record {}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   module _ {𝔭} {𝔓 : Ø 𝔭} where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     open Term 𝔓

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Principal₁⌶Term : Principal₁ Term
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Principal₁⌶Term = record {}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     private

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       mutual

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm : 𝓶ap (Extension Fin) (Extension Term)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm f (i x) = i (f x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm f leaf = leaf
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm f (t1 fork t2) = (𝓶ap⌶ExtensionFin,ExtensionTerm f t1) fork 𝓶ap⌶ExtensionFin,ExtensionTerm f t2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm f (function F ts) = function F (𝓶ap⌶ExtensionFin,ExtensionTerms f ts)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerms : ∀ {N} → 𝓶ap (Extension Fin) (Extension (Terms N))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerms f ∅ = ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerms f (t , ts) = 𝓶ap⌶ExtensionFin,ExtensionTerm f t , 𝓶ap⌶ExtensionFin,ExtensionTerms f ts

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Map⌶ExtensionFin,ExtensionTerm : Map (Extension Fin) (Extension Term)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Map.map Map⌶ExtensionFin,ExtensionTerm = 𝓶ap⌶ExtensionFin,ExtensionTerm

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Map⌶ExtensionFin,ExtensionTerms : ∀ {N} → Map (Extension Fin) (Extension (Terms N))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Map.map Map⌶ExtensionFin,ExtensionTerms = 𝓶ap⌶ExtensionFin,ExtensionTerms

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Thin⌶Fin,Term : Thin Fin Term
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Thin.thin Thin⌶Fin,Term = map ∘ thin

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Equivalence⌶Term : ∀ {n} → Equivalence (Term n) ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Equivalence.equivalence Equivalence⌶Term = Proposequality

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Injectivity⌶ASD : Injectivity

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ThinInjective⌶Fin,Term : ThinInjective Fin Term ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ThinInjective.thin-injective ThinInjective⌶Fin,Term = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Successor₀⌶¶ : Upper Fin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Upper.up Upper⌶Fin = ↑_

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin⌶Fin : ThickAndThin Fin Fin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Fin ∅ y = ↑ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Fin (↑ x) ∅ = ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Fin (↑ x) (↑ y) = ↑ thin x y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin-injective ThickAndThin⌶Fin x x₁ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thick ThickAndThin⌶Fin = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thick∘thin=id ThickAndThin⌶Fin = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.check ThickAndThin⌶Fin = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin-check-id ThickAndThin⌶Fin = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module Term⌶ {𝔭} {𝔓 : Ø 𝔭} where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Term 𝔓

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin⌶Term : ThickAndThin Term
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Term x (i x₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Term x leaf = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Term x (x₁ fork x₂) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Term x (function x₁ x₂) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin-injective ThickAndThin⌶Term = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thick ThickAndThin⌶Term = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thick∘thin=id ThickAndThin⌶Term = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.check ThickAndThin⌶Term = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin-check-id ThickAndThin⌶Term = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Data
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Nat
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ≤↓List -- m ≤ n, n-1...m
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Substitunction
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Substitist
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Record
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Product
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Functor
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Class
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Reflexivity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   IsFunctor
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ThickAndThin

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
















-- -- -- open import Oscar.Data

-- -- -- module _ where

-- -- --   module _ {𝔬} {𝔒 : Ø 𝔬} where

-- -- --     instance

-- -- --       𝓡eflexivity∁Proposequality : 𝓡eflexivity∁ Proposequality⟦ 𝔒 ⟧
-- -- --       𝓡eflexivity∁Proposequality .𝓡eflexivity∁.reflexivity = !

-- -- --       𝓢ymmetry∁Proposequality : 𝓢ymmetry∁ Proposequality⟦ 𝔒 ⟧
-- -- --       𝓢ymmetry∁Proposequality .𝓢ymmetry∁.symmetry ∅ = !

-- -- --       𝓣ransitivity∁Proposequality : 𝓣ransitivity∁ Proposequality⟦ 𝔒 ⟧
-- -- --       𝓣ransitivity∁Proposequality .𝓣ransitivity∁.transitivity ∅ = ¡

-- -- --       IsEquivalence∁Proposequality : IsEquivalence∁ Proposequality⟦ 𝔒 ⟧
-- -- --       IsEquivalence∁Proposequality .IsEquivalence∁.isReflexive = !
-- -- --       IsEquivalence∁Proposequality .IsEquivalence∁.isSymmetric = !
-- -- --       IsEquivalence∁Proposequality .IsEquivalence∁.isTransitive = !

-- -- -- -- open import Oscar.Data using (_≡_{-; ∅-})

-- -- -- {-
-- -- -- transport : ∀ {a b} {A : Set a} (B : A → Set b) {x y} → x ≡ y → B x → B y
-- -- -- transport _ ∅ = ¡

-- -- -- transport₂ : ∀ {a b c} {A : Set a} {B : Set b} (C : A → B → Set c) {x₁ x₂ y₁ y₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → C x₁ y₁ → C x₂ y₂
-- -- -- transport₂ C refl refl cxy = cxy
-- -- -- -}


-- -- -- -- {-
-- -- -- --   instance ⌶𝓘njectivity∁ : ∀ {m : X} {x : A (⇑₀ m)} → 𝓘njectivity∁ (B m) (B (⇑₀ m)) _≈B_ _≈B_
-- -- -- --   ⌶𝓘njectivity∁ {_} {x} = record { f = thin x }
-- -- -- -- -}

-- -- -- --   postulate

-- -- -- --     X : Set
-- -- -- --     X' : Set
-- -- -- --     A : X → Set
-- -- -- --     A' : X → Set
-- -- -- --     B : X → Set
-- -- -- --     E? : Set → Set
-- -- -- --     _≈B_ : ∀ {x} → B x → B x → Set
-- -- -- --     _≈E?_ : ∀ {A : Set} → E? A → E? A → Set
-- -- -- --     just : ∀ {x} → B x → E? (B x)
-- -- -- --     foo : ∀ {m} →
-- -- -- --       A (magic {∅̂} {X → X} m) → B m → B (magic {∅̂} {X → X} m)

-- -- -- --   instance

-- -- -- --     ⌶Thickandthin : Thickandthin _ _ _ _ _ _
-- -- -- --     ⌶Thickandthin = ?

-- -- -- --     ⌶Thickandthin' : Thickandthin _ _ _ _ _ _
-- -- -- --     ⌶Thickandthin' = ?

-- -- -- --   instance

-- -- -- -- --    ⌶𝓢uccessor₀∁X : 𝓢uccessor₀∁ X
-- -- -- -- --    ⌶𝓢uccessor₀∁X .𝓢uccessor₀∁.successor₀ = magic

-- -- -- --     ⌶𝓢uccessor₀∁X' : 𝓢uccessor₀∁ X'
-- -- -- --     ⌶𝓢uccessor₀∁X' .𝓢uccessor₀∁.successor₀ = magic

-- -- -- --   test' : ∀ {m : X} → A' (⇑₀ ⦃ {!Thickandthin.⌶𝓢uccessor₀∁ ⌶Thickandthin!} ⦄ m)
-- -- -- --   test' = {!!}

-- -- -- -- --   test-thin : ∀ {m : X} → A (⇑₀ m) → B m → B (⇑₀ m)
-- -- -- -- --   test-thin = thin

-- -- -- -- --   test-injectivity : ∀ {m : X} {z : A (⇑₀ m)} → ∀ {x y} → thin z x ≈B thin z y → x ≈B y
-- -- -- -- --   test-injectivity = injectivity

-- -- -- -- -- -- record FMap {x} {y} (F : Ø x → Ø y) : Ø (↑̂ x) ∙̂ y where
-- -- -- -- -- --   field fmap : ∀ {A B : Ø x} → (A → B) → F A → F B

-- -- --       -- EqualityExtension : ∀ {x y : A} → Equality (Extension B x y) _
-- -- --       -- EqualityExtension .Equality._≋_ = Proposextensequality
-- -- --       -- EqualityExtension .Equality.isEquivalence = it

-- -- --     EqualitySubstitunction : ∀ {x y} → Equality (Substitunction x y) _
-- -- --     EqualitySubstitunction {x} {y} .Equality._≋_ = Proposextensequality
-- -- --     EqualitySubstitunction {x} {y} .Equality.isEquivalence = it

-- -- --     EqualityExtensionTerm : ∀ {x y} → Equality (Extension Term x y) _
-- -- --     EqualityExtensionTerm .Equality._≋_ = Proposextensequality
-- -- --     EqualityExtensionTerm .Equality.isEquivalence = it

-- -- --     EqualityExtensionTerms : ∀ {N x y} → Equality (Extension (Terms N) x y) _
-- -- --     EqualityExtensionTerms .Equality._≋_ = Proposextensequality
-- -- --     EqualityExtensionTerms .Equality.isEquivalence = it
