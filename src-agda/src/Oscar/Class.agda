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

    infix 4 ≈-syntax
    ≈-syntax : ∀ {𝔬} (𝔒 : Ø 𝔬) {ℓ} ⦃ _ : HasEquivalence 𝔒 ℓ ⦄ → 𝔒 → 𝔒 → Ø ℓ
    ≈-syntax _ = _≈_
    syntax ≈-syntax 𝔒 x y = x ≈[ 𝔒 ] y

module _ where

  record Properthing {𝔬} ℓ (𝔒 : Ø 𝔬) : Ø 𝔬 ∙̂ ↑̂ ℓ where
    field
      ➊ : 𝔒
      _∧_ : 𝔒 → 𝔒 → 𝔒
      ⦃ ⌶HasEquivalence ⦄ : HasEquivalence 𝔒 ℓ
      Nothing : 𝔒 → Ø ℓ
      fact2 : ∀ {P Q} → P ≈ Q → Nothing P → Nothing Q

  open Properthing ⦃ … ⦄ public
