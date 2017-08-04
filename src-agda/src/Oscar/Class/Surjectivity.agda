
open import Oscar.Prelude
open import Oscar.Class.Surjection using (𝓼urjection; 𝓢urjection; surjection)
open import Oscar.Data.Proposequality

module Oscar.Class.Surjectivity where

private

  module _
    {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
    where
    module Visible
      (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
      (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
      (μ : 𝓼urjection 𝔒₁ 𝔒₂)
      where
      𝓼urjectivity = λ x y → x ∼₁ y → μ x ∼₂ μ y
      𝓈urjectivity = ∀ {x y} → 𝓼urjectivity x y
      record 𝓢urjectivity
        {𝓢 : 𝔒₁ → 𝔒₁ → Ø 𝔯₁ ∙̂ 𝔯₂}
        ⦃ _ : 𝓢 ≡ 𝓼urjectivity ⦄
        : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂
        where
        field surjectivity : 𝓈urjectivity
      Surjectivity : Ø _
      Surjectivity = 𝓢urjectivity ⦃ ∅ ⦄
      surjectivity⟦_/_/_⟧ : ⦃ _ : Surjectivity ⦄ → 𝓈urjectivity
      surjectivity⟦_/_/_⟧ = 𝓢urjectivity.surjectivity ⦃ ∅ ⦄ !
    module Hidden
      {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
      {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
      {μ : 𝓼urjection 𝔒₁ 𝔒₂}
      where
      open Visible _∼₁_ _∼₂_ μ
      surjectivity : ⦃ _ : Surjectivity ⦄ → 𝓈urjectivity
      surjectivity = surjectivity⟦_/_/_⟧
    module Hidden0
      {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
      {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
      ⦃ I : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
      where
      open Visible _∼₁_ _∼₂_ (𝓢urjection.surjection I)
      surjectivity! = surjectivity⟦_/_/_⟧
    module Partial0
      (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
      (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
      ⦃ I : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
      where
      open Visible _∼₁_ _∼₂_ (𝓢urjection.surjection I)
      𝓈urjectivity! = 𝓈urjectivity
      𝒮urjectivity = Surjectivity
    module Partial1
      {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
      (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
      ⦃ I : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
      where
      open Visible _∼₁_ _∼₂_ (𝓢urjection.surjection I)
      surjectivity[_] : ⦃ _ : Surjectivity ⦄ → 𝓈urjectivity
      surjectivity[_] = surjectivity⟦_/_/_⟧
    module Partial2
      {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
      (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
      (μ : 𝓼urjection 𝔒₁ 𝔒₂)
      where
      open Visible _∼₁_ _∼₂_ μ
      surjectivity⟦_/_⟧ : ⦃ _ : Surjectivity ⦄ → 𝓈urjectivity
      surjectivity⟦_/_⟧ = surjectivity⟦_/_/_⟧
  module _
    {𝔬₁ 𝔯₁ 𝔬₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
    where
    module ≡-Partial3
      {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
      (μ : 𝓼urjection 𝔒₁ 𝔒₂)
      where
      open Visible _∼₁_ _≡_ μ
      ≡-surjectivity⟦_⟧ : ⦃ _ : Surjectivity ⦄ → 𝓈urjectivity
      ≡-surjectivity⟦_⟧ = surjectivity⟦_/_/_⟧

module NewExtensional
  {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂} {𝔓 : 𝔒₂ → Ø 𝔯₂}
  where
  module _
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    (μ : 𝔒₁ → 𝔒₂)
    where
    open Visible _∼₁_ (Extension 𝔓) μ
    𝓢urjectextensivity = Surjectivity
    𝓼urjectextensivity = 𝓈urjectivity
  module _
    {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
    {μ : 𝔒₁ → 𝔒₂}
    where
    open Visible _∼₁_ (Extension 𝔓) μ
    infixr 10 surjectextensivity
    surjectextensivity = surjectivity⟦_/_/_⟧
    syntax surjectextensivity σ τ = σ ◃ τ
    surjectextensivity!syntax = surjectextensivity
    infixl 10 surjectextensivity!syntax
    syntax surjectextensivity!syntax rxy px = px ● rxy
module OldSurjectextensional
  {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
  where
  module _
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    (𝔓 : 𝔒₂ → Ø 𝔯₂)
    ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
    where
    open Visible _∼₁_ (Extension 𝔓) surjection
    𝓢urjectextensivity = Surjectivity
    𝓼urjectextensivity = 𝓈urjectivity
  module _
    {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
    {𝔓 : 𝔒₂ → Ø 𝔯₂}
    ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
    where
    open Visible _∼₁_ (Extension 𝔓) surjection
    infixr 10 surjectextensivity
    surjectextensivity = surjectivity⟦_/_/_⟧
    syntax surjectextensivity σ τ = σ ◃ τ
    surjectextensivity!syntax = surjectextensivity
    infixl 10 surjectextensivity!syntax
    syntax surjectextensivity!syntax rxy px = px ● rxy

open Visible public
open Hidden public
open Hidden0 public
open Partial0 public
open Partial1 public
open Partial2 public
open ≡-Partial3 public
open Hidden public renaming (surjectivity to §)
open Partial1 public renaming (surjectivity[_] to §[_])
-- TODO rename § to ⟦_⟧?
open 𝓢urjectivity ⦃ … ⦄ renaming (surjectivity to surjectivity‼) public
