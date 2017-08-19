
open import Oscar.Prelude
open import Oscar.Class.Surjection
open import Oscar.Data.Proposequality

module Oscar.Class.Surjectivity where

private

  module _
    {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
    where
    module Visible
      (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
      (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
      (μ : Surjection.type 𝔒₁ 𝔒₂)
      where
      𝓼urjectivity = λ x y → x ∼₁ y → μ x ∼₂ μ y
      𝒮urjectivity = ∀ {x y} → 𝓼urjectivity x y
      record 𝓢urjectivity
        {𝓢 : 𝔒₁ → 𝔒₁ → Ø 𝔯₁ ∙̂ 𝔯₂}
        ⦃ _ : 𝓢 ≡ 𝓼urjectivity ⦄
        : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂
        where
        field surjectivity : 𝒮urjectivity
      Surjectivity : Ø _
      Surjectivity = 𝓢urjectivity ⦃ ∅ ⦄
      surjectivity⟦_/_/_⟧ : ⦃ _ : Surjectivity ⦄ → 𝒮urjectivity
      surjectivity⟦_/_/_⟧ = 𝓢urjectivity.surjectivity ⦃ ∅ ⦄ !
    module Hidden
      {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
      {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
      {μ : Surjection.type 𝔒₁ 𝔒₂}
      where
      open Visible _∼₁_ _∼₂_ μ
      surjectivity : ⦃ _ : Surjectivity ⦄ → 𝒮urjectivity
      surjectivity = surjectivity⟦_/_/_⟧
    module Hidden0
      {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
      {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
      ⦃ I : Surjection.class 𝔒₁ 𝔒₂ ⦄
      where
      open Visible _∼₁_ _∼₂_ surjection
      surjectivity! = surjectivity⟦_/_/_⟧
    module Partial0
      (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
      (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
      ⦃ I : Surjection.class 𝔒₁ 𝔒₂ ⦄
      where
      open Visible _∼₁_ _∼₂_ surjection
      𝓈urjectivity! = 𝒮urjectivity
      𝒮urjectivity! = Surjectivity
    module Partial1
      {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
      (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
      ⦃ I : Surjection.class 𝔒₁ 𝔒₂ ⦄
      where
      open Visible _∼₁_ _∼₂_ surjection
      surjectivity[_] : ⦃ _ : Surjectivity ⦄ → 𝒮urjectivity
      surjectivity[_] = surjectivity⟦_/_/_⟧
    module Partial2
      {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
      (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
      (μ : Surjection.type 𝔒₁ 𝔒₂)
      where
      open Visible _∼₁_ _∼₂_ μ
      surjectivity⟦_/_⟧ : ⦃ _ : Surjectivity ⦄ → 𝒮urjectivity
      surjectivity⟦_/_⟧ = surjectivity⟦_/_/_⟧
  module _
    {𝔬₁ 𝔯₁ 𝔬₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
    where
    module ≡-Partial3
      {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
      (μ : Surjection.type 𝔒₁ 𝔒₂)
      where
      open Visible _∼₁_ _≡_ μ
      ≡-surjectivity⟦_⟧ : ⦃ _ : Surjectivity ⦄ → 𝒮urjectivity
      ≡-surjectivity⟦_⟧ = surjectivity⟦_/_/_⟧

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

module 𝔖urjectivity = Visible
