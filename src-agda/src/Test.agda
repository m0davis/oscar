-- a hodge-podge of tests

module Test where

open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data
open import Oscar.Property
import Test.Transassociativity
import Test.Surjidentity
import Test.SurjidentityI
import Test.SurjidentityP
import Test.Test0
import Test.Test1
import Test.Test2
import Test.Test3
import Test.Test4
import Test.Test5
import Test.Test7

module TestEquivalenceṖroperty
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ : Ł}
  where

  test-sym-regular : {P Q : Ṗroperty ℓ 𝔒} → P ≈ Q → Q ≈ P
  test-sym-regular = symmetry

  test-trans-regular : {P Q R : Ṗroperty ℓ 𝔒} → P ≈ Q → Q ≈ R → P ≈ R
  test-trans-regular P≈Q Q≈R = transitivity P≈Q Q≈R

module TestEquivalenceExtensionṖroperty
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ}
  {ℓ̇} {_↦_ : ∀ {x} → 𝔒 x → 𝔒 x → Ø ℓ̇}
  where

  test-sym-ext : {P Q : ExtensionṖroperty ℓ 𝔒 _↦_} → P ≈ Q → Q ≈ P
  test-sym-ext P≈Q = symmetry P≈Q

  test-trans-ext : {P Q R : ExtensionṖroperty ℓ 𝔒 _↦_} → P ≈ Q → Q ≈ R → P ≈ R
  test-trans-ext P≈Q Q≈R = transitivity P≈Q Q≈R

module TestSymmetrical where
  test-𝓢ymmetrical𝓢ymmetry : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {ℓ} {_∼_ : 𝔒 → 𝔒 → Ø ℓ}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
    → 𝓼ymmetry _∼_
  test-𝓢ymmetrical𝓢ymmetry = symmetrical _ _
