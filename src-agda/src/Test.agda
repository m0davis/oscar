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
import Test.EquivalenceṖroperty
import Test.EquivalenceExtensionṖroperty

module TestSymmetrical where
  test-𝓢ymmetrical𝓢ymmetry : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {ℓ} {_∼_ : 𝔒 → 𝔒 → Ø ℓ}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
    → 𝓼ymmetry _∼_
  test-𝓢ymmetrical𝓢ymmetry = symmetrical _ _
