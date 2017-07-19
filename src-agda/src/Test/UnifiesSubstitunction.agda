
open import Oscar.Prelude
open import Oscar.Data
open import Oscar.Data.Unifies
import Oscar.Property.Functor.SubstitunctionExtensionTerm
import Oscar.Property.Setoid.Proposequality

module Test.UnifiesSubstitunction {𝔭} (𝔓 : Ø 𝔭) where

  open Substitunction 𝔓
  open Term 𝔓
  open Substitist 𝔓

  ≡-Unifies₀-Term : ∀ {m} → Term m → Term m → Ṗroperty ∅̂ (Arrow Fin Term m)
  ≡-Unifies₀-Term = ≡-Unifies₀

  ≡-Unifies₀-Terms : ∀ {N m} → Terms N m → Terms N m → Ṗroperty ∅̂ (Arrow Fin Term m)
  ≡-Unifies₀-Terms = λ x → ≡-Unifies₀ x

  ≡-ExtensionalUnifies-Term : ∀ {m} → Term m → Term m → ArrowExtensionṖroperty ∅̂ Fin Term _≡_ m
  ≡-ExtensionalUnifies-Term = ≡-ExtensionalUnifies

  ≡-ExtensionalUnifies-Terms : ∀ {N m} → Terms N m → Terms N m → LeftExtensionṖroperty ∅̂ (Arrow Fin Term) (Pointwise Proposequality) m
  ≡-ExtensionalUnifies-Terms = ExtensionalUnifies _≡_
