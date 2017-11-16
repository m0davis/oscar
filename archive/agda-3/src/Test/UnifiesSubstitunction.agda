
open import Everything

module Test.UnifiesSubstitunction {𝔭} (𝔓 : Ø 𝔭) where

  open Substitunction 𝔓
  open Term 𝔓
  open Substitist 𝔓

  ≡-Unifies₀-Term : ∀ {m} → Term m → Term m → Ṗroperty ∅̂ (Arrow Fin Term m)
  ≡-Unifies₀-Term = ≡-surjcollation

  ≡-Unifies₀-Term' : ∀ {m} → Term m → Term m → Ṗroperty ∅̂ (Arrow Fin Term m)
  ≡-Unifies₀-Term' = ≡-surjcollation[ Term ]⟦ Substitunction ⟧

  ≡-Unifies₀-Terms : ∀ {N m} → Terms N m → Terms N m → Ṗroperty ∅̂ (Arrow Fin Term m)
  ≡-Unifies₀-Terms = λ x → ≡-surjcollation x

  ≡-ExtensionalUnifies-Term : ∀ {m} → Term m → Term m → ArrowExtensionṖroperty ∅̂ Fin Term _≡_ m
  ≡-ExtensionalUnifies-Term = Surjextenscollation.method Substitunction _≡̇_

  ≡-ExtensionalUnifies-Terms : ∀ {N m} → Terms N m → Terms N m → LeftExtensionṖroperty ∅̂ (Arrow Fin Term) (Pointwise Proposequality) m
  ≡-ExtensionalUnifies-Terms = surjextenscollation⟦ Pointwise _≡_ ⟧
