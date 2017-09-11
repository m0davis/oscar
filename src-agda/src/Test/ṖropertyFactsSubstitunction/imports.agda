
module Test.ṖropertyFactsSubstitunction.imports where

open import Everything public

module Data {𝔭} (𝔓 : Ø 𝔭) (ℓ : Ł) where

  open Term 𝔓 public using () renaming (
    Term to 𝑩;
    Terms to 𝑩';
    i to 𝒖;
    _fork_ to _⊛_)
  open Substitunction 𝔓 public using () renaming (
    Substitunction to 𝑪)

  𝑷⁰ = LeftṖroperty ℓ 𝑪
  𝑷¹ = LeftExtensionṖroperty ℓ 𝑪 _≈_
  infix 18 _∼⁰_
  _∼⁰_ = ≡-surjcollation⟦ 𝑪 ⟧
  open Surjextenscollation 𝑪 _≡̇_ public renaming (_⟹_ to _∼¹_)

  instance

    isSmapoid0 : IsSmapoid 𝑪 𝑷⁰ 𝑷⁰ _≈_ _≈_ _≈_ _≈_
    isSmapoid0 = ∁

    isSmapoid1 : IsSmapoid 𝑪 𝑷¹ 𝑷¹ _≈_ _≈_ _≈_ _≈_
    isSmapoid1 = ∁

    isSmapoid' : IsSmapoidR 𝑪 𝑷¹ 𝑷¹ _≈_ _≈_ _≈_ _≈_
    isSmapoid' = ∁
