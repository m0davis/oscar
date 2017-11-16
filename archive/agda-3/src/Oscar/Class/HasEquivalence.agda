
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.IsEquivalence
open import Oscar.Data.𝟙

module Oscar.Class.HasEquivalence where

module _
  {𝔬} (𝔒 : Ø 𝔬) ℓ
  where
  𝔥asEquivalence : Rℭlass 𝟙
  𝔥asEquivalence = ∁ (𝔒 → 𝔒 → Ø ℓ) IsEquivalence
  open Rℭlass 𝔥asEquivalence using () renaming (GET-CLASS to HasEquivalence) public

module _
  {𝔬} (𝔒 : Ø 𝔬) {ℓ}
  where
  open Rℭlass (𝔥asEquivalence 𝔒 ℓ) using () renaming (GET-METHOD to Equivalence[_]) public

infix 4 ≈-syntax
≈-syntax = Equivalence[_]
syntax ≈-syntax 𝔒 x y = x ≈[ 𝔒 ] y

module _
  {𝔬} {𝔒 : Ø 𝔬} {ℓ}
  where
  open Rℭlass (𝔥asEquivalence 𝔒 ℓ) using () renaming (GET-METHOD to Equivalence) public

infix 4 _≈_
_≈_ = Equivalence
