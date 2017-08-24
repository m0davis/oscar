
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Quadricity where

module Quadricity
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {ℓ} (_↦_ : 𝔅 → 𝔅 → Ø ℓ) (let infix 4 _↦_; _↦_ = _↦_)
  (_∧_ : 𝔅 → 𝔅 → 𝔅) (let infixr 15 _∧_; _∧_ = _∧_)
  (_∼_ : 𝔄 → 𝔄 → 𝔅) (let infix 18 _∼_; _∼_ = _∼_)
  (_⊛_ : 𝔄 → 𝔄 → 𝔄)
  = ℭLASS (_↦_ , _∼_ , _∧_ , _⊛_) (∀ s1 s2 t1 t2 → s1 ⊛ s2 ∼ t1 ⊛ t2 ↦ s1 ∼ t1 ∧ s2 ∼ t2)

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {ℓ} (_↦_ : 𝔅 → 𝔅 → Ø ℓ)
  (_∧_ : 𝔅 → 𝔅 → 𝔅)
  (_∼_ : 𝔄 → 𝔄 → 𝔅)
  (_⊛_ : 𝔄 → 𝔄 → 𝔄)
  where
  open Quadricity _↦_ _∧_ _∼_ _⊛_ public using () renaming (type to 𝒬uadricity)

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {ℓ} (_↦_ : 𝔅 → 𝔅 → Ø ℓ)
  (_∧_ : 𝔅 → 𝔅 → 𝔅)
  (_∼_ : 𝔄 → 𝔄 → 𝔅)
  (_⊛_ : 𝔄 → 𝔄 → 𝔄)
  where
  open Quadricity _↦_ _∧_ _∼_ _⊛_ public using () renaming (class to Quadricity; method to quadricity⟦_/_/_/_⟧) public

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {ℓ} {_↦_ : 𝔅 → 𝔅 → Ø ℓ}
  {_∧_ : 𝔅 → 𝔅 → 𝔅}
  {_∼_ : 𝔄 → 𝔄 → 𝔅}
  {_⊛_ : 𝔄 → 𝔄 → 𝔄}
  where
  open Quadricity _↦_ _∧_ _∼_ _⊛_ public using () renaming (method to quadricity)
