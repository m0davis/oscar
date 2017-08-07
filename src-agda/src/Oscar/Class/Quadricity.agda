
open import Oscar.Prelude
open import Oscar.Class

module Oscar.Class.Quadricity where

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {ℓ} (_↦_ : 𝔅 → 𝔅 → Ø ℓ) (let infix 4 _↦_; _↦_ = _↦_)
  (_∧_ : 𝔅 → 𝔅 → 𝔅) (let infixr 15 _∧_; _∧_ = _∧_)
  (_∼_ : 𝔄 → 𝔄 → 𝔅) (let infix 18 _∼_; _∼_ = _∼_)
  (_⊛_ : 𝔄 → 𝔄 → 𝔄)
  where
  𝒬uadricity = ∀ s1 s2 t1 t2 → s1 ⊛ s2 ∼ t1 ⊛ t2 ↦ s1 ∼ t1 ∧ s2 ∼ t2
  𝔮uadricity : ℭlass (_↦_ , _∼_ , _∧_ , _⊛_)
  𝔮uadricity = ∁ 𝒬uadricity

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {ℓ} (_↦_ : 𝔅 → 𝔅 → Ø ℓ)
  (_∧_ : 𝔅 → 𝔅 → 𝔅)
  (_∼_ : 𝔄 → 𝔄 → 𝔅)
  (_⊛_ : 𝔄 → 𝔄 → 𝔄)
  where
  module 𝓠uadricity = ℭlass (𝔮uadricity _↦_ _∧_ _∼_ _⊛_)

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {ℓ} (_↦_ : 𝔅 → 𝔅 → Ø ℓ)
  (_∧_ : 𝔅 → 𝔅 → 𝔅)
  (_∼_ : 𝔄 → 𝔄 → 𝔅)
  (_⊛_ : 𝔄 → 𝔄 → 𝔄)
  where
  open ℭlass (𝔮uadricity _↦_ _∧_ _∼_ _⊛_) using () renaming (GET-CLASS to Quadricity; GET-METHOD to quadricity⟦_/_/_/_⟧) public

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {ℓ} {_↦_ : 𝔅 → 𝔅 → Ø ℓ}
  {_∧_ : 𝔅 → 𝔅 → 𝔅}
  {_∼_ : 𝔄 → 𝔄 → 𝔅}
  {_⊛_ : 𝔄 → 𝔄 → 𝔄}
  where
  open ℭlass (𝔮uadricity _↦_ _∧_ _∼_ _⊛_) using () renaming (GET-METHOD to quadricity) public
