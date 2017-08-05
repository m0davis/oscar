
open import Oscar.Prelude
open import Oscar.Data.Constraint

module Oscar.Class.Quadricity where

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  where
  module TCVisible
    {ℓ} (_↦_ : 𝔅 → 𝔅 → Ø ℓ) (let infix 4 _↦_; _↦_ = _↦_)
    (_∧_ : 𝔅 → 𝔅 → 𝔅) (let infixr 15 _∧_; _∧_ = _∧_)
    (_∼_ : 𝔄 → 𝔄 → 𝔅) (let infix 18 _∼_; _∼_ = _∼_)
    (_⊛_ : 𝔄 → 𝔄 → 𝔄)
    where
    𝓆uadricity = λ s1 s2 t1 t2 → s1 ⊛ s2 ∼ t1 ⊛ t2 ↦ s1 ∼ t1 ∧ s2 ∼ t2
    𝒬uadricity = ∀ s1 s2 t1 t2 → 𝓆uadricity s1 s2 t1 t2
    record 𝓠uadricity
      ⦃ _ : Constraint _∼_ ⦄
      ⦃ _ : Constraint _∧_ ⦄
      ⦃ _ : Constraint _⊛_ ⦄
      : Ø 𝔞 ∙̂ ℓ
      where
      field ⋆ : 𝒬uadricity
    Quadricity : Ø _
    Quadricity = 𝓠uadricity
    quadricity⟦_/_/_/_⟧ : ⦃ _ : Quadricity ⦄ → 𝒬uadricity
    quadricity⟦_/_/_/_⟧ ⦃ ⌶ ⦄ = 𝓠uadricity.⋆ ⌶
  module TCHidden
    {ℓ} {_↦_ : 𝔅 → 𝔅 → Ø ℓ}
    {_∧_ : 𝔅 → 𝔅 → 𝔅}
    {_∼_ : 𝔄 → 𝔄 → 𝔅}
    {_⊛_ : 𝔄 → 𝔄 → 𝔄}
    where
    open TCVisible _↦_ _∧_ _∼_ _⊛_
    quadricity : ⦃ _ : Quadricity ⦄ → 𝒬uadricity
    quadricity = quadricity⟦_/_/_/_⟧

open TCVisible public
open TCHidden public
