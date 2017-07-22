
open import Oscar.Prelude
open import Oscar.Class.Surjection

module Oscar.Class.Surjectivity where

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  where
  record [𝓢urjectivity] : Ø₀ where
    no-eta-equality
    constructor ∁
  module _
    ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
    where
    𝓼urjectivity = ∀ {x y} → x ∼₁ y → surjection x ∼₂ surjection y
    record 𝓢urjectivity ⦃ _ : [𝓢urjectivity] ⦄ : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ where
      field
        surjectivity : 𝓼urjectivity

private

  module projection where
    open 𝓢urjectivity ⦃ … ⦄ public

    surjectivity[_] : ∀
      {𝔬₁} {𝔒₁ : Ø 𝔬₁}
      {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
      {𝔬₂} {𝔒₂ : Ø 𝔬₂}
      {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
      ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
      ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
      ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
      → 𝓼urjectivity _∼₁_ _∼₂_
    surjectivity[ _ ] = surjectivity

    surjectivity⟦_/_⟧ : ∀
      {𝔬₁} {𝔒₁ : Ø 𝔬₁}
      {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
      {𝔬₂} {𝔒₂ : Ø 𝔬₂}
      {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
      (surjection : 𝔒₁ → 𝔒₂)
      (let instance _ : 𝓢urjection 𝔒₁ 𝔒₂
                    _ = ∁ surjection)
      ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
      ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
      → 𝓼urjectivity _∼₁_ _∼₂_
    surjectivity⟦_/_⟧ {𝔒₁ = 𝔒₁} {𝔒₂ = 𝔒₂} _ surjection =
      let instance _ : 𝓢urjection 𝔒₁ 𝔒₂
                   _ = ∁ surjection
      in surjectivity

    open import Oscar.Data

    ≡-surjectivity⟦_⟧ : ∀
      {𝔬₁} {𝔒₁ : Ø 𝔬₁}
      {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
      {𝔬₂} {𝔒₂ : Ø 𝔬₂}
      (surjection : 𝔒₁ → 𝔒₂)
      (let instance _ : 𝓢urjection 𝔒₁ 𝔒₂
                    _ = ∁ surjection)
      ⦃ _ : [𝓢urjectivity] _∼₁_ Proposequality⟦ 𝔒₂ ⟧ ⦄
      ⦃ _ : 𝓢urjectivity _∼₁_ _≡_ ⦄
      → 𝓼urjectivity _∼₁_ _≡_
    ≡-surjectivity⟦_⟧ {𝔒₁ = 𝔒₁} {𝔒₂ = 𝔒₂} surjection =
      let instance _ : 𝓢urjection 𝔒₁ 𝔒₂
                   _ = ∁ surjection
      in surjectivity

module _ where
  open projection public

module _ where
  open projection public using () renaming (surjectivity to §; surjectivity[_] to §[_])
  -- TODO rename § to ⟦_⟧?
