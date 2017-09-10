
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Transitivity

module Oscar.Class.Transitivity.Function where

module _
  {a}
  where

  instance

    𝓣ransitivityFunction : Transitivity.class Function⟦ a ⟧
    𝓣ransitivityFunction {x∼y = f} {g} .⋆ = g ∘ f
