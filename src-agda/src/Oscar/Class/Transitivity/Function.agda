
open import Oscar.Prelude
open import Oscar.Class.Transitivity

module Oscar.Class.Transitivity.Function where

module _
  {a}
  where

  instance

    𝓣ransitivityFunction : Transitivity.class Function⟦ a ⟧
    𝓣ransitivity.transitivity 𝓣ransitivityFunction f g = g ∘ f
