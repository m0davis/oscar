
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Leftunit
open import Oscar.Class.Reflexivity
open import Oscar.Class.Transitivity
open import Oscar.Class.Transleftidentity

module Oscar.Class.Transleftidentity.ToLeftunit where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  {ℓ} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ}
  {ε : Reflexivity.type _∼_}
  {transitivity : Transitivity.type _∼_}
  where
  instance
    toLeftunitFromTransleftidentity :
      ⦃ _ : Transleftidentity.class _∼_ _∼̇_ ε transitivity ⦄
      → ∀ {x y} {f : x ∼ y} → Leftunit.class _∼̇_ ε (flip transitivity) f
    toLeftunitFromTransleftidentity .⋆ = transleftidentity
