
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data
import Oscar.Property.Setoid.ṖropertyEquivalence

module Oscar.Class.Properthing.Ṗroperty where

instance

  ProperthingṖroperty : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
    {ℓ}
    → Properthing (𝔵 ∙̂ 𝔬 ∙̂ ℓ) (Ṗroperty ℓ 𝔒)
  ProperthingṖroperty .Properthing.➊ = ∁ (λ _ → Lift 𝟙)
  ProperthingṖroperty .Properthing._∧_ (∁ P) (∁ Q) = ∁ (λ f → P f × Q f)
  ProperthingṖroperty .Properthing.⌶HasEquivalence = !
  ProperthingṖroperty {𝔒 = 𝔒} .Properthing.Nothing (∁ P) = Wrap (∀ {n} {f : 𝔒 n} → P f → 𝟘)
  ProperthingṖroperty .Properthing.fact2 (∁ P⇔Q) (∁ NoP) .π₀ Q = NoP $ π₁ P⇔Q Q
  ProperthingṖroperty .Properthing.∧-leftIdentity _ .π₀ = π₁ , (lift ∅ ,_)
