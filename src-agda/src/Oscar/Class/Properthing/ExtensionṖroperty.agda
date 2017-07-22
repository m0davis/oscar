
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data
open import Oscar.Data.ProperlyExtensionNothing
import Oscar.Data.ExtensionṖroperty
import Oscar.Class.Properthing.Ṗroperty
open import Oscar.Data.ProductIndexEquivalence
import Oscar.Class.HasEquivalence.ExtensionṖroperty

module Oscar.Class.Properthing.ExtensionṖroperty where

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ}
  {ℓ̇} {_↦_ : ∀ {x} → 𝔒 x → 𝔒 x → Ø ℓ̇}
  where

  instance

    ProperthingExtensionṖroperty : Properthing (𝔵 ∙̂ 𝔬 ∙̂ ℓ) (ExtensionṖroperty ℓ 𝔒 _↦_)
    ProperthingExtensionṖroperty .Properthing.➊ = ➊ , (λ _ _ → lift ∅)
    ProperthingExtensionṖroperty .Properthing._∧_ P Q = ∁ (λ f → π₀ (π₀ P) f × π₀ (π₀ Q) f) , λ f≐g Pf×Qf → π₁ P f≐g (π₀ Pf×Qf) , π₁ Q f≐g (π₁ Pf×Qf)
    ProperthingExtensionṖroperty .Properthing.⌶HasEquivalence = !
    ProperthingExtensionṖroperty .Properthing.Nothing = ProperlyExtensionNothing
    ProperthingExtensionṖroperty .Properthing.fact2 (∁ (∁ P⇔Q)) (∁ NoP) .π₀ Q = NoP $ π₁ P⇔Q Q
    ProperthingExtensionṖroperty .Properthing.∧-leftIdentity _ .π₀ .π₀ = π₁ , (lift ∅ ,_)
