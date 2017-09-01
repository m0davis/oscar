
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.HasEquivalence
open import Oscar.Class.Surjectextenscongruity
open import Oscar.Class.Properfact1
open import Oscar.Class.Injectivity
open import Oscar.Class.Congruity
open import Oscar.Class.Factsurj3
open import Oscar.Class.Factsurj4
open import Oscar.Class.Factsurj6
open import Oscar.Class.Properthing
open import Oscar.Class.Surjectextensivity
open import Oscar.Class.Surjectivity
open import Oscar.Class.Symmetry
open import Oscar.Data.Fin
open import Oscar.Data.Substitunction
open import Oscar.Data.Term
open import Oscar.Data.Surjcollation
open import Oscar.Data.Surjextenscollation
open import Oscar.Data.Proposequality
open import Oscar.Property.Setoid.Proposequality
open import Oscar.Property.Setoid.Proposextensequality
open import Oscar.Property.Functor.SubstitunctionExtensionTerm
open import Oscar.Property.Thickandthin.FinTermProposequalityMaybeProposequality
import Oscar.Class.Congruity.Proposequality
import Oscar.Class.Congruity.Proposextensequality
import Oscar.Class.Surjection.⋆
open import Oscar.Property.Setoid.ṖropertyEquivalence
import Oscar.Class.Properthing.Ṗroperty
open import Oscar.Data.ProductIndexEquivalence
import Oscar.Data.ExtensionṖroperty
open import Oscar.Data.ProperlyExtensionNothing
import Oscar.Class.Properthing.ExtensionṖroperty
import Oscar.Class.Surjectivity.TransitiveExtensionLeftṖroperty
import Oscar.Class.Surjectivity.ExtensionṖroperty
import Oscar.Class.[ExtensibleType].Proposequality
import Oscar.Class.HasEquivalence.ExtensionṖroperty
import Oscar.Class.HasEquivalence.Ṗroperty
import Oscar.Class.HasEquivalence.Substitunction
open import Oscar.Class.Reflexivity
open import Oscar.Class.Similarity
open import Oscar.Class.Quadricity
open import Oscar.Class.Surjection

module Oscar.Property.Propergroup.Substitunction where

module _
  {𝔭} {𝔓 : Ø 𝔭}
  {ℓ : Ł}
  where
  open Substitunction 𝔓

  instance

    𝓢urjectextenscongruityArrowṖropertySubstitunction : 𝓢urjectextenscongruity Substitunction (LeftṖroperty ℓ Substitunction) _≈_
    𝓢urjectextenscongruityArrowṖropertySubstitunction .⋆ _ (∁ P⇔Q) .π₀ = P⇔Q

    𝓢urjectextenscongruityArrowExtensionṖropertySubstitunction : 𝓢urjectextenscongruity Substitunction (LeftExtensionṖroperty ℓ Substitunction _≈_) _≈_
    𝓢urjectextenscongruityArrowExtensionṖropertySubstitunction .⋆ _ (∁ (∁ P⇔Q)) .π₀ = ∁ P⇔Q -- P⇔Q

module _
  {𝔭} {𝔓 : Ø 𝔭}
  where
  open Term 𝔓

  module S = Surjcollation (Arrow Fin Term) _≡_
  module Ṡ = Surjextenscollation (Arrow Fin Term) _≡̇_

  instance

    𝒫roperfact1UnifiesSubstitunctionFork : ∀ {n} → 𝓟roperfact1 S._⟹_ (_fork_ {n = n})
    𝒫roperfact1UnifiesSubstitunctionFork .⋆ _ _ _ _ .π₀ = (λ s≡t → injectivity₂,₀,₁ s≡t , injectivity₂,₀,₂ s≡t) , uncurry (congruity₂ _fork_)

    𝒫roperfact1ExtensionalUnifiesSubstitunctionFork : ∀ {n} → 𝓟roperfact1 Ṡ._⟹_ (_fork_ {n = n})
    𝒫roperfact1ExtensionalUnifiesSubstitunctionFork .⋆ _ _ _ _ .π₀ .π₀ = (λ s≡t → injectivity₂,₀,₁ s≡t , injectivity₂,₀,₂ s≡t) , uncurry (congruity₂ _fork_)

  instance

    𝓕actsurj3Regular : ∀ {ℓ} → 𝓕actsurj3.class (LeftṖroperty ℓ (Arrow Fin Term)) (Arrow Fin Term)
    𝓕actsurj3Regular .⋆ .π₀ = ¡ , ¡

    𝓕actsurj3Extension : ∀ {ℓ} → Factsurj3.class (LeftExtensionṖroperty ℓ (Arrow Fin Term) (Pointwise Proposequality)) _≈_ (Arrow Fin Term) ε surjection surjectextensivity
    𝓕actsurj3Extension .⋆ .π₀ .π₀ = ¡ , ¡

  open Substitunction 𝔓

  instance

    𝓕actsurj4Regular : ∀ {ℓ} → 𝓕actsurj4 (LeftṖroperty ℓ (Arrow Fin Term)) (Arrow Fin Term) Nothing
    𝓕actsurj4Regular .⋆ _ (∁ nop) .π₀ = nop

    𝓕actsurj4Extension : ∀ {ℓ} → 𝓕actsurj4 (LeftExtensionṖroperty ℓ Substitunction (Pointwise Proposequality)) (Arrow Fin Term) Nothing
    𝓕actsurj4Extension .⋆ _ (∁ nop) .π₀ = nop

  instance

    𝓕actsurj6Extension : ∀ {ℓ} → 𝓕actsurj6 (ArrowExtensionṖroperty ℓ Fin Term Proposequality) Substitunction _≈_ _≈_
    𝓕actsurj6Extension .⋆ P f≐g .π₀ .π₀ {f = h} = π₁ P (congruity (surjectivity h) ∘ f≐g) , π₁ P (Sym.[] (congruity (surjectivity h) ∘ f≐g))
