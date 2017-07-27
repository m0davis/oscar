
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data
open import Oscar.Property.Setoid.Proposequality
open import Oscar.Property.Setoid.Proposextensequality
open import Oscar.Property.Category.ExtensionProposextensequality
open import Oscar.Property.Functor.SubstitunctionExtensionTerm
open import Oscar.Property.Category.AListProposequality
open import Oscar.Property.Monad.Maybe
open import Oscar.Property.Thickandthin.FinFinProposequalityMaybeProposequality
open import Oscar.Property.Thickandthin.FinTermProposequalityMaybeProposequality
open import Oscar.Property.Functor.SubstitistProposequalitySubstitunctionProposextensequality
import Oscar.Class.Congruity.Proposequality
import Oscar.Class.Congruity.Proposextensequality
import Oscar.Class.Transextensionality.Proposequality
import Oscar.Class.Surjection
import Oscar.Class.Injectivity.Vec
import Oscar.Class.IsDecidable.Fin
import Oscar.Class.IsDecidable.¶
import Oscar.Class.Surjectivity.ExtensionFinExtensionTerm
import Oscar.Class.Amgu.Term∃SubstitistMaybe
import Oscar.Class.PropId
open import Oscar.Data.Unifies
import Oscar.Data.ExtensionṖroperty
open import Oscar.Property.Setoid.ṖropertyEquivalence
import Oscar.Class.Properthing.Ṗroperty
open import Oscar.Data.ProductIndexEquivalence
open import Oscar.Property.Setoid.ProductIndexEquivalence
import Oscar.Data.ExtensionṖroperty
open import Oscar.Data.ProperlyExtensionNothing
import Oscar.Class.Properthing.ExtensionṖroperty
import Oscar.Class.Surjectivity.TransitiveExtensionLeftṖroperty
import Oscar.Class.Surjectivity.ExtensionṖroperty
import Oscar.Class.[ExtensibleType].Proposequality
import Oscar.Class.Surjectivity.ExtensionArrowExtensionṖropertyProposequality
import Oscar.Class.Surjectivity.ExtensionLeftṖroperty
import Oscar.Class.HasEquivalence.ExtensionṖroperty
import Oscar.Class.HasEquivalence.Ṗroperty
import Oscar.Class.HasEquivalence.Substitunction

module Oscar.Property.Propergroup.Substitunction where

module _
  {𝔭} {𝔓 : Ø 𝔭}
  {ℓ : Ł}
  where
  open Substitunction 𝔓

  instance

    [𝓢urjectextenscongruity]ArrowṖropertySubstitunction : [𝓢urjectextenscongruity] Substitunction (LeftṖroperty ℓ Substitunction) _≈_
    [𝓢urjectextenscongruity]ArrowṖropertySubstitunction = ∁

    𝓢urjectextenscongruityArrowṖropertySubstitunction : 𝓢urjectextenscongruity Substitunction (LeftṖroperty ℓ Substitunction) _≈_
    𝓢urjectextenscongruityArrowṖropertySubstitunction .𝓢urjectextenscongruity.surjectextenscongruity _ (∁ P⇔Q) .π₀ = P⇔Q

    [𝓢urjectextenscongruity]ArrowExtensionṖropertySubstitunction : [𝓢urjectextenscongruity] Substitunction (LeftExtensionṖroperty ℓ Substitunction _≈_) _≈_
    [𝓢urjectextenscongruity]ArrowExtensionṖropertySubstitunction = ∁

    𝓢urjectextenscongruityArrowExtensionṖropertySubstitunction : 𝓢urjectextenscongruity Substitunction (LeftExtensionṖroperty ℓ Substitunction _≈_) _≈_
    𝓢urjectextenscongruityArrowExtensionṖropertySubstitunction .𝓢urjectextenscongruity.surjectextenscongruity _ (∁ (∁ P⇔Q)) .π₀ = ∁ P⇔Q -- P⇔Q

module _
  {𝔭} {𝔓 : Ø 𝔭}
  where
  open Term 𝔓

  instance

    [𝒫roperfact1]UnifiesSubstitunctionFork : ∀ {n} → [𝓟roperfact1] (≡-surjcollation⟦ Arrow Fin Term ⟧) (_fork_ {n = n})
    [𝒫roperfact1].𝔅 [𝒫roperfact1]UnifiesSubstitunctionFork = _
    [𝒫roperfact1]._∼_ [𝒫roperfact1]UnifiesSubstitunctionFork = ≡-surjcollation⟦ Arrow Fin Term ⟧
    [𝒫roperfact1].⌶Properthing [𝒫roperfact1]UnifiesSubstitunctionFork = !
    [𝒫roperfact1]._⊛_ [𝒫roperfact1]UnifiesSubstitunctionFork = _fork_
    [𝒫roperfact1].⌶CorrectProp [𝒫roperfact1]UnifiesSubstitunctionFork = !

    [𝒫roperfact1]ExtensionalUnifiesSubstitunctionFork : ∀ {n} → [𝓟roperfact1] (≡-surjextenscollation[ Arrow Fin _ ]) (_fork_ {n = n})
    [𝒫roperfact1].𝔅 [𝒫roperfact1]ExtensionalUnifiesSubstitunctionFork = _
    [𝒫roperfact1]._∼_ [𝒫roperfact1]ExtensionalUnifiesSubstitunctionFork = ≡-surjextenscollation[ Arrow Fin _ ]
    [𝒫roperfact1].⌶Properthing [𝒫roperfact1]ExtensionalUnifiesSubstitunctionFork = !
    [𝒫roperfact1]._⊛_ [𝒫roperfact1]ExtensionalUnifiesSubstitunctionFork = _fork_
    [𝒫roperfact1].⌶CorrectProp [𝒫roperfact1]ExtensionalUnifiesSubstitunctionFork = !

    𝒫roperfact1UnifiesSubstitunctionFork : ∀ {n} → 𝓟roperfact1 (≡-surjcollation⟦ Arrow Fin Term ⟧) (_fork_ {n = n})
    𝒫roperfact1.properfact1 𝒫roperfact1UnifiesSubstitunctionFork _ _ _ _ .π₀ = (λ s≡t → injectivity₂,₀,₁ s≡t , injectivity₂,₀,₂ s≡t) , uncurry (congruity₂ _fork_)

    𝒫roperfact1ExtensionalUnifiesSubstitunctionFork : ∀ {n} → 𝓟roperfact1 (≡-surjextenscollation[ Arrow Fin _ ]) (_fork_ {n = n})
    𝒫roperfact1.properfact1 𝒫roperfact1ExtensionalUnifiesSubstitunctionFork _ _ _ _ .π₀ .π₀ = (λ s≡t → injectivity₂,₀,₁ s≡t , injectivity₂,₀,₂ s≡t) , uncurry (congruity₂ _fork_)

  instance

    [𝓕actsurj3]Regular : ∀ {ℓ} → [𝓕actsurj3] (LeftṖroperty ℓ (Arrow Fin Term)) (Arrow Fin Term) 𝔭
    [𝓕actsurj3]Regular .[𝐹actsurj3]._∼ᵣ_ = Arrow Fin Term
    [𝓕actsurj3]Regular .[𝐹actsurj3].⌶Reflexivity = !
    [𝓕actsurj3]Regular .[𝐹actsurj3].⌶Surjectextensivity = !
    [𝓕actsurj3]Regular .[𝐹actsurj3].⌶HasEquivalence = !
    [𝓕actsurj3]Regular .[𝐹actsurj3].⌶CorrectFactsurj3 = !

    𝓕actsurj3Regular : ∀ {ℓ} → 𝓕actsurj3 (LeftṖroperty ℓ (Arrow Fin Term)) (Arrow Fin Term)
    𝓕actsurj3Regular .𝐹actsurj3.factsurj3 .π₀ = ¡ , ¡

    [𝓕actsurj3]Extension : ∀ {ℓ} → [𝓕actsurj3] (LeftExtensionṖroperty ℓ (Arrow Fin Term) (Pointwise Proposequality)) (Arrow Fin Term) 𝔭
    [𝓕actsurj3]Extension .[𝐹actsurj3]._∼ᵣ_ = Arrow Fin Term
    [𝓕actsurj3]Extension .[𝐹actsurj3].⌶Reflexivity = !
    [𝓕actsurj3]Extension .[𝐹actsurj3].⌶Surjectextensivity = !
    [𝓕actsurj3]Extension .[𝐹actsurj3].⌶HasEquivalence = !
    [𝓕actsurj3]Extension .[𝐹actsurj3].⌶CorrectFactsurj3 = !

    𝓕actsurj3Extension : ∀ {ℓ} → 𝓕actsurj3 (LeftExtensionṖroperty ℓ (Arrow Fin Term) (Pointwise Proposequality)) (Arrow Fin Term)
    𝓕actsurj3Extension .𝐹actsurj3.factsurj3 .π₀ .π₀ = ¡ , ¡

  open Substitunction 𝔓

  instance

    [𝓕actsurj4]Regular : ∀ {ℓ} → [𝓕actsurj4] (LeftṖroperty ℓ (Arrow Fin Term)) (Arrow Fin Term) Nothing
    [𝓕actsurj4]Regular = ∁ surjectextensivity

    𝓕actsurj4Regular : ∀ {ℓ} → 𝓕actsurj4 (LeftṖroperty ℓ (Arrow Fin Term)) (Arrow Fin Term) Nothing
    𝓕actsurj4Regular .𝓕actsurj4.factsurj4 _ (∁ nop) .π₀ = nop

    [𝓕actsurj4]Extension : ∀ {ℓ} → [𝓕actsurj4] (ArrowExtensionṖroperty ℓ Fin Term Proposequality) Substitunction Nothing
    [𝓕actsurj4]Extension = ∁ surjectextensivity

    𝓕actsurj4Extension : ∀ {ℓ} → 𝓕actsurj4 (LeftExtensionṖroperty ℓ Substitunction (Pointwise Proposequality)) (Arrow Fin Term) Nothing
    𝓕actsurj4Extension .𝓕actsurj4.factsurj4 _ (∁ nop) .π₀ = nop

  instance

    [𝓕actsurj6]Extension : ∀ {ℓ} → [𝓕actsurj6] (ArrowExtensionṖroperty ℓ Fin Term Proposequality) Substitunction _≈_ _≈_
    [𝓕actsurj6]Extension = ∁

    𝓕actsurj6Extension : ∀ {ℓ} → 𝓕actsurj6 (ArrowExtensionṖroperty ℓ Fin Term Proposequality) Substitunction _≈_ _≈_
    𝓕actsurj6Extension .𝓕actsurj6.factsurj6 P f≐g .π₀ .π₀ {f = h} = π₁ P (congruity (surjectivity h) ∘ f≐g) , π₁ P (symmetry (congruity (surjectivity h) ∘ f≐g))
