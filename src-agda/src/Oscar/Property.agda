--{-# OPTIONS --show-implicit #-}
{-# OPTIONS --postfix-projections #-}
--{-# OPTIONS -v30 #-}
{-# OPTIONS --rewriting #-}
module Oscar.Property where

open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data
open import Oscar.Property.Setoid.Proposequality public
open import Oscar.Property.Setoid.Proposextensequality public
open import Oscar.Property.Category.ExtensionProposextensequality public
open import Oscar.Property.Functor.SubstitunctionExtensionTerm public
open import Oscar.Property.Category.AListProposequality public
open import Oscar.Property.Monad.Maybe public
open import Oscar.Property.Thickandthin.FinFinProposequalityMaybeProposequality public
open import Oscar.Property.Thickandthin.FinTermProposequalityMaybeProposequality public
open import Oscar.Property.Functor.SubstitistProposequalitySubstitunctionProposextensequality public
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
open import Oscar.Property.Setoid.ṖropertyEquivalence public
import Oscar.Class.Properthing.Ṗroperty
open import Oscar.Data.ProductIndexEquivalence public
open import Oscar.Property.Setoid.ProductIndexEquivalence public
import Oscar.Data.ExtensionṖroperty
open import Oscar.Data.ProperlyExtensionNothing public
import Oscar.Class.Properthing.ExtensionṖroperty

instance

  ṖropertySurjectivity : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔯} {_↦_ : 𝔛 → 𝔛 → Ø 𝔯}
    {ℓ : Ł}
    ⦃ _ : 𝓣ransitivity _↦_ ⦄
    ⦃ _ : [𝓢urjectivity] _↦_ (Extension $ LeftṖroperty ℓ _↦_) ⦄
    → 𝓢urjectivity _↦_ (Extension $ LeftṖroperty ℓ _↦_)
  ṖropertySurjectivity .𝓢urjectivity.surjectivity f (∁ P) .π₀ g = P (g ∙ f)

instance

  ExtensionṖropertySurjectivity : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔒₁ : 𝔛 → Ø 𝔞}
    {𝔟} {𝔒₂ : 𝔛 → Ø 𝔟}
    (let _∼_ = Arrow 𝔒₁ 𝔒₂)
    {ℓ}
    {ℓ̇} {_↦_ : ∀̇ π̂² ℓ̇ 𝔒₂}
    ⦃ _ : [ExtensibleType] (λ {x} → _↦_ {x}) ⦄
    ⦃ _ : [𝓢urjectivity] _∼_ (Extension 𝔒₂) ⦄
    ⦃ _ : 𝓢urjectivity _∼_ (Extension 𝔒₂) ⦄
    ⦃ _ : [𝓢urjextensionality] _∼_ (Pointwise _↦_) (Extension 𝔒₂) (Pointwise _↦_) ⦄
    ⦃ _ : 𝓢urjextensionality _∼_ (Pointwise _↦_) (Extension 𝔒₂) (Pointwise _↦_) ⦄
    ⦃ _ : [𝓢urjectivity] _∼_ (Extension $ LeftExtensionṖroperty ℓ _∼_ (Pointwise _↦_)) ⦄
    → 𝓢urjectivity _∼_ (Extension $ LeftExtensionṖroperty ℓ _∼_ (Pointwise _↦_))
  ExtensionṖropertySurjectivity .𝓢urjectivity.surjectivity f P = ∁ (λ g → π₀ (π₀ P) (surjectivity g ∘ f)) , (λ f≐g Pf'◇f → π₁ P (surjextensionality f≐g ∘ f) Pf'◇f)

instance

  [ExtensibleType]Proposequality : ∀ {a} {b} {A : Set a} {B : A → Set b} → [ExtensibleType] (λ {w} → Proposequality⟦ B w ⟧)
  [ExtensibleType]Proposequality = ∁

  [𝓢urjectivity]ArrowE : ∀ {ℓ} {a} {f} {t} {¶ : Set a} {Fin : ¶ → Set f} {Term : ¶ → Set t} → [𝓢urjectivity] (Arrow Fin Term) (Extension $ LeftExtensionṖroperty ℓ (Arrow Fin Term) _≡̇_)
  [𝓢urjectivity]ArrowE = ∁

  [𝓢urjectivity]LeftṖroperty : ∀ {ℓ} {a} {f} {¶ : Set a} {_↦_ : ¶ → ¶ → Set f} → [𝓢urjectivity] _↦_ (Extension $ LeftṖroperty ℓ _↦_)
  [𝓢urjectivity]LeftṖroperty = ∁

instance

  𝓢ymmetrical𝓢ymmetry : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {ℓ} {_∼_ : 𝔒 → 𝔒 → Ø ℓ}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
    → 𝓢ymmetrical 𝔒 (λ s t t' s' → s ∼ t → t' ∼ s')
  𝓢ymmetrical𝓢ymmetry .𝓢ymmetrical.symmetrical x y = symmetry

  𝓢ymmetricalUnifies₀ : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔄 : 𝔛 → 𝔛 → Ø 𝔞}
    {𝔠} {ℭ : 𝔛 → Ø 𝔠}
    ⦃ _ : [𝓢urjectivity] 𝔄 (Extension ℭ) ⦄
    ⦃ _ : 𝓢urjectivity 𝔄 (Extension ℭ) ⦄
    {ℓ} {_≈'_ : ∀ {y} → ℭ y → ℭ y → Ø ℓ}
    ⦃ _ : ∀ {y} → 𝓢ymmetry (_≈'_ {y}) ⦄
    → ∀ {m} → 𝓢ymmetrical (ℭ m) (λ s t t' s' → Unifies₀⟦ 𝔄 ⟧ _≈'_ s t ≈ Unifies₀ _≈'_ t' s')
  𝓢ymmetricalUnifies₀ .𝓢ymmetrical.symmetrical x y .π₀ = symmetry , symmetry

  𝓢ymmetricalExtensionalUnifies : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
    (let _↦_ = Arrow 𝔄 𝔅)
    {𝔠} {ℭ : 𝔛 → Ø 𝔠}
    {ℓ₁} {_∼₁_ : ∀ {y} → 𝔅 y → 𝔅 y → Ø ℓ₁}
    {ℓ₂} {_∼₂_ : ∀ {y} → ℭ y → ℭ y → Ø ℓ₂}
    ⦃ _ : ∀ {y} → 𝓢ymmetry (_∼₂_ {y}) ⦄
    ⦃ _ : ∀ {y} → 𝓣ransitivity (_∼₂_ {y}) ⦄
    ⦃ _ : [𝓢urjectivity] _↦_ (Extension ℭ) ⦄
    ⦃ _ : 𝓢urjectivity _↦_ (Extension ℭ) ⦄
    ⦃ _ : [𝓢urjextensionality] _↦_ (Pointwise _∼₁_) (Extension ℭ) (Pointwise _∼₂_) ⦄
    ⦃ _ : 𝓢urjextensionality _↦_ (Pointwise _∼₁_) (Extension ℭ) (Pointwise _∼₂_) ⦄
    -- {-{ℓ}-} {_≈'_ : ∀ {y} → 𝔅 y → 𝔅 y → Ø ℓ₁}
    ⦃ _ : ∀ {y} → 𝓢ymmetry (_∼₁_ {y}) ⦄
    → ∀ {m} → 𝓢ymmetrical (ℭ m) (λ s t t' s' → ExtensionalUnifies {𝔄 = 𝔄} {𝔅 = 𝔅} _∼₁_ {_∼₂_ = _∼₂_} s t ≈ ExtensionalUnifies _∼₁_ t' s')
  𝓢ymmetricalExtensionalUnifies .𝓢ymmetrical.symmetrical x y .π₀ = ∁ (symmetry , symmetry)

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

    [𝒫roperfact1]UnifiesSubstitunctionFork : ∀ {n} → [𝓟roperfact1] (≡-Unifies₀⟦ Arrow Fin Term ⟧) (_fork_ {n = n})
    [𝒫roperfact1].𝔅 [𝒫roperfact1]UnifiesSubstitunctionFork = _
    [𝒫roperfact1]._∼_ [𝒫roperfact1]UnifiesSubstitunctionFork = ≡-Unifies₀⟦ Arrow Fin Term ⟧
    [𝒫roperfact1].⌶Properthing [𝒫roperfact1]UnifiesSubstitunctionFork = !
    [𝒫roperfact1]._⊛_ [𝒫roperfact1]UnifiesSubstitunctionFork = _fork_
    [𝒫roperfact1].⌶CorrectProp [𝒫roperfact1]UnifiesSubstitunctionFork = !

    [𝒫roperfact1]ExtensionalUnifiesSubstitunctionFork : ∀ {n} → [𝓟roperfact1] (≡-ExtensionalUnifies {𝔄 = Fin}) (_fork_ {n = n})
    [𝒫roperfact1].𝔅 [𝒫roperfact1]ExtensionalUnifiesSubstitunctionFork = _
    [𝒫roperfact1]._∼_ [𝒫roperfact1]ExtensionalUnifiesSubstitunctionFork = ≡-ExtensionalUnifies {𝔄 = Fin}
    [𝒫roperfact1].⌶Properthing [𝒫roperfact1]ExtensionalUnifiesSubstitunctionFork = !
    [𝒫roperfact1]._⊛_ [𝒫roperfact1]ExtensionalUnifiesSubstitunctionFork = _fork_
    [𝒫roperfact1].⌶CorrectProp [𝒫roperfact1]ExtensionalUnifiesSubstitunctionFork = !

    𝒫roperfact1UnifiesSubstitunctionFork : ∀ {n} → 𝓟roperfact1 (≡-Unifies₀⟦ Arrow Fin Term ⟧) (_fork_ {n = n})
    𝒫roperfact1.properfact1 𝒫roperfact1UnifiesSubstitunctionFork _ _ _ _ .π₀ = (λ s≡t → injectivity₂,₀,₁ s≡t , injectivity₂,₀,₂ s≡t) , uncurry (congruity₂ _fork_)

    𝒫roperfact1ExtensionalUnifiesSubstitunctionFork : ∀ {n} → 𝓟roperfact1 (≡-ExtensionalUnifies {𝔄 = Fin}) (_fork_ {n = n})
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
