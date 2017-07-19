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

module _ where

  instance
    PropIdFromTransleftidentity : ∀
      {𝔵} {𝔛 : Ø 𝔵}
      {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
      {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
      (let _∼_ = Arrow 𝔄 𝔅)
      {ℓ̇} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ̇}
      ⦃ _ : 𝓣ransitivity _∼_ ⦄
      ⦃ _ : 𝓡eflexivity _∼_ ⦄
      {ℓ}
      ⦃ _ : [𝓣ransleftidentity] _∼_ _∼̇_ ⦄
      ⦃ _ : 𝓣ransleftidentity _∼_ _∼̇_ ⦄
      ⦃ _ : ∀ {x y} → 𝓢ymmetry (_∼̇_ {x} {y}) ⦄
      → PropId 𝔄 𝔅 _∼̇_ ℓ
    PropIdFromTransleftidentity .PropId.prop-id (_ , P₁) = P₁ $ symmetry transleftidentity

  𝓾nifies₀ : ∀
    {𝔵} {𝔒 : Ø 𝔵}
    {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
    {𝔯₁} (_↦₁_ : π̂² 𝔯₁ 𝔒)
    𝔯₂
    → Ø 𝔵 ∙̂ 𝔭 ∙̂ 𝔯₁ ∙̂ ↑̂ 𝔯₂
  𝓾nifies₀ 𝔓 _↦₁_ 𝔯₂ = ∀ {m} → 𝔓 m → 𝔓 m → Ṗroperty 𝔯₂ (m ↦₁_)

  Unifies₀ : ∀
    {𝔵} {𝔒 : Ø 𝔵}
    {𝔭} {𝔓 : 𝔒 → Ø 𝔭}
    {𝔯₁} {_↦₁_ : π̂² 𝔯₁ 𝔒}
    ⦃ _ : [𝓢urjectivity] _↦₁_ (Extension 𝔓) ⦄
    ⦃ _ : 𝓢urjectivity _↦₁_ (Extension 𝔓) ⦄
    {𝔯₂} (_↦₂_ : ∀̇ π̂² 𝔯₂ 𝔓)
    → 𝓾nifies₀ 𝔓 _↦₁_ 𝔯₂
  Unifies₀ _↦₂_ p q .π₀ x =
    let _↦₂_ = _↦₂_
        infix 4 _↦₂_
    in
    x ◃ p ↦₂ x ◃ q

  Unifies₀⟦_⟧ : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} (𝔄 : 𝔛 → 𝔛 → Ø 𝔞)
    {𝔠} {ℭ : 𝔛 → Ø 𝔠}
    ⦃ _ : [𝓢urjectivity] 𝔄 (Extension ℭ) ⦄
    ⦃ _ : 𝓢urjectivity 𝔄 (Extension ℭ) ⦄
    {ℓ} (_≈_ : ∀ {y} → ℭ y → ℭ y → Ø ℓ)
    → 𝓾nifies₀ ℭ 𝔄 ℓ
  Unifies₀⟦ _ ⟧ = Unifies₀

  ≡-Unifies₀ : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔄 : 𝔛 → 𝔛 → Ø 𝔞}
    {𝔠} {ℭ : 𝔛 → Ø 𝔠}
    ⦃ _ : [𝓢urjectivity] 𝔄 (Extension ℭ) ⦄
    ⦃ _ : 𝓢urjectivity 𝔄 (Extension ℭ) ⦄
    → 𝓾nifies₀ ℭ 𝔄 ∅̂
  ≡-Unifies₀ = Unifies₀ _≡_

  ≡-Unifies₀⟦_⟧ : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} (𝔄 : 𝔛 → 𝔛 → Ø 𝔞)
    {𝔠} {ℭ : 𝔛 → Ø 𝔠}
    ⦃ _ : [𝓢urjectivity] 𝔄 (Extension ℭ) ⦄
    ⦃ _ : 𝓢urjectivity 𝔄 (Extension ℭ) ⦄
    → 𝓾nifies₀ ℭ 𝔄 ∅̂
  ≡-Unifies₀⟦ _ ⟧ = ≡-Unifies₀

  ExtensionalUnifies : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
    (let _↦_ = Arrow 𝔄 𝔅)
    {𝔠} {ℭ : 𝔛 → Ø 𝔠}
    {ℓ₁} (_∼₁_ : ∀ {y} → 𝔅 y → 𝔅 y → Ø ℓ₁)
    {ℓ₂} {_∼₂_ : ∀ {y} → ℭ y → ℭ y → Ø ℓ₂}
    ⦃ _ : ∀ {y} → 𝓢ymmetry (_∼₂_ {y}) ⦄
    ⦃ _ : ∀ {y} → 𝓣ransitivity (_∼₂_ {y}) ⦄
    ⦃ _ : [𝓢urjectivity] _↦_ (Extension ℭ) ⦄
    ⦃ _ : 𝓢urjectivity _↦_ (Extension ℭ) ⦄
    ⦃ _ : [𝓢urjextensionality] _↦_ (Pointwise _∼₁_) (Extension ℭ) (Pointwise _∼₂_) ⦄
    ⦃ _ : 𝓢urjextensionality _↦_ (Pointwise _∼₁_) (Extension ℭ) (Pointwise _∼₂_) ⦄
    → ∀ {m} → ℭ m → ℭ m → ArrowExtensionṖroperty ℓ₂ 𝔄 𝔅 _∼₁_ m
  ExtensionalUnifies _ {_∼₂_ = _∼₂_} s t =
    Unifies₀ _∼₂_ s t , λ f≐g f◃s=f◃t →
      ⟪ f≐g ⟫[ Pointwise _∼₂_ ] t ∙ f◃s=f◃t ∙ symmetry (⟪ f≐g ⟫[ Pointwise _∼₂_ ] s)

  ≡-ExtensionalUnifies : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
    (let _↦_ = Arrow 𝔄 𝔅)
    {𝔠} {ℭ : 𝔛 → Ø 𝔠}
    {ℓ₂} {_∼₂_ : ∀ {y} → ℭ y → ℭ y → Ø ℓ₂}
    ⦃ _ : ∀ {y} → 𝓢ymmetry (_∼₂_ {y}) ⦄
    ⦃ _ : ∀ {y} → 𝓣ransitivity (_∼₂_ {y}) ⦄
    ⦃ _ : [𝓢urjectivity] _↦_ (Extension ℭ) ⦄
    ⦃ _ : 𝓢urjectivity _↦_ (Extension ℭ) ⦄
    ⦃ _ : [𝓢urjextensionality] _↦_ (Pointwise _≡_) (Extension ℭ) (Pointwise _∼₂_) ⦄
    ⦃ _ : 𝓢urjextensionality _↦_ (Pointwise _≡_) (Extension ℭ) (Pointwise _∼₂_) ⦄
    → ∀ {m} → ℭ m → ℭ m → ArrowExtensionṖroperty ℓ₂ 𝔄 𝔅 _≡_ m
  ≡-ExtensionalUnifies {𝔄 = 𝔄} {𝔅 = 𝔅} {_∼₂_ = _∼₂_} s t = ExtensionalUnifies {𝔄 = 𝔄} {𝔅 = 𝔅} _≡_ {_∼₂_ = _∼₂_} s t

module _ where

  ≡-ExtensionṖroperty : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔬₁} ℓ (𝔒₁ : 𝔛 → Ø 𝔬₁)
    {𝔬₂} (𝔒₂ : 𝔛 → Ø 𝔬₂)
    → 𝔛
    → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ
  ≡-ExtensionṖroperty ℓ 𝔒₁ 𝔒₂ x = ArrowExtensionṖroperty ℓ 𝔒₁ 𝔒₂ _≡_ x

module _ {𝔭} (𝔓 : Ø 𝔭) where

  open Substitunction 𝔓
  open Term 𝔓
  open Substitist 𝔓

  prop-id-Substitunction : ∀ {m n ℓ} {f : Substitunction m n} (P : LeftExtensionṖroperty ℓ Substitunction Proposextensequality m) (let P₀ = π₀ (π₀ P)) → P₀ f → P₀ (ε ∙ f)
  prop-id-Substitunction = prop-id

  ≡-Unifies₀-Term : ∀ {m} → Term m → Term m → Ṗroperty ∅̂ (Arrow Fin Term m)
  ≡-Unifies₀-Term = ≡-Unifies₀

  ≡-Unifies₀-Terms : ∀ {N m} → Terms N m → Terms N m → Ṗroperty ∅̂ (Arrow Fin Term m)
  ≡-Unifies₀-Terms = λ x → ≡-Unifies₀ x

  ≡-ExtensionalUnifies-Term : ∀ {m} → Term m → Term m → ArrowExtensionṖroperty ∅̂ Fin Term _≡_ m
  ≡-ExtensionalUnifies-Term = ≡-ExtensionalUnifies

  ≡-ExtensionalUnifies-Terms : ∀ {N m} → Terms N m → Terms N m → LeftExtensionṖroperty ∅̂ (Arrow Fin Term) (Pointwise Proposequality) m
  ≡-ExtensionalUnifies-Terms = ExtensionalUnifies _≡_

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ : Ł}
  where

  ṖropertyEquivalence : Ṗroperty ℓ 𝔒 → Ṗroperty ℓ 𝔒 → Ø 𝔵 ∙̂ 𝔬 ∙̂ ℓ
  ṖropertyEquivalence (∁ P) (∁ Q) = Wrap (∀ {n f} → (P {n} f → Q f) × (Q f → P f))

  instance

    𝓡eflexivityṖroperty : 𝓡eflexivity ṖropertyEquivalence
    𝓡eflexivityṖroperty .𝓡eflexivity.reflexivity .π₀ = ¡ , ¡

    𝓢ymmetryṖroperty : 𝓢ymmetry ṖropertyEquivalence
    𝓢ymmetryṖroperty .𝓢ymmetry.symmetry (∁ P⇔Q) .π₀ = π₁ P⇔Q , π₀ P⇔Q

    𝓣ransitivityṖroperty : 𝓣ransitivity ṖropertyEquivalence
    𝓣ransitivityṖroperty .𝓣ransitivity.transitivity (∁ P⇔Q) (∁ Q⇔R) .π₀ = π₀ Q⇔R ∘ π₀ P⇔Q , π₁ P⇔Q ∘ π₁ Q⇔R

    IsEquivalenceṖroperty : IsEquivalence ṖropertyEquivalence
    IsEquivalenceṖroperty = ∁

instance

  HasEquivalenceṖroperty : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
    {ℓ}
    → HasEquivalence (Ṗroperty ℓ 𝔒) (𝔵 ∙̂ 𝔬 ∙̂ ℓ)
  HasEquivalenceṖroperty .HasEquivalence.Equivalence P Q = ṖropertyEquivalence P Q

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

module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} {ℓ} ⦃ _ : HasEquivalence 𝔒 ℓ ⦄  where

  record _≈₀_ (P Q : Σ 𝔒 𝔓) : Ø ℓ where
    constructor ∁
    field
      π₀ : π₀ P ≈ π₀ Q

  open _≈₀_ public

  instance

    𝓡eflexivityExtensionṖropertyEquivalence : 𝓡eflexivity _≈₀_
    𝓡eflexivityExtensionṖropertyEquivalence .𝓡eflexivity.reflexivity .π₀ = reflexivity

    𝓢ymmetryExtensionṖropertyEquivalence : 𝓢ymmetry _≈₀_
    𝓢ymmetryExtensionṖropertyEquivalence .𝓢ymmetry.symmetry (∁ P≈Q) .π₀ = symmetry P≈Q

    𝓣ransitivityExtensionṖropertyEquivalence : 𝓣ransitivity _≈₀_
    𝓣ransitivityExtensionṖropertyEquivalence .𝓣ransitivity.transitivity (∁ P≈Q) (∁ Q≈R) .π₀ = transitivity P≈Q Q≈R

    IsEquivalenceExtensionṖroperty : IsEquivalence _≈₀_
    IsEquivalenceExtensionṖroperty = ∁

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ}
  {ℓ̇} {_↦_ : ∀ {x} → 𝔒 x → 𝔒 x → Ø ℓ̇}
  where

  instance

    HasEquivalenceExtendedProperty : HasEquivalence (ExtensionṖroperty ℓ 𝔒 _↦_) (𝔵 ∙̂ 𝔬 ∙̂ ℓ)
    HasEquivalenceExtendedProperty .HasEquivalence.Equivalence = _≈₀_

  record ProperlyExtensionNothing (P : ExtensionṖroperty ℓ 𝔒 _↦_) : Ø 𝔵 ∙̂ 𝔬 ∙̂ ℓ where
    constructor ∁
    field
      π₀ : ∀ {n} {f : 𝔒 n} → π₀ (π₀ P) f → 𝟘

  open ProperlyExtensionNothing public

  instance

    ProperthingExtensionṖroperty : Properthing (𝔵 ∙̂ 𝔬 ∙̂ ℓ) (ExtensionṖroperty ℓ 𝔒 _↦_)
    ProperthingExtensionṖroperty .Properthing.➊ = ➊ , (λ _ _ → lift ∅)
    ProperthingExtensionṖroperty .Properthing._∧_ P Q = ∁ (λ f → π₀ (π₀ P) f × π₀ (π₀ Q) f) , λ f≐g Pf×Qf → π₁ P f≐g (π₀ Pf×Qf) , π₁ Q f≐g (π₁ Pf×Qf)
    ProperthingExtensionṖroperty .Properthing.⌶HasEquivalence = !
    ProperthingExtensionṖroperty .Properthing.Nothing = ProperlyExtensionNothing
    ProperthingExtensionṖroperty .Properthing.fact2 (∁ (∁ P⇔Q)) (∁ NoP) .π₀ Q = NoP $ π₁ P⇔Q Q
    ProperthingExtensionṖroperty .Properthing.∧-leftIdentity _ .π₀ .π₀ = π₁ , (lift ∅ ,_)

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
