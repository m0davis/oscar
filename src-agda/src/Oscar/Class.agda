{-# OPTIONS --show-implicit #-}
{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}
module Oscar.Class where

open import Oscar.Prelude
open import Oscar.Data using (_≡_; Proposequality; ∅)
open import Oscar.Class.Reflexivity public
open import Oscar.Class.Transitivity public
open import Oscar.Class.Congruity public
open import Oscar.Class.Symmetrical public
open import Oscar.Class.Symmetry public
open import Oscar.Class.IsEquivalence public
open import Oscar.Class.Setoid public
open import Oscar.Class.Transextensionality public
open import Oscar.Class.Transassociativity public
open import Oscar.Class.IsPrecategory public
open import Oscar.Class.Precategory public
open import Oscar.Class.Surjection public
open import Oscar.Class.Surjectextensivity public
open import Oscar.Class.Surjectivity public
open import Oscar.Class.Surjectextensivity.SurjectivityExtension public
open import Oscar.Class.Surjtranscommutativity public
open import Oscar.Class.Surjextensionality public
open import Oscar.Class.IsPrefunctor public
open import Oscar.Class.Prefunctor public
open import Oscar.Class.Transleftidentity public
open import Oscar.Class.Transrightidentity public
open import Oscar.Class.IsCategory public
open import Oscar.Class.Category public
open import Oscar.Class.Surjidentity public
open import Oscar.Class.IsFunctor public
open import Oscar.Class.Functor public
open import Oscar.Class.Injectivity public
open import Oscar.Class.Successor₀ public
open import Oscar.Class.Successor₁ public
open import Oscar.Class.Map public
open import Oscar.Class.Fmap public
open import Oscar.Class.Apply public
open import Oscar.Class.Pure public
open import Oscar.Class.Bind public
open import Oscar.Class.Thickandthin public
open import Oscar.Class.HasEquivalence public
open import Oscar.Class.IsDecidable public
open import Oscar.Class.Properthing public
open import Oscar.Class.Exotransitivity public
open import Oscar.Class.Amgu public
open import Oscar.Class.Surjectextenscongruity public
open import Oscar.Class.Properfact1 public
open import Oscar.Class.Factsurj3 public
open import Oscar.Class.Factsurj4 public
open import Oscar.Class.Factsurj6 public
open import Oscar.Class.[ExtensibleType] public
open import Oscar.Class.PropId public
open import Oscar.Data

instance

  [𝓢urjectivity]LeftṖroperty : ∀ {ℓ} {a} {f} {¶ : Set a} {_↦_ : ¶ → ¶ → Set f} → [𝓢urjectivity] _↦_ (Extension $ LeftṖroperty ℓ _↦_)
  [𝓢urjectivity]LeftṖroperty = ∁

instance

  𝓢ymmetrical𝓢ymmetry : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {ℓ} {_∼_ : 𝔒 → 𝔒 → Ø ℓ}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
    → 𝓢ymmetrical 𝔒 (λ s t t' s' → s ∼ t → t' ∼ s')
  𝓢ymmetrical𝓢ymmetry .𝓢ymmetrical.symmetrical x y = symmetry

module _ where

  record [IsExtensionB]
    {a} {A : Ø a}
    {b} (B : A → Ø b)
    : Ø₀ where
    constructor ∁
    no-eta-equality
