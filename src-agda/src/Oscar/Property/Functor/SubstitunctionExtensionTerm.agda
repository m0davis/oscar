
open import Oscar.Prelude
open import Oscar.Class.Category
open import Oscar.Class.Congruity
open import Oscar.Class.Functor
open import Oscar.Class.HasEquivalence
open import Oscar.Class.IsCategory
open import Oscar.Class.IsFunctor
open import Oscar.Class.IsPrecategory
open import Oscar.Class.IsPrefunctor
open import Oscar.Class.Precategory
open import Oscar.Class.Prefunctor
open import Oscar.Class.Reflexivity
open import Oscar.Class.Surjection
open import Oscar.Class.Surjectivity
open import Oscar.Class.Surjextensionality
open import Oscar.Class.Surjidentity
open import Oscar.Class.Surjtranscommutativity
open import Oscar.Class.Transassociativity
open import Oscar.Class.Transextensionality
open import Oscar.Class.Transitivity
open import Oscar.Class.Transleftidentity
open import Oscar.Class.Transrightidentity
open import Oscar.Class.[IsExtensionB]
open import Oscar.Data.¶
open import Oscar.Data.Proposequality
open import Oscar.Data.Substitunction
open import Oscar.Data.Term
open import Oscar.Data.Vec
import Oscar.Property.Setoid.Proposequality
import Oscar.Property.Setoid.Proposextensequality
import Oscar.Property.Category.ExtensionProposextensequality
import Oscar.Class.Congruity.Proposequality
import Oscar.Class.HasEquivalence.Substitunction
import Oscar.Class.Surjection.⋆

module Oscar.Property.Functor.SubstitunctionExtensionTerm where

module _ {𝔭} {𝔓 : Ø 𝔭} where

  open Substitunction 𝔓
  open Term 𝔓

  private

    mutual

      𝓼urjectivitySubstitunctionExtensionTerm : 𝓈urjectivity! Substitunction (Extension Term)
      𝓼urjectivitySubstitunctionExtensionTerm σ (i x) = σ x
      𝓼urjectivitySubstitunctionExtensionTerm σ leaf = leaf
      𝓼urjectivitySubstitunctionExtensionTerm σ (τ₁ fork τ₂) = 𝓼urjectivitySubstitunctionExtensionTerm σ τ₁ fork 𝓼urjectivitySubstitunctionExtensionTerm σ τ₂
      𝓼urjectivitySubstitunctionExtensionTerm σ (function p τs) = function p (𝓼urjectivitySubstitunctionExtensionTerms σ τs)

      𝓼urjectivitySubstitunctionExtensionTerms : ∀ {N} → 𝓈urjectivity Substitunction (Extension $ Terms N) surjection
      𝓼urjectivitySubstitunctionExtensionTerms σ ∅ = ∅
      𝓼urjectivitySubstitunctionExtensionTerms σ (τ , τs) = 𝓼urjectivitySubstitunctionExtensionTerm σ τ , 𝓼urjectivitySubstitunctionExtensionTerms σ τs

  instance

    𝓢urjectivitySubstitunctionExtensionTerm : 𝒮urjectivity Substitunction (Extension Term)
    𝓢urjectivitySubstitunctionExtensionTerm .𝓢urjectivity.surjectivity = 𝓼urjectivitySubstitunctionExtensionTerm

    𝓢urjectivitySubstitunctionExtensionTerms : ∀ {N} → 𝒮urjectivity Substitunction (Extension $ Terms N)
    𝓢urjectivitySubstitunctionExtensionTerms .𝓢urjectivity.surjectivity = 𝓼urjectivitySubstitunctionExtensionTerms

  instance

    𝓣ransitivitySubstitunction : 𝓣ransitivity Substitunction
    𝓣ransitivitySubstitunction .𝓣ransitivity.transitivity f g = surjectivity g ∘ f

    [IsExtensionB]Term : [IsExtensionB] Term
    [IsExtensionB]Term = ∁

    [IsExtensionB]Terms : ∀ {N} → [IsExtensionB] (Terms N)
    [IsExtensionB]Terms = ∁

  private

    mutual
      𝓼urjextensionalitySubstitunctionExtensionTerm : 𝓼urjextensionality Substitunction _≈_ (Extension Term) _≈_
      𝓼urjextensionalitySubstitunctionExtensionTerm p (i x) = p x
      𝓼urjextensionalitySubstitunctionExtensionTerm p leaf = ∅
      𝓼urjextensionalitySubstitunctionExtensionTerm p (s fork t) = congruity₂ _fork_ (𝓼urjextensionalitySubstitunctionExtensionTerm p s) (𝓼urjextensionalitySubstitunctionExtensionTerm p t)
      𝓼urjextensionalitySubstitunctionExtensionTerm p (function fn ts) = congruity (function fn) (𝓼urjextensionalitySubstitunctionExtensionTerms p ts)

      𝓼urjextensionalitySubstitunctionExtensionTerms : ∀ {N} → 𝓼urjextensionality Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality
      𝓼urjextensionalitySubstitunctionExtensionTerms p ∅ = ∅
      𝓼urjextensionalitySubstitunctionExtensionTerms p (t , ts) = congruity₂ _,_ (𝓼urjextensionalitySubstitunctionExtensionTerm p t) (𝓼urjextensionalitySubstitunctionExtensionTerms p ts)

  instance

    [𝓢urjextensionality]Substitunction : [𝓢urjextensionality] Substitunction Proposextensequality (Extension Term) Proposextensequality
    [𝓢urjextensionality]Substitunction = ∁

    𝓢urjextensionalitySubstitunction : 𝓢urjextensionality Substitunction Proposextensequality (Extension Term) Proposextensequality
    𝓢urjextensionalitySubstitunction .𝓢urjextensionality.surjextensionality = 𝓼urjextensionalitySubstitunctionExtensionTerm

    [𝓢urjextensionality]Substitunctions : ∀ {N} → [𝓢urjextensionality] Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality
    [𝓢urjextensionality]Substitunctions = ∁

    𝓢urjextensionalitySubstitunctions : ∀ {N} → 𝓢urjextensionality Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality
    𝓢urjextensionalitySubstitunctions .𝓢urjextensionality.surjextensionality = 𝓼urjextensionalitySubstitunctionExtensionTerms

  private

    mutual

      𝓼urjtranscommutativitySubstitunctionExtensionTerm : 𝓼urjtranscommutativity Substitunction (Extension Term) Proposextensequality
      𝓼urjtranscommutativitySubstitunctionExtensionTerm _ _ (i _) = !
      𝓼urjtranscommutativitySubstitunctionExtensionTerm _ _ leaf = !
      𝓼urjtranscommutativitySubstitunctionExtensionTerm _ _ (τ₁ fork τ₂) = congruity₂ _fork_ (𝓼urjtranscommutativitySubstitunctionExtensionTerm _ _ τ₁) (𝓼urjtranscommutativitySubstitunctionExtensionTerm _ _ τ₂)
      𝓼urjtranscommutativitySubstitunctionExtensionTerm f g (function fn ts) = congruity (function fn) (𝓼urjtranscommutativitySubstitunctionExtensionTerms f g ts)

      𝓼urjtranscommutativitySubstitunctionExtensionTerms : ∀ {N} → 𝓼urjtranscommutativity Substitunction (Extension $ Terms N) Proposextensequality
      𝓼urjtranscommutativitySubstitunctionExtensionTerms _ _ ∅ = !
      𝓼urjtranscommutativitySubstitunctionExtensionTerms _ _ (τ , τs) = congruity₂ _,_ (𝓼urjtranscommutativitySubstitunctionExtensionTerm _ _ τ) (𝓼urjtranscommutativitySubstitunctionExtensionTerms _ _ τs)

  instance

    [𝓢urjtranscommutativity]SubstitunctionExtensionTerm = [𝓢urjtranscommutativity] Substitunction (Extension Term) Proposextensequality ∋ ∁
    𝓢urjtranscommutativitySubstitunctionExtensionTerm : 𝓢urjtranscommutativity Substitunction (Extension Term) Proposextensequality
    𝓢urjtranscommutativitySubstitunctionExtensionTerm .𝓢urjtranscommutativity.surjtranscommutativity = 𝓼urjtranscommutativitySubstitunctionExtensionTerm

    [𝓢urjtranscommutativity]SubstitunctionExtensionTerms = λ {N} → [𝓢urjtranscommutativity] Substitunction (Extension $ Terms N) Proposextensequality ∋ ∁
    𝓢urjtranscommutativitySubstitunctionExtensionTerms : ∀ {N} → 𝓢urjtranscommutativity Substitunction (Extension $ Terms N) Proposextensequality
    𝓢urjtranscommutativitySubstitunctionExtensionTerms .𝓢urjtranscommutativity.surjtranscommutativity = 𝓼urjtranscommutativitySubstitunctionExtensionTerms

  instance

    [𝓣ransassociativity]Substitunction : [𝓣ransassociativity] Substitunction _≈_
    [𝓣ransassociativity]Substitunction = ∁

    𝓣ransassociativitySubstitunction : 𝓣ransassociativity Substitunction _≈_
    𝓣ransassociativitySubstitunction .𝓣ransassociativity.transassociativity f g h = surjtranscommutativity g h ∘ f

    [𝓣ransextensionality]Substitunction : [𝓣ransextensionality] Substitunction _≈_
    [𝓣ransextensionality]Substitunction = ∁

    𝓣ransextensionalitySubstitunction : 𝓣ransextensionality Substitunction _≈_
    𝓣ransextensionalitySubstitunction .𝓣ransextensionality.transextensionality {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = surjextensionality g₁≡̇g₂ $ f₂ x

    IsPrecategorySubstitunction : IsPrecategory Substitunction _≈_
    IsPrecategorySubstitunction = ∁

    IsPrefunctorSubstitunctionExtensionTerm : IsPrefunctor Substitunction _≈_ (Extension Term) _≈_
    IsPrefunctorSubstitunctionExtensionTerm = ∁

    IsPrefunctorSubstitunctionExtensionTerms : ∀ {N} → IsPrefunctor Substitunction _≈_ (Extension $ Terms N) _≈_
    IsPrefunctorSubstitunctionExtensionTerms = ∁

    𝓡eflexivitySubstitunction : 𝓡eflexivity Substitunction
    𝓡eflexivitySubstitunction .𝓡eflexivity.reflexivity = i

  private

    mutual

      𝓼urjidentitySubstitunctionExtensionTerm : 𝓼urjidentity Substitunction (Extension Term) _≈_
      𝓼urjidentitySubstitunctionExtensionTerm (i x) = ∅
      𝓼urjidentitySubstitunctionExtensionTerm leaf = ∅
      𝓼urjidentitySubstitunctionExtensionTerm (s fork t) = congruity₂ _fork_ (𝓼urjidentitySubstitunctionExtensionTerm s) (𝓼urjidentitySubstitunctionExtensionTerm t)
      𝓼urjidentitySubstitunctionExtensionTerm (function fn ts) = congruity (function fn) (𝓼urjidentitySubstitunctionExtensionTerms ts)

      𝓼urjidentitySubstitunctionExtensionTerms : ∀ {N} → 𝓼urjidentity Substitunction (Extension $ Terms N) _≈_
      𝓼urjidentitySubstitunctionExtensionTerms ∅ = ∅
      𝓼urjidentitySubstitunctionExtensionTerms (t , ts) = congruity₂ _,_ (𝓼urjidentitySubstitunctionExtensionTerm t) (𝓼urjidentitySubstitunctionExtensionTerms ts)

  instance

    𝓢urjidentitySubstitunctionExtensionTerm : 𝓢urjidentity Substitunction (Extension Term) _≈_
    𝓢urjidentitySubstitunctionExtensionTerm .𝒮urjidentity.surjidentity' = 𝓼urjidentitySubstitunctionExtensionTerm

    𝓢urjidentitySubstitunctionExtensionTerms : ∀ {N} → 𝓢urjidentity Substitunction (Extension $ Terms N) _≈_
    𝓢urjidentitySubstitunctionExtensionTerms .𝒮urjidentity.surjidentity' = 𝓼urjidentitySubstitunctionExtensionTerms

    [𝓣ransleftidentitySubstitunction] : [𝓣ransleftidentity] Substitunction _≈_
    [𝓣ransleftidentitySubstitunction] = ∁

    𝓣ransleftidentitySubstitunction : 𝓣ransleftidentity Substitunction _≈_
    𝓣ransleftidentitySubstitunction .𝓣ransleftidentity.transleftidentity {f = f} = surjidentity ∘ f

    [𝓣ransrightidentitySubstitunction] : [𝓣ransrightidentity] Substitunction _≈_
    [𝓣ransrightidentitySubstitunction] = ∁

    𝓣ransrightidentitySubstitunction : 𝓣ransrightidentity Substitunction _≈_
    𝓣ransrightidentitySubstitunction .𝓣ransrightidentity.transrightidentity _ = !

    IsCategorySubstitunction : IsCategory Substitunction _≈_
    IsCategorySubstitunction = ∁

    IsFunctorSubstitunctionExtensionTerm : IsFunctor Substitunction _≈_ (Extension Term) _≈_
    IsFunctorSubstitunctionExtensionTerm = ∁

    IsFunctorSubstitunctionExtensionTerms : ∀ {N} → IsFunctor Substitunction _≈_ (Extension $ Terms N) _≈_
    IsFunctorSubstitunctionExtensionTerms = ∁

module _ {𝔭} (𝔓 : Ø 𝔭) where

  open Substitunction 𝔓
  open Term 𝔓

  PrecategorySubstitunction : Precategory _ _ _
  PrecategorySubstitunction = ∁ Substitunction _≈_

  PrefunctorSubstitunctionExtensionTerm : Prefunctor _ _ _ _ _ _
  PrefunctorSubstitunctionExtensionTerm = ∁ Substitunction _≈_ (Extension Term) _≈_

  CategorySubstitunction : Category _ _ _
  CategorySubstitunction = ∁ Substitunction _≈_

  FunctorSubstitunctionExtensionTerm : Functor _ _ _ _ _ _
  FunctorSubstitunctionExtensionTerm = ∁ Substitunction _≈_ (Extension Term) _≈_

  module _ (N : ¶) where

    FunctorSubstitunctionExtensionTerms : Functor _ _ _ _ _ _
    FunctorSubstitunctionExtensionTerms = ∁ Substitunction _≈_ (Extension $ Terms N) _≈_
