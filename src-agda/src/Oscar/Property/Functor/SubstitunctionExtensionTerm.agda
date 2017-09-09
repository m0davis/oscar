
open import Oscar.Prelude
open import Oscar.Class
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
open import Oscar.Class.Smap
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

      𝓼urjectivitySubstitunctionExtensionTerm : Smap!.type Substitunction (Extension Term)
      𝓼urjectivitySubstitunctionExtensionTerm σ (i x) = σ x
      𝓼urjectivitySubstitunctionExtensionTerm σ leaf = leaf
      𝓼urjectivitySubstitunctionExtensionTerm σ (τ₁ fork τ₂) = 𝓼urjectivitySubstitunctionExtensionTerm σ τ₁ fork 𝓼urjectivitySubstitunctionExtensionTerm σ τ₂
      𝓼urjectivitySubstitunctionExtensionTerm σ (function p τs) = function p (𝓼urjectivitySubstitunctionExtensionTerms σ τs)

      𝓼urjectivitySubstitunctionExtensionTerms : ∀ {N} → Smap.type Substitunction (Extension $ Terms N) surjection surjection
      𝓼urjectivitySubstitunctionExtensionTerms σ ∅ = ∅
      𝓼urjectivitySubstitunctionExtensionTerms σ (τ , τs) = 𝓼urjectivitySubstitunctionExtensionTerm σ τ , 𝓼urjectivitySubstitunctionExtensionTerms σ τs

  instance

    𝓢urjectivitySubstitunctionExtensionTerm : Smap!.class Substitunction (Extension Term)
    𝓢urjectivitySubstitunctionExtensionTerm .⋆ _ _ = 𝓼urjectivitySubstitunctionExtensionTerm

    𝓢urjectivitySubstitunctionExtensionTerms : ∀ {N} → Smap!.class Substitunction (Extension $ Terms N)
    𝓢urjectivitySubstitunctionExtensionTerms .⋆ _ _ = 𝓼urjectivitySubstitunctionExtensionTerms

  instance

    𝓣ransitivitySubstitunction : Transitivity.class Substitunction
    𝓣ransitivitySubstitunction {x∼y = f} {g} .⋆ = smap g ∘ f

    [IsExtensionB]Term : [IsExtensionB] Term
    [IsExtensionB]Term = ∁

    [IsExtensionB]Terms : ∀ {N} → [IsExtensionB] (Terms N)
    [IsExtensionB]Terms = ∁

  private

    mutual
      𝓼urjextensionalitySubstitunctionExtensionTerm : Surjextensionality!.TYPE Substitunction _≈_ (Extension Term) _≈_
      𝓼urjextensionalitySubstitunctionExtensionTerm p (i x) = p x
      𝓼urjextensionalitySubstitunctionExtensionTerm p leaf = ∅
      𝓼urjextensionalitySubstitunctionExtensionTerm p (s fork t) = congruity₂ _fork_ (𝓼urjextensionalitySubstitunctionExtensionTerm p s) (𝓼urjextensionalitySubstitunctionExtensionTerm p t)
      𝓼urjextensionalitySubstitunctionExtensionTerm p (function fn ts) = congruity (function fn) (𝓼urjextensionalitySubstitunctionExtensionTerms p ts)

      𝓼urjextensionalitySubstitunctionExtensionTerms : ∀ {N} → Surjextensionality!.TYPE Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality
      𝓼urjextensionalitySubstitunctionExtensionTerms p ∅ = ∅
      𝓼urjextensionalitySubstitunctionExtensionTerms p (t , ts) = congruity₂ _,_ (𝓼urjextensionalitySubstitunctionExtensionTerm p t) (𝓼urjextensionalitySubstitunctionExtensionTerms p ts)

  instance

    𝓢urjextensionalitySubstitunction : Surjextensionality!.class Substitunction Proposextensequality (Extension Term) Proposextensequality
    𝓢urjextensionalitySubstitunction .⋆ _ _ _ _ = 𝓼urjextensionalitySubstitunctionExtensionTerm

    𝓢urjextensionalitySubstitunctions : ∀ {N} → Surjextensionality!.class Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality
    𝓢urjextensionalitySubstitunctions .⋆ _ _ _ _ = 𝓼urjextensionalitySubstitunctionExtensionTerms

  private

    mutual

      𝓼urjtranscommutativitySubstitunctionExtensionTerm : Surjtranscommutativity!.type Substitunction (Extension Term) Proposextensequality
      𝓼urjtranscommutativitySubstitunctionExtensionTerm _ _ (i _) = !
      𝓼urjtranscommutativitySubstitunctionExtensionTerm _ _ leaf = !
      𝓼urjtranscommutativitySubstitunctionExtensionTerm _ _ (τ₁ fork τ₂) = congruity₂ _fork_ (𝓼urjtranscommutativitySubstitunctionExtensionTerm _ _ τ₁) (𝓼urjtranscommutativitySubstitunctionExtensionTerm _ _ τ₂)
      𝓼urjtranscommutativitySubstitunctionExtensionTerm f g (function fn ts) = congruity (function fn) (𝓼urjtranscommutativitySubstitunctionExtensionTerms f g ts)

      𝓼urjtranscommutativitySubstitunctionExtensionTerms : ∀ {N} → Surjtranscommutativity!.type Substitunction (Extension $ Terms N) Proposextensequality
      𝓼urjtranscommutativitySubstitunctionExtensionTerms _ _ ∅ = !
      𝓼urjtranscommutativitySubstitunctionExtensionTerms _ _ (τ , τs) = congruity₂ _,_ (𝓼urjtranscommutativitySubstitunctionExtensionTerm _ _ τ) (𝓼urjtranscommutativitySubstitunctionExtensionTerms _ _ τs)

  instance

    𝓢urjtranscommutativitySubstitunctionExtensionTerm : Surjtranscommutativity!.class Substitunction (Extension Term) Proposextensequality
    𝓢urjtranscommutativitySubstitunctionExtensionTerm .⋆ = 𝓼urjtranscommutativitySubstitunctionExtensionTerm

    𝓢urjtranscommutativitySubstitunctionExtensionTerms : ∀ {N} → Surjtranscommutativity!.class Substitunction (Extension $ Terms N) Proposextensequality
    𝓢urjtranscommutativitySubstitunctionExtensionTerms .⋆ = 𝓼urjtranscommutativitySubstitunctionExtensionTerms

  instance

    𝓣ransassociativitySubstitunction : Transassociativity!.class Substitunction _≈_
    𝓣ransassociativitySubstitunction .⋆ f g h = surjtranscommutativity g h ∘ f

    𝓣ransextensionalitySubstitunction : Transextensionality!.class Substitunction _≈_
    𝓣ransextensionalitySubstitunction .⋆ {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = surjextensionality g₁≡̇g₂ $ f₂ x

    IsPrecategorySubstitunction : IsPrecategory Substitunction _≈_ transitivity[ Substitunction ]
    IsPrecategorySubstitunction = ∁

    IsPrefunctorSubstitunctionExtensionTerm : IsPrefunctor Substitunction _≈_ transitivity[ Substitunction ] (Extension Term) _≈_ transitivity[ Extension Term ]
    IsPrefunctorSubstitunctionExtensionTerm = ∁

    IsPrefunctorSubstitunctionExtensionTerms : ∀ {N} → IsPrefunctor Substitunction _≈_ transitivity[ Substitunction ] (Extension $ Terms N) _≈_ transitivity[ Extension $ Terms N ]
    IsPrefunctorSubstitunctionExtensionTerms = ∁

    𝓡eflexivitySubstitunction : Reflexivity.class Substitunction
    𝓡eflexivitySubstitunction .⋆ = i

  private

    mutual

      𝓼urjidentitySubstitunctionExtensionTerm : Surjidentity!.type Substitunction (Extension Term) _≈_
      𝓼urjidentitySubstitunctionExtensionTerm (i x) = ∅
      𝓼urjidentitySubstitunctionExtensionTerm leaf = ∅
      𝓼urjidentitySubstitunctionExtensionTerm (s fork t) = congruity₂ _fork_ (𝓼urjidentitySubstitunctionExtensionTerm s) (𝓼urjidentitySubstitunctionExtensionTerm t)
      𝓼urjidentitySubstitunctionExtensionTerm (function fn ts) = congruity (function fn) (𝓼urjidentitySubstitunctionExtensionTerms ts)

      𝓼urjidentitySubstitunctionExtensionTerms : ∀ {N} → Surjidentity!.type Substitunction (Extension $ Terms N) _≈_
      𝓼urjidentitySubstitunctionExtensionTerms ∅ = ∅
      𝓼urjidentitySubstitunctionExtensionTerms (t , ts) = congruity₂ _,_ (𝓼urjidentitySubstitunctionExtensionTerm t) (𝓼urjidentitySubstitunctionExtensionTerms ts)

  instance

    𝓢urjidentitySubstitunctionExtensionTerm : Surjidentity!.class Substitunction (Extension Term) _≈_
    𝓢urjidentitySubstitunctionExtensionTerm .⋆ = 𝓼urjidentitySubstitunctionExtensionTerm

    𝓢urjidentitySubstitunctionExtensionTerms : ∀ {N} → Surjidentity!.class Substitunction (Extension $ Terms N) _≈_
    𝓢urjidentitySubstitunctionExtensionTerms .⋆ = 𝓼urjidentitySubstitunctionExtensionTerms

    𝓣ransleftidentitySubstitunction : Transleftidentity!.class Substitunction _≈_
    𝓣ransleftidentitySubstitunction .⋆ {f = f} = surjidentity ∘ f

    𝓣ransrightidentitySubstitunction : Transrightidentity!.class Substitunction _≈_
    𝓣ransrightidentitySubstitunction .⋆ _ = !

    IsCategorySubstitunction : IsCategory Substitunction _≈_ transitivity[ Substitunction ]
    IsCategorySubstitunction = ∁

    IsFunctorSubstitunctionExtensionTerm : IsFunctor Substitunction _≈_ transitivity[ Substitunction ] (Extension Term) _≈_ transitivity[ Extension Term ]
    IsFunctorSubstitunctionExtensionTerm = ∁

    IsFunctorSubstitunctionExtensionTerms : ∀ {N} → IsFunctor Substitunction _≈_ transitivity[ Substitunction ] (Extension $ Terms N) _≈_ transitivity[ Extension $ Terms N ]
    IsFunctorSubstitunctionExtensionTerms = ∁

module _ {𝔭} (𝔓 : Ø 𝔭) where

  open Substitunction 𝔓
  open Term 𝔓

  PrecategorySubstitunction : Precategory _ _ _
  PrecategorySubstitunction = ∁ Substitunction _≈_ transitivity[ Substitunction ]

  PrefunctorSubstitunctionExtensionTerm : Prefunctor _ _ _ _ _ _
  PrefunctorSubstitunctionExtensionTerm = ∁ Substitunction _≈_ transitivity[ Substitunction ] (Extension Term) _≈_ transitivity[ Extension Term ]

  CategorySubstitunction : Category _ _ _
  CategorySubstitunction = ∁ Substitunction _≈_ transitivity[ Substitunction ]

  FunctorSubstitunctionExtensionTerm : Functor _ _ _ _ _ _
  FunctorSubstitunctionExtensionTerm = ∁ Substitunction _≈_ transitivity[ Substitunction ] (Extension Term) _≈_ transitivity[ Extension Term ]

  module _ (N : ¶) where

    FunctorSubstitunctionExtensionTerms : Functor _ _ _ _ _ _
    FunctorSubstitunctionExtensionTerms = ∁ Substitunction _≈_ transitivity[ Substitunction ] (Extension $ Terms N) _≈_ transitivity[ Extension $ Terms N ]
