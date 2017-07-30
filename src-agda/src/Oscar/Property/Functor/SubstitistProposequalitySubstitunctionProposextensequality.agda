
open import Oscar.Prelude
open import Oscar.Class.Reflexivity
open import Oscar.Class.Surjectivity
open import Oscar.Class.Surjextensionality
open import Oscar.Class.Surjidentity
open import Oscar.Class.Surjtranscommutativity
open import Oscar.Class.HasEquivalence
open import Oscar.Class.Transitivity
open import Oscar.Class.Thickandthin
open import Oscar.Class.IsPrefunctor
open import Oscar.Class.IsFunctor
open import Oscar.Data.Maybe
open import Oscar.Data.¶
open import Oscar.Data.Fin
open import Oscar.Data.Proposequality
open import Oscar.Data.Substitunction
open import Oscar.Data.Term
open import Oscar.Data.Substitist
open import Oscar.Data.Descender
import Oscar.Property.Setoid.Proposextensequality
import Oscar.Property.Functor.SubstitunctionExtensionTerm
import Oscar.Property.Category.AListProposequality
import Oscar.Property.Category.ExtensionProposextensequality
import Oscar.Property.Thickandthin.FinFinProposequalityMaybeProposequality
import Oscar.Class.HasEquivalence.Substitunction
import Oscar.Class.Surjection.⋆

module Oscar.Property.Functor.SubstitistProposequalitySubstitunctionProposextensequality where

module _ {𝔭} {𝔓 : Ø 𝔭} where

  open Substitunction 𝔓
  open Term 𝔓
  open Substitist 𝔓

  _for_ : ∀ {n} (t' : Term n) (x : Fin (↑ n)) → Fin (↑ n) → Term n
  (t for x) y = maybe′ ε t (check[ Maybe ] x y)

  instance

    [𝓢urjectivity]Substitist,Substitunction : [𝓢urjectivity] Substitist Substitunction
    [𝓢urjectivity]Substitist,Substitunction = ∁

    𝓢urjectivitySubstitist,Substitunction : 𝓢urjectivity Substitist Substitunction
    𝓢urjectivitySubstitist,Substitunction .𝓢urjectivity.surjectivity ∅ = i
    𝓢urjectivitySubstitist,Substitunction .𝓢urjectivity.surjectivity ((x , t) , σ) = surjectivity σ ∙ (t for x)

    [𝓢urjextensionality]Substitist,Substitunction : [𝓢urjextensionality] Substitist Proposequality Substitunction _≈_
    [𝓢urjextensionality]Substitist,Substitunction = ∁

    𝓢urjextensionalitySubstitist,Substitunction : 𝓢urjextensionality Substitist Proposequality Substitunction _≈_
    𝓢urjextensionalitySubstitist,Substitunction .𝓢urjextensionality.surjextensionality ∅ _ = ∅

    [𝓢urjtranscommutativity]Substitist,Substitunction : [𝓢urjtranscommutativity] Substitist Substitunction _≈_
    [𝓢urjtranscommutativity]Substitist,Substitunction = ∁

    𝓢urjtranscommutativitySubstitist,Substitunction : 𝓢urjtranscommutativity Substitist Substitunction _≈_
    𝓢urjtranscommutativitySubstitist,Substitunction .𝓢urjtranscommutativity.surjtranscommutativity ∅ _ _ = ∅
    𝓢urjtranscommutativitySubstitist,Substitunction .𝓢urjtranscommutativity.surjtranscommutativity ((π₀ , π₁) , f) g =
        (
            § g ⟪∙⟫ §[ Substitunction ] f
          ∙
            ⟪ surjtranscommutativity {_∼̇₂_ = Proposextensequality} f g ⟫
        )
      ∘
        π₁ for π₀

    IsPrefunctorSubstitist,Substitunction : IsPrefunctor Substitist Proposequality Substitunction _≈_
    IsPrefunctorSubstitist,Substitunction = ∁

    [𝓢urjidentity]Substitist,Substitunction : [𝓢urjidentity] Substitist Substitunction _≈_
    [𝓢urjidentity]Substitist,Substitunction = ∁ Substitist Substitunction _≈_

    𝓢urjidentitySubstitist,Substitunction : 𝓢urjidentity Substitist Substitunction _≈_
    𝓢urjidentitySubstitist,Substitunction .𝒮urjidentity.surjidentity _ = ∅

    IsFunctorSubstitist,Substitunction : IsFunctor Substitist Proposequality Substitunction _≈_
    IsFunctorSubstitist,Substitunction = ∁
