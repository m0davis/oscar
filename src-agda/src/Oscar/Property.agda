
module Oscar.Property where

open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data

module Nat⌶ where



module Proposequality⌶ where

  module _ {𝔬} {𝔒 : Ø 𝔬} where

    instance

      ReflexivityProposequality : Reflexivity Proposequality⟦ 𝔒 ⟧
      Reflexivity.reflexivity ReflexivityProposequality = ∅

      SymmetryProposequality : Symmetry Proposequality⟦ 𝔒 ⟧
      Symmetry.symmetry SymmetryProposequality ∅ = ∅

      TransitivityProposequality : Transitivity Proposequality⟦ 𝔒 ⟧
      Transitivity.transitivity TransitivityProposequality ∅ = ¡

      IsSetoidProposequality : IsSetoid Proposequality⟦ 𝔒 ⟧
      IsSetoidProposequality = record {}

  instance

    CongruityProposequality : ∀ {a b} → Congruity a b Proposequality
    Congruity.congruity CongruityProposequality _ ∅ = ∅

    Congruity₂Proposequality : ∀ {a b c} → Congruity₂ a b c Proposequality
    Congruity₂.congruity₂ Congruity₂Proposequality _ ∅ ∅ = ∅

  instance

    Extensionality₂⌶Proposequality : ∀ {a} {A : Set a} {b} {B : A → A → Ø b}
      → {T : 𝓽ransitivity B}
      → Extensionality₂′ B Proposequality (λ f₁ f₂ g₁ g₂ → T f₁ g₁ ≡ T f₂ g₂)
    Extensionality₂′.extensionality₂ Extensionality₂⌶Proposequality = congruity₂ _

open Proposequality⌶ public

module ProposequalityØ where

  module _ {𝔬} (𝔒 : Ø 𝔬) where

    SetoidProposequality : Setoid _ _
    Setoid.Object SetoidProposequality = _
    Setoid.Eq SetoidProposequality = Proposequality⟦ 𝔒 ⟧

open ProposequalityØ public

module Proposextensequality⌶ where

  module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} where

    instance

      ReflexivityProposextensequality : Reflexivity Proposextensequality⟦ 𝔓 ⟧
      Reflexivity.reflexivity ReflexivityProposextensequality _ = ∅

      SymmetryProposextensequality : Symmetry Proposextensequality⟦ 𝔓 ⟧
      Symmetry.symmetry SymmetryProposextensequality f₁≡̇f₂ x rewrite f₁≡̇f₂ x = ∅

      TransitivityProposextensequality : Transitivity Proposextensequality⟦ 𝔓 ⟧
      Transitivity.transitivity TransitivityProposextensequality f₁≡̇f₂ f₂≡̇f₃ x rewrite f₁≡̇f₂ x | f₂≡̇f₃ x = ∅

      IsSetoidProposextensequality : IsSetoid Proposextensequality⟦ 𝔓 ⟧
      IsSetoidProposextensequality = record {}

  instance

    ĊongruityProposextensequality : ∀ {a b} → Ċongruity a b Proposextensequality
    Ċongruity.ċongruity ĊongruityProposextensequality F f≡̇g x rewrite f≡̇g x = ∅

open Proposextensequality⌶ public

module ProposextensequalityØ where

  module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) where

    SetoidProposextensequality : Setoid _ _
    Setoid.Object SetoidProposextensequality = _
    Setoid.Eq SetoidProposextensequality = Proposextensequality⟦ 𝔓 ⟧

open ProposextensequalityØ public

module Function⌶ where

  module _
    {a}
    where

    instance

      ReflexivityFunction : Reflexivity Function⟦ a ⟧
      Reflexivity.reflexivity ReflexivityFunction = ¡

      TransitivityFunction : Transitivity Function⟦ a ⟧
      Transitivity.transitivity TransitivityFunction f g = g ∘ f

open Function⌶ public

module Extension⌶ where

  module _
    {a} {A : Ø a} {b} {B : A → Ø b}
    where

    instance

      ReflexivityExtension : Reflexivity (Extension B)
      Reflexivity.reflexivity ReflexivityExtension = ¡

      TransitivityExtension : Transitivity (Extension B)
      Transitivity.transitivity TransitivityExtension f g = g ∘ f

      EquivalenceExtension : ∀ {x y} → Equivalence (Extension B x y) b
      Equivalence.equivalence EquivalenceExtension = Proposextensequality

      MorphismEquivalenceExtension : MorphismEquivalence (Extension B) b
      MorphismEquivalence.morphismEquivalence MorphismEquivalenceExtension = Proposextensequality

      Extensionality₂Extension : Extensionality₂ (Extension B) b
      Extensionality₂′.extensionality₂ Extensionality₂Extension {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = g₁≡̇g₂ (f₂ x)

      AssociativityExtension : Associativity (Extension B) b
      Associativity′.associativity AssociativityExtension _ _ _ _ = ∅

      IsSemigroupoidExtension : IsSemigroupoid (Extension B) b
      IsSemigroupoidExtension = record {}

      LeftIdentityExtension : LeftIdentity (Extension B) b
      LeftIdentity′.left-identity LeftIdentityExtension _ _ = ∅

      RightIdentityExtension : RightIdentity (Extension B) b
      RightIdentity′.right-identity RightIdentityExtension _ _ = ∅

      IsCategoryExtension : IsCategory (Extension B) _
      IsCategoryExtension = record {}

open Extension⌶ public

record Substitunction⌶ {𝔭} (𝔓 : Ø 𝔭) : Ø₀ where
  no-eta-equality

  open Substitunction 𝔓
  open Term 𝔓

  instance

    MorphismEquivalenceSubstitunction : MorphismEquivalence Substitunction _
    MorphismEquivalence.morphismEquivalence MorphismEquivalenceSubstitunction = Proposextensequality

  private

    mutual

      𝓶apSubstitunctionExtensionTerm : 𝓶ap Substitunction (Extension Term)
      𝓶apSubstitunctionExtensionTerm σ (i x) = σ x
      𝓶apSubstitunctionExtensionTerm σ leaf = leaf
      𝓶apSubstitunctionExtensionTerm σ (τ₁ fork τ₂) = 𝓶apSubstitunctionExtensionTerm σ τ₁ fork 𝓶apSubstitunctionExtensionTerm σ τ₂
      𝓶apSubstitunctionExtensionTerm σ (function p τs) = function p (𝓶apSubstitunctionExtensionTerms σ τs)

      𝓶apSubstitunctionExtensionTerms : ∀ {N} → 𝓶ap Substitunction (Extension $ Terms N)
      𝓶apSubstitunctionExtensionTerms σ ∅ = ∅
      𝓶apSubstitunctionExtensionTerms σ (τ , τs) = 𝓶apSubstitunctionExtensionTerm σ τ , 𝓶apSubstitunctionExtensionTerms σ τs

  instance

    Substitunction,ExtensionTerm⌶Map : Map Substitunction (Extension Term)
    Map.map Substitunction,ExtensionTerm⌶Map = 𝓶apSubstitunctionExtensionTerm

    Substitunction,ExtensionTerms⌶Map : ∀ {N} → Map Substitunction (Extension $ Terms N)
    Map.map Substitunction,ExtensionTerms⌶Map = 𝓶apSubstitunctionExtensionTerms

    TransitivitySubstitunction : Transitivity Substitunction
    Transitivity.transitivity TransitivitySubstitunction f g = map g ∘ f

  private

    mutual

      𝓮xtensionality₁SubstitunctionExtensionTerm : 𝓮xtensionality₁ Substitunction _ (Extension Term) _ ¡
      𝓮xtensionality₁SubstitunctionExtensionTerm p (i x) = p x
      𝓮xtensionality₁SubstitunctionExtensionTerm p leaf = ∅
      𝓮xtensionality₁SubstitunctionExtensionTerm p (s fork t) = congruity₂ _fork_ (𝓮xtensionality₁SubstitunctionExtensionTerm p s) (𝓮xtensionality₁SubstitunctionExtensionTerm p t)
      𝓮xtensionality₁SubstitunctionExtensionTerm p (function fn ts) = congruity (function fn) (𝓮xtensionality₁SubstitunctionExtensionTerms p ts)

      𝓮xtensionality₁SubstitunctionExtensionTerms : ∀ {N} → 𝓮xtensionality₁ Substitunction _ (Extension $ Terms N) _ ¡
      𝓮xtensionality₁SubstitunctionExtensionTerms p ∅ = ∅
      𝓮xtensionality₁SubstitunctionExtensionTerms p (t , ts) = congruity₂ _,_ (𝓮xtensionality₁SubstitunctionExtensionTerm p t) (𝓮xtensionality₁SubstitunctionExtensionTerms p ts)

  instance

    Extensionality₁Substitunction : Extensionality₁ Substitunction _ (Extension Term) _ ¡
    Extensionality₁′.extensionality₁ Extensionality₁Substitunction = 𝓮xtensionality₁SubstitunctionExtensionTerm

    Extensionality₁Substitunctions : ∀ {N} → Extensionality₁ Substitunction _ (Extension $ Terms N) _ ¡
    Extensionality₁′.extensionality₁ Extensionality₁Substitunctions = 𝓮xtensionality₁SubstitunctionExtensionTerms

  private

    mutual

      𝓬ommutativitySubstitunctionExtensionTerm : 𝓬ommutativity Substitunction (Extension Term) _ ¡
      𝓬ommutativitySubstitunctionExtensionTerm _ _ (i _) = ∅
      𝓬ommutativitySubstitunctionExtensionTerm _ _ leaf = ∅
      𝓬ommutativitySubstitunctionExtensionTerm _ _ (τ₁ fork τ₂) = congruity₂ _fork_ (𝓬ommutativitySubstitunctionExtensionTerm _ _ τ₁) (𝓬ommutativitySubstitunctionExtensionTerm _ _ τ₂)
      𝓬ommutativitySubstitunctionExtensionTerm f g (function fn ts) = congruity (function fn) (𝓬ommutativitySubstitunctionExtensionTerms f g ts)

      𝓬ommutativitySubstitunctionExtensionTerms : ∀ {N} → 𝓬ommutativity Substitunction (Extension $ Terms N) _ ¡
      𝓬ommutativitySubstitunctionExtensionTerms _ _ ∅ = ∅
      𝓬ommutativitySubstitunctionExtensionTerms _ _ (τ , τs) = congruity₂ _,_ (𝓬ommutativitySubstitunctionExtensionTerm _ _ τ) (𝓬ommutativitySubstitunctionExtensionTerms _ _ τs)

  instance

    CommtativitySubstitunctionExtensionTerm : Commutativity Substitunction (Extension Term) _ ¡
    Commutativity′.commutativity CommtativitySubstitunctionExtensionTerm = 𝓬ommutativitySubstitunctionExtensionTerm

    CommtativitySubstitunctionExtensionTerms : ∀ {N} → Commutativity Substitunction (Extension $ Terms N) _ ¡
    Commutativity′.commutativity CommtativitySubstitunctionExtensionTerms = 𝓬ommutativitySubstitunctionExtensionTerms

    AssociativitySubstitunction : Associativity Substitunction _
    Associativity′.associativity AssociativitySubstitunction f g h x = commutativity g h $ f x

    Extensionality₂Substitunction : Extensionality₂ Substitunction _
    Extensionality₂′.extensionality₂ Extensionality₂Substitunction {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = extensionality₁ g₁≡̇g₂ $ f₂ x

    IsSemigroupoidSubstitunction : IsSemigroupoid Substitunction _
    IsSemigroupoidSubstitunction = record {}

    IsSemifunctorSubstitunctionExtensionTerm : IsSemifunctor Substitunction _ (Extension Term) _ ¡
    IsSemifunctorSubstitunctionExtensionTerm = record {}

    IsSemifunctorSubstitunctionExtensionTerms : ∀ {N} → IsSemifunctor Substitunction _ (Extension $ Terms N) _ ¡
    IsSemifunctorSubstitunctionExtensionTerms = record {}

    ReflexivitySubstitunction : Reflexivity Substitunction
    Reflexivity.reflexivity ReflexivitySubstitunction = i

  private

    mutual

      𝓲dentitySubstitunctionExtensionTerm : 𝓲dentity Substitunction (Extension Term) _ ¡
      𝓲dentitySubstitunctionExtensionTerm (i x) = ∅
      𝓲dentitySubstitunctionExtensionTerm leaf = ∅
      𝓲dentitySubstitunctionExtensionTerm (s fork t) = congruity₂ _fork_ (𝓲dentitySubstitunctionExtensionTerm s) (𝓲dentitySubstitunctionExtensionTerm t)
      𝓲dentitySubstitunctionExtensionTerm (function fn ts) = congruity (function fn) (𝓲dentitySubstitunctionExtensionTerms ts)

      𝓲dentitySubstitunctionExtensionTerms : ∀ {N} → 𝓲dentity Substitunction (Extension $ Terms N) _ ¡
      𝓲dentitySubstitunctionExtensionTerms ∅ = ∅
      𝓲dentitySubstitunctionExtensionTerms (t , ts) = congruity₂ _,_ (𝓲dentitySubstitunctionExtensionTerm t) (𝓲dentitySubstitunctionExtensionTerms ts)

  instance

    IdentitySubstitunctionExtensionTerm : Identity Substitunction (Extension Term) _ ¡
    Identity′.identity IdentitySubstitunctionExtensionTerm = 𝓲dentitySubstitunctionExtensionTerm

    IdentitySubstitunctionExtensionTerms : ∀ {N} → Identity Substitunction (Extension $ Terms N) _ ¡
    Identity′.identity IdentitySubstitunctionExtensionTerms = 𝓲dentitySubstitunctionExtensionTerms

    LeftIdentitySubstitunction : LeftIdentity Substitunction _
    LeftIdentity′.left-identity LeftIdentitySubstitunction f = identity ∘ f

    RightIdentitySubstitunction : RightIdentity Substitunction _
    RightIdentity′.right-identity RightIdentitySubstitunction _ _ = ∅

    IsCategorySubstitunction : IsCategory Substitunction _
    IsCategorySubstitunction = record {}

    IsFunctorSubstitunctionExtensionTerm : IsFunctor Substitunction _ (Extension Term) _ ¡
    IsFunctorSubstitunctionExtensionTerm = record {}

    IsFunctorSubstitunctionExtensionTerms : ∀ {N} → IsFunctor Substitunction _ (Extension $ Terms N) _ ¡
    IsFunctorSubstitunctionExtensionTerms = record {}

module SubstitunctionØ {𝔭} (𝔓 : Ø 𝔭) where

  open Substitunction 𝔓
  open Term 𝔓

  open Substitunction⌶ (Substitunction⌶ 𝔓 ∋ record {})

  SemigroupoidSubstitunction : Semigroupoid _ _ _
  Semigroupoid.Object SemigroupoidSubstitunction = _
  Semigroupoid.Morphism SemigroupoidSubstitunction = Substitunction

  SemifunctorSubstitunctionExtensionTerm : Semifunctor _ _ _ _ _ _
  Semifunctor.Object₁ SemifunctorSubstitunctionExtensionTerm = _
  Semifunctor.Morphism₁ SemifunctorSubstitunctionExtensionTerm = Substitunction
  Semifunctor.Object₂ SemifunctorSubstitunctionExtensionTerm = _
  Semifunctor.Morphism₂ SemifunctorSubstitunctionExtensionTerm = Extension Term
  Semifunctor.μ SemifunctorSubstitunctionExtensionTerm = ¡

  CategorySubstitunction : Category _ _ _
  Category.Object CategorySubstitunction = _
  Category.Morphism CategorySubstitunction = Substitunction

  FunctorSubstitunctionExtensionTerm : Functor _ _ _ _ _ _
  Functor.Object₁ FunctorSubstitunctionExtensionTerm = _
  Functor.Morphism₁ FunctorSubstitunctionExtensionTerm = Substitunction
  Functor.Object₂ FunctorSubstitunctionExtensionTerm = _
  Functor.Morphism₂ FunctorSubstitunctionExtensionTerm = Extension Term
  Functor.μ FunctorSubstitunctionExtensionTerm = ¡

  module _ (N : ¶) where

    FunctorSubstitunctionExtensionTerms : Functor _ _ _ _ _ _
    Functor.Object₁ FunctorSubstitunctionExtensionTerms = _
    Functor.Morphism₁ FunctorSubstitunctionExtensionTerms = Substitunction
    Functor.Object₂ FunctorSubstitunctionExtensionTerms = _
    Functor.Morphism₂ FunctorSubstitunctionExtensionTerms = Extension $ Terms N
    Functor.μ FunctorSubstitunctionExtensionTerms = ¡

open SubstitunctionØ public

module AList⌶ {a} {A : Nat → Set a} where

  private AList = Descender⟨ A ⟩

  instance

    Reflexivity⌶AList : Reflexivity AList
    Reflexivity.reflexivity Reflexivity⌶AList = ∅

    Transitivity⌶AList : Transitivity AList
    Transitivity.transitivity Transitivity⌶AList f ∅ = f
    Transitivity.transitivity Transitivity⌶AList f (x , g) = x , transitivity f g

    MorphismEquivalence⌶AList : MorphismEquivalence AList _
    MorphismEquivalence.morphismEquivalence MorphismEquivalence⌶AList = Proposequality

    Associativity⌶AList : Associativity AList _
    Associativity′.associativity Associativity⌶AList _ _ ∅ = ∅
    Associativity′.associativity Associativity⌶AList f g (x , h) = congruity (x ,_) $ associativity f g h

    IsSemigroupoid⌶AList : IsSemigroupoid AList _
    IsSemigroupoid⌶AList = record {}

    LeftIdentity⌶AList : LeftIdentity AList _
    LeftIdentity′.left-identity LeftIdentity⌶AList _ = ∅

    RightIdentity⌶AList : RightIdentity AList _
    RightIdentity′.right-identity RightIdentity⌶AList ∅ = ∅
    RightIdentity′.right-identity RightIdentity⌶AList (x , f) = congruity (x ,_) $ right-identity f

    IsCategory⌶AList : IsCategory AList _
    IsCategory⌶AList = record {}

module Substitist⌶ {𝔭} {𝔓 : Ø 𝔭} where

  open Substitunction 𝔓
  open Term 𝔓
  open Substitist 𝔓
  open Substitunction⌶ (Substitunction⌶ 𝔓 ∋ record {})

  postulate
    _for_ : ∀ {n} (t' : Term n) (x : Fin (↑ n)) -> Fin (↑ n) -> Term n

  instance

    Map⌶Substitist,Substitunction : Map Substitist Substitunction
    Map.map Map⌶Substitist,Substitunction ∅ = i
    Map.map Map⌶Substitist,Substitunction ((x , t) , σ) = map σ ∙ (t for x)

-- module Fin⌶ where

--   instance

--     Upper⌶Fin : Upper Fin
--     Upper.up Upper⌶Fin = ↑_

--     ThickAndThin⌶Fin : ThickAndThin Fin Fin
--     ThickAndThin.thin ThickAndThin⌶Fin ∅ y = ↑ y
--     ThickAndThin.thin ThickAndThin⌶Fin (↑ x) ∅ = ∅
--     ThickAndThin.thin ThickAndThin⌶Fin (↑ x) (↑ y) = ↑ thin x y
--     ThickAndThin.thin-injective ThickAndThin⌶Fin x x₁ = {!!}
--     ThickAndThin.thick ThickAndThin⌶Fin = {!!}
--     ThickAndThin.thick∘thin=id ThickAndThin⌶Fin = {!!}
--     ThickAndThin.check ThickAndThin⌶Fin = {!!}
--     ThickAndThin.thin-check-id ThickAndThin⌶Fin = {!!}

-- module Term⌶ {𝔭} {𝔓 : Ø 𝔭} where

--   open Term 𝔓

-- --   instance

-- --     ThickAndThin⌶Term : ThickAndThin Term
-- --     ThickAndThin.thin ThickAndThin⌶Term x (i x₁) = {!!}
-- --     ThickAndThin.thin ThickAndThin⌶Term x leaf = {!!}
-- --     ThickAndThin.thin ThickAndThin⌶Term x (x₁ fork x₂) = {!!}
-- --     ThickAndThin.thin ThickAndThin⌶Term x (function x₁ x₂) = {!!}
-- --     ThickAndThin.thin-injective ThickAndThin⌶Term = {!!}
-- --     ThickAndThin.thick ThickAndThin⌶Term = {!!}
-- --     ThickAndThin.thick∘thin=id ThickAndThin⌶Term = {!!}
-- --     ThickAndThin.check ThickAndThin⌶Term = {!!}
-- --     ThickAndThin.thin-check-id ThickAndThin⌶Term = {!!}

-- -- {-
-- -- Data
-- --   Nat
-- --   ≤↓List -- m ≤ n, n-1...m
-- --   Substitunction
-- --   Substitist
-- -- Record
-- --   Product
-- --   Functor
-- -- Class
-- --   Reflexivity
-- --   IsFunctor
-- --   ThickAndThin

-- -- -}
