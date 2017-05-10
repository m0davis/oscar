-- {-# OPTIONS --show-implicit #-}
module Oscar.Property9 where

open import Oscar.Prelude
open import Oscar.Class9
open import Oscar.Data

module Proposequality⌶ where

  module _ {𝔬} {𝔒 : Ø 𝔬} where

    instance

      IsEquivalenceProposequality : IsEquivalence Proposequality⟦ 𝔒 ⟧
      IsEquivalence.≋-reflexivity IsEquivalenceProposequality = ∅
      IsEquivalence.≋-symmetry IsEquivalenceProposequality ∅ = ∅
      IsEquivalence.≋-transitivity IsEquivalenceProposequality ∅ = ¡

module Proposextensequality⌶ where

  module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} where

    instance

      IsEquivalenceProposextensequality : IsEquivalence Proposextensequality⟦ 𝔓 ⟧
      IsEquivalence.≋-reflexivity IsEquivalenceProposextensequality _ = ∅
      IsEquivalence.≋-symmetry IsEquivalenceProposextensequality f₁≡̇f₂ x rewrite f₁≡̇f₂ x = ∅
      IsEquivalence.≋-transitivity IsEquivalenceProposextensequality f₁≡̇f₂ f₂≡̇f₃ x rewrite f₁≡̇f₂ x | f₂≡̇f₃ x = ∅

module Function⌶ where

  module _
--    {a}
    where

    instance

      EquivalenceFunction : ∀ {a} {A : Ø a} {b} {B : A → Ø b} → Equivalence ((x : A) → B x) _
      Equivalence._≋_ EquivalenceFunction = Proposextensequality
      Equivalence.⌶IsEquivalence EquivalenceFunction = it

      IsSemigroupoidFunction : ∀ {a} → IsSemigroupoid Function⟦ a ⟧ _
      IsSemigroupoid._∙_ IsSemigroupoidFunction g f = g ∘ f
      IsSemigroupoid.∙-extensionality IsSemigroupoidFunction {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = g₁≡̇g₂ $ f₂ x
      IsSemigroupoid.∙-associativity IsSemigroupoidFunction _ _ _ _ = ∅

record Substitunction⌶ {𝔭} (𝔓 : Ø 𝔭) : Ø₀ where
  no-eta-equality

  open Substitunction 𝔓
  open Term 𝔓

  instance

    IsSemigroupoidSubstitunction : IsSemigroupoid Substitunction _

    IsSemigroupoidExtensionTerm : IsSemigroupoid (Extension Term) _

    IsSemifunctorSubstitunction : IsSemifunctor Substitunction _ (Extension Term) _ ¡
    IsSemifunctorSubstitunctions : ∀ {N} → IsSemifunctor Substitunction _ (Extension $ Terms N) _ ¡

  private

    mutual

      𝓶apSubstitunctionExtensionTerm : ∀ {x y} → Substitunction x y → Extension Term x y
      𝓶apSubstitunctionExtensionTerm σ (i x) = σ x
      𝓶apSubstitunctionExtensionTerm σ leaf = leaf
      𝓶apSubstitunctionExtensionTerm σ (τ₁ fork τ₂) = 𝓶apSubstitunctionExtensionTerm σ τ₁ fork 𝓶apSubstitunctionExtensionTerm σ τ₂
      𝓶apSubstitunctionExtensionTerm σ (function p τs) = function p (𝓶apSubstitunctionExtensionTerms σ τs)

      𝓶apSubstitunctionExtensionTerms : ∀ {N x y} → Substitunction x y → (Extension $ Terms N) x y
      𝓶apSubstitunctionExtensionTerms σ ∅ = ∅
      𝓶apSubstitunctionExtensionTerms σ (τ , τs) = 𝓶apSubstitunctionExtensionTerm σ τ , 𝓶apSubstitunctionExtensionTerms σ τs

  private

    mutual

      𝓮xtensionality₁SubstitunctionExtensionTerm : ∀ {x y} {f₁ f₂ :  Substitunction x y} → f₁ ≋ f₂ → map {_⊸₂_ = Extension Term} {μ = ¡} f₁ ≋ map {_⊸₂_ = Extension Term} f₂
      𝓮xtensionality₁SubstitunctionExtensionTerm = {!!}

--       𝓮xtensionality₁SubstitunctionExtensionTerm p (i x) = p x
--       𝓮xtensionality₁SubstitunctionExtensionTerm p leaf = ∅
--       𝓮xtensionality₁SubstitunctionExtensionTerm p (s fork t) = ? -- congruity₂ _fork_ (𝓮xtensionality₁SubstitunctionExtensionTerm p s) (𝓮xtensionality₁SubstitunctionExtensionTerm p t)
--       𝓮xtensionality₁SubstitunctionExtensionTerm p (function fn ts) = ? -- congruity (function fn) (𝓮xtensionality₁SubstitunctionExtensionTerms p ts)

--       𝓮xtensionality₁SubstitunctionExtensionTerms : ∀ {N} → ∀ {x y} {f₁ f₂ :  Substitunction x y} → f₁ ≋ f₂ → map {_⊸₂_ = Extension $ Terms N} f₁ ≋ map f₂
--       𝓮xtensionality₁SubstitunctionExtensionTerms p ∅ = ∅
--       𝓮xtensionality₁SubstitunctionExtensionTerms p (t , ts) = ? -- congruity₂ _,_ (𝓮xtensionality₁SubstitunctionExtensionTerm p t) (𝓮xtensionality₁SubstitunctionExtensionTerms p ts)

  IsSemigroupoidSubstitunction = {!!}
  IsSemigroupoidExtensionTerm = {!!}
  IsSemifunctorSubstitunction = {!!}
  IsSemifunctorSubstitunctions = {!!}


--       ReflexivityProposextensequality : Reflexivity Proposextensequality⟦ 𝔓 ⟧
--       Reflexivity.reflexivity ReflexivityProposextensequality _ = ∅

--       SymmetryProposextensequality : Symmetry Proposextensequality⟦ 𝔓 ⟧
--       Symmetry.symmetry SymmetryProposextensequality f₁≡̇f₂ x rewrite f₁≡̇f₂ x = ∅

--       TransitivityProposextensequality : Transitivity Proposextensequality⟦ 𝔓 ⟧
--       Contiguity.contiguity TransitivityProposextensequality f₁≡̇f₂ f₂≡̇f₃ x rewrite f₁≡̇f₂ x | f₂≡̇f₃ x = ∅

--       IsSetoidProposextensequality : IsSetoid Proposextensequality⟦ 𝔓 ⟧
--       IsSetoidProposextensequality = {!record {}!}

-- --   instance

-- --     ĊongruityProposextensequality : ∀ {a b} → Ċongruity a b Proposextensequality
-- --     Ċongruity.ċongruity ĊongruityProposextensequality F f≡̇g x rewrite f≡̇g x = ∅

-- --       ReflexivityProposequality : Reflexivity Proposequality⟦ 𝔒 ⟧
-- --       Reflexivity.reflexivity ReflexivityProposequality = ∅

-- --       SymmetryProposequality : Symmetry Proposequality⟦ 𝔒 ⟧
-- --       Symmetry.symmetry SymmetryProposequality ∅ = ∅

-- --       TransitivityProposequality : Transitivity Proposequality⟦ 𝔒 ⟧
-- --       Contiguity.contiguity TransitivityProposequality ∅ = ¡

-- --       IsSetoidProposequality : IsSetoid Proposequality⟦ 𝔒 ⟧
-- --       IsSetoidProposequality = {!record {}!}

-- --   instance

-- --     CongruityProposequality : ∀ {a b} → Congruity a b Proposequality
-- --     Congruity.congruity CongruityProposequality _ ∅ = ∅

-- --     Congruity₂Proposequality : ∀ {a b c} → Congruity₂ a b c Proposequality
-- --     Congruity₂.congruity₂ Congruity₂Proposequality _ ∅ ∅ = ∅

-- --   instance

-- --     Extensionality₂⌶Proposequality : ∀ {a} {A : Set a} {b} {B : A → A → Ø b}
-- --       → {T : 𝓽ransitivity B}
-- --       → Extensionality₂′ B Proposequality (λ f₁ f₂ g₁ g₂ → T f₁ g₁ ≡ T f₂ g₂)
-- --     Extensionality₂′.extensionality₂ Extensionality₂⌶Proposequality = congruity₂ _

-- -- open Proposequality⌶ public

-- -- module ProposequalityØ where

-- --   module _ {𝔬} (𝔒 : Ø 𝔬) where

-- --     SetoidProposequality : Setoid _ _
-- --     Setoid.Object SetoidProposequality = _
-- --     Setoid.Eq SetoidProposequality = Proposequality⟦ 𝔒 ⟧

-- -- open ProposequalityØ public

-- -- open Proposextensequality⌶ public

-- -- module ProposextensequalityØ where

-- --   module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) where

-- --     SetoidProposextensequality : Setoid _ _
-- --     Setoid.Object SetoidProposextensequality = _
-- --     Setoid.Eq SetoidProposextensequality = Proposextensequality⟦ 𝔓 ⟧

-- -- open ProposextensequalityØ public

-- -- module Function⌶ where

-- --   module _
-- --     {a}
-- --     where

-- --     instance

-- --       ReflexivityFunction : Reflexivity Function⟦ a ⟧
-- --       Reflexivity.reflexivity ReflexivityFunction = ¡

-- --       TransitivityFunction : Transitivity Function⟦ a ⟧
-- --       Contiguity.contiguity TransitivityFunction f g = g ∘ f

-- -- open Function⌶ public

-- -- module Extension⌶ where

-- --   module _
-- --     {a} {A : Ø a} {b} {B : A → Ø b}
-- --     where

-- --     instance

-- --       ReflexivityExtension : Reflexivity (Extension B)
-- --       Reflexivity.reflexivity ReflexivityExtension = ¡

-- --       TransitivityExtension : Transitivity (Extension B)
-- --       Contiguity.contiguity TransitivityExtension f g = g ∘ f

-- --       EquivalenceExtension : ∀ {x y} → Equivalence (Extension B x y) b
-- --       Equivalence.equivalence EquivalenceExtension = Proposextensequality

-- --       MorphismEquivalenceExtension : MorphismEquivalence (Extension B) b
-- --       MorphismEquivalence.morphismEquivalence MorphismEquivalenceExtension = Proposextensequality

-- --       Extensionality₂Extension : Extensionality₂ (Extension B) b
-- --       Extensionality₂′.extensionality₂ Extensionality₂Extension {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = g₁≡̇g₂ (f₂ x)

-- --       AssociativityExtension : Associativity (Extension B) b
-- --       Associativity.associativity AssociativityExtension _ _ _ _ = ∅

-- --       IsSemigroupoidExtension : IsSemigroupoid (Extension B) b
-- --       IsSemigroupoidExtension = record {}

-- --       LeftIdentityExtension : LeftIdentity (Extension B) b
-- --       LeftIdentity.left-identity LeftIdentityExtension _ _ = ∅

-- --       RightIdentityExtension : RightIdentity (Extension B) b
-- --       RightIdentity.right-identity RightIdentityExtension _ _ = ∅

-- --       IsCategoryExtension : IsCategory (Extension B) _
-- --       IsCategoryExtension = record {}

-- -- open Extension⌶ public

-- -- record Substitunction⌶ {𝔭} (𝔓 : Ø 𝔭) : Ø₀ where
-- --   no-eta-equality

-- --   open Substitunction 𝔓
-- --   open Term 𝔓

-- --   instance

-- --     MorphismEquivalenceSubstitunction : MorphismEquivalence Substitunction _
-- --     MorphismEquivalence.morphismEquivalence MorphismEquivalenceSubstitunction = Proposextensequality

-- --   instance

-- --     Substitunction,ExtensionTerm⌶Map : Map Substitunction (Extension Term)
-- --     Map.map Substitunction,ExtensionTerm⌶Map = 𝓶apSubstitunctionExtensionTerm

-- --     Substitunction,ExtensionTerms⌶Map : ∀ {N} → Map Substitunction (Extension $ Terms N)
-- --     Map.map Substitunction,ExtensionTerms⌶Map = 𝓶apSubstitunctionExtensionTerms

-- --     TransitivitySubstitunction : Transitivity Substitunction
-- --     Contiguity.contiguity TransitivitySubstitunction f g = map g ∘ f

-- --   private

-- --     mutual

-- --       𝓮xtensionality₁SubstitunctionExtensionTerm : 𝓮xtensionality₁ Substitunction _ (Extension Term) _ ¡
-- --       𝓮xtensionality₁SubstitunctionExtensionTerm p (i x) = p x
-- --       𝓮xtensionality₁SubstitunctionExtensionTerm p leaf = ∅
-- --       𝓮xtensionality₁SubstitunctionExtensionTerm p (s fork t) = congruity₂ _fork_ (𝓮xtensionality₁SubstitunctionExtensionTerm p s) (𝓮xtensionality₁SubstitunctionExtensionTerm p t)
-- --       𝓮xtensionality₁SubstitunctionExtensionTerm p (function fn ts) = congruity (function fn) (𝓮xtensionality₁SubstitunctionExtensionTerms p ts)

-- --       𝓮xtensionality₁SubstitunctionExtensionTerms : ∀ {N} → 𝓮xtensionality₁ Substitunction _ (Extension $ Terms N) _ ¡
-- --       𝓮xtensionality₁SubstitunctionExtensionTerms p ∅ = ∅
-- --       𝓮xtensionality₁SubstitunctionExtensionTerms p (t , ts) = congruity₂ _,_ (𝓮xtensionality₁SubstitunctionExtensionTerm p t) (𝓮xtensionality₁SubstitunctionExtensionTerms p ts)

-- --   instance

-- --     Extensionality₁Substitunction : Extensionality₁ Substitunction _ (Extension Term) _ ¡
-- --     Extensionality₁′.extensionality₁ Extensionality₁Substitunction = 𝓮xtensionality₁SubstitunctionExtensionTerm

-- --     Extensionality₁Substitunctions : ∀ {N} → Extensionality₁ Substitunction _ (Extension $ Terms N) _ ¡
-- --     Extensionality₁′.extensionality₁ Extensionality₁Substitunctions = 𝓮xtensionality₁SubstitunctionExtensionTerms

-- --   private

-- --     mutual

-- --       𝓬ommutativitySubstitunctionExtensionTerm : 𝓬ommutativity Substitunction (Extension Term) _ ¡
-- --       𝓬ommutativitySubstitunctionExtensionTerm _ _ (i _) = ∅
-- --       𝓬ommutativitySubstitunctionExtensionTerm _ _ leaf = ∅
-- --       𝓬ommutativitySubstitunctionExtensionTerm _ _ (τ₁ fork τ₂) = congruity₂ _fork_ (𝓬ommutativitySubstitunctionExtensionTerm _ _ τ₁) (𝓬ommutativitySubstitunctionExtensionTerm _ _ τ₂)
-- --       𝓬ommutativitySubstitunctionExtensionTerm f g (function fn ts) = congruity (function fn) (𝓬ommutativitySubstitunctionExtensionTerms f g ts)

-- --       𝓬ommutativitySubstitunctionExtensionTerms : ∀ {N} → 𝓬ommutativity Substitunction (Extension $ Terms N) _ ¡
-- --       𝓬ommutativitySubstitunctionExtensionTerms _ _ ∅ = ∅
-- --       𝓬ommutativitySubstitunctionExtensionTerms _ _ (τ , τs) = congruity₂ _,_ (𝓬ommutativitySubstitunctionExtensionTerm _ _ τ) (𝓬ommutativitySubstitunctionExtensionTerms _ _ τs)

-- --   instance

-- --     CommutativitySubstitunctionExtensionTerm : Commutativity Substitunction (Extension Term) _ ¡
-- --     Contiguity.contiguity CommutativitySubstitunctionExtensionTerm = 𝓬ommutativitySubstitunctionExtensionTerm

-- --     CommutativitySubstitunctionExtensionTerms : ∀ {N} → Commutativity Substitunction (Extension $ Terms N) _ ¡
-- --     Contiguity.contiguity CommutativitySubstitunctionExtensionTerms = 𝓬ommutativitySubstitunctionExtensionTerms
-- -- -- !!!!!
-- --     AssociativitySubstitunction : Associativity Substitunction _
-- --     Associativity.associativity AssociativitySubstitunction f g h x = contiguity' g h $ (f x)

-- --     Extensionality₂Substitunction : Extensionality₂ Substitunction _
-- --     Extensionality₂′.extensionality₂ Extensionality₂Substitunction {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = extensionality₁ g₁≡̇g₂ $ f₂ x

-- --     IsSemigroupoidSubstitunction : IsSemigroupoid Substitunction _
-- --     IsSemigroupoidSubstitunction = record {}

-- --     IsSemifunctorSubstitunctionExtensionTerm : IsSemifunctor Substitunction _ (Extension Term) _ ¡
-- --     IsSemifunctorSubstitunctionExtensionTerm = record {}

-- --     IsSemifunctorSubstitunctionExtensionTerms : ∀ {N} → IsSemifunctor Substitunction _ (Extension $ Terms N) _ ¡
-- --     IsSemifunctorSubstitunctionExtensionTerms = record {}

-- --     ReflexivitySubstitunction : Reflexivity Substitunction
-- --     Reflexivity.reflexivity ReflexivitySubstitunction = i

-- --   private

-- --     mutual

-- --       𝓲dentitySubstitunctionExtensionTerm : 𝓲dentity Substitunction (Extension Term) _ ¡
-- --       𝓲dentitySubstitunctionExtensionTerm (i x) = ∅
-- --       𝓲dentitySubstitunctionExtensionTerm leaf = ∅
-- --       𝓲dentitySubstitunctionExtensionTerm (s fork t) = congruity₂ _fork_ (𝓲dentitySubstitunctionExtensionTerm s) (𝓲dentitySubstitunctionExtensionTerm t)
-- --       𝓲dentitySubstitunctionExtensionTerm (function fn ts) = congruity (function fn) (𝓲dentitySubstitunctionExtensionTerms ts)

-- --       𝓲dentitySubstitunctionExtensionTerms : ∀ {N} → 𝓲dentity Substitunction (Extension $ Terms N) _ ¡
-- --       𝓲dentitySubstitunctionExtensionTerms ∅ = ∅
-- --       𝓲dentitySubstitunctionExtensionTerms (t , ts) = congruity₂ _,_ (𝓲dentitySubstitunctionExtensionTerm t) (𝓲dentitySubstitunctionExtensionTerms ts)

-- --   instance

-- -- {-
-- --     Identity!SubstitunctionExtensionTerm : Identity! Substitunction (Extension Term) _ ¡
-- --     Identity!.identity! Identity!SubstitunctionExtensionTerm = {!!} -- 𝓲dentitySubstitunctionExtensionTerm

-- --     Identity!SubstitunctionExtensionTerms : ∀ {N} → Identity! Substitunction (Extension $ Terms N) _ ¡
-- --     Identity!.identity! Identity!SubstitunctionExtensionTerms = {!!} -- 𝓲dentitySubstitunctionExtensionTerms

-- --     Identity?SubstitunctionExtensionTerm : Identity? Substitunction (Extension Term) _ ¡
-- --     Identity?.identity? Identity?SubstitunctionExtensionTerm = 𝓲dentitySubstitunctionExtensionTerm

-- --     Identity?SubstitunctionExtensionTerms : ∀ {N} → Identity? Substitunction (Extension $ Terms N) _ ¡
-- --     Identity?.identity? Identity?SubstitunctionExtensionTerms = 𝓲dentitySubstitunctionExtensionTerms

-- --     LeftIdentity!Substitunction : LeftIdentity! Substitunction _
-- --     LeftIdentity!.left-identity! LeftIdentity!Substitunction f x = ((Term _ → Proposequality (𝓶apSubstitunctionExtensionTerm i (f x)) (f x)) ∋ identity?) (f x) -- {!{!identity!!} ∘ f!}
-- -- -}

-- --     IdentitySubstitunctionExtensionTerm : Identity Substitunction (Extension Term) _ ¡
-- --     Identity′.identity IdentitySubstitunctionExtensionTerm = 𝓲dentitySubstitunctionExtensionTerm

-- --     IdentitySubstitunctionExtensionTerms : ∀ {N} → Identity Substitunction (Extension $ Terms N) _ ¡
-- --     Identity′.identity IdentitySubstitunctionExtensionTerms = 𝓲dentitySubstitunctionExtensionTerms

-- --     LeftIdentitySubstitunction : LeftIdentity Substitunction _
-- --     LeftIdentity.left-identity LeftIdentitySubstitunction f = identity ∘ f

-- --     RightIdentitySubstitunction : RightIdentity Substitunction _
-- --     RightIdentity.right-identity RightIdentitySubstitunction _ _ = ∅

-- --     IsCategorySubstitunction : IsCategory Substitunction _
-- --     IsCategorySubstitunction = record {}

-- --     IsFunctorSubstitunctionExtensionTerm : IsFunctor Substitunction _ (Extension Term) _ ¡
-- --     IsFunctorSubstitunctionExtensionTerm = record {}

-- --     IsFunctorSubstitunctionExtensionTerms : ∀ {N} → IsFunctor Substitunction _ (Extension $ Terms N) _ ¡
-- --     IsFunctorSubstitunctionExtensionTerms = record {}

-- -- module SubstitunctionØ {𝔭} (𝔓 : Ø 𝔭) where

-- --   open Substitunction 𝔓
-- --   open Term 𝔓

-- --   open Substitunction⌶ (Substitunction⌶ 𝔓 ∋ record {})

-- --   SemigroupoidSubstitunction : Semigroupoid _ _ _
-- --   Semigroupoid.Object SemigroupoidSubstitunction = _
-- --   Semigroupoid.Morphism SemigroupoidSubstitunction = Substitunction

-- --   SemifunctorSubstitunctionExtensionTerm : Semifunctor _ _ _ _ _ _
-- --   Semifunctor.Object₁ SemifunctorSubstitunctionExtensionTerm = _
-- --   Semifunctor.Morphism₁ SemifunctorSubstitunctionExtensionTerm = Substitunction
-- --   Semifunctor.Object₂ SemifunctorSubstitunctionExtensionTerm = _
-- --   Semifunctor.Morphism₂ SemifunctorSubstitunctionExtensionTerm = Extension Term
-- --   Semifunctor.μ SemifunctorSubstitunctionExtensionTerm = ¡

-- --   CategorySubstitunction : Category _ _ _
-- --   Category.Object CategorySubstitunction = _
-- --   Category.Morphism CategorySubstitunction = Substitunction

-- --   FunctorSubstitunctionExtensionTerm : Functor _ _ _ _ _ _
-- --   Functor.Object₁ FunctorSubstitunctionExtensionTerm = _
-- --   Functor.Morphism₁ FunctorSubstitunctionExtensionTerm = Substitunction
-- --   Functor.Object₂ FunctorSubstitunctionExtensionTerm = _
-- --   Functor.Morphism₂ FunctorSubstitunctionExtensionTerm = Extension Term
-- --   Functor.μ FunctorSubstitunctionExtensionTerm = ¡

-- --   module _ (N : ¶) where

-- --     FunctorSubstitunctionExtensionTerms : Functor _ _ _ _ _ _
-- --     Functor.Object₁ FunctorSubstitunctionExtensionTerms = _
-- --     Functor.Morphism₁ FunctorSubstitunctionExtensionTerms = Substitunction
-- --     Functor.Object₂ FunctorSubstitunctionExtensionTerms = _
-- --     Functor.Morphism₂ FunctorSubstitunctionExtensionTerms = Extension $ Terms N
-- --     Functor.μ FunctorSubstitunctionExtensionTerms = ¡

-- -- open SubstitunctionØ public

-- -- module AList⌶ {a} {A : Nat → Set a} where

-- --   private AList = Descender⟨ A ⟩

-- --   instance

-- --     Reflexivity⌶AList : Reflexivity AList
-- --     Reflexivity.reflexivity Reflexivity⌶AList = ∅

-- --     Transitivity⌶AList : Transitivity AList
-- --     Contiguity.contiguity Transitivity⌶AList f ∅ = f
-- --     Contiguity.contiguity Transitivity⌶AList f (x , g) = x , contiguity f g

-- --     MorphismEquivalence⌶AList : MorphismEquivalence AList _
-- --     MorphismEquivalence.morphismEquivalence MorphismEquivalence⌶AList = Proposequality

-- --     Associativity⌶AList : Associativity AList _
-- --     Associativity.associativity Associativity⌶AList _ _ ∅ = ∅
-- --     Associativity.associativity Associativity⌶AList f g (x , h) = congruity (x ,_) $ associativity f g h

-- --     IsSemigroupoid⌶AList : IsSemigroupoid AList _
-- --     IsSemigroupoid⌶AList = record {}

-- --     LeftIdentity⌶AList : LeftIdentity AList _
-- --     LeftIdentity.left-identity LeftIdentity⌶AList _ = ∅

-- --     RightIdentity⌶AList : RightIdentity AList _
-- --     RightIdentity.right-identity RightIdentity⌶AList ∅ = ∅
-- --     RightIdentity.right-identity RightIdentity⌶AList (x , f) = congruity (x ,_) $ right-identity f

-- --     IsCategory⌶AList : IsCategory AList _
-- --     IsCategory⌶AList = record {}

-- -- module Substitist⌶ {𝔭} {𝔓 : Ø 𝔭} where

-- --   open Substitunction 𝔓
-- --   open Term 𝔓
-- --   open Substitist 𝔓
-- --   open Substitunction⌶ (Substitunction⌶ 𝔓 ∋ record {})

-- --   postulate
-- --     _for_ : ∀ {n} (t' : Term n) (x : Fin (↑ n)) -> Fin (↑ n) -> Term n

-- --   instance

-- --     Map⌶Substitist,Substitunction : Map Substitist Substitunction
-- --     Map.map Map⌶Substitist,Substitunction ∅ = i
-- --     Map.map Map⌶Substitist,Substitunction ((x , t) , σ) = map σ ∙ (t for x)

-- -- module Fin⌶ where

-- --   instance

-- --     Map⌶Maybe : ∀ {x} → Map {A = Ø x} (λ x y → x → y) (λ x y → Maybe x → Maybe y)
-- --     Map.map Map⌶Maybe f ∅ = ∅
-- --     Map.map Map⌶Maybe f (↑ x) = ↑ (f x)

-- --   instance

-- --     Successor₀⌶¶ : Successor₀ ¶
-- --     Successor₀.⇑₀ Successor₀⌶¶ = ↑_

-- --     Principal₁Fin : Principal₁ Fin
-- --     Principal₁Fin = record {}

-- --     Successor₁⌶Fin : Successor₁ Fin
-- --     Successor₁.⇑₁ Successor₁⌶Fin = ↑_

-- --     Thin⌶Fin,Fin : Thin Fin Fin
-- --     Thin.thin Thin⌶Fin,Fin ∅ = ↑_
-- --     Thin.thin Thin⌶Fin,Fin (↑ x) ∅ = ∅
-- --     Thin.thin Thin⌶Fin,Fin (↑ x) (↑ y) = ↑ (thin x y)

-- --     Equivalence⌶Fin : ∀ {n} → Equivalence (Fin n) ∅̂
-- --     Equivalence.equivalence Equivalence⌶Fin = Proposequality

-- --     Equivalence⌶¶ : Equivalence ¶ ∅̂
-- --     Equivalence.equivalence Equivalence⌶¶ = Proposequality

-- --     pattern Fin↑ n = ¶⟨<_⟩.↑_ {n = n}

-- --     Injectivity₀⌶¶↑ : Injectivity₀ ¶.↑_ ∅̂ ∅̂
-- --     Injectivity₀⌶¶↑ = {!!}

-- --     Injectivity₀⌶Fin↑ : ∀ {n} → Injectivity₀ (Fin↑ n) ∅̂ ∅̂
-- --     Injectivity₀.injectivity₀ (Injectivity₀⌶Fin↑ {n}) = {!!}

-- --     Injectivity₁⌶Fin↑ : Injectivity₁ Fin↑ ∅̂ ∅̂
-- --     Injectivity₁.injectivity₁ Injectivity₁⌶Fin↑ = {!!}

-- --     Injectivity!⌶Fin↑ : Injectivity? Fin↑ ∅̂ ∅̂
-- --     Injectivity!.injectivity! Injectivity!⌶Fin↑ = {!!}

-- --     Injectivity₁⌶ThinFin : ∀ {m} → Injectivity₁ (thin {A = Fin} {B = Fin} {m = m}) ∅̂ ∅̂
-- --     Injectivity₁.injectivity₁ (Injectivity₁⌶ThinFin {m}) (∅ {n = .m}) {x} {y} x₁ = injectivity₁[ Fin↑ ] _ x₁
-- --     Injectivity₁.injectivity₁ (Injectivity₁⌶ThinFin {m}) (↑_ {n = .m} w) {x} {y} x₁ = {!!}

-- --     Injectivity!⌶ThinFin : ∀ {m} → Injectivity? (thin {A = Fin} {B = Fin} {m = m}) ∅̂ ∅̂
-- --     Injectivity!.injectivity! (Injectivity!⌶ThinFin {m}) (∅ {n = .m}) {x} {y} x₁ = injectivity?[ Fin↑ ] _ x₁
-- --     Injectivity!.injectivity! (Injectivity!⌶ThinFin {m}) (↑_ {n = .m} w) {x} {y} x₁ = {!!}

-- --     Injectivity₂⌶ThinFin : ∀ {m} → Injectivity₂ (thin {A = Fin} {B = Fin} {m = m}) ∅̂ ∅̂
-- --     Injectivity₂.injectivity₂ (Injectivity₂⌶ThinFin {m}) (∅ {n = .m}) {x} {y} x₁ = injectivity₀[ Fin↑ m ] x₁
-- --     Injectivity₂.injectivity₂ (Injectivity₂⌶ThinFin {m}) (↑_ {n = .m} w) {x} {y} x₁ = {!!}

-- --   test-thin-injective : ∀ {m} (x : Fin (↑ m)) {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- --   test-thin-injective x eq = injectivity₂[ thin[ Fin ] ] x eq

-- --   -- injectivity₂[ thin[ Fin ] ] x eq
-- --   -- injectivity₁[ thin[ Fin ] ] x eq

-- --     -- ∀ {n} → Injectivity₁ (thin {A = Fin} {B = Fin} {m = n}) ∅̂ ∅̂
-- --     -- Injectivity₁⌶ThinFin = ?


-- -- --     Injectivity₁.injectivity₁ (Injectivity₁⌶ThinFin {n}) (∅ {n = .n}) {x} {y} eq = injectivity![ (λ n → ¶⟨<_⟩.↑_ {n = n}) ] _ _ _ eq
-- -- --       -- injectivity₁⋆[ (λ {n} → ¶⟨<_⟩.↑_ {n}) ] eq -- injectivity₀[ ¶⟨<_⟩.↑_ {n = n} ] eq
-- -- --     Injectivity₁.injectivity₁ (Injectivity₁⌶ThinFin {n}) (↑_ {n = .n} w) {x} {y} eq = {!!}

-- -- -- -- --     InjThinFin : ∀ {m} {x : Fin (↑ m)} → INJ (thin[ Fin ] x) ∅̂ ∅̂
-- -- -- -- --     INJ.inj (InjThinFin {m} {∅ {n = .m}}) {x} {y} = INj (¶⟨<_⟩.↑_ {m}) ⦃ it ⦄ ⦃ it ⦄ ⦃ {!InjThinFin {m = m} {x = ∅}!} ⦄ {x} {y}
-- -- -- -- --     INJ.inj (InjThinFin {m} {↑_ {n = .m} x}) {x₁} {y} = {!!}

-- -- -- -- --   test-thin-injective : ∀ {m} {x : Fin (↑ m)} {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- --   test-thin-injective {m = m} {x = x} eq = INj2 (thin {A = Fin} {B = Fin}) {w = x} eq -- INj2 (thin[ Fin ]) {w = x} eq -- INj2 (thin {A = Fin} {B = Fin}) eq

-- -- -- -- --   test-thin-injective2 : ∀ {m} {x : Fin (↑ m)} {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- --   test-thin-injective2 {x = x} = test-thin-injective {x = x}

-- -- -- -- -- --   instance

-- -- -- -- -- --     Injectivity⌶↑¶ : Injectivity ¶.↑_ ∅̂ ∅̂
-- -- -- -- -- --     Injectivity.injectivity Injectivity⌶↑¶ ∅ = ∅

-- -- -- -- -- --     Injectivity⌶↑Fin : ∀ {n} → Injectivity {A = ¶⟨< n ⟩} {B = ¶⟨< ↑ n ⟩} ¶⟨<_⟩.↑_ ∅̂ ∅̂
-- -- -- -- -- --     Injectivity.injectivity (Injectivity⌶↑Fin {n}) {x} {.x} ∅ = ∅

-- -- -- -- -- --   Injectivity⌶ThinFin : ∀ {m} {x : Fin (⇑₀ m)} → Injectivity (thin[ Fin ] x) ∅̂ ∅̂
-- -- -- -- -- --   Injectivity.injectivity (Injectivity⌶ThinFin {m = m} {x = ∅}) e = injectivity {B = Fin (↑ m)} {f = ↑_ {n = m}} e -- injectivity {B = Fin m} {f = ↑_ {n = _}} e -- injectivity {f = ¶⟨<_⟩.↑_ {n = _}} ⦃ r = {!!} ⦄ {!e!} -- injectivity {f = ¶⟨<_⟩.↑_} e
-- -- -- -- -- --       -- injectivity[ ¶⟨<_⟩.↑_ ] ⦃ e1 = it ⦄ ⦃ e2 = Equivalence⌶Fin ⦄ ⦃ i1 = Injectivity⌶↑Fin ⦄ e
-- -- -- -- -- --       -- injectivity[ ¶.↑_ ] e
-- -- -- -- -- --   Injectivity.injectivity (Injectivity⌶ThinFin {.(↑ _)} {↑_ {n = .(↑ n)} x}) {∅ {n = n}} {y} x₂ = {!!}
-- -- -- -- -- --   Injectivity.injectivity (Injectivity⌶ThinFin {.(↑ _)} {↑_ {n = .(↑ n)} x}) {↑_ {n = n} x₁} {y} x₂ = {!!}

-- -- -- -- -- --   instance

-- -- -- -- -- --     ThinInjective⌶Fin,Fin : ThinInjective Fin Fin ∅̂
-- -- -- -- -- --     ThinInjective.iInjectivity ThinInjective⌶Fin,Fin {m} {x} = Injectivity⌶ThinFin {m} {x} -- Injectivity⌶ThinFin

-- -- -- -- -- --   test-thin-injective : ∀ {m} {x : Fin (↑ m)} {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- --   test-thin-injective {x = x} = thin-injective {B = Fin} { x = x }

-- -- -- -- -- --   instance I1 = Injectivity⌶ThinFin

-- -- -- -- -- --   test-thin-injective' : ∀ {m} {x : Fin (↑ m)} {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- --   test-thin-injective' {m} {x = x} eq = injectivity {A = Fin m} {B = Fin (↑ m)} {f = thin {A = Fin} {B = λ v → Fin v} x} ⦃ r = I1 {m} {{!!}} ⦄ eq --

-- -- -- -- -- --   instance

-- -- -- -- -- --     InjectivityP⌶Fin : ∀ {m} {x : Fin m} → InjectivityP (¶⟨<_⟩.↑_ {n = m})
-- -- -- -- -- --     InjectivityP.injectivityP (InjectivityP⌶Fin {m} {x}) = {!!}

-- -- -- -- -- --     InjectivityP⌶ThinFin : ∀ {m} {x : Fin (⇑₀ m)} → InjectivityP (thin[ Fin ] x)
-- -- -- -- -- --     InjectivityP.injectivityP (InjectivityP⌶ThinFin {m} {∅ {n = .m}}) {x} {y} x₂ = injectivityP x₂
-- -- -- -- -- --     InjectivityP.injectivityP (InjectivityP⌶ThinFin {m} {↑_ {n = .m} x}) {x₁} {y} x₂ = {!!}

-- -- -- -- -- -- --   test-fin-injective : ∀ {m} {y₁ y₂ : Fin m} → ¶⟨<_⟩.↑ y₁ ≋ ↑ y₂ → y₁ ≋ y₂
-- -- -- -- -- -- --   test-fin-injective {m} = injectivity {f = λ v → ¶⟨<_⟩.↑_ {m} v}


-- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- --     ThinInjective⌶Fin,Fin : ThinInjective Fin Fin ∅̂
-- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ∅} e = {!!}
-- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ↑ x} {∅} {∅} _ = ∅
-- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ↑ x} {∅} {↑ _} ()
-- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ↑ x} {↑ _} {∅} ()
-- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ↑ x} {↑ y₁} {↑ y₂} = {!!}
-- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- --     Thick⌶Fin,Fin : Thick Fin Fin
-- -- -- -- -- -- -- --     Thick.thick Thick⌶Fin,Fin = {!!}

-- -- -- -- -- -- -- --     ThickThinId⌶Fin,Fin : ThickThinId Fin Fin ∅̂
-- -- -- -- -- -- -- --     ThickThinId.thick∘thin=id ThickThinId⌶Fin,Fin = {!!}

-- -- -- -- -- -- -- --     Maybe*⌶ : ∀ {a} → Maybe* a
-- -- -- -- -- -- -- --     Maybe*.Maybe Maybe*⌶ = Maybe
-- -- -- -- -- -- -- --     Maybe*.just Maybe*⌶ = ↑_

-- -- -- -- -- -- -- --     Check⌶Fin,Fin : Check Fin Fin
-- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin ∅ ∅ = ∅
-- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin ∅ (↑ y) = ↑ y
-- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin {∅} (↑ ()) _
-- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin {↑ _} (↑ x) ∅ = ↑ ∅
-- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin {↑ _} (↑ x) (↑ y) = map ¶⟨<_⟩.↑_ $ check x y

-- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- --     Equivalence⌶Maybe : ∀ {a} {A : Ø a} {ℓ} ⦃ _ : Equivalence A ℓ ⦄ → Equivalence (Maybe A) ℓ
-- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶Maybe ∅ ∅ = {!!}
-- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶Maybe ∅ (↑ x₁) = {!!}
-- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶Maybe (↑ x₁) ∅ = {!!}
-- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶Maybe (↑ x₁) (↑ x₂) = {!!}
-- -- -- -- -- -- -- --     Equivalence.⌶IsSetoid Equivalence⌶Maybe = {!!}
-- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- --     Equivalence⌶MaybeFin : ∀ {n} → Equivalence (Maybe (Fin n)) ∅̂
-- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶MaybeFin = Proposequality

-- -- -- -- -- -- -- --     ThinCheckId⌶Fin,Fin : ThinCheckId Fin Fin ∅̂ ∅̂
-- -- -- -- -- -- -- --     ThinCheckId.thin-check-id ThinCheckId⌶Fin,Fin x y y' x₁ = {!!}

-- -- -- -- -- -- -- --     ThickAndThin⌶FinFin : ThickAndThin Fin Fin ∅̂ ∅̂
-- -- -- -- -- -- -- --     ThickAndThin⌶FinFin = record {}

-- -- -- -- -- -- -- --   module _ {𝔭} {𝔓 : Ø 𝔭} where

-- -- -- -- -- -- -- --     open Term 𝔓

-- -- -- -- -- -- -- --     instance

-- -- -- -- -- -- -- --       Principal₁⌶Term : Principal₁ Term
-- -- -- -- -- -- -- --       Principal₁⌶Term = record {}

-- -- -- -- -- -- -- --     private

-- -- -- -- -- -- -- --       mutual

-- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm : 𝓶ap (Extension Fin) (Extension Term)
-- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm f (i x) = i (f x)
-- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm f leaf = leaf
-- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm f (t1 fork t2) = (𝓶ap⌶ExtensionFin,ExtensionTerm f t1) fork 𝓶ap⌶ExtensionFin,ExtensionTerm f t2
-- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm f (function F ts) = function F (𝓶ap⌶ExtensionFin,ExtensionTerms f ts)

-- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerms : ∀ {N} → 𝓶ap (Extension Fin) (Extension (Terms N))
-- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerms f ∅ = ∅
-- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerms f (t , ts) = 𝓶ap⌶ExtensionFin,ExtensionTerm f t , 𝓶ap⌶ExtensionFin,ExtensionTerms f ts

-- -- -- -- -- -- -- --     instance

-- -- -- -- -- -- -- --       Map⌶ExtensionFin,ExtensionTerm : Map (Extension Fin) (Extension Term)
-- -- -- -- -- -- -- --       Map.map Map⌶ExtensionFin,ExtensionTerm = 𝓶ap⌶ExtensionFin,ExtensionTerm

-- -- -- -- -- -- -- --       Map⌶ExtensionFin,ExtensionTerms : ∀ {N} → Map (Extension Fin) (Extension (Terms N))
-- -- -- -- -- -- -- --       Map.map Map⌶ExtensionFin,ExtensionTerms = 𝓶ap⌶ExtensionFin,ExtensionTerms

-- -- -- -- -- -- -- --       Thin⌶Fin,Term : Thin Fin Term
-- -- -- -- -- -- -- --       Thin.thin Thin⌶Fin,Term = map ∘ thin

-- -- -- -- -- -- -- --       Equivalence⌶Term : ∀ {n} → Equivalence (Term n) ∅̂
-- -- -- -- -- -- -- --       Equivalence.equivalence Equivalence⌶Term = Proposequality

-- -- -- -- -- -- -- -- --       Injectivity⌶ASD : Injectivity

-- -- -- -- -- -- -- -- --       ThinInjective⌶Fin,Term : ThinInjective Fin Term ∅̂
-- -- -- -- -- -- -- -- --       ThinInjective.thin-injective ThinInjective⌶Fin,Term = {!!}

-- -- -- -- -- -- -- -- -- --     Successor₀⌶¶ : Upper Fin
-- -- -- -- -- -- -- -- -- --     Upper.up Upper⌶Fin = ↑_

-- -- -- -- -- -- -- -- -- -- --     ThickAndThin⌶Fin : ThickAndThin Fin Fin
-- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Fin ∅ y = ↑ y
-- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Fin (↑ x) ∅ = ∅
-- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Fin (↑ x) (↑ y) = ↑ thin x y
-- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin-injective ThickAndThin⌶Fin x x₁ = {!!}
-- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thick ThickAndThin⌶Fin = {!!}
-- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thick∘thin=id ThickAndThin⌶Fin = {!!}
-- -- -- -- -- -- -- -- -- -- --     ThickAndThin.check ThickAndThin⌶Fin = {!!}
-- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin-check-id ThickAndThin⌶Fin = {!!}

-- -- -- -- -- -- -- -- -- -- -- module Term⌶ {𝔭} {𝔓 : Ø 𝔭} where

-- -- -- -- -- -- -- -- -- -- --   open Term 𝔓

-- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin⌶Term : ThickAndThin Term
-- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Term x (i x₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Term x leaf = {!!}
-- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Term x (x₁ fork x₂) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Term x (function x₁ x₂) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin-injective ThickAndThin⌶Term = {!!}
-- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thick ThickAndThin⌶Term = {!!}
-- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thick∘thin=id ThickAndThin⌶Term = {!!}
-- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.check ThickAndThin⌶Term = {!!}
-- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin-check-id ThickAndThin⌶Term = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- Data
-- -- -- -- -- -- -- -- -- -- -- --   Nat
-- -- -- -- -- -- -- -- -- -- -- --   ≤↓List -- m ≤ n, n-1...m
-- -- -- -- -- -- -- -- -- -- -- --   Substitunction
-- -- -- -- -- -- -- -- -- -- -- --   Substitist
-- -- -- -- -- -- -- -- -- -- -- -- Record
-- -- -- -- -- -- -- -- -- -- -- --   Product
-- -- -- -- -- -- -- -- -- -- -- --   Functor
-- -- -- -- -- -- -- -- -- -- -- -- Class
-- -- -- -- -- -- -- -- -- -- -- --   Reflexivity
-- -- -- -- -- -- -- -- -- -- -- --   IsFunctor
-- -- -- -- -- -- -- -- -- -- -- --   ThickAndThin

-- -- -- -- -- -- -- -- -- -- -- -- -}
