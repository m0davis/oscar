
module Oscar.Property where

open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data

module PropertyProposequality where

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

  module _ {𝔬} (𝔒 : Ø 𝔬) where

    SetoidProposequality : Setoid _ _
    Setoid.Obj SetoidProposequality = _
    Setoid.Eq SetoidProposequality = Proposequality⟦ 𝔒 ⟧

  instance

    CongruityProposequality : ∀ {a b} → Congruity a b Proposequality
    Congruity.congruity CongruityProposequality _ ∅ = ∅

    Congruity₂Proposequality : ∀ {a b c} → Congruity₂ a b c Proposequality
    Congruity₂.congruity₂ Congruity₂Proposequality _ ∅ ∅ = ∅

open PropertyProposequality public

module PropertyProposextensequality where

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

  module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) where

    SetoidProposextensequality : Setoid _ _
    Setoid.Obj SetoidProposextensequality = _
    Setoid.Eq SetoidProposextensequality = Proposextensequality⟦ 𝔓 ⟧

  instance

    ĊongruityProposextensequality : ∀ {a b} → Ċongruity a b Proposextensequality
    Ċongruity.ċongruity ĊongruityProposextensequality F f≡̇g x rewrite f≡̇g x = ∅

open PropertyProposextensequality public

Function : ∀ {a} (A B : Ø a) → Ø a
Function A B = A → B

Function⟦_⟧ : ∀ a (A B : Ø a) → Ø a
Function⟦ a ⟧ = Function {a = a}

module PropertyFunction where

  module _
    {a}
    where

    instance

      ReflexivityFunction : Reflexivity Function⟦ a ⟧
      Reflexivity.reflexivity ReflexivityFunction = ¡

      TransitivityFunction : Transitivity Function⟦ a ⟧
      Transitivity.transitivity TransitivityFunction f g = g ∘ f

open PropertyFunction public

module PropertyExtension where

  module _
    {a} {A : Ø a} {b} {B : A → Ø b}
    where

    instance

      ReflexivityExtension : Reflexivity (Extension B)
      Reflexivity.reflexivity ReflexivityExtension = ¡

      TransitivityExtension : Transitivity (Extension B)
      Transitivity.transitivity TransitivityExtension f g = g ∘ f

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

open PropertyExtension public

module SubstitunctionExtensionTermProperty {𝔭} (𝔓 : Ø 𝔭) where

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

    MapSubstitunctionExtensionTerm : Map Substitunction (Extension Term)
    Map.map MapSubstitunctionExtensionTerm = 𝓶apSubstitunctionExtensionTerm

    MapSubstitunctionExtensionTerms : ∀ {N} → Map Substitunction (Extension $ Terms N)
    Map.map MapSubstitunctionExtensionTerms = 𝓶apSubstitunctionExtensionTerms

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
    Associativity′.associativity AssociativitySubstitunction f g h x rewrite commutativity g h $ f x = ∅

    Extensionality₂Substitunction : Extensionality₂ Substitunction ∅̂
    Extensionality₂′.extensionality₂ Extensionality₂Substitunction {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = extensionality₁ g₁≡̇g₂ $ f₂ x

    IsSemigroupoidSubstitunction : IsSemigroupoid Substitunction ∅̂
    IsSemigroupoidSubstitunction = record {}

  SemigroupoidSubstitunction : Semigroupoid _ _ _
  Semigroupoid.Obj SemigroupoidSubstitunction = _
  Semigroupoid.Hom SemigroupoidSubstitunction = Substitunction

  instance

    IsSemifunctorSubstitunctionExtensionTerm : IsSemifunctor Substitunction _ (Extension Term) _ ¡
    IsSemifunctorSubstitunctionExtensionTerm = record {}

    IsSemifunctorSubstitunctionExtensionTerms : ∀ {N} → IsSemifunctor Substitunction _ (Extension $ Terms N) _ ¡
    IsSemifunctorSubstitunctionExtensionTerms = record {}

  SemifunctorSubstitunctionExtensionTerm : Semifunctor _ _ _ _ _ _
  Semifunctor.Obj₁ SemifunctorSubstitunctionExtensionTerm = _
  Semifunctor.Hom₁ SemifunctorSubstitunctionExtensionTerm = Substitunction
  Semifunctor.Obj₂ SemifunctorSubstitunctionExtensionTerm = _
  Semifunctor.Hom₂ SemifunctorSubstitunctionExtensionTerm = Extension Term
  Semifunctor.μ SemifunctorSubstitunctionExtensionTerm = ¡

  instance

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

  instance

    LeftIdentitySubstitunction : LeftIdentity Substitunction _
    LeftIdentity′.left-identity LeftIdentitySubstitunction f = identity ∘ f

    RightIdentitySubstitunction : RightIdentity Substitunction _
    RightIdentity′.right-identity RightIdentitySubstitunction _ _ = ∅

  instance

    IsCategorySubstitunction : IsCategory Substitunction _
    IsCategorySubstitunction = record {}

  CategorySubstitunction : Category _ _ _
  Category.Obj CategorySubstitunction = _
  Category.Hom CategorySubstitunction = Substitunction

  instance

    IsFunctorSubstitunctionExtensionTerm : IsFunctor Substitunction _ (Extension Term) _ ¡
    IsFunctorSubstitunctionExtensionTerm = record {}

    IsFunctorSubstitunctionExtensionTerms : ∀ {N} → IsFunctor Substitunction _ (Extension $ Terms N) _ ¡
    IsFunctorSubstitunctionExtensionTerms = record {}

  FunctorSubstitunctionExtensionTerm : Functor _ _ _ _ _ _
  Functor.Obj₁ FunctorSubstitunctionExtensionTerm = _
  Functor.Hom₁ FunctorSubstitunctionExtensionTerm = Substitunction
  Functor.Obj₂ FunctorSubstitunctionExtensionTerm = _
  Functor.Hom₂ FunctorSubstitunctionExtensionTerm = Extension Term
  Functor.μ FunctorSubstitunctionExtensionTerm = ¡

  FunctorSubstitunctionExtensionTerms : ¶ → Functor _ _ _ _ _ _
  Functor.Obj₁ (FunctorSubstitunctionExtensionTerms _) = _
  Functor.Hom₁ (FunctorSubstitunctionExtensionTerms _) = Substitunction
  Functor.Obj₂ (FunctorSubstitunctionExtensionTerms _) = _
  Functor.Hom₂ (FunctorSubstitunctionExtensionTerms N) = Extension $ Terms N
  Functor.μ (FunctorSubstitunctionExtensionTerms _) = ¡
