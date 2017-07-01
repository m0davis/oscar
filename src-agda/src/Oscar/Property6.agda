
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

      Extensionality₂Extension : Extensionality₂ (Extension B) Proposextensequality
      Extensionality₂′.extensionality₂ Extensionality₂Extension {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = g₁≡̇g₂ (f₂ x)

      AssociativityExtension : Associativity (Extension B) Proposextensequality
      Associativity′.associativity AssociativityExtension _ _ _ _ = ∅

      IsSemigroupoidExtension : IsSemigroupoid (Extension B) Proposextensequality
      IsSemigroupoidExtension = record {}

      LeftIdentityExtension : LeftIdentity (Extension B) Proposextensequality
      LeftIdentity′.left-identity LeftIdentityExtension _ _ = ∅

      RightIdentityExtension : RightIdentity (Extension B) Proposextensequality
      RightIdentity′.right-identity RightIdentityExtension _ _ = ∅

      IsCategoryExtension : IsCategory (Extension B) Proposextensequality
      IsCategoryExtension = record {}

open PropertyExtension public

module SubstitunctionExtensionTermProperty {𝔭} (𝔓 : Ø 𝔭) where

  open Substitunction 𝔓
  open Term 𝔓

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

      𝓮xtensionality₁SubstitunctionExtensionTerm : 𝓮xtensionality₁ Substitunction Proposextensequality (Extension Term) Proposextensequality ¡
      𝓮xtensionality₁SubstitunctionExtensionTerm p (i x) = p x
      𝓮xtensionality₁SubstitunctionExtensionTerm p leaf = ∅
      𝓮xtensionality₁SubstitunctionExtensionTerm p (s fork t) = congruity₂ _fork_ (𝓮xtensionality₁SubstitunctionExtensionTerm p s) (𝓮xtensionality₁SubstitunctionExtensionTerm p t)
      𝓮xtensionality₁SubstitunctionExtensionTerm p (function fn ts) = congruity (function fn) (𝓮xtensionality₁SubstitunctionExtensionTerms p ts)

      𝓮xtensionality₁SubstitunctionExtensionTerms : ∀ {N} → 𝓮xtensionality₁ Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality ¡
      𝓮xtensionality₁SubstitunctionExtensionTerms p ∅ = ∅
      𝓮xtensionality₁SubstitunctionExtensionTerms p (t , ts) = congruity₂ _,_ (𝓮xtensionality₁SubstitunctionExtensionTerm p t) (𝓮xtensionality₁SubstitunctionExtensionTerms p ts)

  instance

    Extensionality₁Substitunction : Extensionality₁ Substitunction Proposextensequality (Extension Term) Proposextensequality ¡
    Extensionality₁′.extensionality₁ Extensionality₁Substitunction = 𝓮xtensionality₁SubstitunctionExtensionTerm

    Extensionality₁Substitunctions : ∀ {N} → Extensionality₁ Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality ¡
    Extensionality₁′.extensionality₁ Extensionality₁Substitunctions = 𝓮xtensionality₁SubstitunctionExtensionTerms

  private

    mutual

      𝓬ommutativitySubstitunctionExtensionTerm : 𝓬ommutativity Substitunction (Extension Term) Proposextensequality ¡
      𝓬ommutativitySubstitunctionExtensionTerm _ _ (i _) = ∅
      𝓬ommutativitySubstitunctionExtensionTerm _ _ leaf = ∅
      𝓬ommutativitySubstitunctionExtensionTerm _ _ (τ₁ fork τ₂) = congruity₂ _fork_ (𝓬ommutativitySubstitunctionExtensionTerm _ _ τ₁) (𝓬ommutativitySubstitunctionExtensionTerm _ _ τ₂)
      𝓬ommutativitySubstitunctionExtensionTerm f g (function fn ts) = congruity (function fn) (𝓬ommutativitySubstitunctionExtensionTerms f g ts)

      𝓬ommutativitySubstitunctionExtensionTerms : ∀ {N} → 𝓬ommutativity Substitunction (Extension $ Terms N) Proposextensequality ¡
      𝓬ommutativitySubstitunctionExtensionTerms _ _ ∅ = ∅
      𝓬ommutativitySubstitunctionExtensionTerms _ _ (τ , τs) = congruity₂ _,_ (𝓬ommutativitySubstitunctionExtensionTerm _ _ τ) (𝓬ommutativitySubstitunctionExtensionTerms _ _ τs)

  instance

    CommtativitySubstitunctionExtensionTerm : Commutativity Substitunction (Extension Term) Proposextensequality ¡
    Commutativity′.commutativity CommtativitySubstitunctionExtensionTerm = 𝓬ommutativitySubstitunctionExtensionTerm

    CommtativitySubstitunctionExtensionTerms : ∀ {N} → Commutativity Substitunction (Extension $ Terms N) Proposextensequality ¡
    Commutativity′.commutativity CommtativitySubstitunctionExtensionTerms = 𝓬ommutativitySubstitunctionExtensionTerms

    AssociativitySubstitunction : Associativity Substitunction Proposextensequality
    Associativity′.associativity AssociativitySubstitunction f g h x rewrite commutativity g h $ f x = ∅

    Extensionality₂Substitunction : Extensionality₂ Substitunction Proposextensequality
    Extensionality₂′.extensionality₂ Extensionality₂Substitunction {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = extensionality₁ g₁≡̇g₂ $ f₂ x

    IsSemigroupoidSubstitunction : IsSemigroupoid Substitunction Proposextensequality
    IsSemigroupoidSubstitunction = record {}

  SemigroupoidSubstitunction : Semigroupoid _ _ _
  Semigroupoid.Obj SemigroupoidSubstitunction = _
  Semigroupoid.Hom SemigroupoidSubstitunction = Substitunction
  Semigroupoid.Eq SemigroupoidSubstitunction = Proposextensequality

  instance

    IsSemifunctorSubstitunctionExtensionTerm : IsSemifunctor Substitunction Proposextensequality (Extension Term) Proposextensequality ¡
    IsSemifunctorSubstitunctionExtensionTerm = record {}

    IsSemifunctorSubstitunctionExtensionTerms : ∀ {N} → IsSemifunctor Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality ¡
    IsSemifunctorSubstitunctionExtensionTerms = record {}

  SemifunctorSubstitunctionExtensionTerm : Semifunctor _ _ _ _ _ _
  Semifunctor.Obj₁ SemifunctorSubstitunctionExtensionTerm = _
  Semifunctor.Hom₁ SemifunctorSubstitunctionExtensionTerm = Substitunction
  Semifunctor.Eq₁ SemifunctorSubstitunctionExtensionTerm = Proposextensequality
  Semifunctor.Obj₂ SemifunctorSubstitunctionExtensionTerm = _
  Semifunctor.Hom₂ SemifunctorSubstitunctionExtensionTerm = Extension Term
  Semifunctor.Eq₂ SemifunctorSubstitunctionExtensionTerm = Proposextensequality
  Semifunctor.μ SemifunctorSubstitunctionExtensionTerm = ¡

  instance

    ReflexivitySubstitunction : Reflexivity Substitunction
    Reflexivity.reflexivity ReflexivitySubstitunction = i

  private

    mutual

      𝓲dentitySubstitunctionExtensionTerm : 𝓲dentity Substitunction (Extension Term) Proposextensequality ¡
      𝓲dentitySubstitunctionExtensionTerm (i x) = ∅
      𝓲dentitySubstitunctionExtensionTerm leaf = ∅
      𝓲dentitySubstitunctionExtensionTerm (s fork t) = congruity₂ _fork_ (𝓲dentitySubstitunctionExtensionTerm s) (𝓲dentitySubstitunctionExtensionTerm t)
      𝓲dentitySubstitunctionExtensionTerm (function fn ts) = congruity (function fn) (𝓲dentitySubstitunctionExtensionTerms ts)

      𝓲dentitySubstitunctionExtensionTerms : ∀ {N} → 𝓲dentity Substitunction (Extension $ Terms N) Proposextensequality ¡
      𝓲dentitySubstitunctionExtensionTerms ∅ = ∅
      𝓲dentitySubstitunctionExtensionTerms (t , ts) = congruity₂ _,_ (𝓲dentitySubstitunctionExtensionTerm t) (𝓲dentitySubstitunctionExtensionTerms ts)

  instance

    IdentitySubstitunctionExtensionTerm : Identity Substitunction (Extension Term) Proposextensequality ¡
    Identity′.identity IdentitySubstitunctionExtensionTerm = 𝓲dentitySubstitunctionExtensionTerm

    IdentitySubstitunctionExtensionTerms : ∀ {N} → Identity Substitunction (Extension $ Terms N) Proposextensequality ¡
    Identity′.identity IdentitySubstitunctionExtensionTerms = 𝓲dentitySubstitunctionExtensionTerms

  instance

    LeftIdentitySubstitunction : LeftIdentity Substitunction Proposextensequality
    LeftIdentity′.left-identity LeftIdentitySubstitunction f = identity ∘ f

    RightIdentitySubstitunction : RightIdentity Substitunction Proposextensequality
    RightIdentity′.right-identity RightIdentitySubstitunction _ _ = ∅

  instance

    IsCategorySubstitunction : IsCategory Substitunction Proposextensequality
    IsCategorySubstitunction = record {}

  CategorySubstitunction : Category _ _ _
  Category.Obj CategorySubstitunction = _
  Category.Hom CategorySubstitunction = Substitunction
  Category.Eq CategorySubstitunction = Proposextensequality

  instance

    IsFunctorSubstitunctionExtensionTerm : IsFunctor Substitunction Proposextensequality (Extension Term) Proposextensequality ¡
    IsFunctorSubstitunctionExtensionTerm = record {}

    IsFunctorSubstitunctionExtensionTerms : ∀ {N} → IsFunctor Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality ¡
    IsFunctorSubstitunctionExtensionTerms = record {}

  FunctorSubstitunctionExtensionTerm : Functor _ _ _ _ _ _
  Functor.Obj₁ FunctorSubstitunctionExtensionTerm = _
  Functor.Hom₁ FunctorSubstitunctionExtensionTerm = Substitunction
  Functor.Eq₁ FunctorSubstitunctionExtensionTerm = Proposextensequality
  Functor.Obj₂ FunctorSubstitunctionExtensionTerm = _
  Functor.Hom₂ FunctorSubstitunctionExtensionTerm = Extension Term
  Functor.Eq₂ FunctorSubstitunctionExtensionTerm = Proposextensequality
  Functor.μ FunctorSubstitunctionExtensionTerm = ¡

  FunctorSubstitunctionExtensionTerms : ¶ → Functor _ _ _ _ _ _
  Functor.Obj₁ (FunctorSubstitunctionExtensionTerms _) = _
  Functor.Hom₁ (FunctorSubstitunctionExtensionTerms _) = Substitunction
  Functor.Eq₁ (FunctorSubstitunctionExtensionTerms _) = Proposextensequality
  Functor.Obj₂ (FunctorSubstitunctionExtensionTerms _) = _
  Functor.Hom₂ (FunctorSubstitunctionExtensionTerms N) = Extension $ Terms N
  Functor.Eq₂ (FunctorSubstitunctionExtensionTerms _) = Proposextensequality
  Functor.μ (FunctorSubstitunctionExtensionTerms _) = ¡

--   Functor.Obj₁ FunctorSubstitunctionExtensionTerm = _
--   Functor.Hom₁ FunctorSubstitunctionExtensionTerm = Substitunction
--   Functor.Eq₁ FunctorSubstitunctionExtensionTerm = Proposextensequality
--   Functor.Obj₂ FunctorSubstitunctionExtensionTerm = _
--   Functor.Hom₂ FunctorSubstitunctionExtensionTerm = Extension Term
--   Functor.Eq₂ FunctorSubstitunctionExtensionTerm = Proposextensequality
--   Functor.μ FunctorSubstitunctionExtensionTerm = ¡

-- -- open import Oscar.Prelude
-- -- open import Oscar.R
-- -- open import Oscar.Class
-- -- open import Oscar.Class.Alias
-- -- open import Oscar.Data

-- -- module _ {𝔬} {𝔒 : Ø 𝔬} where

-- --   instance

-- --     DiagonalProposequality : 𝓓iagonal Proposequality⟦ 𝔒 ⟧
-- --     𝓡₁.𝓻₁ DiagonalProposequality _ = ∅

-- --     SymmetryProposequality : 𝓢ymmetry′ Proposequality⟦ 𝔒 ⟧
-- --     𝓡₃.𝓻₃ SymmetryProposequality _ _ ∅ = ∅

-- --     TransitivityProposequality : 𝓣ransitivity′ Proposequality⟦ 𝔒 ⟧
-- --     𝓡₅.𝓻₅ TransitivityProposequality _ _ ∅ _ = ¡

-- --     CongruityProposequality : 𝓒ongruity′ Proposequality⟦ 𝔒 ⟧
-- --     𝓡₄.𝓻₄ CongruityProposequality _ _ _ ∅ = ∅

-- -- instance

-- --   Congruity⋆Proposequality : ∀ {a b} → 𝓒ongruity⋆ Proposequality a b
-- --   𝓡₆.𝓻₆ Congruity⋆Proposequality _ _ _ _ _ ∅ = ∅

-- -- module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} where

-- --   instance

-- --     DiagonalProposextensequality : 𝓓iagonal Proposextensequality⟦ 𝔓 ⟧
-- --     𝓡₁.𝓻₁ DiagonalProposextensequality _ _ = ∅

-- --     SymmetryProposextensequality : 𝓢ymmetry′ Proposextensequality⟦ 𝔓 ⟧
-- --     𝓡₃.𝓻₃ SymmetryProposextensequality _ _ f₁≡̇f₂ x rewrite f₁≡̇f₂ x = ∅

-- --     TransitivityProposextensequality : 𝓣ransitivity′ Proposextensequality⟦ 𝔓 ⟧
-- --     𝓡₅.𝓻₅ TransitivityProposextensequality _ _ f₁≡̇f₂ _ f₂≡̇f₃ x rewrite f₁≡̇f₂ x | f₂≡̇f₃ x = ∅

-- --     ĊongruityProposextensequality : 𝓒̇ongruity′ Proposextensequality⟦ 𝔓 ⟧
-- --     𝓡₄.𝓻₄ ĊongruityProposextensequality F f₁ f₂ f₁≡̇f₂ x rewrite f₁≡̇f₂ x = ∅

-- -- module ¶Group₂ where

-- --   record Semigroup₁ : Set where
-- --     no-eta-equality
-- --     instance
-- --       𝓤nit¶ : 𝓤nit ¶
-- --       𝓡₀.𝓻₀ 𝓤nit¶ = 0

-- --       Unit¶ : Unit ¶
-- --       Unit.⋆ Unit¶ = it

-- --   record Semigroup₂ : Set where
-- --     no-eta-equality
-- --     instance
-- --       𝓤nit¶ : 𝓤nit ¶
-- --       𝓡₀.𝓻₀ 𝓤nit¶ = 1

-- --       Unit¶ : Unit ¶
-- --       Unit.⋆ Unit¶ = it

-- --   record Semigroups : Set where
-- --     no-eta-equality
-- --     instance

-- --       𝓤nit₂¶ : 𝓤nit² ¶
-- --       𝓡₀,₂.𝓻₀,₀ 𝓤nit₂¶ = let open Semigroup₁ record {} in unit
-- --       𝓡₀,₂.𝓻₀,₁ 𝓤nit₂¶ = let open Semigroup₂ record {} in unit
-- --       -- 𝓡₀,₂¶ : 𝓡₀,₂ ¶
-- --       -- 𝓡₀,₂.𝓻₀,₀ 𝓡₀,₂¶ = let open Semigroup₁ record {} in unit
-- --       -- 𝓡₀,₂.𝓻₀,₁ 𝓡₀,₂¶ = let open Semigroup₂ record {} in unit

-- --       Unit²¶ : Unit² ¶
-- --       Unit².⋆ Unit²¶ = it

-- --   record SG (A : Set) : Set where
-- --     field
-- --       ⦃ I-Unit² ⦄ : Unit² A
-- --       ⦃ I-Magma₂ ⦄ : Magma₂ A

-- --     u0*u1 : A
-- --     u0*u1 = unit₁ * unit₀

-- --   open SG ⦃ … ⦄

-- --   u0*u1' : ∀ {A : Set} ⦃ I-Unit² : Unit² A ⦄ ⦃ I-Magma₂ : Magma₂ A ⦄ → A
-- --   u0*u1' = unit₁ * unit₀

-- --   record SG2 (A : Set) : Set where
-- --     field
-- --       ⦃ I-𝓤nit² ⦄ : 𝓤nit² A
-- --       ⦃ I-Magma₂ ⦄ : 𝓜agma₂ A

-- --     UNIT₀ : A
-- --     UNIT₀ = 𝓻₀,₀

-- --   open SG2 ⦃ … ⦄

-- --   record SG3 (A : Set) : Set where
-- --     field
-- --       ⦃ I-𝓤nit1 ⦄ : Unit A
-- --       -- ⦃ I-𝓤nit2 ⦄ : Unit A
-- --       ⦃ I-Magma₂ ⦄ : 𝓜agma₂ A

-- --     UNIT0 : A
-- --     UNIT0 = unit -- ⦃ I-𝓤nit1 ⦄

-- --   open SG3 ⦃ … ⦄

-- --   record SG4 (A : Set) : Set where
-- --     field
-- --       ⦃ I-𝓤nit² ⦄ : Unit² A
-- --       ⦃ I-Magma₂ ⦄ : 𝓜agma₂ A

-- --     UNIT41 : A
-- --     UNIT41 = unit₀

-- --   open SG4 ⦃ … ⦄

-- --   record IsEquivalence {𝔬} {𝔒 : 𝓾nit (Ø 𝔬)} {𝔮} (𝔔 : 𝓹rop₂ 𝔒 𝔮) : Ø 𝔬 ∙̂ 𝔮 where
-- --     field ⦃ I-Reflexivity ⦄ : Diagonal 𝔔
-- --     reflexivity : 𝓭iagonal 𝔔
-- --     reflexivity = diagonal ⦃ I-Reflexivity ⦄
-- --     field ⦃ I-Symmetry ⦄ : Symmetry′ 𝔔
-- --     field ⦃ I-Transitivity ⦄ : Transitivity′ 𝔔
-- --   open IsEquivalence ⦃ … ⦄

-- --   record Equivalence {𝔬} (𝔒 : Ø 𝔬) 𝔮 : Ø 𝔬 ∙̂ ↑̂ 𝔮 where
-- --     field ⦃ I-Equality ⦄ : Prop₂ 𝔒 𝔮
-- --     infix 4 _≋_
-- --     _≋_ : 𝓹rop₂ 𝔒 𝔮
-- --     _≋_ = prop₂ ⦃ I-Equality ⦄
-- --     field ⦃ I-IsEquivalence ⦄ : IsEquivalence _≋_
-- --   open Equivalence ⦃ … ⦄

-- --   test-isequiv : ⦃ _ : Equivalence ¶ ∅̂ ⦄ → prop₂ (↑ ∅) 1 -- ↑ ∅ ≋ 1
-- --   test-isequiv ⦃ x ⦄ = reflexivity

-- --   test-sym : ⦃ _ : Equivalence ¶ ∅̂ ⦄ → ∀ {x y : ¶} → x ≋ y → prop₂ y x  -- ↑ ∅ ≋ 1
-- --   test-sym ⦃ x ⦄ = symmetry -- reflexivity

-- --   postulate
-- --     eq¶ : ¶ → ¶ → Ø ∅̂

-- --   test-isequiv' : ⦃ _ : IsEquivalence eq¶ ⦄ → eq¶ (↑ ∅) 1 -- ↑ ∅ ≋ 1
-- --   test-isequiv' ⦃ x ⦄ = reflexivity


-- --   record IsSemigroupoid
-- --     {𝔬} (𝔒 : Ø 𝔬)
-- --     {𝔪} (𝔐 : 𝔒 → 𝔒 → Ø 𝔪)
-- --     {𝔮} (𝔔 : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮)
-- --     ⦃ Composition : 𝓣ransitivity′ 𝔐 ⦄
-- --     : Ø 𝔬 ∙̂ 𝔪 ∙̂ 𝔮 where
-- --   -- open IsSemigroupoid ⦃ … ⦄

-- --   trans : ∀
-- --     {𝔬₀} {𝔒₀ : Ø 𝔬₀}
-- --     {𝔬₁} {𝔒₁ : 𝔒₀ → Ø 𝔬₁}
-- --     {𝔬₂} {𝔒₂ : ∀ x₀ → 𝔒₁ x₀ → Ø 𝔬₂}
-- --     {𝔬₃} {𝔒₃ : ∀ x₀ x₁ → 𝔒₂ x₀ x₁ → Ø 𝔬₃}
-- --     {𝔬₄} {𝔒₄ : ∀ x₀ x₁ x₂ → 𝔒₃ x₀ x₁ x₂ → Ø 𝔬₄}
-- --     {𝔬₅} {𝔒₅ : ∀ x₀ x₁ x₂ x₃ → 𝔒₄ x₀ x₁ x₂ x₃ → Ø 𝔬₅}
-- --     → ⦃ _ : 𝓡₅ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ 𝔒₄ 𝔒₅ ⦄
-- --     → ∀ {x₀ x₁} x₂ {x₃} x₄ → 𝔒₅ x₀ x₁ x₂ x₃ x₄
-- --   trans _ = 𝓻₅ _ _ _ _


-- --   test-isSemigroupoid : ∀
-- --     {𝔬} (𝔒 : Ø 𝔬)
-- --     {𝔪} (𝔐 : 𝔒 → 𝔒 → Ø 𝔪)
-- --     {𝔮} (𝔔 : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮)
-- --     {𝔮} (𝔔₁ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮)
-- --     ⦃ _ : 𝓣ransitivity′ 𝔐 ⦄
-- --     ⦃ _ : IsSemigroupoid 𝔒 𝔐 𝔔 ⦄
-- --     ⦃ _ : IsSemigroupoid 𝔒 𝔐 𝔔₁ ⦄
-- --     → 𝓽ransitivity′ 𝔐
-- --   test-isSemigroupoid _ _ _ _ = trans -- transitivity


-- --   record Semigroupoid 𝔬 𝔪 𝔮 : Ø ↑̂ (𝔬 ∙̂ 𝔪 ∙̂ 𝔮) where
-- --     field ⦃ Object ⦄ : Unit (Ø 𝔬)
-- --     Obj : 𝓾nit (Ø 𝔬)
-- --     Obj = unit
-- --     field ⦃ Homomorphism ⦄ : Prop₂ Obj 𝔪
-- --     Hom = prop₂ ⦃ Homomorphism ⦄
-- --     field ⦃ Equality ⦄ : ∀ {x y} → Prop₂ (Hom x y) 𝔮
-- --     Eq = λ {x y : Obj} → prop₂ ⦃ Equality {x} {y} ⦄
-- --     field ⦃ isSemigroupoid ⦄ : IsSemigroupoid Obj Hom Eq
-- --     -- field ⦃ Composition ⦄ : Transitivity′ Hom
-- --     _∙'_ : 𝓽ransitivity′ Hom
-- --     _∙'_ = trans -- transitivity
-- --   open Semigroupoid ⦃ … ⦄

-- --   record Semigroupoids 𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂ : Ø ↑̂ (𝔬₁ ∙̂ 𝔪₁ ∙̂ 𝔮₁ ∙̂ 𝔬₂ ∙̂ 𝔪₂ ∙̂ 𝔮₂) where
-- --     field
-- --       ⦃ S1 ⦄ : Semigroupoid 𝔬₁ 𝔪₁ 𝔮₁
-- --       ⦃ S2 ⦄ : Semigroupoid 𝔬₂ 𝔪₂ 𝔮₂
-- --     Obj₁ = Obj ⦃ S1 ⦄
-- --     Obj₂ = Obj ⦃ S2 ⦄
-- --     Hom₁ = Hom ⦃ S1 ⦄
-- --     open Semigroupoid S2 public using () renaming (Hom to Hom₂)
-- --     -- Hom₂ = Hom ⦃ S2 ⦄
-- --     module ⒈ = Semigroupoid S1
-- --     module ⒉ = Semigroupoid S2
-- --   open Semigroupoids ⦃ … ⦄

-- --   record Semifunctor 𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂ : Ø ↑̂ (𝔬₁ ∙̂ 𝔪₁ ∙̂ 𝔮₁ ∙̂ 𝔬₂ ∙̂ 𝔪₂ ∙̂ 𝔮₂) where
-- --     field
-- --       ⦃ Ss ⦄ : Semigroupoids 𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂
-- --       μ : Obj₁ → Obj₂
-- --       ⦃ I-Map2 ⦄ : Remap Hom₁ Hom₂ μ
-- --       -- ⦃ I-Map2 ⦄ : 𝓡emap Hom₁ Hom₂ μ
-- --       -- ⦃ I-Map2 ⦄ : 𝓡emap Hom₁ ⒉.Hom μ
-- --     module SGs = Semigroupoids Ss
-- --     open 𝓡₃ ⦃ … ⦄ public using () renaming (r3' to FMAP)
-- --     open R3M public renaming (threemap to FMAP3)
-- --     fmap : 𝓻emap Hom₁ ⒉.Hom μ
-- --     fmap = 𝓻₃ _ _
-- --       {-
-- --     fmap : 𝓻emap Hom₁ ⒉.Hom μ
-- --     fmap = remap ⦃ I-Map2 ⦄
-- --       -}
-- --       -- ⦃ I-Map2 ⦄ : ∀ {x y} → REMAPR Hom₁ x y ⒉.Hom (μ x) (μ y)
-- --       -- ⦃ I-Map2 ⦄ : ∀ {x y} → REMAPR2 x y Hom₁ μ ⒉.Hom
-- --   open Semifunctor ⦃ … ⦄

-- --   open 𝓡₃ ⦃ … ⦄ using () renaming (r3' to REREmap)
-- --   open R3M using () renaming (threemap to map3)

-- --   test-remap : ∀
-- --     {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔮₁}
-- --     {𝔔₁ : 𝔒₁ → 𝔒₁ → Ø 𝔮₁}
-- --     {𝔬₂} {𝔒₂ : Ø 𝔬₂} {𝔮₂}
-- --     {𝔔₂ : 𝔒₂ → 𝔒₂ → Ø 𝔮₂}
-- --     {μ : 𝔒₁ → 𝔒₂}
-- --     → ⦃ _ : Remap 𝔔₁ 𝔔₂ μ ⦄ → 𝓻emap 𝔔₁ 𝔔₂ μ
-- --   test-remap = map3  -- REREmap -- OhRemap -- REREmap -- r3' -- 𝓻₃ _ _

-- --   module TestSemifunctors
-- --     {𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂}
-- --     (SF1 : Semifunctor 𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂)
-- --     (SF2 : Semifunctor 𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂)
-- --     where
-- --     module S1 = Semifunctor SF1
-- --     module S2 = Semifunctor SF2
-- --     fooμ = μ
-- --     instance _ = SF1
-- --     instance _ = SF2

-- --     bar : 𝓻emap Hom₁ Hom₂ μ
-- --     bar = S1.fmap

-- --     bar2 : 𝓻emap S1.SGs.Hom₁ Hom₂ μ
-- --     bar2 = map3


-- --   test-semifunctor : ∀ {𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂} → ⦃ _ : Semifunctor 𝔬₁ 𝔪₁ 𝔮₁ 𝔬₂ 𝔪₂ 𝔮₂ ⦄ → 𝓻emap Hom₁ ⒉.Hom μ
-- --   test-semifunctor = FMAP3 -- FMAP -- r3' -- REREmap -- remap
-- --   -- test-remap ⦃ I-Map2 ⦄ -- 𝓻₃ _ _ -- remap
-- -- {-
-- -- 𝓻₃
-- -- Have: {𝔬₀ : Ł} {𝔒₀ : Set 𝔬₀} {𝔬₁ : Ł} {𝔒₁ : 𝔒₀ → Set 𝔬₁} {𝔬₂ : Ł}
-- --       {𝔒₂ : (x₀ : 𝔒₀) → 𝔒₁ x₀ → Set 𝔬₂} {𝔬₃ : Ł}
-- --       {𝔒₃ : (x₀ : 𝔒₀) (x₁ : 𝔒₁ x₀) → 𝔒₂ x₀ x₁ → Set 𝔬₃}
-- --       {{r : 𝓡₃ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃}} (x₀ : 𝔒₀) (x₁ : 𝔒₁ x₀) (x₂ : 𝔒₂ x₀ x₁) →
-- --       𝔒₃ x₀ x₁ x₂
-- -- remap
-- -- Have: {𝔬₁ : Ł} {𝔒₁ : Set 𝔬₁} {𝔮₁ : Ł} {𝔔₁ : 𝔒₁ → 𝔒₁ → Set 𝔮₁}
-- --       {𝔬₂ : Ł} {𝔒₂ : Set 𝔬₂} {𝔮₂ : Ł} {𝔔₂ : 𝔒₂ → 𝔒₂ → Set 𝔮₂}
-- --       {μ = μ₁ : 𝔒₁ → 𝔒₂} {{r : Remap 𝔔₁ 𝔔₂ μ₁}} {x y : 𝔒₁} →
-- --       𝔔₁ x y → 𝔔₂ (μ₁ x) (μ₁ y)
-- -- REMAP
-- -- Have: {𝔬₁ : Ł} {𝔒₁ : Set 𝔬₁} {𝔮₁ : Ł} {𝔔₁ : 𝔒₁ → 𝔒₁ → Set 𝔮₁}
-- --       {x y : 𝔒₁} {𝔬₂ : Ł} {𝔒₂ : Set 𝔬₂} {𝔮₂ : Ł} {𝔔₂ : 𝔒₂ → 𝔒₂ → Set 𝔮₂}
-- --       {μx μy : 𝔒₂} {{r : REMAPR 𝔔₁ x y 𝔔₂ μx μy}} →
-- --       𝔔₁ x y → 𝔔₂ μx μy

-- -- ⦃ r : REMAP2 μ x y 𝔔₁ 𝔔₂ ⦄ → 𝔔₁ x y → 𝔔₂ (μ x) (μ y)

-- -- {𝔬₁ : Ł} {𝔒₁ : Set 𝔬₁} {𝔮₁ : Ł} {𝔔₁ : 𝔒₁ → 𝔒₁ → Set 𝔮₁}
-- -- {𝔬₂ : Ł} {𝔒₂ : Set 𝔬₂} {𝔮₂ : Ł} {𝔔₂ : 𝔒₂ → 𝔒₂ → Set 𝔮₂}
-- -- {μ = μ₁ : 𝔒₁ → 𝔒₂}
-- -- {x y : 𝔒₁}
-- -- ⦃ r : Remap 𝔔₁ 𝔔₂ (μ₁ x) (μ₁ y) ⦄ → 𝔔₁ x y → 𝔔₂ (μ₁ x) (μ₁ y)

-- -- -}
-- -- --  record IsSemigrouopid {𝔬} (𝔒 : Ø 𝔬) {𝔪}


-- --   -- open Semigroup₁ record {}
-- --   -- open Semigroups record {}
-- --   z : ⦃ _ : SG ¶ ⦄ ⦃ _ : SG2 ¶ ⦄ ⦃ _ : SG3 ¶ ⦄ → ¶
-- --   z = UNIT0











-- -- -- module ¶Group₁ where

-- -- --   record Group : Set where
-- -- --     field
-- -- --       ε₀ : ¶
-- -- --       ε₁ : ¶
-- -- --       _+_ : ¶ → ¶ → ¶
-- -- --       _*_ : ¶ → ¶ → ¶

-- -- --   record RR (A : Set) (B : A → Set) : Set where
-- -- --     field
-- -- --       F1 : A
-- -- --       F2 : B F1
-- -- --   open RR ⦃ … ⦄

-- -- --   record SS (A : Set) : Set where
-- -- --     field
-- -- --       G1 : A
-- -- --       G2 : A
-- -- --   open SS ⦃ … ⦄

-- -- --   instance ¶RR : RR ¶ (λ _ → ¶)
-- -- --   RR.F1 ¶RR = 0
-- -- --   RR.F2 ¶RR = 1

-- -- --   instance ¶SS : SS ¶
-- -- --   SS.G1 ¶SS = 0
-- -- --   SS.G2 ¶SS = 1

-- -- --   instance ¶𝓤nit0 : 𝓤nit ¶
-- -- --   𝓡₀.𝓻₀ ¶𝓤nit0 = 0

-- -- --   instance ¶Unit0 : Unit ¶
-- -- --   Unit.⋆ ¶Unit0 = it

-- -- --   z : ¶
-- -- --   z = G2

-- -- -- module SubstitunctionProperty {𝔭} (𝔓 : Ø 𝔭) where

-- -- --   open Substitunction 𝔓
-- -- --   open Term 𝔓

-- -- --   private

-- -- --     mutual

-- -- --       𝓶apSubstitunctionExtensionTerm : 𝓶ap Substitunction (_⟨ Term ⟩→_)
-- -- --       𝓶apSubstitunctionExtensionTerm σ (i x) = σ x
-- -- --       𝓶apSubstitunctionExtensionTerm σ leaf = leaf
-- -- --       𝓶apSubstitunctionExtensionTerm σ (τ₁ fork τ₂) = 𝓶apSubstitunctionExtensionTerm σ τ₁ fork 𝓶apSubstitunctionExtensionTerm σ τ₂
-- -- --       𝓶apSubstitunctionExtensionTerm σ (function p τs) = function p (𝓶apSubstitunctionExtensionTerms σ τs)

-- -- --       𝓶apSubstitunctionExtensionTerms : ∀ {N} → 𝓶ap Substitunction (_⟨ Terms N ⟩→_)
-- -- --       𝓶apSubstitunctionExtensionTerms σ ∅ = ∅
-- -- --       𝓶apSubstitunctionExtensionTerms σ (τ , τs) = 𝓶apSubstitunctionExtensionTerm σ τ , 𝓶apSubstitunctionExtensionTerms σ τs

-- -- --   instance

-- -- --     𝓜apSubstitunctionExtensionTerm : 𝓜ap Substitunction (_⟨ Term ⟩→_)
-- -- --     𝓡₃.𝓻₃ 𝓜apSubstitunctionExtensionTerm _ _ σ τ = 𝓶apSubstitunctionExtensionTerm σ τ

-- -- --     𝓜apSubstitunctionExtensionTerms : ∀ {N} → 𝓜ap Substitunction (_⟨ Terms N ⟩→_)
-- -- --     𝓡₃.𝓻₃ 𝓜apSubstitunctionExtensionTerms _ _ σ τs = 𝓶apSubstitunctionExtensionTerms σ τs

-- -- --   instance

-- -- --     MapSubstitunctionExtensionTerm : Map Substitunction (_⟨ Term ⟩→_)
-- -- --     Map.⋆ MapSubstitunctionExtensionTerm = it

-- -- --     MapSubstitunctionExtensionTerms : ∀ {N} → Map Substitunction (_⟨ Terms N ⟩→_)
-- -- --     Map.⋆ MapSubstitunctionExtensionTerms = it

-- -- --   instance

-- -- --     Map'SubstitunctionExtensionTerm : Map' Substitunction (_⟨ Term ⟩→_)
-- -- --     Map'SubstitunctionExtensionTerm = record {}

-- -- --     Map'SubstitunctionExtensionTerms : ∀ {N} → Map' Substitunction (_⟨ Terms N ⟩→_)
-- -- --     Map'SubstitunctionExtensionTerms = record {}

-- -- --   𝓶apSubstitunctionExtensionTerm' : 𝓶ap Substitunction (_⟨ Term ⟩→_)
-- -- --   𝓶apSubstitunctionExtensionTerm' σ (i x) = σ x
-- -- --   𝓶apSubstitunctionExtensionTerm' σ leaf = leaf
-- -- --   𝓶apSubstitunctionExtensionTerm' σ (τ₁ fork τ₂) = (map' σ $ τ₁) fork (𝓻₃ _ _ σ $ τ₂)
-- -- --   𝓶apSubstitunctionExtensionTerm' σ (function p τs) = function p (map σ $ τs)

-- -- --   test-r3 : 𝓶ap Substitunction (_⟨ Term ⟩→_)
-- -- --   test-r3 = 𝓻₃ _ _

-- -- --   test-map : 𝓶ap Substitunction (_⟨ Term ⟩→_)
-- -- --   test-map = map

-- -- --   postulate
-- -- --     -- instance
-- -- --     𝓣ransitivitySubstitunction1 : 𝓣ransitivity′ Substitunction
-- -- --     𝓣ransitivitySubstitunction2 : 𝓣ransitivity′ Substitunction
-- -- -- --     𝓡₅.𝓻₅ 𝓣ransitivitySubstitunction _ _ f _ g = map g ∘ f

-- -- --   TransitivitySubstitunction1 : Transitivity′ Substitunction
-- -- --   Transitivity.⋆ TransitivitySubstitunction1 = 𝓣ransitivitySubstitunction1

-- -- --   TransitivitySubstitunctionI11 : Transitivity′-I₁ Substitunction
-- -- --   Transitivity-I₁.⋆ TransitivitySubstitunctionI11 = 𝓣ransitivitySubstitunction1

-- -- --   TransitivitySubstitunctionI22 : Transitivity′-I₂ Substitunction
-- -- --   Transitivity-I₂.⋆ TransitivitySubstitunctionI22 = 𝓣ransitivitySubstitunction2

-- -- --   TransitivitySubstitunctionI21 : Transitivity′-I₂ Substitunction
-- -- --   Transitivity-I₂.⋆ TransitivitySubstitunctionI21 = 𝓣ransitivitySubstitunction1

-- -- --   record RawSemigroupoid 𝔬 𝔪 𝔮 : Ø ↑̂ (𝔬 ∙̂ 𝔪 ∙̂ 𝔮) where
-- -- --     field
-- -- --       𝔒 : Ø 𝔬
-- -- --       𝔐 : 𝔒 → 𝔒 → Ø 𝔪
-- -- --       _≋_ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮
-- -- --       ≋-diagonal : ∀ {x y} → 𝓭iagonal (_≋_ {x} {y})
-- -- --       _∙_ : 𝓽ransitivity′ 𝔐

-- -- --   makeRawSemigroupoid : ∀ {𝔬} (𝔒 : Ø 𝔬) {𝔪} (𝔐 : 𝔒 → 𝔒 → Ø 𝔪) {𝔮} (_≋_ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮)
-- -- --     ⦃ _ : ∀ {x y} → 𝓓iagonal (_≋_ {x} {y}) ⦄
-- -- --     ⦃ _ : Transitivity′ 𝔐 ⦄
-- -- --     ⦃ _ : Transitivity′-I₁ 𝔐 ⦄
-- -- --     ⦃ _ : Transitivity′-I₂ 𝔐 ⦄
-- -- --     → RawSemigroupoid 𝔬 𝔪 𝔮
-- -- --   RawSemigroupoid.𝔒 (makeRawSemigroupoid 𝔒 𝔐 _≋_) = 𝔒
-- -- --   RawSemigroupoid.𝔐 (makeRawSemigroupoid 𝔒 𝔐 _≋_) = 𝔐
-- -- --   RawSemigroupoid._≋_ (makeRawSemigroupoid 𝔒 𝔐 _≋_) = _≋_
-- -- --   RawSemigroupoid.≋-diagonal (makeRawSemigroupoid 𝔒 𝔐 _≋_) = 𝓻₁ _
-- -- --   RawSemigroupoid._∙_ (makeRawSemigroupoid 𝔒 𝔐 _≋_) = transitivity -- 𝓻₅ _ _ 𝔐xy _

-- -- -- --   test-make : RawSemigroupoid _ _ _
-- -- -- --   test-make = makeRawSemigroupoid ¶ Substitunction Proposextensequality



-- -- -- -- -- _∙_ : ∀ {m n} → m ⊸ n → ∀ {l} → l ⊸ m → l ⊸ n
-- -- -- -- -- _∙_ f g = (f ◂_) ∘ g


-- -- -- -- -- -- record Σ {𝔬} (𝔒 : Ø 𝔬) {𝔭} (𝔓 : 𝔒 → Ø 𝔭) : Ø 𝔬 ∙̂ 𝔭 where
-- -- -- -- -- --   constructor _,_
-- -- -- -- -- --   field
-- -- -- -- -- --     π₀ : 𝔒
-- -- -- -- -- --     π₁ : 𝔓 π₀

-- -- -- -- -- -- open Σ

-- -- -- -- -- -- uncurry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} →
-- -- -- -- -- --             (∀ x (y : B x) → C x y) → (p : Σ A B) → C (π₀ p) (π₁ p)
-- -- -- -- -- -- uncurry f (x , y) = f x y

-- -- -- -- -- -- record Equivalence {𝔬} {𝔒 : Ø 𝔬} {𝔮} (_≋_ : 𝔒 → 𝔒 → Ø 𝔮) : Ø 𝔬 ∙̂ 𝔮 where
-- -- -- -- -- --   field
-- -- -- -- -- --     ≋-reflexivity : ∀ {x} → x ≋ x
-- -- -- -- -- --     ≋-symmetry : ∀ {x y} → x ≋ y → y ≋ x
-- -- -- -- -- --     ≋-transitivity : ∀ {x y} → x ≋ y → ∀ {z} → y ≋ z → x ≋ z

-- -- -- -- -- -- record IsSetoid {𝔬} (𝔒 : Ø 𝔬) 𝔮 : Ø 𝔬 ∙̂ ↑̂ 𝔮 where
-- -- -- -- -- --   infix 4 _≋_
-- -- -- -- -- --   field
-- -- -- -- -- --     _≋_ : 𝔒 → 𝔒 → Ø 𝔮
-- -- -- -- -- --     ≋-reflexivity : ∀ {x} → x ≋ x
-- -- -- -- -- --     ≋-symmetry : ∀ {x y} → x ≋ y → y ≋ x
-- -- -- -- -- --     ≋-transitivity : ∀ {x y} → x ≋ y → ∀ {z} → y ≋ z → x ≋ z

-- -- -- -- -- -- IsSetoid' : ∀ {𝔬} (𝔒 : Ø 𝔬) 𝔮 → Ø 𝔬 ∙̂ ↑̂ 𝔮
-- -- -- -- -- -- IsSetoid' 𝔒 𝔮 = Σ (𝔒 → 𝔒 → Ø 𝔮) Equivalence

-- -- -- -- -- -- record IsSetoid'' {𝔬} {𝔒 : Ø 𝔬} {𝔮} (isSetoid' : IsSetoid' 𝔒 𝔮) : Ø 𝔬 ∙̂ ↑̂ 𝔮 where
-- -- -- -- -- --   infix 4 _≋_
-- -- -- -- -- --   _≋_ : 𝔒 → 𝔒 → Ø 𝔮
-- -- -- -- -- --   _≋_ = Σ.π₀ isSetoid'

-- -- -- -- -- -- --  ≋-reflexivity : ∀ {x} → x ≋ x
-- -- -- -- -- -- --  ≋-symmetry : ∀ {x y} → x ≋ y → y ≋ x
-- -- -- -- -- -- --  ≋-transitivity : ∀ {x y} → x ≋ y → ∀ {z} → y ≋ z → x ≋ z

-- -- -- -- -- -- record RSetoid 𝔬 𝔮 : Ø ↑̂ (𝔬 ∙̂ 𝔮) where
-- -- -- -- -- --   field
-- -- -- -- -- --     𝔒 : Ø 𝔬
-- -- -- -- -- --     isSetoid : IsSetoid 𝔒 𝔮

-- -- -- -- -- -- Setoid : ∀ 𝔬 𝔮 → Ø ↑̂ (𝔬 ∙̂ 𝔮)
-- -- -- -- -- -- Setoid 𝔬 𝔮 = Σ (Ø 𝔬) (λ 𝔒 → IsSetoid 𝔒 𝔮)

-- -- -- -- -- -- record OpenedSetoid {𝔬 𝔮} (setoid : Setoid 𝔬 𝔮) : Ø₀ where
-- -- -- -- -- --   private
-- -- -- -- -- --     𝔒 = Σ.π₀ setoid
-- -- -- -- -- --     isSetoid = Σ.π₁ setoid

-- -- -- -- -- --   open IsSetoid isSetoid public

-- -- -- -- -- -- record IsSemigroupoid
-- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬}
-- -- -- -- -- --   {𝔪} (𝔐 : 𝔒 → 𝔒 → Ø 𝔪)
-- -- -- -- -- --   {𝔮} (𝔐-setoid : ∀ {x y} → IsSetoid (𝔐 x y) 𝔮)
-- -- -- -- -- --   : Ø 𝔬 ∙̂ 𝔪 ∙̂ 𝔮 where
-- -- -- -- -- --   instance _ = λ {x y} → 𝔐-setoid {x} {y}
-- -- -- -- -- --   open IsSetoid ⦃ … ⦄ using (_≋_)
-- -- -- -- -- --   infixr 9 _∙_
-- -- -- -- -- --   field
-- -- -- -- -- --     _∙_ : ∀ {y z} → 𝔐 y z → ∀ {x} → 𝔐 x y → 𝔐 x z
-- -- -- -- -- --     ∙-extensionality : ∀ {x y} {f₁ f₂ : 𝔐 x y} → f₁ ≋ f₂ → ∀ {z} {g₁ g₂ : 𝔐 y z} → g₁ ≋ g₂ → g₁ ∙ f₁ ≋ g₂ ∙ f₂
-- -- -- -- -- --     ∙-associativity : ∀ {w x} (f : 𝔐 w x) {y} (g : 𝔐 x y) {z} (h : 𝔐 y z) → (h ∙ g) ∙ f ≋ h ∙ (g ∙ f)

-- -- -- -- -- -- record IsCategory
-- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬}
-- -- -- -- -- --   {𝔪} {𝔐 : 𝔒 → 𝔒 → Ø 𝔪}
-- -- -- -- -- --   {𝔮} {𝔐-setoid : ∀ {x y} → IsSetoid (𝔐 x y) 𝔮}
-- -- -- -- -- --   (semigroupoid : IsSemigroupoid 𝔐 𝔐-setoid)
-- -- -- -- -- --   : Ø 𝔬 ∙̂ 𝔪 ∙̂ 𝔮 where
-- -- -- -- -- --   instance _ = λ {x y} → 𝔐-setoid {x} {y}
-- -- -- -- -- --   open IsSetoid ⦃ … ⦄ using (_≋_)
-- -- -- -- -- --   open IsSemigroupoid semigroupoid using (_∙_)
-- -- -- -- -- --   field
-- -- -- -- -- --     ε : ∀ {x} → 𝔐 x x
-- -- -- -- -- --     ε-left-identity : ∀ {x y} {f : 𝔐 x y} → ε ∙ f ≋ f
-- -- -- -- -- --     ε-right-identity : ∀ {x y} {f : 𝔐 x y} → f ∙ ε ≋ f

-- -- -- -- -- -- record IsSemifunctor
-- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁}
-- -- -- -- -- --   {𝔪₁} {𝔐₁ : 𝔒₁ → 𝔒₁ → Ø 𝔪₁}
-- -- -- -- -- --   {𝔮₁} {𝔐₁-setoid : ∀ {x y} → IsSetoid (𝔐₁ x y) 𝔮₁}
-- -- -- -- -- --   (semigroupoid₁ : IsSemigroupoid 𝔐₁ 𝔐₁-setoid)
-- -- -- -- -- --   {𝔬₂} {𝔒₂ : Ø 𝔬₂}
-- -- -- -- -- --   {𝔪₂} {𝔐₂ : 𝔒₂ → 𝔒₂ → Ø 𝔪₂}
-- -- -- -- -- --   {𝔮₂} {𝔐₂-setoid : ∀ {x y} → IsSetoid (𝔐₂ x y) 𝔮₂}
-- -- -- -- -- --   (semigroupoid₂ : IsSemigroupoid 𝔐₂ 𝔐₂-setoid)
-- -- -- -- -- --   : Ø 𝔬₁ ∙̂ 𝔪₁ ∙̂ 𝔮₁ ∙̂ 𝔬₂ ∙̂ 𝔪₂ ∙̂ 𝔮₂
-- -- -- -- -- --   where
-- -- -- -- -- --   instance _ = λ {x y} → 𝔐₁-setoid {x} {y}
-- -- -- -- -- --   instance _ = λ {x y} → 𝔐₂-setoid {x} {y}
-- -- -- -- -- --   open IsSetoid ⦃ … ⦄ using (_≋_)
-- -- -- -- -- --   module ⒈ = IsSemigroupoid semigroupoid₁
-- -- -- -- -- --   module ⒉ = IsSemigroupoid semigroupoid₂
-- -- -- -- -- --   field
-- -- -- -- -- --     {μ} : 𝔒₁ → 𝔒₂
-- -- -- -- -- --     𝔣 : ∀ {x y} → 𝔐₁ x y → 𝔐₂ (μ x) (μ y)
-- -- -- -- -- --     𝔣-extensionality : ∀ {x y} → {f₁ f₂ : 𝔐₁ x y} → f₁ ≋ f₂ → 𝔣 f₁ ≋ 𝔣 f₂
-- -- -- -- -- --     𝔣-commutativity : ∀ {x y} {f : 𝔐₁ x y} {z} {g : 𝔐₁ y z} → 𝔣 (g ⒈.∙ f) ≋ 𝔣 g ⒉.∙ 𝔣 f

-- -- -- -- -- -- record Congruity
-- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔮₁} (𝔔₁ : 𝔒₁ → 𝔒₁ → Ø 𝔮₁)
-- -- -- -- -- --   {𝔬₂} {𝔒₂ : Ø 𝔬₂} {𝔮₂} (𝔔₂ : ∀ (f : 𝔒₁ → 𝔒₂) → ∀ {x y} → 𝔔₁ x y → Ø 𝔮₂)
-- -- -- -- -- --   : Ø 𝔬₁ ∙̂ 𝔮₁ ∙̂ 𝔬₂ ∙̂ 𝔮₂ where
-- -- -- -- -- --   field
-- -- -- -- -- --     congruity : (f : 𝔒₁ → 𝔒₂) → ∀ {x y : 𝔒₁} → (q₁ : 𝔔₁ x y) → 𝔔₂ f q₁

-- -- -- -- -- -- open Congruity ⦃ … ⦄

-- -- -- -- -- -- test-congruity : ∀
-- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔮₁} (𝔔₁ : 𝔒₁ → 𝔒₁ → Ø 𝔮₁)
-- -- -- -- -- --   {𝔬₂} {𝔒₂ : Ø 𝔬₂} {𝔮₂} (𝔔₂ : ∀ (f : 𝔒₁ → 𝔒₂) → ∀ {x y} → 𝔔₁ x y → Ø 𝔮₂)
-- -- -- -- -- --   ⦃ _ : Congruity 𝔔₁ 𝔔₂ ⦄
-- -- -- -- -- --   → (f : 𝔒₁ → 𝔒₂) → ∀ {x y : 𝔒₁} → (q₁ : 𝔔₁ x y) → 𝔔₂ f q₁
-- -- -- -- -- -- test-congruity _ _ = congruity

-- -- -- -- -- -- postulate
-- -- -- -- -- --   _==_ : ∀ {A : Set} → A → A → Set
-- -- -- -- -- --   _=='_ : ∀ {A : Set} → A → A → Set
-- -- -- -- -- --   instance C== : ∀ {A B} → Congruity (_==_ {A}) (λ (f : A → B) {x y} _ → f x == f y)
-- -- -- -- -- --   instance C==' : ∀ {A B} → Congruity (_==_ {A}) (λ (f : A → B) {x y} _ → f x ==' f y)

-- -- -- -- -- -- testC : ∀ {A B} → (f : A → B) → ∀ {x y} → x == y → f x == f y
-- -- -- -- -- -- testC = congruity

-- -- -- -- -- -- record IsCongruity'
-- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔮₁} (𝔒₁-setoid : IsSetoid 𝔒₁ 𝔮₁)
-- -- -- -- -- --   {𝔬₂} {𝔒₂ : Ø 𝔬₂} {𝔮₂} (𝔒₂-setoid : IsSetoid 𝔒₂ 𝔮₂)
-- -- -- -- -- --   : Ø 𝔬₁ ∙̂ 𝔮₁ ∙̂ 𝔬₂ ∙̂ 𝔮₂ where
-- -- -- -- -- --   instance _ = 𝔒₁-setoid
-- -- -- -- -- --   instance _ = 𝔒₂-setoid
-- -- -- -- -- --   open IsSetoid ⦃ … ⦄ using (_≋_)
-- -- -- -- -- --   field
-- -- -- -- -- --     congruity' : (f : 𝔒₁ → 𝔒₂) → ∀ {x y} → x ≋ y → f x ≋ f y

-- -- -- -- -- -- open IsCongruity' ⦃ … ⦄
-- -- -- -- -- -- {-
-- -- -- -- -- -- module _ where

-- -- -- -- -- --   open IsSetoid ⦃ … ⦄
-- -- -- -- -- --   test-congruity' : ∀
-- -- -- -- -- --     {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔮₁} ⦃ 𝔒₁-setoid : IsSetoid 𝔒₁ 𝔮₁ ⦄
-- -- -- -- -- --     {𝔬₂} {𝔒₂ : Ø 𝔬₂} {𝔮₂} ⦃ 𝔒₂-setoid : IsSetoid 𝔒₂ 𝔮₂ ⦄
-- -- -- -- -- --     ⦃ _ : IsCongruity' 𝔒₁-setoid 𝔒₂-setoid ⦄
-- -- -- -- -- --     → (f : 𝔒₁ → 𝔒₂) → ∀ {x y} → x ≋ y → f x ≋ f y
-- -- -- -- -- --   test-congruity' f e = {!congruity' f e!}
-- -- -- -- -- -- -}
-- -- -- -- -- -- record IsFunctor
-- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁}
-- -- -- -- -- --   {𝔪₁} {𝔐₁ : 𝔒₁ → 𝔒₁ → Ø 𝔪₁}
-- -- -- -- -- --   {𝔮₁} {𝔐₁-setoid : ∀ {x y} → IsSetoid (𝔐₁ x y) 𝔮₁}
-- -- -- -- -- --   {semigroupoid₁ : IsSemigroupoid 𝔐₁ 𝔐₁-setoid}
-- -- -- -- -- --   {𝔬₂} {𝔒₂ : Ø 𝔬₂}
-- -- -- -- -- --   {𝔪₂} {𝔐₂ : 𝔒₂ → 𝔒₂ → Ø 𝔪₂}
-- -- -- -- -- --   {𝔮₂} {𝔐₂-setoid : ∀ {x y} → IsSetoid (𝔐₂ x y) 𝔮₂}
-- -- -- -- -- --   {semigroupoid₂ : IsSemigroupoid 𝔐₂ 𝔐₂-setoid}
-- -- -- -- -- --   (semifunctor : IsSemifunctor semigroupoid₁ semigroupoid₂)
-- -- -- -- -- --   (category₁ : IsCategory semigroupoid₁)
-- -- -- -- -- --   (category₂ : IsCategory semigroupoid₂)
-- -- -- -- -- --   : Ø 𝔬₁ ∙̂ 𝔪₁ ∙̂ 𝔮₁ ∙̂ 𝔬₂ ∙̂ 𝔪₂ ∙̂ 𝔮₂
-- -- -- -- -- --   where
-- -- -- -- -- --   instance _ = λ {x y} → 𝔐₂-setoid {x} {y}
-- -- -- -- -- --   open IsSetoid ⦃ … ⦄ using (_≋_)
-- -- -- -- -- --   open IsSemifunctor semifunctor using (𝔣; μ)
-- -- -- -- -- --   module ⒈ = IsCategory category₁
-- -- -- -- -- --   module ⒉ = IsCategory category₂
-- -- -- -- -- --   field
-- -- -- -- -- --     𝔣-identity : ∀ {x : 𝔒₁} → 𝔣 (⒈.ε {x = x}) ≋ (⒉.ε {x = μ x})





-- -- open import Oscar.Data
-- -- postulate P : Set
-- -- open Substitunction P
-- -- postulate
-- --   instance TransitivitySubstitunction : Transitivity Substitunction
-- --   Substitist : ¶ → ¶ → Set
-- --   instance SMap : Map Substitist Substitunction

-- -- test : Substitist 3 4 → Substitunction 3 4
-- -- test σ x = map σ $ x


-- -- --     ⦃ ⌶Equivalence ⦄ : ∀ {x y} → Equivalence (_≋_ {x} {y})
-- -- --     -- C : ∀ {x y} → B x y → B x y → Ø c
-- -- --     --⦃ ⌶IsEq ⦄ : ∀ {x y} → IsEq (B x y) c
-- -- --     ⦃ ⌶Transitivity ⦄ : Transitivity B
-- -- --     ⦃ ⌶Associativity ⦄ : Associativity B (λ {w x} f {y} g {z} h → (h ◆ g) ◆ f ≋ h ◆ g ◆ f)




-- -- -- -- open import Oscar.R
-- -- -- -- open import Oscar.Data


-- -- -- -- open import Oscar.Prelude renaming (_∘_ to _∘′_)
-- -- -- -- open import Oscar.R
-- -- -- -- open import Oscar.Data

-- -- -- -- unhide : ∀ {a} {A : Set a} {b} {B : A → Set b} → ({x : A} → B x) → (x : A) → B x
-- -- -- -- unhide f x = f {x}

-- -- -- -- infixr 9 ∙-syntax
-- -- -- -- ∙-syntax : ∀
-- -- -- --   {𝔞} {A : Ø 𝔞}
-- -- -- --   {𝔟} {B : A → Ø 𝔟}
-- -- -- --   {𝔠} {C : ∀ a → B a → Ø 𝔠} →
-- -- -- --   ⦃ _ : 𝓡₃,₁ A B C ⦄
-- -- -- --   → ∀ (f : A)
-- -- -- --       (g : B f)
-- -- -- --     → C f g
-- -- -- -- ∙-syntax f g = 𝓻₃,₁,₀ f g

-- -- -- -- syntax ∙-syntax f g = g ∙ f

-- -- -- -- infixr 9 ∘-syntax
-- -- -- -- ∘-syntax : ∀
-- -- -- --   {𝔦} {I : Ø 𝔦}
-- -- -- --   {𝔞} {A : Ø 𝔞}
-- -- -- --   {𝔟} {B : A → I → Ø 𝔟}
-- -- -- --   {𝔠} {C : ∀ a → (∀ i → B a i) → Ø 𝔠} →
-- -- -- --   ⦃ _ : 𝓡₃,₁ A (λ f → (i : I) → B f i) (λ f g → C f g) ⦄
-- -- -- --   → ∀ (f : A)
-- -- -- --       (g : {i : I} → B f i)
-- -- -- --     → C f (λ x → g {x})
-- -- -- -- ∘-syntax f g = 𝓻₃,₁,₀ f (λ x → g {x})

-- -- -- -- syntax ∘-syntax f g = g ∘ f

-- -- -- -- {-
-- -- -- -- instance

-- -- -- --   FunctionComposition : ∀
-- -- -- --     {𝔞} {A : Ø 𝔞}
-- -- -- --     {𝔟} {B : A → Ø 𝔟}
-- -- -- --     {𝔠} {C : ∀ {a} → B a → Ø 𝔠}
-- -- -- --     → 𝓡₃,₁
-- -- -- --       ((a : A) → B a)
-- -- -- --       (λ _ → (a : A) → (b : B a) → C b)
-- -- -- --       (λ f _ → (a : A) → C (f a))
-- -- -- --   𝓡₃,₁.𝓻₃,₁,₀ FunctionComposition f g x = g x (f x)
-- -- -- -- -}

-- -- -- -- open Substitunction

-- -- -- -- instance

-- -- -- --   SubstitunctionComposition : ∀ {𝔭} {𝔓 : Ø 𝔭} {l m n} →
-- -- -- --     𝓡₃,₁
-- -- -- --       (Substitunction 𝔓 l m)
-- -- -- --       (λ _ → Substitunction 𝔓 m n)
-- -- -- --       (λ _ _ → Substitunction 𝔓 l n)
-- -- -- --   𝓡₃,₁.𝓻₃,₁,₀ SubstitunctionComposition f g = {!!}

-- -- -- -- postulate Substitist : ¶ → ¶ → Set

-- -- -- -- instance

-- -- -- --   SubstitistComposition : ∀ {l m n} →
-- -- -- --     𝓡₃,₁
-- -- -- --       (Substitist l m)
-- -- -- --       (λ _ → Substitist m n)
-- -- -- --       (λ _ _ → Substitist l n)
-- -- -- --   𝓡₃,₁.𝓻₃,₁,₀ SubstitistComposition f g = {!!}

-- -- -- -- test-fc : ∀ {a b c}
-- -- -- --          {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- -- -- --          (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- -- -- --          ((x : A) → C (f x))
-- -- -- -- test-fc g f = {!!}
-- -- -- -- -- g ∘ f

-- -- -- -- test-substitunction : ∀ {P : Set} {l m} → Substitunction P l m → ∀ {n} → Substitunction P m n → Substitunction P l n
-- -- -- -- test-substitunction f g = g ∙ f

-- -- -- -- test-substitist : ∀ {l m} → Substitist l m → ∀ {n} → Substitist m n → Substitist l n
-- -- -- -- test-substitist f g = g ∙ f

-- -- -- -- test-substitist-associativity : ∀
-- -- -- --   {k l} (f : Substitist k l) {m} (g : Substitist l m) {n} (h : Substitist m n)
-- -- -- --   → Proposequality⟦ Substitist _ _ ⟧ ((h ∙ g) ∙ f) (h ∙ g ∙ f)
-- -- -- -- test-substitist-associativity = {!!}

-- -- -- -- postulate
-- -- -- --   A B C D : Set
-- -- -- --   f : A → B
-- -- -- --   g : B → C
-- -- -- --   h : C → D

-- -- -- -- foo : A → D
-- -- -- -- foo = {!!}
-- -- -- -- -- h ∘ g ∘ f

-- -- -- -- postulate
-- -- -- --   K L M N : ¶
-- -- -- --   f' : Substitunction A K L
-- -- -- --   g' : Substitunction A L M
-- -- -- --   h' : Substitunction A M N

-- -- -- -- bar : Substitunction A K N
-- -- -- -- bar = h' ∙ g' ∙ f'

-- -- -- -- postulate
-- -- -- --   f'' : Substitist K L
-- -- -- --   g'' : Substitist L M
-- -- -- --   h'' : Substitist M N

-- -- -- -- qux : Substitist K N
-- -- -- -- qux = h'' ∙ g'' ∙ f''

-- -- -- -- foobar : {!!}
-- -- -- -- foobar = {!h'' ∙ g'' ∙ f'' ≡ h'' ∙ g'' ∙ f''!}

-- -- -- -- --record Compositional (A : Ø₀) (M : A → A → Ø₀) (l m n : A) : Ø₀ where
-- -- -- -- --  infixr 9 _◆_
-- -- -- -- --  field
-- -- -- -- --    _◆_ : (g : M m n) (f : M l m) → M l n


-- -- -- -- module _ {𝔬₀} (O : Ø 𝔬₀) where
-- -- -- --   module _ {𝔬₁} (M : O → O → Ø 𝔬₁) where
-- -- -- -- --    module _ {𝔬₂} (𝔒₂ : ∀ ⓪ → 𝔒₁ ⓪ → Ø 𝔬₂) where
-- -- -- --       record 𝓒 ℓ : Ø 𝔬₀ ∙̂ 𝔬₁ {-∙̂ 𝔬₂-} ∙̂ ↑̂ ℓ where
-- -- -- --         infixr 9 _◆_
-- -- -- --         field _◆_ : ∀ {y z} → M y z → ∀ {x} → M x y → M x z
-- -- -- --         --field _≋_ : ∀ {⓪ ⑴} → (_ _ : 𝔒₂ ⓪ ⑴) → Ø ℓ
-- -- -- --         field _≋_ : ∀ {⓪ ⑴} → (_ _ : M ⓪ ⑴) → Ø ℓ
-- -- -- --         field associativity : ∀
-- -- -- --                 {k l} (f : M k l) {m} (g : M l m) {n} (h : M m n)
-- -- -- --                 → ((h ◆ g) ◆ f) ≋ (h ◆ g ◆ f)

-- -- -- -- open 𝓒 ⦃ … ⦄

-- -- -- -- postulate
-- -- -- --   instance SubstitunctionComposition' : 𝓒 ¶ (Substitunction A) ∅̂


-- -- -- -- instance
-- -- -- --   SubstitistComposition' : -- ∀ {l m n} →
-- -- -- --     𝓒 ¶ Substitist ∅̂
-- -- -- -- {-
-- -- -- --       (Substitist l m)
-- -- -- --       (λ _ → Substitist m n)
-- -- -- --       (λ _ _ → Substitist l n)
-- -- -- --       ∅̂
-- -- -- -- -}
-- -- -- --   𝓒._◆_ SubstitistComposition' f g = {!!}
-- -- -- --   𝓒._≋_ SubstitistComposition' f g = {!!}
-- -- -- --   𝓒.associativity SubstitistComposition' f g h = {!!}

-- -- -- -- test-substitist-associativity' : ∀
-- -- -- --   {k l} (f : Substitist k l) {m} (g : Substitist l m) {n} (h : Substitist m n)
-- -- -- --   → ((h ◆ g) ◆ f) ≋ (h ◆ g ◆ f)
-- -- -- -- test-substitist-associativity' = associativity

-- -- -- -- foobar'' = ((h' ◆ g') ◆ f') ≡ (h' ◆ g' ◆ f')

-- -- -- -- record SemigroupoidLaws
-- -- -- --   (Obj : Set)
-- -- -- --   (Hom : Obj → Obj → Set)
-- -- -- --   (_◆_ : ∀ {y z} → Hom y z → ∀ {x} → Hom x y → Hom x z)
-- -- -- --   (_≋_ : ∀ {x y} → Hom x y → Hom x y → Set)
-- -- -- --   : Set
-- -- -- --   where
-- -- -- --   field
-- -- -- --     assoc : ∀ {k l} (f : Hom k l) {m} (g : Hom l m) {n} (h : Hom m n)
-- -- -- --             → ((h ◆ g) ◆ f) ≋ (h ◆ (g ◆ f))

-- -- -- -- open SemigroupoidLaws ⦃ … ⦄

-- -- -- -- postulate
-- -- -- --   eqTunction : ∀ {x y} → Substitunction A x y → Substitunction A x y → Set
-- -- -- --   instance SemigroupoidLawsSubstitunction : SemigroupoidLaws ¶ (Substitunction A) _◆_ _≡_
-- -- -- --   instance SemigroupoidLawsSubstitunction' : SemigroupoidLaws ¶ (Substitunction A) _◆_ eqTunction
-- -- -- --   instance SemigroupoidLawsSubstitist : SemigroupoidLaws ¶ Substitist _◆_ _≡_

-- -- -- -- test-assoc1 : ∀
-- -- -- --   {k l} (f : Substitist k l) {m} (g : Substitist l m) {n} (h : Substitist m n)
-- -- -- --   → ((h ◆ g) ◆ f) ≡ (h ◆ g ◆ f)
-- -- -- -- test-assoc1 = assoc ⦃ SemigroupoidLawsSubstitist ⦄

-- -- -- -- record AssocClass
-- -- -- --   {Obj : Set}
-- -- -- --   {𝔐 : Obj → Obj → Set}
-- -- -- --   (assocRelation : ∀ {w x} → 𝔐 w x → ∀ {y} → 𝔐 x y → ∀ {z} → 𝔐 y z → Set)
-- -- -- --   : Set
-- -- -- --   where
-- -- -- --   field
-- -- -- --     assocC : ∀ {w x} (f : 𝔐 w x) {y} (g : 𝔐 x y) {z} (h : 𝔐 y z) → assocRelation f g h

-- -- -- -- open AssocClass ⦃ … ⦄

-- -- -- -- postulate
-- -- -- --   _≋S_ : ∀ {x y} → Substitist x y → Substitist x y → Set

-- -- -- -- module _
-- -- -- -- --  {Obj : Set}
-- -- -- -- --  {𝔐 : Obj → Obj → Set}
-- -- -- -- --  {𝒯 : ∀ {y z} → 𝔐 y z → ∀ {x} → 𝔐 x y → 𝔐 x z}
-- -- -- -- --  {𝔔 : ∀ {x y} → 𝔐 x y → 𝔐 x y → Set}
-- -- -- --   where

-- -- -- --   instance
-- -- -- --     AssocSubstitist : AssocClass {𝔐 = Substitist} (λ f g h → (h ◆ g ◆ f) ≡ ((h ◆ g) ◆ f))
-- -- -- --     AssocSubstitist = {!!}

-- -- -- --   instance
-- -- -- --     AssocSubstitist' : AssocClass {𝔐 = Substitist} (λ f g h → (h ◆ g ◆ f) ≋S ((h ◆ g) ◆ f))
-- -- -- --     AssocSubstitist' = {!!}

-- -- -- -- test-assocs' : ∀
-- -- -- --   {k l} (f : Substitist k l) {m} (g : Substitist l m) {n} (h : Substitist m n)
-- -- -- --   → (h ◆ g ◆ f) ≡ ((h ◆ g) ◆ f)
-- -- -- -- test-assocs' = assocC

-- -- -- -- test-assocs'' : ∀
-- -- -- --   {k l} (f : Substitist k l) {m} (g : Substitist l m) {n} (h : Substitist m n)
-- -- -- --   → (h ◆ g ◆ f) ≋S ((h ◆ g) ◆ f)
-- -- -- -- test-assocs'' = assocC

-- -- -- -- record ExtensClass
-- -- -- --   {Obj : Set}
-- -- -- --   {𝔐 : Obj → Obj → Set}
-- -- -- --   (extensRelation : ∀ {x y} → 𝔐 x y → 𝔐 x y → ∀ {z} → 𝔐 y z → 𝔐 y z → Set)
-- -- -- --   : Set
-- -- -- --   where
-- -- -- --   field
-- -- -- --     extension : ∀ {x y} (f₁ f₂ : 𝔐 x y) {z} (g₁ g₂ : 𝔐 y z) → extensRelation f₁ f₂ g₁ g₂

-- -- -- -- open ExtensClass ⦃ … ⦄


-- -- -- -- module _
-- -- -- --   (Obj : Set)
-- -- -- --   (𝔐 : Obj → Obj → Set)
-- -- -- --   (𝒯 : ∀ {y z} → 𝔐 y z → ∀ {x} → 𝔐 x y → 𝔐 x z)
-- -- -- --   (𝔔 : ∀ {x y} → 𝔐 x y → 𝔐 x y → Set)
-- -- -- --   where
-- -- -- --   Associative = 𝓡₈,₁ _ _ 𝔐 _ (λ _ x _ → 𝔐 x) _ (λ _ _ _ y _ → 𝔐 y) (λ _ _ f _ g _ h → 𝔔 (𝒯 h (𝒯 g f)) (𝒯 (𝒯 h g) f))
-- -- -- --   𝓐ssociative = ∀ {w x} (f : 𝔐 w x) {y} (g : 𝔐 x y) {z} (h : 𝔐 y z) → 𝔔 (𝒯 h (𝒯 g f)) (𝒯 (𝒯 h g) f)

-- -- -- -- postulate
-- -- -- --   instance AssociativeSubstitunction : Associative ¶ (Substitunction A) _◆_ _≡_
-- -- -- --   instance AssociativeSubstitist : Associative ¶ Substitist _◆_ _≡_

-- -- -- -- test-assoc2 : ∀
-- -- -- --   {k l} (f : Substitist k l) {m} (g : Substitist l m) {n} (h : Substitist m n)
-- -- -- --   → (h ◆ g ◆ f) ≡ ((h ◆ g) ◆ f)
-- -- -- -- test-assoc2 {k} {l} f {m} g {n} h = 𝓻₈,₁,₀ _ _ f _ g _ h





-- -- -- -- {-
-- -- -- -- g : M A (λ a → (b : B a) → C b)
-- -- -- -- f : M A (λ a → B a)
-- -- -- -- ∴ : M A (λ a → C (f a))
-- -- -- -- -}

-- -- -- -- -- -- module _ {𝔬₀} (𝔒₀ : Ø 𝔬₀) where
-- -- -- -- -- --   record 𝓘dentity : Ø 𝔬₀ where
-- -- -- -- -- --     field ID : 𝑹₀ 𝔒₀

-- -- -- -- -- --   module _ {𝔬₁} (𝔒₁ : 𝔒₀ → Ø 𝔬₁) where
-- -- -- -- -- --     module _ {𝔬₂} (𝔒₂ : ∀ ⓪ → 𝔒₁ ⓪ → Ø 𝔬₂) where
-- -- -- -- -- --       record 𝓒omposition9r : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ where
-- -- -- -- -- --         infixr 9 _∙_
-- -- -- -- -- --         field _∙_ : ∀ (x₀ : 𝔒₀) (x₁ : 𝔒₁ x₀) → 𝔒₂ x₀ x₁

-- -- -- -- -- -- record 𝓒omposition9r'
-- -- -- -- -- --   {𝔞} (A : Ø 𝔞)
-- -- -- -- -- --   {𝔟₀} (B₀ : A → Ø 𝔟₀)
-- -- -- -- -- --   {𝔟₁} (B₁ : A → Ø 𝔟₁)
-- -- -- -- -- --   {𝔠} (C : ∀ {a} → B₀ a → B₁ a → Ø 𝔠)
-- -- -- -- -- --   : Ø 𝔞 ∙̂ 𝔟₀ ∙̂ 𝔟₁ ∙̂ 𝔠 where
-- -- -- -- -- --   field composer9r' : ∀
-- -- -- -- -- --                 (a : A)
-- -- -- -- -- --                 (b₀ : (a : A) → B₀ a)
-- -- -- -- -- --                 (b₁ : (a : A) → B₁ a)
-- -- -- -- -- --                 → C (b₀ a) (b₁ a)

-- -- -- -- -- -- record R4
-- -- -- -- -- --   {𝔞} (A : Ø 𝔞)
-- -- -- -- -- --   {𝔟} (B : A → Ø 𝔟)
-- -- -- -- -- --   {𝔠} (C : ∀ {a} → B a → Ø 𝔠)
-- -- -- -- -- --   {𝔡} (D : ∀ {a} {b : B a} → C b → Ø 𝔡)
-- -- -- -- -- --   : Ø 𝔞 ∙̂ 𝔟 ∙̂ 𝔠 ∙̂ 𝔡 where
-- -- -- -- -- --   field r4 : ∀ (a : A)
-- -- -- -- -- --                (b : B a)
-- -- -- -- -- --                (c : C b)
-- -- -- -- -- --                → D c

-- -- -- -- -- -- record R3'
-- -- -- -- -- --   {𝔞} (A : Ø 𝔞)
-- -- -- -- -- --   {𝔟} (B : A → Ø 𝔟)
-- -- -- -- -- --   {𝔠} (C : ∀ {a} → B a → Ø 𝔠)
-- -- -- -- -- --   : Ø 𝔞 ∙̂ 𝔟 ∙̂ 𝔠 where
-- -- -- -- -- --   field r3' : ∀ (a : A)
-- -- -- -- -- --                 (b : (a : A) → B a)
-- -- -- -- -- --                 → C (b a)

-- -- -- -- -- -- instance

-- -- -- -- -- --   R3'Composition : ∀
-- -- -- -- -- --     {a} {A : Ø a} {b} {B : A → Ø b} {c} {C : {x : A} → B x → Ø c} →
-- -- -- -- -- --     R3'
-- -- -- -- -- --       A
-- -- -- -- -- --       (λ x → B x)
-- -- -- -- -- --       (λ {x} f → (g : ∀ {x} (y : B x) → C y) → C f)
-- -- -- -- -- --   R3'.r3' R3'Composition x f g = g (f x)

-- -- -- -- -- -- open R3' ⦃ … ⦄

-- -- -- -- -- -- infixr 9 _r∙_
-- -- -- -- -- -- _r∙_ : ∀
-- -- -- -- -- --   {𝔞} {A : Ø 𝔞}
-- -- -- -- -- --   {𝔟} {B : A → Ø 𝔟}
-- -- -- -- -- --   {𝔠} {C : ∀ {a} → B a → Ø 𝔠}
-- -- -- -- -- --   ⦃ _ : R3' A B C ⦄
-- -- -- -- -- --   → ∀ (c : {a : A} → (b : B a) → C b)
-- -- -- -- -- --       (b : (a : A) → B a)
-- -- -- -- -- --       (a : A)
-- -- -- -- -- --       → C (b a)
-- -- -- -- -- -- (c r∙ b) a = r3' a b -- c (b a)

-- -- -- -- -- -- test-r3' : ∀ {a b c}
-- -- -- -- -- --          {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- -- -- -- -- --          (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- -- -- -- -- --          ((x : A) → C (f x))
-- -- -- -- -- -- test-r3' g f x = {!!} -- (g r∙ f) x

-- -- -- -- -- -- record R4'
-- -- -- -- -- --   {𝔞} (A : Ø 𝔞)
-- -- -- -- -- --   {𝔟} (B : A → Ø 𝔟)
-- -- -- -- -- --   {𝔠} (C : ∀ {a} → B a → Ø 𝔠)
-- -- -- -- -- --   {𝔡} (D : ∀ {a} {b : B a} → C b → Ø 𝔡)
-- -- -- -- -- --   : Ø 𝔞 ∙̂ 𝔟 ∙̂ 𝔠 ∙̂ 𝔡 where
-- -- -- -- -- --   field r4' : ∀ (a : A)
-- -- -- -- -- --                 (b : B a)
-- -- -- -- -- --                 (c : B a → C b)
-- -- -- -- -- --                 → D (c b)

-- -- -- -- -- -- record S4
-- -- -- -- -- --   {𝔞} (A : Ø 𝔞)
-- -- -- -- -- --   {𝔟} (B : A → Ø 𝔟)
-- -- -- -- -- --   {𝔠} (C : ∀ {a} → B a → Ø 𝔠)
-- -- -- -- -- --   {𝔡} (D : ∀ {a} {b : B a} → C b → Ø 𝔡)
-- -- -- -- -- --   : Ø 𝔞 ∙̂ 𝔟 ∙̂ 𝔠 ∙̂ 𝔡 where
-- -- -- -- -- --   field s4 : ∀ (a : A)
-- -- -- -- -- --                (b : (a : A) → B a)
-- -- -- -- -- --                (c : (a : A) → (b : B a) → C b)
-- -- -- -- -- --                → D (c a (b a))

-- -- -- -- -- -- open S4 ⦃ … ⦄


-- -- -- -- -- -- record S4''
-- -- -- -- -- --   {𝔞} (A : Ø 𝔞)
-- -- -- -- -- --   {𝔟} (B : A → Ø 𝔟)
-- -- -- -- -- --   {𝔠} (C : ∀ {a} → B a → Ø 𝔠)
-- -- -- -- -- --   {𝔡} (D : ∀ {a} {b : B a} → C b → Ø 𝔡)
-- -- -- -- -- --   : Ø 𝔞 ∙̂ 𝔟 ∙̂ 𝔠 ∙̂ 𝔡 where
-- -- -- -- -- --   field s4'' : ∀ (a : A)
-- -- -- -- -- --                  (b : (a : A) → B a)
-- -- -- -- -- --                  (c : (a : A) → C (b a))
-- -- -- -- -- --                  → D (c a)

-- -- -- -- -- -- open S4'' ⦃ … ⦄

-- -- -- -- -- -- test-s4'' : ∀
-- -- -- -- -- --   {𝔞} (A : Ø 𝔞)
-- -- -- -- -- --   {𝔟} (B : A → Ø 𝔟)
-- -- -- -- -- --   {𝔠} (C : ∀ {a} → B a → Ø 𝔠)
-- -- -- -- -- --   {𝔡} (D : ∀ {a} {b : B a} → C b → Ø 𝔡)
-- -- -- -- -- --   ⦃ _ : S4'' A B C D ⦄
-- -- -- -- -- --   → ∀ (a : A)
-- -- -- -- -- --       (b : (a : A) → B a)
-- -- -- -- -- --       (c : (a : A) → C (b a))
-- -- -- -- -- --       → D (c a)
-- -- -- -- -- -- test-s4'' A B C D a b c = s4'' a b c

-- -- -- -- -- -- open R4 ⦃ … ⦄

-- -- -- -- -- -- test-r4s4 : ∀
-- -- -- -- -- --     {𝔞} {A : Ø 𝔞}
-- -- -- -- -- --     {𝔟} {B : A → Ø 𝔟}
-- -- -- -- -- --     {𝔠} {C : ∀ {a} → B a → Ø 𝔠}
-- -- -- -- -- --     ⦃ _ : R4
-- -- -- -- -- --             A
-- -- -- -- -- --             (λ _ → (a : A) → B a)
-- -- -- -- -- --             (λ {_} _ → {a : A} → (b : B a) → C b)
-- -- -- -- -- --             (λ {a} {b} c → C (b a)) ⦄
-- -- -- -- -- --     → (a : A)
-- -- -- -- -- --       (b : (a : A) → B a)
-- -- -- -- -- --       (c : {a : A} → (b : B a) → C b)
-- -- -- -- -- --       → C (b a)
-- -- -- -- -- -- test-r4s4 ⦃ i ⦄ a b c = r4 a b (λ {w} → c {w})
-- -- -- -- -- -- {-
-- -- -- -- -- -- instance
-- -- -- -- -- --   R4S4 : ∀
-- -- -- -- -- --     {𝔞} {A : Ø 𝔞}
-- -- -- -- -- --     {𝔟} {B : A → Ø 𝔟}
-- -- -- -- -- --     {𝔠} {C : ∀ {a} → B a → Ø 𝔠}
-- -- -- -- -- --     → R4
-- -- -- -- -- --         A
-- -- -- -- -- --         (λ _ → (a : A) → B a)
-- -- -- -- -- --         (λ {_} _ → {a : A} → (b : B a) → C b)
-- -- -- -- -- --         (λ {a} {b} c → C (b a))
-- -- -- -- -- --   R4.r4 R4S4 a b c = c {a} (b a)
-- -- -- -- -- -- -}
-- -- -- -- -- -- instance
-- -- -- -- -- --   R4S4' : ∀
-- -- -- -- -- --     {𝔞} {A : Ø 𝔞}
-- -- -- -- -- --     {𝔟} {B : A → Ø 𝔟}
-- -- -- -- -- --     {𝔠} {C : ∀ {a} → B a → Ø 𝔠}
-- -- -- -- -- --     → R4
-- -- -- -- -- --         A
-- -- -- -- -- --         (λ _ → (a : A) → B a)
-- -- -- -- -- --         (λ {_} _ → (a : A) → (b : B a) → C b)
-- -- -- -- -- --         (λ {a} {b} c → C (b a))
-- -- -- -- -- --   R4.r4 R4S4' a b c = c a (b a)

-- -- -- -- -- -- test-r4s4' : ∀
-- -- -- -- -- --     {𝔞} {A : Ø 𝔞}
-- -- -- -- -- --     {𝔟} {B : A → Ø 𝔟}
-- -- -- -- -- --     {𝔠} {C : ∀ {a} → B a → Ø 𝔠}
-- -- -- -- -- --     → (a : A)
-- -- -- -- -- --       (b : (a : A) → B a)
-- -- -- -- -- --       (c : {a : A} → (b : B a) → C b)
-- -- -- -- -- --       → C (b a)
-- -- -- -- -- -- test-r4s4' a b c = {!!} -- test-r4s4 a b c
-- -- -- -- -- -- -- r4 a b (λ w → c {w})

-- -- -- -- -- -- unhide : ∀ {a} {A : Set a} {b} {B : A → Set b} → ({x : A} → B x) → (x : A) → B x
-- -- -- -- -- -- unhide x x₁ = x {x₁}


-- -- -- -- -- -- test-r42 : ∀ {a b c}
-- -- -- -- -- --          {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- -- -- -- -- --          (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- -- -- -- -- --          ((x : A) → C (f x))
-- -- -- -- -- -- test-r42 g f x = r4 x f (unhide g)
-- -- -- -- -- -- -- s4 x f (λ a b → g b)
-- -- -- -- -- -- --test-s4 g f x = (g s∙ f) x

-- -- -- -- -- -- copy-r4s4 : ∀
-- -- -- -- -- --   {𝔞} {A : Ø 𝔞}
-- -- -- -- -- --   {𝔟} {B : A → Ø 𝔟}
-- -- -- -- -- --   {𝔠} {C : ∀ {a} → B a → Ø 𝔠}
-- -- -- -- -- --   {𝔡} {D : ∀ {a} {b : B a} → C b → Ø 𝔡}
-- -- -- -- -- --   ⦃ _ : R4 A B C D ⦄
-- -- -- -- -- --   → ∀ (a : A)
-- -- -- -- -- --       (b : B a)
-- -- -- -- -- --       (c : C b)
-- -- -- -- -- --       → D c
-- -- -- -- -- -- copy-r4s4 a b c = r4 a b c

-- -- -- -- -- -- adapt-r4 : ∀
-- -- -- -- -- --   {𝔞} {A : Ø 𝔞}
-- -- -- -- -- --   {𝔟} {B : A → Ø 𝔟}
-- -- -- -- -- --   {𝔠} {C : A → ∀ {a} → B a → Ø 𝔠}
-- -- -- -- -- --   {𝔡} {D : ∀ {a} {b : B a} → C a b → Ø 𝔡}
-- -- -- -- -- --   ⦃ _ : R4 A B (λ {x} y → (x' : A) → C x' y) (λ {x} {y} z → D (z x)) ⦄
-- -- -- -- -- --   → ∀ (a : A)
-- -- -- -- -- --       (b : B a)
-- -- -- -- -- --       (c : {x : A} → C x b)
-- -- -- -- -- --       → D c
-- -- -- -- -- -- adapt-r4 a b c = r4 a b (unhide c)


-- -- -- -- -- -- test-r4 : ∀ {a b c}
-- -- -- -- -- --          {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- -- -- -- -- --          (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- -- -- -- -- --          ((x : A) → C (f x))
-- -- -- -- -- -- test-r4 g f x = adapt-r4 x f g


-- -- -- -- -- -- infixr 9 _s∙_
-- -- -- -- -- -- _s∙_ : ∀
-- -- -- -- -- --   {𝔞} {A : Ø 𝔞}
-- -- -- -- -- --   {𝔟} {B : A → Ø 𝔟}
-- -- -- -- -- --   {𝔠} {C : ∀ {a} → B a → Ø 𝔠}
-- -- -- -- -- --   {𝔡} {D : ∀ {a} {b : B a} → C b → Ø 𝔡}
-- -- -- -- -- --   ⦃ _ : S4 A B C D ⦄
-- -- -- -- -- --   → ∀ (c : {a : A} → (b : B a) → C b)
-- -- -- -- -- --       (b : (a : A) → B a)
-- -- -- -- -- --       (a : A)
-- -- -- -- -- --       → D (c {a} (b a))
-- -- -- -- -- -- (c s∙ b) a = s4 a b (λ _ → c)
-- -- -- -- -- -- -- r4 a b (λ w → c {w})
-- -- -- -- -- --   --

-- -- -- -- -- -- instance

-- -- -- -- -- --   S4Composition : ∀
-- -- -- -- -- --     {a} {A : Ø a} {b} {B : A → Ø b} {c} {C : {x : A} → B x → Ø c} →
-- -- -- -- -- --     S4
-- -- -- -- -- --       A
-- -- -- -- -- --       (λ x → B x)
-- -- -- -- -- --       (λ {x} f → C f)
-- -- -- -- -- --       (λ {x} {f} g → C f)
-- -- -- -- -- --   S4.s4 S4Composition a₁ b₁ c₁ = c₁ a₁ (b₁ a₁)

-- -- -- -- -- -- test-s4 : ∀ {a b c}
-- -- -- -- -- --          {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- -- -- -- -- --          (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- -- -- -- -- --          ((x : A) → C (f x))
-- -- -- -- -- -- test-s4 g f x = s4 x f (λ a b → g b)
-- -- -- -- -- -- --test-s4 g f x = (g s∙ f) x

-- -- -- -- -- -- {-
-- -- -- -- -- -- _∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
-- -- -- -- -- --         (g : ∀ {x} (y : B x) → C x y) (f : ∀ x → B x) →
-- -- -- -- -- --         ∀ x → C x (f x)
-- -- -- -- -- -- (g ∘ f) x = g (f x)
-- -- -- -- -- -- -}

-- -- -- -- -- -- instance

-- -- -- -- -- --   FunctionComposition' : ∀
-- -- -- -- -- --     {a} {A : Ø a} {b} {B : A → Ø b} {c} {C : {x : A} → B x → Ø c} →
-- -- -- -- -- --     𝓒omposition9r'
-- -- -- -- -- --       A
-- -- -- -- -- --       (λ x → (y : B x) → C y)
-- -- -- -- -- --       (λ x → B x)
-- -- -- -- -- --       (λ {x} g f → C f)
-- -- -- -- -- --   𝓒omposition9r'.composer9r' FunctionComposition' x g f = g x (f x)

-- -- -- -- -- -- {-
-- -- -- -- -- -- record 𝓒omposition4
-- -- -- -- -- --   {𝔬₀} (𝔒₀ : Ø 𝔬₀)
-- -- -- -- -- --   {𝔬₁} (𝔒₁ : 𝔒₀ → Ø 𝔬₁)
-- -- -- -- -- --   {𝔬₂} (𝔒₂ : ∀ ⓪ → 𝔒₁ ⓪ → Ø 𝔬₂)
-- -- -- -- -- --   {𝔬₃} (𝔒₃ : ∀ ⓪ ⑴ → 𝔒₂ ⓪ ⑴ → Ø 𝔬₃)
-- -- -- -- -- --   : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ where
-- -- -- -- -- --   infixr 9 _∙''_
-- -- -- -- -- --   field
-- -- -- -- -- --     composition4 : ∀ ⓪ ⑴ ⑵ → 𝔒₃ ⓪ ⑴ ⑵

-- -- -- -- -- -- instance FunctionComposition4
-- -- -- -- -- -- -}

-- -- -- -- -- -- open 𝓘dentity ⦃ … ⦄
-- -- -- -- -- -- open 𝓒omposition9r ⦃ … ⦄
-- -- -- -- -- -- open 𝓒omposition9r' ⦃ … ⦄

-- -- -- -- -- -- composer' : ∀
-- -- -- -- -- --   {𝔬₀} {𝔒₀ : Ø 𝔬₀}
-- -- -- -- -- --   {𝔬₁} {𝔒₁ : 𝔒₀ → Ø 𝔬₁}
-- -- -- -- -- --   {𝔬₁'} {𝔒₁' : 𝔒₀ → Ø 𝔬₁'}
-- -- -- -- -- --   {𝔬₂} {𝔒₂ : ∀ {⓪} → 𝔒₁ ⓪ → 𝔒₁' ⓪ → Ø 𝔬₂}
-- -- -- -- -- --   ⦃ _ : 𝓒omposition9r' 𝔒₀ 𝔒₁ 𝔒₁' 𝔒₂ ⦄
-- -- -- -- -- --   → (g : {x : 𝔒₀} → 𝔒₁ x)
-- -- -- -- -- --                 (f : (x : 𝔒₀) → 𝔒₁' x)
-- -- -- -- -- --                 (x : 𝔒₀)
-- -- -- -- -- --                 → 𝔒₂ (g {x}) (f x)
-- -- -- -- -- -- composer' g f x = composer9r' x (λ x → g {x}) f

-- -- -- -- -- -- test-composer : ∀ {a b c}
-- -- -- -- -- --          {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- -- -- -- -- --          (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- -- -- -- -- --          ((x : A) → C (f x))
-- -- -- -- -- -- test-composer g f x = composer' g f x


-- -- -- -- -- -- instance
-- -- -- -- -- --   IdentityI : ∀ {A : Set} → 𝓘dentity ({x : A} → A)
-- -- -- -- -- --   𝓘dentity.ID IdentityI {x} = x

-- -- -- -- -- -- instance

-- -- -- -- -- --   FunctionComposition : ∀
-- -- -- -- -- --     {a} {A : Ø a} {b} {B : A → Ø b} {c} {C : {x : A} → B x → Ø c} →
-- -- -- -- -- --     𝓒omposition9r
-- -- -- -- -- --       ({x : A} (y : B x) → C y)
-- -- -- -- -- --       (λ g → (x : A) → B x)
-- -- -- -- -- --       (λ g f → (x : A) → C (f x))
-- -- -- -- -- --   𝓒omposition9r._∙_ FunctionComposition g f x = g (f x)

-- -- -- -- -- -- compos : ∀
-- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬}
-- -- -- -- -- --   {𝔤} {𝔊 : 𝔒 → Ø 𝔤}
-- -- -- -- -- --   {𝔣} {𝔉 : 𝔒 → Ø 𝔣}
-- -- -- -- -- --   {𝔤∙𝔣} {𝔊∙𝔉 : ∀ {o} → {-𝔊 o → -}𝔉 o → Ø 𝔤∙𝔣}
-- -- -- -- -- --   ⦃ _ : 𝓒omposition9r ({x : 𝔒} → 𝔊 x) (λ g → (x : 𝔒) → 𝔉 x) (λ g f → (x : 𝔒) → 𝔊∙𝔉 {-x-} {-(g {x}) -} (f x)) ⦄
-- -- -- -- -- --   → (g : ({x : 𝔒} → 𝔊 x))
-- -- -- -- -- --   → (f : (x : 𝔒) → 𝔉 x)
-- -- -- -- -- --   → (x : 𝔒) → 𝔊∙𝔉 {-x (g {x})-} (f x)
-- -- -- -- -- -- compos g f x = (λ {_} → g {_}) ∙ f $ x

-- -- -- -- -- -- infixr 9 _∘'_
-- -- -- -- -- -- _∘'_ = compos

-- -- -- -- -- -- instance

-- -- -- -- -- --   Function'Composition : ∀
-- -- -- -- -- --     {a} {A : Ø a} {b} {B : Ø b} {c} {C : Ø c} →
-- -- -- -- -- --     𝓒omposition9r
-- -- -- -- -- --       (B → C)
-- -- -- -- -- --       (λ g → A → B)
-- -- -- -- -- --       (λ g f → A → C)
-- -- -- -- -- --   𝓒omposition9r._∙_ Function'Composition g f x = g (f x)

-- -- -- -- -- -- -- {a} {A : Ø a} {b} {B : A → A → Ø b}
-- -- -- -- -- -- postulate
-- -- -- -- -- --   A : Set
-- -- -- -- -- --   B : A → A → Set

-- -- -- -- -- -- instance

-- -- -- -- -- --   TransitiveAB : ∀
-- -- -- -- -- --     {x y z : A} →
-- -- -- -- -- --     𝓒omposition9r
-- -- -- -- -- --       (B y z)
-- -- -- -- -- --       (λ g → B x y)
-- -- -- -- -- --       (λ g f → B x z)
-- -- -- -- -- --   𝓒omposition9r._∙_ TransitiveAB f g = {!!}

-- -- -- -- -- -- test-c : ∀ {a b c}
-- -- -- -- -- --          {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- -- -- -- -- --          (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- -- -- -- -- --          ((x : A) → C (f x))
-- -- -- -- -- -- --test-c g f x = _∙'_ g f x -- ({!g!} ∙ f) $ x
-- -- -- -- -- -- test-c {A = A} {B} {C} g f x = (composer' g f x) --  (λ {_} → g {_}) f) $ x
-- -- -- -- -- -- --test-c {A = A} {B} {C} g f x = (compos {𝔊∙𝔉 = λ {-o x₁-} x₂ → C x₂} g f $ x) --  (λ {_} → g {_}) f) $ x
-- -- -- -- -- -- -- test-c g f x = _∙_ (λ {_} → g {_}) f $ x -- ({!g!} ∙ f) $ x
-- -- -- -- -- -- -- _∙_ ⦃ FunctionComposition ⦄
-- -- -- -- -- -- --test-c g f x = ((λ {_} → g {_}) ∙ f) $ x

-- -- -- -- -- -- test-c' : ∀ {a b c}
-- -- -- -- -- --          {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- -- -- -- -- --          (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- -- -- -- -- --          ((x : A) → C (f x))
-- -- -- -- -- -- test-c' g f x = (g ∘ f) x

-- -- -- -- -- -- test-c2 : ∀ {x y z} → B y z → B x y → B x z
-- -- -- -- -- -- test-c2 g f = g ∙ f

-- -- -- -- -- -- test-c3 : ∀ {A B C : Set} (g : B → C) (f : A → B) → A → C
-- -- -- -- -- -- test-c3 g f = g ∙ f

-- -- -- -- -- -- test-c3' : ∀ {A B C : Set} (g : B → C) (f : A → B) → A → C
-- -- -- -- -- -- test-c3' g f = g ∘ f






-- -- -- -- -- -- -- comp! : ∀ {a b c}
-- -- -- -- -- -- --         {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- -- -- -- -- -- --         (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- -- -- -- -- -- --         ((x : A) → C (f x))
-- -- -- -- -- -- -- comp! {a} {b} {c} {A} {B} {C} g f x = 𝓻₄,₁,₀ x f (λ {_} → g {_})



-- -- -- -- -- -- -- module _
-- -- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂} {𝔮₁}
-- -- -- -- -- -- --     (𝔔₁ : ∀ x → 𝔒₂ x → Ø 𝔮₁)
-- -- -- -- -- -- --   {𝔬₃} {𝔒₃ : ∀ {x} → 𝔒₂ x → Ø 𝔬₃} {𝔮₂}
-- -- -- -- -- -- --     (𝔔₂ : ∀ {x} (y : 𝔒₂ x) → 𝔒₃ y → Ø 𝔮₂)
-- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- --     (𝔔₃ : (x : 𝔒₁) → ∀ {y : 𝔒₂ x} → 𝔒₃ y → Ø 𝔮₃)
-- -- -- -- -- -- --   where
-- -- -- -- -- -- --   Transitive! = 𝓡₆,₁ _ _ 𝔔₁ _ (λ _ y _ → 𝔔₂ y) (λ x _ _ z _ → 𝔔₃ x z)
-- -- -- -- -- -- --   𝓣ransitive! = ∀ {x} {y : 𝔒₂ x} → 𝔔₁ x y → ∀ {z : 𝔒₃ y} → 𝔔₂ y z → 𝔔₃ x z
-- -- -- -- -- -- --   𝓽ransitive! = ⦃ _ : Transitive! ⦄ → 𝓣ransitive!

-- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- instance

-- -- -- -- -- -- --   CT1 : ∀ {a b c} →
-- -- -- -- -- -- --     Transitive! {𝔒₁ = Ø a} {𝔒₂ = λ A → A → Ø b}
-- -- -- -- -- -- --       (λ A B → (x : A) → B x) {𝔒₃ = λ {A} B → {x : A} → B x → Ø c} -- (x : A) → B x
-- -- -- -- -- -- --       (λ {A} B C → {x : A} (y : B x) → C y )
-- -- -- -- -- -- --       (λ A {B} C → (x : A) → C {!!})
-- -- -- -- -- -- --   CT1 = {!!}
-- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- module _
-- -- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔬₂} {𝔒₂ : Ø 𝔬₂} {𝔮₁}
-- -- -- -- -- -- --     (𝔔₁ : 𝔒₁ → 𝔒₂ → Ø 𝔮₁)
-- -- -- -- -- -- --   {𝔬₃} {𝔒₃ : Ø 𝔬₃} {𝔮₂}
-- -- -- -- -- -- --     (𝔔₂ : 𝔒₂ → 𝔒₃ → Ø 𝔮₂)
-- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- --     (𝔔₃ : 𝔒₁ → 𝔒₃ → Ø 𝔮₃)
-- -- -- -- -- -- --   where
-- -- -- -- -- -- --   Transitive!' = Transitive! 𝔔₁ 𝔔₂ (λ x → 𝔔₃ x)
-- -- -- -- -- -- --   Transitive' = 𝓡₆,₁ _ _ 𝔔₁ _ (λ _ y _ → 𝔔₂ y) (λ x _ _ z _ → 𝔔₃ x z)
-- -- -- -- -- -- --   𝓣ransitive' = ∀ {x y} → 𝔔₁ x y → ∀ {z} → 𝔔₂ y z → 𝔔₃ x z
-- -- -- -- -- -- --   𝓽ransitive' = ⦃ _ : Transitive' ⦄ → 𝓣ransitive'

-- -- -- -- -- -- -- module _
-- -- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂} {𝔮₁}
-- -- -- -- -- -- --     (𝔔₁ : (x : 𝔒₁) → 𝔒₂ x → Ø 𝔮₁)
-- -- -- -- -- -- --   {𝔬₃} {𝔒₃ : ∀ {x} → 𝔒₂ x → Ø 𝔬₃} {𝔮₂}
-- -- -- -- -- -- --     (𝔔₂ : ∀ x (y : 𝔒₂ x) → 𝔒₃ y → Ø 𝔮₂)
-- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- --     (𝔔₃ : ∀ x (y : 𝔒₂ x) → 𝔒₃ y → Ø 𝔮₃)
-- -- -- -- -- -- --   where
-- -- -- -- -- -- --   Transitive'' = 𝓡₆,₁ _ _ 𝔔₁ _ (λ _ y _ → 𝔔₂ _ y) (λ x _ _ z _ → 𝔔₃ x _ z)
-- -- -- -- -- -- -- --  𝓣ransitive'' = ∀ {x y} → 𝔔₁ x y → ∀ {z} → 𝔔₂ y z → 𝔔₃ x z
-- -- -- -- -- -- -- --  𝓽ransitive'' = ⦃ _ : Transitive'' ⦄ → 𝓣ransitive''

-- -- -- -- -- -- -- instance Transitive''Function : ∀ {𝔬 𝔭 𝔮} →
-- -- -- -- -- -- --            Transitive''
-- -- -- -- -- -- --              {𝔒₁ = Ø 𝔬} {𝔒₂ = λ x → Ø 𝔭}
-- -- -- -- -- -- --                (λ x y → x → y)
-- -- -- -- -- -- --              {𝔒₃ = λ {x} y → Ø 𝔮}
-- -- -- -- -- -- --                (λ x y z → y → z)
-- -- -- -- -- -- --                (λ x y z → x → z)
-- -- -- -- -- -- -- 𝓡₆,₁.𝓻₆,₁,₀ Transitive''Function ⓪ ⑴ f ⑶ g x = {!!} -- g (f x)

-- -- -- -- -- -- -- module _ where
-- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- --   A : Set a
-- -- -- -- -- -- -- --   B : A → Set b
-- -- -- -- -- -- -- --   f : (x : A) → B x
-- -- -- -- -- -- -- --   C : {x : A} → B x → Set c
-- -- -- -- -- -- -- --   g : {x : A} (y : B x) → C y
-- -- -- -- -- -- -- --   Goal : (x : A) → C (f x)
-- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- CompFunction = {!!}

-- -- -- -- -- -- -- instance

-- -- -- -- -- -- --   CompFunction : ∀
-- -- -- -- -- -- --     {a b c} →
-- -- -- -- -- -- --     𝓡₆,₁
-- -- -- -- -- -- --       (Ø a)
-- -- -- -- -- -- --       (λ A → A → Ø b)
-- -- -- -- -- -- --       (λ A B → (x : A) → B x)
-- -- -- -- -- -- --       (λ A B f → {x : A} → B x → Ø c)
-- -- -- -- -- -- --       (λ A B f C → {x : A} (y : B x) → C y)
-- -- -- -- -- -- --       (λ A B f C g → (x : A) → C (f x))
-- -- -- -- -- -- --   𝓡₆,₁.𝓻₆,₁,₀ CompFunction A B f C g x = g (f x)

-- -- -- -- -- -- -- transitive : ∀
-- -- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- -- -- -- -- --   {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴             → 𝔒₂ ⓪ ⑴             → Ø 𝔬₃}
-- -- -- -- -- -- --   {𝔬₄} {𝔒₄ : ∀ ⓪ ⑴ ⑵           → 𝔒₃ ⓪ ⑴ ⑵           → Ø 𝔬₄}
-- -- -- -- -- -- --   {𝔬₅} {𝔒₅ : ∀ ⓪ ⑴ ⑵ ⑶         → 𝔒₄ ⓪ ⑴ ⑵ ⑶         → Ø 𝔬₅}
-- -- -- -- -- -- --   ⦃ _ : 𝓡₆,₁ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ 𝔒₄ 𝔒₅ ⦄
-- -- -- -- -- -- --   → ∀ {⓪ ⑴} ⑵ {⑶} ⑷ → 𝔒₅ ⓪ ⑴ ⑵ ⑶ ⑷
-- -- -- -- -- -- -- transitive ⑵ = 𝓻₆,₁,₀ _ _ ⑵ _

-- -- -- -- -- -- -- _∘'_ : ∀ {a b c}
-- -- -- -- -- -- --         {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- -- -- -- -- -- --         (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- -- -- -- -- -- --         ((x : A) → C (f x))
-- -- -- -- -- -- -- _∘'_ {a} {b} {c} {A} {B} {C} g f = 𝓻₆,₁,₀ _ _ _ _ (λ {_} → g {_})

-- -- -- -- -- -- -- instance

-- -- -- -- -- -- --   CompFunction' : ∀
-- -- -- -- -- -- --     {a b c} →
-- -- -- -- -- -- --     𝓡₇,₁
-- -- -- -- -- -- --       (Ø a)
-- -- -- -- -- -- --       (λ A → A → Ø b)
-- -- -- -- -- -- --       (λ A B → (x : A) → B x)
-- -- -- -- -- -- --       (λ A B f → {x : A} → B x → Ø c)
-- -- -- -- -- -- --       (λ A B f C → {x : A} (y : B x) → C y)
-- -- -- -- -- -- --       (λ A B f C g → A)
-- -- -- -- -- -- --       (λ A B f C g x → C (f x))
-- -- -- -- -- -- --   𝓡₇,₁.𝓻₇,₁,₀ CompFunction' A B f C g x = g (f x)

-- -- -- -- -- -- -- _∘''_ : ∀ {a b c}
-- -- -- -- -- -- --         {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- -- -- -- -- -- --         (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- -- -- -- -- -- --         ((x : A) → C (f x))
-- -- -- -- -- -- -- _∘''_ {a} {b} {c} {A} {B} {C} g f x = 𝓻₇,₁,₀ A B f (λ {v} → C {v}) (λ {v} → g {v}) x -- transitive ⦃ Transitive''Function ⦄ ? ? -- f g -- g f

-- -- -- -- -- -- -- instance

-- -- -- -- -- -- --   CompFunction6' : ∀
-- -- -- -- -- -- --     {a b c} →
-- -- -- -- -- -- --     𝓡₆,₁
-- -- -- -- -- -- --       (Ø a)
-- -- -- -- -- -- --       (λ A → A → Ø b)
-- -- -- -- -- -- --       (λ A B → (x : A) → B x)
-- -- -- -- -- -- --       (λ A B f → {x : A} → B x → Ø c)
-- -- -- -- -- -- --       (λ A B f C → {x : A} (y : B x) → C y)
-- -- -- -- -- -- --       (λ A B f C g → (x : A) → C (f x))
-- -- -- -- -- -- --   𝓡₆,₁.𝓻₆,₁,₀ CompFunction6' A B f C g x = g (f x)

-- -- -- -- -- -- -- _∘6'_ : ∀ {a b c}
-- -- -- -- -- -- --         {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
-- -- -- -- -- -- --         (g : ∀ {x} (y : B x) → C y) → (f : (x : A) → B x) →
-- -- -- -- -- -- --         ((x : A) → C (f x))
-- -- -- -- -- -- -- _∘6'_ {a} {b} {c} {A} {B} {C} g f =
-- -- -- -- -- -- --   transitive f (λ {v} → g {v})

-- -- -- -- -- -- --   -- 𝓻₆,₁,₀ A B f (λ {v} → C {v}) (λ {v} → g {v}) -- transitive ⦃ Transitive''Function ⦄ ? ? -- f g -- g f

-- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂} {𝔮₁}
-- -- -- -- -- -- -- --     (𝔔₁ : (x : 𝔒₁) → 𝔒₂ x → Ø 𝔮₁)
-- -- -- -- -- -- -- --   {𝔬₃} {𝔒₃ : ∀ {x} → 𝔒₂ x → Ø 𝔬₃} {𝔮₂}
-- -- -- -- -- -- -- --     (𝔔₂ : ∀ x (y : 𝔒₂ x) → 𝔒₃ y → Ø 𝔮₂)
-- -- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- -- --     (𝔔₃ : ∀ x (y : 𝔒₂ x) → 𝔒₃ y → Ø 𝔮₃)
-- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- --   Comp = 𝓡₆,₁ 𝔒₁ (λ A → 𝔒₂ A) 𝔔₁ _ (λ _ y 𝔔₁xy → 𝔔₂ _ y) (λ _ _ f z _ → 𝔔₃ _ _ z)
-- -- -- -- -- -- -- -- --  𝓣ransitive'' = ∀ {x y} → 𝔔₁ x y → ∀ {z} → 𝔔₂ y z → 𝔔₃ x z
-- -- -- -- -- -- -- -- --  𝓽ransitive'' = ⦃ _ : Transitive'' ⦄ → 𝓣ransitive''

-- -- -- -- -- -- -- -- -- instance CompFunction : ∀ {a b c} →
-- -- -- -- -- -- -- -- --            Comp
-- -- -- -- -- -- -- -- --              {𝔒₁ = Ø a} {𝔒₂ = λ A → A → Ø b}
-- -- -- -- -- -- -- -- --                (λ A B → (x : A) → B x)
-- -- -- -- -- -- -- -- --              {𝔒₃ = λ {A} B → {x : A} → B x → Ø c}
-- -- -- -- -- -- -- -- --                (λ A B C → {x : A} → (y : B x) → C y)
-- -- -- -- -- -- -- -- --                (λ A B C → {!!})
-- -- -- -- -- -- -- -- -- CompFunction = {!!}
-- -- -- -- -- -- -- -- -- -- 𝓡₆,₁.𝓻₆,₁,₀ CompFunction A B f C g x = {!!} -- g (f x)
-- -- -- -- -- -- -- -- -- -- A ⑴ f ⑶ g x

-- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮₁}
-- -- -- -- -- -- -- -- -- --     (𝔔₁ : 𝔒 → 𝔒 → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- --     (𝔔₂ : 𝔒 → 𝔒 → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- -- -- -- --     (𝔔₃ : 𝔒 → 𝔒 → Ø 𝔮₃)
-- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- --   Transitive = 𝓡₆,₁ _ _ 𝔔₁ _ (λ _ y _ → 𝔔₂ y) (λ x _ _ z _ → 𝔔₃ x z)
-- -- -- -- -- -- -- -- -- --   𝓣ransitive = ∀ {x y} → 𝔔₁ x y → ∀ {z} → 𝔔₂ y z → 𝔔₃ x z
-- -- -- -- -- -- -- -- -- --   𝓽ransitive = ⦃ _ : Transitive ⦄ → 𝓣ransitive

-- -- -- -- -- -- -- -- -- -- --instance TransitiveFunction : ∀ {𝔬} {𝔒 : Ø 𝔬} → Transitive {𝔮₁ = 𝔬} (λ x y → x → y) (λ x y → x → y) (λ x y → x → y)
-- -- -- -- -- -- -- -- -- -- --𝓡₆,₁.𝓻₆,₁,₀ TransitiveFunction ⓪ ⑴ f ⑶ g x = g (f x)

-- -- -- -- -- -- -- -- -- -- instance Transitive'Function : ∀ {𝔬} → Transitive' {𝔮₁ = 𝔬} (λ (x : Ø 𝔬) (y : Ø 𝔬) → x → y) {𝔮₂ = 𝔬} (λ x (y : Ø 𝔬) → x → y) {𝔮₃ = 𝔬} (λ x y → x → y)
-- -- -- -- -- -- -- -- -- -- 𝓡₆,₁.𝓻₆,₁,₀ Transitive'Function ⓪ ⑴ f ⑶ g x = g (f x)

-- -- -- -- -- -- -- -- -- -- test-trans' : (f : ¶ → 𝟙) (g : 𝟙 → 𝟘) → ¶ → 𝟘
-- -- -- -- -- -- -- -- -- -- test-trans' f g = transitive f g


-- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮}
-- -- -- -- -- -- -- -- -- --     (𝔔 : 𝔒 → 𝔒 → Ø 𝔮)
-- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- --   Reflexive = 𝓡₂,₁ _ (λ x → 𝔔 x x)
-- -- -- -- -- -- -- -- -- --   Antireflexive = 𝓡₂,₁ _ (λ x → 𝔔 x x → 𝟘)
-- -- -- -- -- -- -- -- -- --   Symmetric = 𝓡₄,₁ _ _ 𝔔 (λ x y _ → 𝔔 y x)
-- -- -- -- -- -- -- -- -- --   𝓢ymmetric = ∀ {x y} → 𝔔 x y → 𝔔 y x
-- -- -- -- -- -- -- -- -- --   Antisymmetric = 𝓡₄,₁ _ _ 𝔔 (λ x y _ → 𝔔 y x → 𝟘)
-- -- -- -- -- -- -- -- -- --   𝓐ntisymmetric = ∀ {x y} → 𝔔 x y → 𝔔 y x → 𝟘
-- -- -- -- -- -- -- -- -- --   Transitive′ = Transitive 𝔔 𝔔 𝔔
-- -- -- -- -- -- -- -- -- --   𝓣ransitive′ = 𝓣ransitive 𝔔 𝔔 𝔔
-- -- -- -- -- -- -- -- -- --   𝓽ransitive′ = ⦃ _ : Transitive′ ⦄ → 𝓣ransitive′
-- -- -- -- -- -- -- -- -- --   record Equivalence : Ø 𝔬 ∙̂ 𝔮 where
-- -- -- -- -- -- -- -- -- --     field ⦃ Reflexive⌶ ⦄ : Reflexive
-- -- -- -- -- -- -- -- -- --     field ⦃ Symmetric⌶ ⦄ : Symmetric
-- -- -- -- -- -- -- -- -- --     field ⦃ Transitive⌶ ⦄ : Transitive′
-- -- -- -- -- -- -- -- -- --   record StrictOrdering : Ø 𝔬 ∙̂ 𝔮 where
-- -- -- -- -- -- -- -- -- --     field ⦃ Antireflexive⌶ ⦄ : Antireflexive
-- -- -- -- -- -- -- -- -- --     field ⦃ Antisymmetric⌶ ⦄ : Antisymmetric
-- -- -- -- -- -- -- -- -- --     field ⦃ Transitive⌶ ⦄ : Transitive′

-- -- -- -- -- -- -- -- -- -- instance ReflexiveProposextensequality : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} → Reflexive Proposextensequality⟦ 𝔓 ⟧
-- -- -- -- -- -- -- -- -- -- 𝓡₂,₁.𝓻₂,₁,₀ ReflexiveProposextensequality _ _ = ∅

-- -- -- -- -- -- -- -- -- -- instance ReflexiveProposequality : ∀ {𝔬} {𝔒 : Ø 𝔬} → Reflexive Proposequality⟦ 𝔒 ⟧
-- -- -- -- -- -- -- -- -- -- 𝓡₂,₁.𝓻₂,₁,₀ ReflexiveProposequality _ = ∅

-- -- -- -- -- -- -- -- -- -- instance AntireflexiveProposantiequality : ∀ {𝔬} {𝔒 : Ø 𝔬} → Antireflexive Proposantiequality⟦ 𝔒 ⟧
-- -- -- -- -- -- -- -- -- -- 𝓡₂,₁.𝓻₂,₁,₀ AntireflexiveProposantiequality ⓪ x = x ∅

-- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- --   {𝔬} (𝔒 : Ø 𝔬)
-- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- --   Next = 𝓡₂,₁ 𝔒 (λ _ → 𝔒)

-- -- -- -- -- -- -- -- -- -- foo = {!Next ¶!}
-- -- -- -- -- -- -- -- -- -- bar = {!Reflexive Proposequality⟦ ¶ ⟧!}

-- -- -- -- -- -- -- -- -- -- instance Next¶ : Next ¶
-- -- -- -- -- -- -- -- -- -- 𝓡₂,₁.𝓻₂,₁,₀ Next¶ = ↑_

-- -- -- -- -- -- -- -- -- -- next : ∀
-- -- -- -- -- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- --   ⦃ _ : 𝓡₂,₁ 𝔒₀ 𝔒₁ ⦄
-- -- -- -- -- -- -- -- -- --   → ∀ ⓪ → 𝔒₁ ⓪
-- -- -- -- -- -- -- -- -- -- next = 𝓻₂,₁,₀

-- -- -- -- -- -- -- -- -- -- reflexive : ∀
-- -- -- -- -- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- --   ⦃ _ : 𝓡₂,₁ 𝔒₀ 𝔒₁ ⦄
-- -- -- -- -- -- -- -- -- --   → ∀ {⓪} → 𝔒₁ ⓪
-- -- -- -- -- -- -- -- -- -- reflexive {⓪} = 𝓻₂,₁,₀ _

-- -- -- -- -- -- -- -- -- -- test-next₁ : ¶
-- -- -- -- -- -- -- -- -- -- test-next₁ = next 3

-- -- -- -- -- -- -- -- -- -- test-reflexive₁ : ∀ (x : ¶) → x ≡ x
-- -- -- -- -- -- -- -- -- -- test-reflexive₁ = reflexive

-- -- -- -- -- -- -- -- -- -- test-reflexive₂ : ∀ {f : ¶ → ¶} → f ≡̇ f
-- -- -- -- -- -- -- -- -- -- test-reflexive₂ = reflexive

-- -- -- -- -- -- -- -- -- -- test-antireflexive₁ : 3 ≢ 3 → 𝟘
-- -- -- -- -- -- -- -- -- -- test-antireflexive₁ = next _

-- -- -- -- -- -- -- -- -- -- symmetric : ∀
-- -- -- -- -- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- --   {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴             → 𝔒₂ ⓪ ⑴             → Ø 𝔬₃}
-- -- -- -- -- -- -- -- -- --   ⦃ _ : 𝓡₄,₁ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ ⦄
-- -- -- -- -- -- -- -- -- --   → ∀ {⓪ ⑴} ⑵ → 𝔒₃ ⓪ ⑴ ⑵
-- -- -- -- -- -- -- -- -- -- symmetric = 𝓻₄,₁,₀ _ _

-- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- --   𝔬 𝔮
-- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- --   Transitivity′ =
-- -- -- -- -- -- -- -- -- --     𝓡₉,₁
-- -- -- -- -- -- -- -- -- --       (Ø 𝔬)
-- -- -- -- -- -- -- -- -- --       (λ 𝔒 → 𝔒 → 𝔒 → Ø 𝔮)
-- -- -- -- -- -- -- -- -- --       (λ _ 𝔔 → Transitive′ 𝔔)
-- -- -- -- -- -- -- -- -- --       _ _ (λ _ 𝔔 _ → 𝔔)
-- -- -- -- -- -- -- -- -- --       _ (λ _ 𝔔 _ _ y _ → 𝔔 y)
-- -- -- -- -- -- -- -- -- --       (λ _ 𝔔 _ x _ _ z _ → 𝔔 x z)

-- -- -- -- -- -- -- -- -- -- -- infixr 9 _∙_
-- -- -- -- -- -- -- -- -- -- transitivity′ : ∀
-- -- -- -- -- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- --   {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴             → 𝔒₂ ⓪ ⑴             → Ø 𝔬₃}
-- -- -- -- -- -- -- -- -- --   {𝔬₄} {𝔒₄ : ∀ ⓪ ⑴ ⑵           → 𝔒₃ ⓪ ⑴ ⑵           → Ø 𝔬₄}
-- -- -- -- -- -- -- -- -- --   {𝔬₅} {𝔒₅ : ∀ ⓪ ⑴ ⑵ ⑶         → 𝔒₄ ⓪ ⑴ ⑵ ⑶         → Ø 𝔬₅}
-- -- -- -- -- -- -- -- -- --   {𝔬₆} {𝔒₆ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷       → 𝔒₅ ⓪ ⑴ ⑵ ⑶ ⑷       → Ø 𝔬₆}
-- -- -- -- -- -- -- -- -- --   {𝔬₇} {𝔒₇ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸     → 𝔒₆ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸     → Ø 𝔬₇}
-- -- -- -- -- -- -- -- -- --   {𝔬₈} {𝔒₈ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹   → 𝔒₇ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹   → Ø 𝔬₈}
-- -- -- -- -- -- -- -- -- --   ⦃ _ : 𝓡₉,₁ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ 𝔒₄ 𝔒₅ 𝔒₆ 𝔒₇ 𝔒₈ ⦄ →
-- -- -- -- -- -- -- -- -- --   ∀ {⓪ ⑴} ⦃ ⑵ ⦄ {⑶ ⑷} ⑸ {⑹} ⑺ → 𝔒₈ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺
-- -- -- -- -- -- -- -- -- -- transitivity′ ⑸ = 𝓻₉,₁,₀ _ _ _ _ _ ⑸ _

-- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- --   {𝔬} (𝔒 : Ø 𝔬) 𝔮
-- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- --   Relation = 𝓡₃,₁ 𝔒 (λ _ → 𝔒) (λ _ _ → Ø 𝔮)
-- -- -- -- -- -- -- -- -- --   𝓡elation = 𝔒 → 𝔒 → Ø 𝔮

-- -- -- -- -- -- -- -- -- --   record Equivalent : Ø ↑̂ 𝔬 ∙̂ ↑̂ 𝔮 where
-- -- -- -- -- -- -- -- -- --     infix 4 _≋_
-- -- -- -- -- -- -- -- -- --     field _≋_ : 𝓡elation
-- -- -- -- -- -- -- -- -- --     field Equivalence⌶ : Equivalence _≋_

-- -- -- -- -- -- -- -- -- --   record StrictOrder : Ø ↑̂ 𝔬 ∙̂ ↑̂ 𝔮 where
-- -- -- -- -- -- -- -- -- --     infix 6 _<_
-- -- -- -- -- -- -- -- -- --     field _<_ : 𝓡elation
-- -- -- -- -- -- -- -- -- --     field StrictOrdering⌶ : StrictOrdering _<_

-- -- -- -- -- -- -- -- -- -- relation : ∀
-- -- -- -- -- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- --   ⦃ _ : 𝓡₃,₁ 𝔒₀ 𝔒₁ 𝔒₂ ⦄
-- -- -- -- -- -- -- -- -- --   → ∀ ⓪ ⑴ → 𝔒₂ ⓪ ⑴
-- -- -- -- -- -- -- -- -- -- relation = 𝓻₃,₁,₀

-- -- -- -- -- -- -- -- -- -- open Equivalence ⦃ … ⦄
-- -- -- -- -- -- -- -- -- -- open Equivalent ⦃ … ⦄
-- -- -- -- -- -- -- -- -- -- open StrictOrder ⦃ … ⦄

-- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔪}
-- -- -- -- -- -- -- -- -- --     {𝔐 : 𝔒 → 𝔒 → Ø 𝔪}
-- -- -- -- -- -- -- -- -- --     (𝒯 : 𝓣ransitive′ 𝔐)
-- -- -- -- -- -- -- -- -- --   {𝔮}
-- -- -- -- -- -- -- -- -- --     (𝔔 : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮)
-- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- --   Associative = 𝓡₈,₁ _ _ 𝔐 _ (λ _ x _ → 𝔐 x) _ (λ _ _ _ y _ → 𝔐 y) (λ _ _ f _ g _ h → 𝔔 (𝒯 f (𝒯 g h)) (𝒯 (𝒯 f g) h))
-- -- -- -- -- -- -- -- -- --   𝓐ssociative = ∀ {w x} (f : 𝔐 w x) {y} (g : 𝔐 x y) {z} (h : 𝔐 y z) → 𝔔 (𝒯 f (𝒯 g h)) (𝒯 (𝒯 f g) h)

-- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔪}
-- -- -- -- -- -- -- -- -- --     (𝔐 : 𝔒 → 𝔒 → Ø 𝔪)
-- -- -- -- -- -- -- -- -- --     (𝒯 : 𝓣ransitive′ 𝔐)
-- -- -- -- -- -- -- -- -- --   {𝔮₁}
-- -- -- -- -- -- -- -- -- --     (𝔔₁ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- --     (𝔔₂ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- -- -- -- --     (𝔔₃ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₃)
-- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- --   Extensional = 𝓡₁₀,₁ _ _ _ _ (λ x y (f₁ : 𝔐 x y) (f₂ : 𝔐 x y) → 𝔔₁ f₁ f₂) _ (λ _ y _ _ _ z → 𝔐 y z) _ (λ _ _ _ _ _ _ g₁ g₂ → 𝔔₂ g₁ g₂) (λ _ _ f₁ f₂ _ _ g₁ g₂ _ → 𝔔₃ (𝒯 f₁ g₁) (𝒯 f₂ g₂))
-- -- -- -- -- -- -- -- -- --   𝓔xtensional = ∀ {x y} {f₁ f₂ : 𝔐 x y} → 𝔔₁ f₁ f₂ → ∀ {z} {g₁ g₂ : 𝔐 y z} → 𝔔₂ g₁ g₂ → 𝔔₃ (𝒯 f₁ g₁) (𝒯 f₂ g₂)

-- -- -- -- -- -- -- -- -- -- --  record EXTENSIONAL (x : 𝔒) (y : ∀ x → (λ _ → 𝔒) x) (f₁ : ∀ x y → (λ x y → 𝔐 x y) x y) : Ø _ where
-- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- --   record EXTENSIONAL (x : 𝔒) (y : ∀ x → 𝔒) (f₁ : ∀ x y → 𝔐 x y) (f₂ : 𝔐 x y) (𝔔₁f₁f₂ : 𝔔₁ f₁ f₂) (z : 𝔒) (g₁ : 𝔐 y z) (g₂ : 𝔐 y z) (𝔔₂g₁g₂ : 𝔔₂ g₁ g₂) (ext : 𝔔₃ (𝒯 f₁ g₁) (𝒯 f₂ g₂))
-- -- -- -- -- -- -- -- -- --     : Ø _ where
-- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- --   record EXTENSIONAL (x : 𝔒) (y : 𝔒) (f₁ : 𝔐 x y) (f₂ : 𝔐 x y) (𝔔₁f₁f₂ : 𝔔₁ f₁ f₂) (z : 𝔒) (g₁ : 𝔐 y z) (g₂ : 𝔐 y z) (𝔔₂g₁g₂ : 𝔔₂ g₁ g₂)
-- -- -- -- -- -- -- -- -- --     : Ø _ where
-- -- -- -- -- -- -- -- -- -- --    field
-- -- -- -- -- -- -- -- -- -- --      extensional : ∀ {x y} → 𝔔₃ (𝒯 f₁ g₁) (𝒯 f₂ g₂)

-- -- -- -- -- -- -- -- -- --   record EXTENSIONAL'
-- -- -- -- -- -- -- -- -- --     {𝔬₀} (𝔒₀ : Ø 𝔬₀)
-- -- -- -- -- -- -- -- -- --     {𝔬₁} (𝔒₁ :
-- -- -- -- -- -- -- -- -- --     (y : 𝔒) (f₁ : 𝔐 x y) (f₂ : 𝔐 x y) (𝔔₁f₁f₂ : 𝔔₁ f₁ f₂) (z : 𝔒) (g₁ : 𝔐 y z) (g₂ : 𝔐 y z) (𝔔₂g₁g₂ : 𝔔₂ g₁ g₂)
-- -- -- -- -- -- -- -- -- --     : Ø _ where
-- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- --  record EXTENSIONAL _ _ _ _ (_ : ∀ x y (f₁ : 𝔐 x y) (f₂ : 𝔐 x y) → 𝔔₁ f₁ f₂) _ (_ : ∀ _ y _ _ _ z → 𝔐 y z) _ (_ : ∀ _ _ _ _ _ _ g₁ g₂ → 𝔔₂ g₁ g₂) (_ : ∀ _ _ f₁ f₂ _ _ g₁ g₂ _ → 𝔔₃ (𝒯 f₁ g₁) (𝒯 f₂ g₂))
-- -- -- -- -- -- -- -- -- -- --    : Ø _ where
-- -- -- -- -- -- -- -- -- --   -- _ (λ _ y _ _ _ z → 𝔐 y z) _ (λ _ _ _ _ _ _ g₁ g₂ → 𝔔₂ g₁ g₂) (λ _ _ f₁ f₂ _ _ g₁ g₂ _ → 𝔔₃ (𝒯 f₁ g₁) (𝒯 f₂ g₂)) : Ø _ where



-- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔪}
-- -- -- -- -- -- -- -- -- -- --     (𝔐 : 𝔒 → 𝔒 → Ø 𝔪)
-- -- -- -- -- -- -- -- -- -- --     (𝒯 : 𝓣ransitive′ 𝔐)
-- -- -- -- -- -- -- -- -- -- --   {𝔮₁}
-- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- -- -- -- -- --     (𝔔₃ : ∀ {x y} → 𝔐 x y → 𝔐 x y → ∀ {z} → 𝔐 y z → 𝔐 y z → Ø 𝔮₃)
-- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- --   𝓔xtensionality = 𝓡₉ _ _ _ _ (λ x y (f₁ : 𝔐 x y) (f₂ : 𝔐 x y) → 𝔔₁ f₁ f₂) _ (λ _ y _ _ _ z → 𝔐 y z) _ (λ _ _ _ _ _ _ g₁ g₂ → 𝔔₂ g₁ g₂) (λ _ _ f₁ f₂ _ _ g₁ g₂ _ → 𝔔₃ f₁ f₂ g₁ g₂)
-- -- -- -- -- -- -- -- -- -- --   𝓮xtensionality = ∀ {x y} {f₁ f₂ : 𝔐 x y} → 𝔔₁ f₁ f₂ → ∀ {z} {g₁ g₂ : 𝔐 y z} → 𝔔₂ g₁ g₂ → 𝔔₃ f₁ f₂ g₁ g₂
-- -- -- -- -- -- -- -- -- -- --   record Extensionality : Ø 𝔬 ∙̂ 𝔪 ∙̂ 𝔮₁ ∙̂ 𝔮₂ ∙̂ 𝔮₃ where field extensionality : 𝓮xtensionality
-- -- -- -- -- -- -- -- -- -- --   open Extensionality ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- postulate
-- -- -- -- -- -- -- -- -- -- --   A : Set
-- -- -- -- -- -- -- -- -- -- --   B : Set
-- -- -- -- -- -- -- -- -- -- --   instance eqA : Equivalent A ∅̂
-- -- -- -- -- -- -- -- -- -- --   instance eqB : Equivalent B ∅̂
-- -- -- -- -- -- -- -- -- -- --   instance refA : Reflexive {𝔒 = A} _≋_
-- -- -- -- -- -- -- -- -- -- --   instance refB : Reflexive {𝔒 = B} _≋_
-- -- -- -- -- -- -- -- -- -- --   --instance eqB : Equivalent B ∅̂
-- -- -- -- -- -- -- -- -- -- --   --instance soA : StrictOrder A ∅̂
-- -- -- -- -- -- -- -- -- -- --   --instance soB : StrictOrder B ∅̂

-- -- -- -- -- -- -- -- -- -- -- testA= : (x y : A) → x ≋ x
-- -- -- -- -- -- -- -- -- -- -- --testA= x y = reflexive ⦃ eqA .Equivalent.Equivalence⌶ .Equivalence.Reflexive⌶ ⦄
-- -- -- -- -- -- -- -- -- -- -- testA= x y = reflexive
-- -- -- -- -- -- -- -- -- -- -- -- 𝓻₂,₁,₀


-- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- -- -- {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- -- -- {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- -- -- {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴             → 𝔒₂ ⓪ ⑴             → Ø 𝔬₃}
-- -- -- -- -- -- -- -- -- -- -- {𝔬₄} {𝔒₄ : ∀ ⓪ ⑴ ⑵           → 𝔒₃ ⓪ ⑴ ⑵           → Ø 𝔬₄}
-- -- -- -- -- -- -- -- -- -- -- {𝔬₅} {𝔒₅ : ∀ ⓪ ⑴ ⑵ ⑶         → 𝔒₄ ⓪ ⑴ ⑵ ⑶         → Ø 𝔬₅}
-- -- -- -- -- -- -- -- -- -- -- {𝔬₆} {𝔒₆ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷       → 𝔒₅ ⓪ ⑴ ⑵ ⑶ ⑷       → Ø 𝔬₆}
-- -- -- -- -- -- -- -- -- -- -- {𝔬₇} {𝔒₇ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸     → 𝔒₆ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸     → Ø 𝔬₇}
-- -- -- -- -- -- -- -- -- -- -- {𝔬₈} {𝔒₈ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹   → 𝔒₇ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹   → Ø 𝔬₈}
-- -- -- -- -- -- -- -- -- -- -- {𝔬₉} {𝔒₉ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺ → 𝔒₈ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺ → Ø 𝔬₉}

-- -- -- -- -- -- -- -- -- -- -- 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ 𝔒₄ 𝔒₅ 𝔒₆ 𝔒₇ 𝔒₈ 𝔒₉
-- -- -- -- -- -- -- -- -- -- -- ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺ ⑻
-- -- -- -- -- -- -- -- -- -- -- -}


-- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- --   𝔬 𝔮
-- -- -- -- -- -- -- -- -- -- -- --   where

-- -- -- -- -- -- -- -- -- -- -- -- --  𝓔quality = λ {𝔒 : Ø 𝔬} (𝔔 : 𝔒 → 𝔒 → Ø 𝔮) → ⦃ _ : Transitive′ 𝔔 ⦄ → 𝓡elation 𝔔


-- -- -- -- -- -- -- -- -- -- -- -- -- --  record Equivalent : Ø ↑̂ 𝔬 ∙̂ ↑̂ 𝔮 where
-- -- -- -- -- -- -- -- -- -- -- -- -- --    field ⦃ Relation⌶ ⦄ : Relation
-- -- -- -- -- -- -- -- -- -- -- -- -- --    field ⦃ Equivalence⌶ ⦄ : Equivalence 𝓻₃,₁,₀

-- -- -- -- -- -- -- -- -- -- -- -- --   record Equivalent : Ø ↑̂ 𝔬 ∙̂ ↑̂ 𝔮 where
-- -- -- -- -- -- -- -- -- -- -- -- --     infix 4 _≋_
-- -- -- -- -- -- -- -- -- -- -- -- --     field _≋_ : 𝓡elation
-- -- -- -- -- -- -- -- -- -- -- -- --     field instance Equivalence⌶ : Equivalence _≋_

-- -- -- -- -- -- -- -- -- -- -- -- --   Equality :
-- -- -- -- -- -- -- -- -- -- -- -- --   𝓔quality = λ {𝔒 : Ø 𝔬} (𝔔 : 𝔒 → 𝔒 → Ø 𝔮) → ⦃ _ : Transitive′ 𝔔 ⦄ → 𝓡elation 𝔔

-- -- -- -- -- -- -- -- -- -- -- -- -- postulate
-- -- -- -- -- -- -- -- -- -- -- -- --   A : Set
-- -- -- -- -- -- -- -- -- -- -- -- --   B : Set
-- -- -- -- -- -- -- -- -- -- -- -- --   instance eqA : Equivalent A ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- --   instance eqB : Equivalent B ∅̂

-- -- -- -- -- -- -- -- -- -- -- -- -- open Equivalent ⦃ … ⦄

-- -- -- -- -- -- -- -- -- -- -- -- -- testA= : (x y : A) → x ≋ x
-- -- -- -- -- -- -- -- -- -- -- -- -- testA= x y = 𝓻₂,₁,₀ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝓻₂,₁,₀

-- -- -- -- -- -- -- -- -- -- -- -- -- --  instance orA : StrictOrdering A
-- -- -- -- -- -- -- -- -- -- -- -- -- --  instance orB : StrictOrdering B
-- -- -- -- -- -- -- -- -- -- -- -- --   -- relA< : Relation A ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- --   -- relA= : Relation A ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- --  instance ltI : Antisymmetric (𝓻₃,₁,₀ ⦃ relA< ⦄)
-- -- -- -- -- -- -- -- -- -- -- -- -- --  instance eqI : Symmetric (𝓻₃,₁,₀ ⦃ relA= ⦄)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- postulate
-- -- -- -- -- -- -- -- -- -- -- -- -- --   A : Set
-- -- -- -- -- -- -- -- -- -- -- -- -- --   LA1 LA2 : List A
-- -- -- -- -- -- -- -- -- -- -- -- -- --   Nat : Set

-- -- -- -- -- -- -- -- -- -- -- -- -- -- want:

-- -- -- -- -- -- -- -- -- -- -- -- -- --   : (x y : Nat) → x ≋ y
-- -- -- -- -- -- -- -- -- -- -- -- -- --   : (x y : Nat) → x < y
-- -- -- -- -- -- -- -- -- -- -- -- -- --   : (x y : List A) → x < (x + y)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   : (x y : List A) → x < (x + y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} (𝔒 : Ø 𝔬) 𝔮
-- -- -- -- -- -- -- -- -- -- -- -- -- --   where

-- -- -- -- -- -- -- -- -- -- -- -- -- --   Equality = 𝓡₆,₁ (Relation 𝔒 𝔮) (λ _ → 𝔒 → 𝔒 → Ø 𝔮) (λ _ 𝔔 → Symmetric 𝔔) (λ _ _ _ → 𝔒) (λ _ _ _ _ → 𝔒) (λ _ 𝔔 _ → 𝔔)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  𝓔quality = λ {𝔒 : Ø 𝔬} (𝔔 : 𝔒 → 𝔒 → Ø 𝔮) → ⦃ _ : Symmetric 𝔔 ⦄ → 𝓡elation 𝔔

-- -- -- -- -- -- -- -- -- -- -- -- -- -- _≋_ : ∀
-- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴             → 𝔒₂ ⓪ ⑴             → Ø 𝔬₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₄} {𝔒₄ : ∀ ⓪ ⑴ ⑵           → 𝔒₃ ⓪ ⑴ ⑵           → Ø 𝔬₄}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₅} {𝔒₅ : ∀ ⓪ ⑴ ⑵ ⑶         → 𝔒₄ ⓪ ⑴ ⑵ ⑶         → Ø 𝔬₅}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   ⦃ _ : 𝓡₆,₁ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ 𝔒₄ 𝔒₅ ⦄ →
-- -- -- -- -- -- -- -- -- -- -- -- -- --   ∀ {{⓪}} {⑴} {{⑵}} ⑶ ⑷ → 𝔒₅ ⓪ ⑴ ⑵ ⑶ ⑷
-- -- -- -- -- -- -- -- -- -- -- -- -- -- _≋_ = 𝓻₆,₁,₀ _ _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- postulate
-- -- -- -- -- -- -- -- -- -- -- -- -- --   A : Set
-- -- -- -- -- -- -- -- -- -- -- -- -- --   instance relA< : Relation A ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- --   instance relA= : Relation A ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- --   instance ltI : Antisymmetric (𝓻₃,₁,₀ ⦃ relA< ⦄)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   instance eqI : Symmetric (𝓻₃,₁,₀ ⦃ relA= ⦄)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- instance ⌶Equality : Equality A ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝓡₆,₁.𝓻₆,₁,₀ ⌶Equality r q s x y = {!𝓻₃,₁,₀ ⦃ r ⦄!} -- 𝓻₃,₁,₀ ⦃ r ⦄ x y

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- instance ⌶Equality : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔮} → Equality 𝔒 𝔮
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝓡₅,₁.𝓻₅,₁,₀ ⌶Equality r s x y = {!!} -- 𝓻₃,₁,₀ ⦃ r ⦄ x y


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- testA= : (x y : A) → x ≋ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- testA= x = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _≤_ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔮}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ⦃ _ : Relation 𝔒 𝔮 ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ⦃ _ : Antisymmetric 𝓻₃,₁,₀ ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → 𝔒 → 𝔒 → Ø 𝔮
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _≤_ = 𝓻₃,₁,₀

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _≋_ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔮}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ⦃ _ : Relation 𝔒 𝔮 ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ⦃ _ : Symmetric 𝓻₃,₁,₀ ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → 𝔒 → 𝔒 → Ø 𝔮
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _≋_ = 𝓻₃,₁,₀

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- postulate
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   A : Set
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance relA< : Relation A ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance relA= : Relation A ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance ltI : Antisymmetric (𝓻₃,₁,₀ ⦃ relA< ⦄)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance eqI : Symmetric (𝓻₃,₁,₀ ⦃ relA= ⦄)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- testA= : (x y : A) → x ≋ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- testA= x = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- testA< : (x y : A) → x ≤ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- testA< x y = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∀ {x y} → 𝔔 x y → 𝔔 x y → Ø 𝔮
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔪}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {𝔐 : 𝔒 → 𝔒 → Ø 𝔪}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝒯 : 𝓣ransitive′ 𝔐)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔 : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Associative = 𝓡₈,₁ _ _ 𝔐 _ (λ _ x _ → 𝔐 x) _ (λ _ _ _ y _ → 𝔐 y) (λ _ _ f _ g _ h → 𝔔 (𝒯 f (𝒯 g h)) (𝒯 (𝒯 f g) h))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓐ssociative = ∀ {w x} (f : 𝔐 w x) {y} (g : 𝔐 x y) {z} (h : 𝔐 y z) → 𝔔 (𝒯 f (𝒯 g h)) (𝒯 (𝒯 f g) h)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝔬 𝔪 𝔮
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Associativity = 𝓡₁₃,₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓐ssociativity = λ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {𝔒 : Ø 𝔬} {𝔐 : 𝔒 → 𝔒 → Ø 𝔪}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (𝒯 : ∀ {x y} → 𝔐 x y → ∀ {z} → 𝔐 y z → 𝔐 x z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (𝔔 : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ⦃ _ : Associative 𝒯 𝔔 ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → 𝓐ssociative 𝒯 𝔔

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Transitivity = 𝓡₉,₁ (Ø 𝔬) (λ 𝔒 → 𝔒 → 𝔒 → Ø 𝔮) (λ _ 𝔔 → Transitive′ 𝔔) _ _ (λ _ 𝔔 _ → 𝔔) _ (λ _ 𝔔 _ _ y _ → 𝔔 y) (λ _ 𝔔 _ x _ _ z _ → 𝔔 x z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓣ransitivity = λ {𝔒 : Ø 𝔬} (𝔔 : 𝔒 → 𝔒 → Ø 𝔮) ⦃ _ : Transitive′ 𝔔 ⦄ → 𝓣ransitive′ 𝔔
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔪}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {𝔐 : 𝔒 → 𝔒 → Ø 𝔪}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝒯 : ∀ {x y} → 𝔐 x y → ∀ {z} → 𝔐 y z → 𝔐 x z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₃ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝔬 𝔮
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Transitivity = 𝓡₉,₁ (Ø 𝔬) (λ 𝔒 → 𝔒 → 𝔒 → Ø 𝔮) (λ _ 𝔔 → Transitive′ 𝔔) _ _ (λ _ 𝔔 _ → 𝔔) _ (λ _ 𝔔 _ _ y _ → 𝔔 y) (λ _ 𝔔 _C x _ _ z _ → 𝔔 x z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓣ransitivity = λ {𝔒 : Ø 𝔬} (𝔔 : 𝔒 → 𝔒 → Ø 𝔮) → ⦃ _ : Transitive′ 𝔔 ⦄ → 𝓣ransitive′ 𝔔

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ➊ : ∀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⦃ _ : 𝓡₂,₁ 𝔒₀ 𝔒₁ ⦄ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∀ {⓪} → 𝔒₁ ⓪
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ➊ = 𝓻₂,₁,₀ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ➋ : ∀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴             → 𝔒₂ ⓪ ⑴             → Ø 𝔬₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⦃ _ : 𝓡₄,₁ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ ⦄ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∀ {⓪ ⑴} ⑵ → 𝔒₃ ⓪ ⑴ ⑵
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ➋ = 𝓻₄,₁,₀ _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- infixl 21 _⟨➋➊⟩_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _⟨➋➊⟩_ : ∀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴             → 𝔒₂ ⓪ ⑴             → Ø 𝔬₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₄} {𝔒₄ : ∀ ⓪ ⑴ ⑵           → 𝔒₃ ⓪ ⑴ ⑵           → Ø 𝔬₄}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₅} {𝔒₅ : ∀ ⓪ ⑴ ⑵ ⑶         → 𝔒₄ ⓪ ⑴ ⑵ ⑶         → Ø 𝔬₅}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⦃ _ : 𝓡₆,₁ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ 𝔒₄ 𝔒₅ ⦄ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∀ {⓪ ⑴} ⑵ {⑶} ⑷ → 𝔒₅ ⓪ ⑴ ⑵ ⑶ ⑷
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _⟨➋➊⟩_ ⑵ = 𝓻₆,₁,₀ _ _ ⑵ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- infixr 9 _∙_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _∙_ : ∀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴             → 𝔒₂ ⓪ ⑴             → Ø 𝔬₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₄} {𝔒₄ : ∀ ⓪ ⑴ ⑵           → 𝔒₃ ⓪ ⑴ ⑵           → Ø 𝔬₄}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₅} {𝔒₅ : ∀ ⓪ ⑴ ⑵ ⑶         → 𝔒₄ ⓪ ⑴ ⑵ ⑶         → Ø 𝔬₅}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₆} {𝔒₆ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷       → 𝔒₅ ⓪ ⑴ ⑵ ⑶ ⑷       → Ø 𝔬₆}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₇} {𝔒₇ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸     → 𝔒₆ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸     → Ø 𝔬₇}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₈} {𝔒₈ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹   → 𝔒₇ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹   → Ø 𝔬₈}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⦃ _ : 𝓡₉,₁ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ 𝔒₄ 𝔒₅ 𝔒₆ 𝔒₇ 𝔒₈ ⦄ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∀ {⓪ ⑴} ⦃ ⑵ ⦄ {⑶ ⑷} ⑸ {⑹} ⑺ → 𝔒₈ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _∙_ ⑸ = 𝓻₉,₁,₀ _ _ _ _ _ ⑸ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- instance ⌶Transitivity : ∀ {𝔬} {𝔮} → Transitivity 𝔬 𝔮
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝓡₉,₁.𝓻₉,₁,₀ ⌶Transitivity ⓪ _≋_ ⑵ x y x≋y z y≋z = let instance _ = ⑵ in x≋y ⟨➋➊⟩ y≋z

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module TestTransitivityInTransitive′
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔 : 𝔒 → 𝔒 → Ø 𝔮)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test⟨➋➊⟩ : 𝓣ransitivity _ _ 𝔔
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test⟨➋➊⟩ xy yz = xy ⟨➋➊⟩ yz

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test∙ : 𝓣ransitivity _ _ 𝔔
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test∙ xy yz = xy ∙ yz

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test : 𝓣ransitivity _ _ 𝔔
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test xy yz = {!_∙_!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module TestTransitivityInTransitive
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : 𝔒 → 𝔒 → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : 𝔒 → 𝔒 → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₃ : 𝔒 → 𝔒 → Ø 𝔮₃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test⟨➋➊⟩ : ⦃ _ : Transitive 𝔔₁ 𝔔₂ 𝔔₃ ⦄ → 𝓣ransitive 𝔔₁ 𝔔₂ 𝔔₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test⟨➋➊⟩ xy yz = xy ⟨➋➊⟩ yz

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test∙ : ⦃ _ : Transitive 𝔔₁ 𝔔₂ 𝔔₃ ⦄ → 𝓣ransitive 𝔔₁ 𝔔₂ 𝔔₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test∙ xy yz = {!xy ∙ yz!} -- fails, correctly. _∙_

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test : ⦃ _ : Transitive 𝔔₁ 𝔔₂ 𝔔₃ ⦄ → 𝓣ransitive 𝔔₁ 𝔔₂ 𝔔₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test xy yz = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔪} {𝔐 : 𝔒 → 𝔒 → Ø 𝔪}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝒯
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔 : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Associativity = 𝓡₂,₁ _ _ 𝔐 _ (λ _ x _ → 𝔐 x) _ (λ _ _ _ y _ → 𝔐 y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- (λ x → 𝔔 x x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Symmetricity = 𝓡₄,₁ _ _ 𝔔 (λ x y _ → 𝔔 y x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Transitivity = 𝓡₆,₁ _ _ 𝔔 _ (λ _ y _ → 𝔔 y) (λ x _ _ z _ → 𝔔 x z)




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₀} {𝔒₀ :                                           Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₁} {𝔒₁ :                     𝔒₀                 → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₂} {𝔒₂ : ∀ ⓪               → 𝔒₁ ⓪               → Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₃} {𝔒₃ : ∀ ⓪ ⑴             → 𝔒₂ ⓪ ⑴             → Ø 𝔬₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₄} {𝔒₄ : ∀ ⓪ ⑴ ⑵           → 𝔒₃ ⓪ ⑴ ⑵           → Ø 𝔬₄}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₅} {𝔒₅ : ∀ ⓪ ⑴ ⑵ ⑶         → 𝔒₄ ⓪ ⑴ ⑵ ⑶         → Ø 𝔬₅}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₆} {𝔒₆ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷       → 𝔒₅ ⓪ ⑴ ⑵ ⑶ ⑷       → Ø 𝔬₆}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₇} {𝔒₇ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸     → 𝔒₆ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸     → Ø 𝔬₇}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₈} {𝔒₈ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹   → 𝔒₇ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹   → Ø 𝔬₈}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {𝔬₉} {𝔒₉ : ∀ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺ → 𝔒₈ ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺ → Ø 𝔬₉}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ 𝔒₄ 𝔒₅ 𝔒₆ 𝔒₇ 𝔒₈ 𝔒₉
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ⓪ ⑴ ⑵ ⑶ ⑷ ⑸ ⑹ ⑺ ⑻
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔 : 𝔒 → 𝔒 → Ø 𝔮)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓓iagonal = 𝓡₂,₁ _ (λ x → 𝔔 x x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓓iagonal' = ∀ {x} → 𝔔 x x

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝓓iagonal3 : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔮} (𝔔 : 𝔒 → 𝔒 → Ø 𝔮) → Ø _ -- 𝔬 ∙̂ 𝔮
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝓓iagonal3 𝔔 = 𝓡₂,₁ _ (_ ∋ λ x → 𝔔 x x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- infix 4 _≋_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _≋_ : ∀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₀} {𝔒₀ : Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ : 𝔒₀ → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : ∀ x₀ → 𝔒₁ x₀ → Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₃} {𝔒₃ : ∀ x₀ x₁ → 𝔒₂ x₀ x₁ → Ø 𝔬₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⦃ _ : 𝓡₄,₁ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ ⦄ → ∀ {x₀ x₁} x₂ → 𝔒₃ x₀ x₁ x₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _≋_ = 𝓻₄,₁,₀ _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔 : 𝔒 → 𝔒 → Ø 𝔮)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓡elation₁ = 𝓡₂,₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓻elation₁ = ∀ x y → 𝔔 x y

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔒 : Ø 𝔬)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     𝔮
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓟rop₂ = 𝓡₂ 𝔒 (λ _ → 𝔒) (λ _ _ → Ø 𝔮)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓹rop₂ = 𝔒 → 𝔒 → Ø 𝔮

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- prop
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Prop₂ : Ø 𝔬 ∙̂ ↑̂ 𝔮 where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓟rop₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     prop₂ : 𝓹rop₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     prop₂ = 𝓻₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Prop₂ ⦃ … ⦄ public hiding (⋆)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔒 : Ø 𝔬)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓤nit = 𝓡₀ 𝔒
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓾nit = 𝔒
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Unit : Ø 𝔬 where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓤nit
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     unit : 𝓾nit
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     unit = 𝓻₀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓤nit² = 𝓡₀,₂ 𝔒
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Unit² : Ø 𝔬 where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓤nit²
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     unit₀ : 𝓾nit
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     unit₀ = 𝓻₀,₀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     unit₁ : 𝓾nit
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     unit₁ = 𝓻₀,₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓶agma = 𝔒 → 𝔒 → 𝔒
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓜agma₁ = 𝓡₂ 𝔒 (λ _ → 𝔒) (λ _ _ → 𝔒)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Magma₁ : Ø 𝔬 where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓜agma₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     infixr 9 _∙_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _∙_ : 𝓶agma
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _∙_ = 𝓻₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓜agma₂ = 𝓡₂,₂ 𝔒 (λ _ → 𝔒) (λ _ _ → 𝔒)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Magma₂ : Ø 𝔬 where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓜agma₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     infixl 6 _+_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _+_ : 𝓶agma
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _+_ = 𝓻₂,₂,₀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     infixl 8 _*_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _*_ : 𝓶agma
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _*_ = 𝓻₂,₂,₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Unit ⦃ … ⦄ public hiding (⋆)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Unit² ⦃ … ⦄ public hiding (⋆)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Magma₁ ⦃ … ⦄ public hiding (⋆)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Magma₂ ⦃ … ⦄ public hiding (⋆)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔 : 𝔒 → 𝔒 → Ø 𝔮)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓓iagonal = 𝓡₁ _ (λ x → 𝔔 x x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓭iagonal = ∀ {x} → 𝔔 x x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Diagonal : Ø 𝔬 ∙̂ 𝔮 where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓓iagonal
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     diagonal : 𝓭iagonal
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     diagonal = 𝓻₁ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Diagonal ⦃ … ⦄ public hiding (⋆)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : 𝔒₁ → 𝔒₁ → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : Ø 𝔬₂} {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : 𝔒₂ → 𝔒₂ → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (μ : 𝔒₁ → 𝔒₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓡emap = 𝓡₃ _ _ (λ x y → 𝔔₁ x y) (λ x y _ → 𝔔₂ (μ x) (μ y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓻emap = ∀ {x y} → 𝔔₁ x y → 𝔔₂ (μ x) (μ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Remap : Ø 𝔬₁ ∙̂ 𝔮₁ ∙̂ 𝔬₂ ∙̂ 𝔮₂ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓡emap
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     remap : 𝓻emap
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     remap = 𝓻₃ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     open 𝓡₃ ⋆ public using () renaming (r3' to remap!)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     open 𝓡₃ ⦃ … ⦄ public using () renaming (r3' to OhRemap)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     threemap' : ∀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {𝔬₀} {𝔒₀ : Ø 𝔬₀}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {𝔬₁} {𝔒₁ : 𝔒₀ → Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {𝔬₂} {𝔒₂ : ∀ x₀ → 𝔒₁ x₀ → Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {𝔬₃} {𝔒₃ : ∀ x₀ x₁ → 𝔒₂ x₀ x₁ → Ø 𝔬₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ⦃ _ : 𝓡₃ 𝔒₀ 𝔒₁ 𝔒₂ 𝔒₃ ⦄ → ∀ {x₀ x₁} x₂ → 𝔒₃ x₀ x₁ x₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     threemap' = 𝓻₃ _ _



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Remap ⦃ … ⦄ public hiding (⋆)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {𝔔₁ : 𝔒₁ → 𝔒₁ → Ø 𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : Ø 𝔬₂} {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {𝔔₂ : 𝔒₂ → 𝔒₂ → Ø 𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {μ : 𝔒₁ → 𝔒₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   REMAP : ⦃ _ : 𝓡emap 𝔔₁ 𝔔₂ μ ⦄ → 𝓻emap 𝔔₁ 𝔔₂ μ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   REMAP = 𝓻₃ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : 𝔒₁ → 𝔒₁ → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : Ø 𝔬₂} {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : 𝔒₂ → 𝔒₂ → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (μ : 𝔒₁ → 𝔒₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓡emap2 = 𝓡₄ μ _ _ (λ _ x y → 𝔔₁ x y) (λ _ x y _ → 𝔔₂ (μ x) (μ y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓻emap2 = ∀ {x y} → 𝔔₁ x y → 𝔔₂ (μ x) (μ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Remap2 : Ø 𝔬₁ ∙̂ 𝔮₁ ∙̂ 𝔬₂ ∙̂ 𝔮₂ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓡emap2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     remap2 : 𝓻emap2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     remap2 = {!𝓻₃ _ _!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Remap2 ⦃ … ⦄ public hiding (⋆)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record REMAPR
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : 𝔒₁ → 𝔒₁ → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (x y : 𝔒₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : Ø 𝔬₂} {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : 𝔒₂ → 𝔒₂ → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (μx μy : 𝔒₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   : Ø 𝔬₁ ∙̂ 𝔮₁ ∙̂ 𝔬₂ ∙̂ 𝔮₂ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     REMAP : 𝔔₁ x y → 𝔔₂ μx μy
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open REMAPR ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record REMAPR2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (x y : 𝔒₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : 𝔒₁ → 𝔒₁ → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : Ø 𝔬₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (μ : 𝔒₁ → 𝔒₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : 𝔒₂ → 𝔒₂ → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   : Ø 𝔬₁ ∙̂ 𝔮₁ ∙̂ 𝔬₂ ∙̂ 𝔮₂ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     REMAP2 : 𝔔₁ x y → 𝔔₂ (μ x) (μ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open REMAPR2 ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : 𝔒 → 𝔒 → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : 𝔒 → 𝔒 → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓢ymmetry = 𝓡₃ _ _ 𝔔₁ (λ x y _ → 𝔔₂ y x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓼ymmetry = ∀ {x y} → 𝔔₁ x y → 𝔔₂ y x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Symmetry : Ø 𝔬 ∙̂ 𝔮₁ ∙̂ 𝔮₂ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓢ymmetry
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     symmetry : 𝓼ymmetry
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     symmetry = 𝓻₃ _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓜ap = 𝓡₃ _ _ 𝔔₁ (λ x y _ → 𝔔₂ x y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓶ap = ∀ {x y} → 𝔔₁ x y → 𝔔₂ x y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Map : Ø 𝔬 ∙̂ 𝔮₁ ∙̂ 𝔮₂ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓜ap
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     map : 𝓶ap
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     map = 𝓻₃ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Map' ⦃ _ : 𝓜ap ⦄ : Ø 𝔬 ∙̂ 𝔮₁ ∙̂ 𝔮₂ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     map' : 𝓶ap
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     map' 𝔔₁xy = 𝓻₃ _ _ 𝔔₁xy
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Map'' ⦃ ⋆ : 𝓜ap ⦄ : Ø 𝔬 ∙̂ 𝔮₁ ∙̂ 𝔮₂ where map'' = λ {x y} 𝔔₁xy → 𝓻₃ ⦃ ⋆ ⦄ x y 𝔔₁xy
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Symmetry ⦃ … ⦄ public hiding (⋆)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Map ⦃ … ⦄ public hiding (⋆)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Map' ⦃ … ⦄ public
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Map'' ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : 𝔒 → 𝔒 → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : 𝔒 → 𝔒 → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₃ : 𝔒 → 𝔒 → Ø 𝔮₃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓣ransitivity! :
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (∀ {𝔬₀} (𝔒₀ : Ø 𝔬₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {𝔬₁} (𝔒₁ : 𝔒₀ → Ø 𝔬₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {𝔬₂} (𝔒₂ : ∀ x₀ → 𝔒₁ x₀ → Ø 𝔬₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {𝔬₃} (𝔒₃ : ∀ x₀ x₁ → 𝔒₂ x₀ x₁ → Ø 𝔬₃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {𝔬₄} (𝔒₄ : ∀ x₀ x₁ x₂ → 𝔒₃ x₀ x₁ x₂ → Ø 𝔬₄)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {𝔬₅} (𝔒₅ : ∀ x₀ x₁ x₂ x₃ → 𝔒₄ x₀ x₁ x₂ x₃ → Ø 𝔬₅)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Ø 𝔬 ∙̂ 𝔮₁ ∙̂ 𝔮₂ ∙̂ 𝔮₃ -- Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ 𝔬₄ ∙̂ 𝔬₅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓣ransitivity! R = R 𝔒 (λ _ → 𝔒) ((λ x y → 𝔔₁ x y)) _ (λ _ y _ z → 𝔔₂ y z) (λ x _ _ z _ → 𝔔₃ x z) -- R _ _ (λ x y → 𝔔₁ x y) _ (λ _ y _ z → 𝔔₂ y z) (λ x _ _ z _ → 𝔔₃ x z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓣ransitivity = 𝓣ransitivity! 𝓡₅ -- 𝓡₅ _ _ (λ x y → 𝔔₁ x y) _ (λ _ y _ z → 𝔔₂ y z) (λ x _ _ z _ → 𝔔₃ x z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓽ransitivity = ∀ {x y} → 𝔔₁ x y → ∀ {z} → 𝔔₂ y z → 𝔔₃ x z
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓣ransitivity-I₁ = 𝓣ransitivity! 𝓡₅-I₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓣ransitivity-I₂ = 𝓣ransitivity! 𝓡₅-I₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Transitivity : Ø 𝔬 ∙̂ 𝔮₁ ∙̂ 𝔮₂ ∙̂ 𝔮₃ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⦃ ⋆ ⦄ : 𝓣ransitivity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     transitivity : 𝓽ransitivity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     transitivity 𝔔₁xy = 𝓻₅ _ _ 𝔔₁xy _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   transitivity' : ⦃ _ : 𝓣ransitivity ⦄ → 𝓽ransitivity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   transitivity' f g = 𝓻₅ _ _ f _ g
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Transitivity-I₁ : Ø 𝔬 ∙̂ 𝔮₁ ∙̂ 𝔮₂ ∙̂ 𝔮₃ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⋆ : 𝓣ransitivity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     instance _ = ⋆
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     transitivity-I₁ : 𝓽ransitivity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     transitivity-I₁ 𝔔₁xy = 𝓻₅ _ _ 𝔔₁xy _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Transitivity-I₂ : Ø 𝔬 ∙̂ 𝔮₁ ∙̂ 𝔮₂ ∙̂ 𝔮₃ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field ⋆ : 𝓣ransitivity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     instance _ = ⋆
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     transitivity-I₂ : 𝓽ransitivity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     transitivity-I₂ 𝔔₁xy = 𝓻₅ _ _ 𝔔₁xy _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Transitivity ⦃ … ⦄ public hiding (⋆)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Transitivity-I₁ ⦃ … ⦄ public hiding (⋆)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open Transitivity-I₂ ⦃ … ⦄ public hiding (⋆)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {𝔔₁ : 𝔒 → 𝔒 → Ø 𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {𝔔₂ : 𝔒 → 𝔒 → Ø 𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {𝔔₃ : 𝔒 → 𝔒 → Ø 𝔮₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   transitivity'' : ⦃ _ : 𝓣ransitivity 𝔔₁ 𝔔₂ 𝔔₃ ⦄ → 𝓽ransitivity 𝔔₁ 𝔔₂ 𝔔₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   transitivity'' f g = 𝓻₅ _ _ f _ g
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   transitivity''2 : ⦃ _ : 𝓣ransitivity 𝔔₁ 𝔔₂ 𝔔₃ ⦄ → 𝓽ransitivity 𝔔₁ 𝔔₂ 𝔔₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   transitivity''2 f g = 𝓻₅ _ _ f _ g
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   transitivity''3 : ⦃ _ : 𝓣ransitivity 𝔔₁ 𝔔₂ 𝔔₃ ⦄ → 𝓽ransitivity 𝔔₁ 𝔔₂ 𝔔₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   transitivity''3 f g = 𝓻₅ _ _ f _ g

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔 : ∀ {𝔬} {𝔒 : Ø 𝔬} → 𝔒 → 𝔒 → Ø 𝔮)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓒ongruity⋆ = 𝓡₆ _ _ (λ (A : Ø a) (B : Ø b) → A → B) _ _ (λ _ _ _ x y → 𝔔 x y) (λ _ _ f x y _ → 𝔔 (f x) (f y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓬ongruity⋆ = ∀ {A : Ø a} {B : Ø b} → (f : A → B) → ∀ {x y} → 𝔔 x y → 𝔔 (f x) (f y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Congruity⋆ : Ø 𝔮 ∙̂ ↑̂ (a ∙̂ b) where field congruity⋆ : 𝓬ongruity⋆
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Congruity⋆ ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₁} {𝔒₁ : Ø 𝔬₁} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : 𝔒₁ → 𝔒₁ → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬₂} {𝔒₂ : Ø 𝔬₂} {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : 𝔒₂ → 𝔒₂ → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓒ongruity = 𝓡₄ (_ → _) _ _ (λ _ x y → 𝔔₁ x y) (λ f x y _ → 𝔔₂ (f x) (f y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓬ongruity = ∀ (f : _ → _) → ∀ {x y} → 𝔔₁ x y → 𝔔₂ (f x) (f y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Congruity : Ø 𝔬₁ ∙̂ 𝔮₁ ∙̂ 𝔬₂ ∙̂ 𝔮₂ where field congruity : 𝓬ongruity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Congruity ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : ((o : 𝔒) → 𝔓 o) → ((o : 𝔒) → 𝔓 o) → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : ((o : 𝔒) → 𝔓 o → 𝔓 o) → ((o : 𝔒) → 𝔓 o) → ((o : 𝔒) → 𝔓 o) → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓒̇ongruity = 𝓡₄ ((o : 𝔒) → 𝔓 o → 𝔓 o) _ _ (λ _ x y → 𝔔₁ x y) (λ f x y _ → 𝔔₂ f x y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓬̇ongruity = ∀ (f : (o : 𝔒) → 𝔓 o → 𝔓 o) → ∀ {x y : (o : 𝔒) → 𝔓 o} → 𝔔₁ x y → 𝔔₂ f x y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Ċongruity : Ø 𝔬 ∙̂ 𝔭 ∙̂ 𝔮₁ ∙̂ 𝔮₂ where field ċongruity : 𝓬̇ongruity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Ċongruity ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔪}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔐 : 𝔒 → 𝔒 → Ø 𝔪)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : ∀ {x y} → 𝔐 x y → 𝔐 x y → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₃ : ∀ {x y} → 𝔐 x y → 𝔐 x y → ∀ {z} (g₁ g₂ : 𝔐 y z) → Ø 𝔮₃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓔xtensionality = 𝓡₉ _ _ _ _ (λ x y (f₁ : 𝔐 x y) (f₂ : 𝔐 x y) → 𝔔₁ f₁ f₂) _ (λ _ y _ _ _ z → 𝔐 y z) _ (λ _ _ _ _ _ _ g₁ g₂ → 𝔔₂ g₁ g₂) (λ _ _ f₁ f₂ _ _ g₁ g₂ _ → 𝔔₃ f₁ f₂ g₁ g₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓮xtensionality = ∀ {x y} {f₁ f₂ : 𝔐 x y} → 𝔔₁ f₁ f₂ → ∀ {z} {g₁ g₂ : 𝔐 y z} → 𝔔₂ g₁ g₂ → 𝔔₃ f₁ f₂ g₁ g₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Extensionality : Ø 𝔬 ∙̂ 𝔪 ∙̂ 𝔮₁ ∙̂ 𝔮₂ ∙̂ 𝔮₃ where field extensionality : 𝓮xtensionality
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Extensionality ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔬} {𝔒 : Ø 𝔬} {𝔮₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₁ : 𝔒 → 𝔒 → Ø 𝔮₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₂}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₂ : ∀ {x y} → 𝔔₁ x y → 𝔔₁ x y → Ø 𝔮₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₃}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₃ : ∀ {x y} {f₁ f₂ : 𝔔₁ x y} → 𝔔₂ f₁ f₂ → ∀ {z} → 𝔔₁ y z → 𝔔₁ y z → Ø 𝔮₃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {𝔮₄}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔔₄ : ∀ {x y} {f₁ f₂ : 𝔔₁ x y} {q₂ : 𝔔₂ f₁ f₂} {z} {g₁ g₂ : 𝔔₁ y z} → 𝔔₃ q₂ g₁ g₂ → Ø 𝔮₄)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓔xtensionality = 𝓡₉ _ _ _ _ (λ x y (f₁ : 𝔔₁ x y) (f₂ : 𝔔₁ x y) → 𝔔₂ f₁ f₂) _ (λ _ y _ _ _ z → 𝔔₁ y z) _ (λ x y _ _ q₂ _ g₁ g₂ → 𝔔₃ q₂ g₁ g₂) (λ _ _ _ _ _ _ _ _ q₃ → 𝔔₄ q₃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓮xtensionality = ∀ {x y} {f₁ f₂ : 𝔔₁ x y} → (q₂ : 𝔔₂ f₁ f₂) → ∀ {z} {g₁ g₂ : 𝔔₁ y z} → (q₃ : 𝔔₃ q₂ g₁ g₂) → 𝔔₄ q₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Extensionality : Ø 𝔬 ∙̂ 𝔮₁ ∙̂ 𝔮₂ ∙̂ 𝔮₃ ∙̂ 𝔮₄ where field extensionality : 𝓮xtensionality

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓔xtensionality′ = 𝓔xtensionality 𝔐 𝔔₁ (λ _ g₁ g₂ → 𝔔₂ g₁ g₂) (λ {_ _ f₁ f₂ _ _ g₁ g₂} _ → 𝔔₃ f₁ f₂ g₁ g₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝓮xtensionality′ = 𝓮xtensionality 𝔐 𝔔₁ (λ _ g₁ g₂ → 𝔔₂ g₁ g₂) (λ {_ _ f₁ f₂ _ _ g₁ g₂} _ → 𝔔₃ f₁ f₂ g₁ g₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
