--{-# OPTIONS --show-implicit #-}
{-# OPTIONS --postfix-projections #-}
--{-# OPTIONS -v30 #-}
{-# OPTIONS --rewriting #-}
module Oscar.Property where

open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data

-- SetoidProposequality
module _ where

  module _ {𝔬} {𝔒 : Ø 𝔬} where

    instance

      𝓡eflexivityProposequality : 𝓡eflexivity Proposequality⟦ 𝔒 ⟧
      𝓡eflexivityProposequality .𝓡eflexivity.reflexivity = !

      𝓢ymmetryProposequality : 𝓢ymmetry Proposequality⟦ 𝔒 ⟧
      𝓢ymmetryProposequality .𝓢ymmetry.symmetry ∅ = !

      𝓣ransitivityProposequality : 𝓣ransitivity Proposequality⟦ 𝔒 ⟧
      𝓣ransitivityProposequality .𝓣ransitivity.transitivity ∅ = ¡

      IsEquivalenceProposequality : IsEquivalence Proposequality⟦ 𝔒 ⟧
      IsEquivalenceProposequality = ∁

  module _ {𝔬} (𝔒 : Ø 𝔬) where

    SetoidProposequality : Setoid _ _
    SetoidProposequality = ∁ Proposequality⟦ 𝔒 ⟧

module _ where

  instance

    𝓒ongruityProposequality : ∀ {a b} → 𝓒ongruity Proposequality a b
    𝓒ongruityProposequality .𝓒ongruity.congruity _ ∅ = !

    𝓒ongruity₂Proposequality : ∀ {a b c} → 𝓒ongruity₂ Proposequality a b c
    𝓒ongruity₂Proposequality .𝓒ongruity₂.congruity₂ _ ∅ ∅ = !

    [𝓣ransextensionality]Proposequality : ∀
      {a} {A : Ø a}
      {m} {_⊸_ : A → A → Ø m}
      → [𝓣ransextensionality] _⊸_ Proposequality
    [𝓣ransextensionality]Proposequality = ∁

    𝓣ransextensionalityProposequality : ∀
      {a} {A : Ø a}
      {m} {_⊸_ : A → A → Ø m}
      ⦃ _ : 𝓣ransitivity _⊸_ ⦄
      → 𝓣ransextensionality _⊸_ Proposequality
    𝓣ransextensionalityProposequality .𝓣ransextensionality.transextensionality = congruity₂ _

-- SetoidProposextensequality
module _ where

  module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} where

    instance

      𝓡eflexivityProposextensequality : 𝓡eflexivity Proposextensequality⟦ 𝔓 ⟧
      𝓡eflexivity.reflexivity 𝓡eflexivityProposextensequality _ = ∅

      𝓢ymmetryProposextensequality : 𝓢ymmetry Proposextensequality⟦ 𝔓 ⟧
      𝓢ymmetry.symmetry 𝓢ymmetryProposextensequality f₁≡̇f₂ x rewrite f₁≡̇f₂ x = ∅

      𝓣ransitivityProposextensequality : 𝓣ransitivity Proposextensequality⟦ 𝔓 ⟧
      𝓣ransitivity.transitivity 𝓣ransitivityProposextensequality f₁≡̇f₂ f₂≡̇f₃ x rewrite f₁≡̇f₂ x = f₂≡̇f₃ x

      IsEquivalenceProposextensequality : IsEquivalence Proposextensequality⟦ 𝔓 ⟧
      IsEquivalenceProposextensequality = ∁

  module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) where

    SetoidProposextensequality : Setoid _ _
    SetoidProposextensequality = ∁ Proposextensequality⟦ 𝔓 ⟧

module _ where

  instance

    𝓒̇ongruityProposextensequality : ∀ {a b} → 𝓒̇ongruity a b Proposextensequality
    𝓒̇ongruity.ċongruity 𝓒̇ongruityProposextensequality _ f≡̇g x rewrite f≡̇g x = ∅

module _ where

  module _
    {a}
    where

    instance

      𝓡eflexivityFunction : 𝓡eflexivity Function⟦ a ⟧
      𝓡eflexivity.reflexivity 𝓡eflexivityFunction = ¡

      𝓣ransitivityFunction : 𝓣ransitivity Function⟦ a ⟧
      𝓣ransitivity.transitivity 𝓣ransitivityFunction f g = g ∘ f

-- CategoryExtensionProposextensequality
module _ where

  module _
    {a} {A : Ø a} {b} {B : A → Ø b}
    where

    instance

      𝓡eflexivityExtension : 𝓡eflexivity (Extension B)
      𝓡eflexivity.reflexivity 𝓡eflexivityExtension = ¡

      𝓣ransitivityExtension : 𝓣ransitivity (Extension B)
      𝓣ransitivity.transitivity 𝓣ransitivityExtension f g = g ∘ f

      [𝓣ransassociativity]ExtensionProposextensequality : [𝓣ransassociativity] (Extension B) Proposextensequality
      [𝓣ransassociativity]ExtensionProposextensequality = ∁

      𝓣ransassociativityExtensionProposextensequality : 𝓣ransassociativity (Extension B) Proposextensequality
      𝓣ransassociativityExtensionProposextensequality .𝓣ransassociativity.transassociativity _ _ _ _ = !

      [𝓣ransextensionality]ExtensionProposextensequality : [𝓣ransextensionality] (Extension B) Proposextensequality
      [𝓣ransextensionality]ExtensionProposextensequality = ∁

      𝓣ransextensionalityExtensionProposextensequality : 𝓣ransextensionality (Extension B) Proposextensequality
      𝓣ransextensionalityExtensionProposextensequality .𝓣ransextensionality.transextensionality {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = g₁≡̇g₂ (f₂ x)

      [𝓣ransleftidentity]ExtensionProposextensequality : [𝓣ransleftidentity] (Extension B) Proposextensequality
      [𝓣ransleftidentity]ExtensionProposextensequality = ∁

      𝓣ransleftidentityExtensionProposextensequality : 𝓣ransleftidentity (Extension B) Proposextensequality
      𝓣ransleftidentityExtensionProposextensequality .𝓣ransleftidentity.transleftidentity _ = !

      [𝓣ransrightidentity]ExtensionProposextensequality : [𝓣ransrightidentity] (Extension B) Proposextensequality
      [𝓣ransrightidentity]ExtensionProposextensequality = ∁

      𝓣ransrightidentityExtensionProposextensequality : 𝓣ransrightidentity (Extension B) Proposextensequality
      𝓣ransrightidentityExtensionProposextensequality .𝓣ransrightidentity.transrightidentity _ = !

      -- -- {- TODO
      -- HasEquivalenceExtension : ∀ {x y : A} → HasEquivalence (Extension B x y) _
      -- HasEquivalenceExtension = ∁ Proposextensequality
      -- -- -}
      -- HasËquivalenceExtension : HasËquivalence (Extension B) _
      -- HasËquivalenceExtension = ∁ Proposextensequality

  module _
    {a} {A : Ø a} {b} {B : A → Ø b}
    where

    instance

      IsPrecategoryExtension : IsPrecategory (Extension B) Proposextensequality
      IsPrecategoryExtension = ∁

      IsCategoryExtension : IsCategory (Extension B) Proposextensequality
      IsCategoryExtension = ∁

  module _
    {a} {A : Ø a} {b} (B : A → Ø b)
    where

    PrecategoryExtension : Precategory _ _ _
    PrecategoryExtension = ∁ (Extension B) Proposextensequality

    CategoryExtension : Category _ _ _
    CategoryExtension = ∁ (Extension B) Proposextensequality

-- FunctorSubstitunctionProposextensequalityExtensionTermProposextensequality
module _
  {𝔬} {𝔒 : Ø 𝔬}
  where
  instance
    𝓢urjectionIdentity : 𝓢urjection 𝔒 𝔒
    𝓢urjectionIdentity .𝓢urjection.surjection = ¡

record Substitunction⌶ {𝔭} (𝔓 : Ø 𝔭) : Ø₀ where
  constructor ∁
  no-eta-equality

  open Substitunction 𝔓
  open Term 𝔓

  private

    mutual

      𝓼urjectivitySubstitunctionExtensionTerm : 𝓼urjectivity Substitunction (Extension Term)
      𝓼urjectivitySubstitunctionExtensionTerm σ (i x) = σ x
      𝓼urjectivitySubstitunctionExtensionTerm σ leaf = leaf
      𝓼urjectivitySubstitunctionExtensionTerm σ (τ₁ fork τ₂) = 𝓼urjectivitySubstitunctionExtensionTerm σ τ₁ fork 𝓼urjectivitySubstitunctionExtensionTerm σ τ₂
      𝓼urjectivitySubstitunctionExtensionTerm σ (function p τs) = function p (𝓼urjectivitySubstitunctionExtensionTerms σ τs)

      𝓼urjectivitySubstitunctionExtensionTerms : ∀ {N} → 𝓼urjectivity Substitunction (Extension $ Terms N)
      𝓼urjectivitySubstitunctionExtensionTerms σ ∅ = ∅
      𝓼urjectivitySubstitunctionExtensionTerms σ (τ , τs) = 𝓼urjectivitySubstitunctionExtensionTerm σ τ , 𝓼urjectivitySubstitunctionExtensionTerms σ τs

  instance

    [𝓢urjectivity]SubstitunctionExtensionTerm : [𝓢urjectivity] Substitunction (Extension Term)
    [𝓢urjectivity]SubstitunctionExtensionTerm = ∁

    𝓢urjectivitySubstitunctionExtensionTerm : 𝓢urjectivity Substitunction (Extension Term)
    𝓢urjectivitySubstitunctionExtensionTerm .𝓢urjectivity.surjectivity = 𝓼urjectivitySubstitunctionExtensionTerm

    [𝓢urjectivity]SubstitunctionExtensionTerms : ∀ {N} → [𝓢urjectivity] Substitunction (Extension $ Terms N)
    [𝓢urjectivity]SubstitunctionExtensionTerms = ∁

    𝓢urjectivitySubstitunctionExtensionTerms : ∀ {N} → 𝓢urjectivity Substitunction (Extension $ Terms N)
    𝓢urjectivitySubstitunctionExtensionTerms .𝓢urjectivity.surjectivity = 𝓼urjectivitySubstitunctionExtensionTerms

  instance

    𝓣ransitivitySubstitunction : 𝓣ransitivity Substitunction
    𝓣ransitivitySubstitunction .𝓣ransitivity.transitivity f g = surjectivity g ∘ f

    HasEquivalenceSubstitunction : ∀ {x y} → HasEquivalence (Substitunction x y) _
    HasEquivalenceSubstitunction = ∁ Proposextensequality

    HasEquivalenceExtensionTerm : ∀ {x y} → HasEquivalence (Extension Term x y) _
    HasEquivalenceExtensionTerm = ∁ Proposextensequality

    HasEquivalenceExtensionTerms : ∀ {N x y} → HasEquivalence (Extension (Terms N) x y) _
    HasEquivalenceExtensionTerms = ∁ Proposextensequality

  private

    mutual
      -- TODO
      -- 𝓼urjextensionalitySubstitunctionExtensionTerm : 𝓼urjextensionality Substitunction _≈_ (Extension Term) (λ {x} {y} → _≈̈_ {x = x} {y})
      --𝓼urjextensionalitySubstitunctionExtensionTerm : 𝓼urjextensionality Substitunction _≈_ (Extension Term) (λ {x} {y} → _≈̈_ {x = x} {y}) -- (λ {x y} → _≈̈_ ⦃ HasËquivalenceExtension ⦄ {x} {_})
      -- 𝓼urjextensionalitySubstitunctionExtensionTerm : 𝓼urjextensionality Substitunction _≈_ (Extension Term) (λ {x y} → _≈_ ⦃ HasEquivalenceExtension {x = x} {y = y} ⦄)
      -- 𝓼urjextensionalitySubstitunctionExtensionTerm : 𝓼urjextensionality Substitunction _≈_ (Extension Term) (λ {x y} → _≈_ {𝔒 = Extension Term x y})
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

    [𝓢urjidentity]SubstitunctionExtensionTerm : [𝓢urjidentity] Substitunction (Extension Term) _≈_ _ _ _
    [𝓢urjidentity]SubstitunctionExtensionTerm = ∁ Substitunction (Extension Term) _≈_

    𝓢urjidentitySubstitunctionExtensionTerm : 𝓢urjidentity Substitunction (Extension Term) _≈_
    𝓢urjidentitySubstitunctionExtensionTerm .𝒮urjidentity.surjidentity = 𝓼urjidentitySubstitunctionExtensionTerm

    [𝓢urjidentity]SubstitunctionExtensionTerms : ∀ {N} → [𝓢urjidentity] Substitunction (Extension $ Terms N) _≈_ _ _ _
    [𝓢urjidentity]SubstitunctionExtensionTerms {N} = ∁ Substitunction (Extension $ Terms N) _≈_

    𝓢urjidentitySubstitunctionExtensionTerms : ∀ {N} → 𝓢urjidentity Substitunction (Extension $ Terms N) _≈_
    𝓢urjidentitySubstitunctionExtensionTerms .𝒮urjidentity.surjidentity = 𝓼urjidentitySubstitunctionExtensionTerms

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

module SubstitunctionØ {𝔭} (𝔓 : Ø 𝔭) where

  open Substitunction 𝔓
  open Term 𝔓

  open Substitunction⌶ (Substitunction⌶ 𝔓 ∋ ∁)

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

open SubstitunctionØ public


-- CategoryAListProposequality
module _ where

  module _ {a} {A : ¶ → Set a} where

    private AList = Descender⟨ A ⟩

    instance

      𝓡eflexivityAList : 𝓡eflexivity AList
      𝓡eflexivity.reflexivity 𝓡eflexivityAList = ∅

      𝓣ransitivityAList : 𝓣ransitivity AList
      𝓣ransitivityAList .𝓣ransitivity.transitivity f ∅ = f
      𝓣ransitivityAList .𝓣ransitivity.transitivity f (x , g) = x , g ∙ f

  --    HasEquivalenceAList : HasEquivalence AList
  --     MorphismEquivalence⌶AList : MorphismEquivalence AList _
  --     MorphismEquivalence.morphismEquivalence MorphismEquivalence⌶AList = Proposequality

      [𝓣ransassociativity]AList : [𝓣ransassociativity] AList Proposequality
      [𝓣ransassociativity]AList = ∁

      𝓣ransassociativityAList : 𝓣ransassociativity AList Proposequality
      𝓣ransassociativityAList .𝓣ransassociativity.transassociativity f g ∅ = ∅
      𝓣ransassociativityAList .𝓣ransassociativity.transassociativity f g (x , h) = congruity (x ,_) $ h ⟨∙ _ ⟨∙ _

      IsPrecategoryAList : IsPrecategory AList Proposequality
      IsPrecategoryAList = ∁

      [𝓣ransleftidentity]AList : [𝓣ransleftidentity] AList Proposequality
      [𝓣ransleftidentity]AList = ∁

      𝓣ransleftidentityAList : 𝓣ransleftidentity AList Proposequality
      𝓣ransleftidentityAList .𝓣ransleftidentity.transleftidentity = ∅

      [𝓣ransrightidentity]AList : [𝓣ransrightidentity] AList Proposequality
      [𝓣ransrightidentity]AList = ∁

      𝓣ransrightidentityAList : 𝓣ransrightidentity AList Proposequality
      𝓣ransrightidentityAList .𝓣ransrightidentity.transrightidentity {f = ∅} = ∅
      𝓣ransrightidentityAList .𝓣ransrightidentity.transrightidentity {f = x , f} = congruity (x ,_) transrightidentity

      IsCategoryAList : IsCategory AList Proposequality
      IsCategoryAList = ∁

  module _ {a} (A : ¶ → Ø a) where

    private AList = Descender⟨ A ⟩

    PrecategoryAListProposequality : Precategory _ _ _
    PrecategoryAListProposequality = ∁ AList Proposequality

    CategoryAListProposequality : Category _ _ _
    CategoryAListProposequality = ∁ AList Proposequality


module Substitist⌶ {𝔭} {𝔓 : Ø 𝔭} where

  open Substitunction 𝔓
  open Term 𝔓
  open Substitist 𝔓
  open Substitunction⌶ (Substitunction⌶ 𝔓 ∋ record {})

  postulate
    _for_ : ∀ {n} (t' : Term n) (x : Fin (↑ n)) -> Fin (↑ n) -> Term n

  instance

    [𝓢urjectivity]Substitist,Substitunction : [𝓢urjectivity] Substitist Substitunction
    [𝓢urjectivity]Substitist,Substitunction = ∁

    𝓢urjectivitySubstitist,Substitunction : 𝓢urjectivity Substitist Substitunction
    𝓢urjectivitySubstitist,Substitunction .𝓢urjectivity.surjectivity ∅ = i
    𝓢urjectivitySubstitist,Substitunction .𝓢urjectivity.surjectivity ((x , t) , σ) = surjectivity σ ∙ (t for x)

    [𝓢urjtranscommutativity]Substitist,Substitunction : [𝓢urjtranscommutativity] Substitist Substitunction _≈_
    [𝓢urjtranscommutativity]Substitist,Substitunction = ∁

    𝓢urjtranscommutativitySubstitist,Substitunction : 𝓢urjtranscommutativity Substitist Substitunction _≈_
    𝓢urjtranscommutativitySubstitist,Substitunction = {!!}

module _ where

  instance

    𝓕mapMaybe : ∀ {𝔬₁ 𝔬₂} → 𝓕map Maybe 𝔬₁ 𝔬₂
    𝓕mapMaybe .𝓕map.fmap f ∅ = ∅
    𝓕mapMaybe .𝓕map.fmap f (↑ x) = ↑ f x

    𝓟ureMaybe : ∀ {𝔬} → 𝓟ure (Maybe {𝔬})
    𝓟ureMaybe .𝓟ure.pure = ↑_

    𝓐pplyMaybe : ∀ {𝔬₁ 𝔬₂} → 𝓐pply Maybe 𝔬₁ 𝔬₂
    𝓐pplyMaybe .𝓐pply.apply ∅ x = ∅
    𝓐pplyMaybe .𝓐pply.apply (↑ f) x = fmap f x

module _ where

  instance

    𝓢uccessor₀¶ : 𝓢uccessor₀ ¶
    𝓢uccessor₀¶ .𝓢uccessor₀.successor₀ = ↑_

    [𝓢uccessor₁]Fin : [𝓢uccessor₁] Fin
    [𝓢uccessor₁]Fin = ∁

    𝓢uccessor₁Fin : 𝓢uccessor₁ Fin
    𝓢uccessor₁Fin .𝓢uccessor₁.successor₁ = ↑_

    [𝓘njectivity₁]Fin : ∀ {m} → [𝓘njectivity₁] (λ (_ : Fin m) → Fin (⇑₀ m)) Proposequality Proposequality
    [𝓘njectivity₁]Fin = ∁

    𝓘njectivity₁Fin : ∀ {m} → 𝓘njectivity₁ (λ (_ : Fin m) → Fin (⇑₀ m)) Proposequality Proposequality
    𝓘njectivity₁Fin .𝓘njectivity₁.injectivity₁ ∅ = ∅

    [𝓣hick]Fin,Fin : [𝓣hick] Fin Fin
    [𝓣hick]Fin,Fin = ∁

    𝓣hickFin,Fin : 𝓣hick Fin Fin
    𝓣hickFin,Fin .𝓣hick.thick {∅} () ∅
    𝓣hickFin,Fin .𝓣hick.thick {↑ _} _ ∅ = ∅
    𝓣hickFin,Fin .𝓣hick.thick ∅ (↑ y) = y
    𝓣hickFin,Fin .𝓣hick.thick (↑ x) (↑ y) = ↑ thick x y

    [𝓣hin]Fin,Fin : [𝓣hin] Fin Fin
    [𝓣hin]Fin,Fin = ∁

    𝓣hinFin,Fin : 𝓣hin Fin Fin
    𝓣hinFin,Fin .𝓣hin.thin ∅ = ↑_
    𝓣hinFin,Fin .𝓣hin.thin (↑ x) ∅ = ∅
    𝓣hinFin,Fin .𝓣hin.thin (↑ x) (↑ y) = ↑ (thin x y)

    [𝓘njectivity₂,₁]ThinFinFin : ∀ {m} → [𝓘njectivity₂,₁] (𝔱hin Fin Fin m) Proposequality Proposequality
    [𝓘njectivity₂,₁]ThinFinFin = ∁

    𝓘njectivity₂,₁ThinFinFin : ∀ {m} → 𝓘njectivity₂,₁ (𝔱hin Fin Fin m) Proposequality Proposequality
    𝓘njectivity₂,₁ThinFinFin .𝓘njectivity₂,₁.injectivity₂,₁ ∅ ∅ = ∅
    𝓘njectivity₂,₁ThinFinFin .𝓘njectivity₂,₁.injectivity₂,₁ (↑ _) {∅}    {∅} _ = ∅
    𝓘njectivity₂,₁ThinFinFin .𝓘njectivity₂,₁.injectivity₂,₁ (↑ _) {∅}    {↑ _} ()
    𝓘njectivity₂,₁ThinFinFin .𝓘njectivity₂,₁.injectivity₂,₁ (↑ _) {↑ _}  {∅}   ()
    𝓘njectivity₂,₁ThinFinFin .𝓘njectivity₂,₁.injectivity₂,₁ (↑ x) {↑ _}  {↑ _} = congruity ↑_ ∘ injectivity₂,₁ x ∘ injectivity₁[ Proposequality ]

    [𝓒heck]FinFinMaybe : [𝓒heck] Fin Fin Maybe
    [𝓒heck]FinFinMaybe = ∁

    𝓒heckFinFinMaybe : 𝓒heck Fin Fin Maybe
    𝓒heckFinFinMaybe .𝓒heck.check ∅ ∅ = ∅
    𝓒heckFinFinMaybe .𝓒heck.check ∅ (↑ y) = ↑ y
    𝓒heckFinFinMaybe .𝓒heck.check {∅} (↑ ()) _
    𝓒heckFinFinMaybe .𝓒heck.check {↑ _} (↑ x) ∅ = ↑ ∅
    𝓒heckFinFinMaybe .𝓒heck.check {↑ _} (↑ x) (↑ y) = fmap ¶⟨<_⟩.↑_ $ check x y

    [𝓣hick/thin=1]FinFin : [𝓣hick/thin=1] Fin Fin Proposequality
    [𝓣hick/thin=1]FinFin = ∁

    𝓣hick/thin=1FinFin : 𝓣hick/thin=1 Fin Fin Proposequality
    𝓣hick/thin=1FinFin .𝓣hick/thin=1.thick/thin=1 x ∅ = ∅
    𝓣hick/thin=1FinFin .𝓣hick/thin=1.thick/thin=1 ∅ (↑ y) = ∅
    𝓣hick/thin=1FinFin .𝓣hick/thin=1.thick/thin=1 (↑ x) (↑ y) = congruity ↑_ (thick/thin=1 x y)

    [𝓒heck/thin=1FinFin] : [𝓒heck/thin=1] Fin Fin Maybe Proposequality
    [𝓒heck/thin=1FinFin] = ∁

    𝓒heck/thin=1FinFin : 𝓒heck/thin=1 Fin Fin Maybe Proposequality
    𝓒heck/thin=1FinFin .𝓒heck/thin=1.check/thin=1 ∅ y = ∅
    𝓒heck/thin=1FinFin .𝓒heck/thin=1.check/thin=1 (↑ x) ∅ = ∅
    𝓒heck/thin=1FinFin .𝓒heck/thin=1.check/thin=1 (↑ x) (↑ y) rewrite check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x y = ∅

    IsThickandthinFinFin : IsThickandthin Fin Fin Proposequality Maybe Proposequality
    IsThickandthinFinFin = ∁

  ThickandthinFinFin : Thickandthin _ _ _ _ _ _
  ThickandthinFinFin = ∁ Fin Fin Proposequality Maybe Proposequality


module _ where

  instance

    𝓘njection₂Vec : ∀ {N} {𝔭} {𝔓 : ¶ → Ø 𝔭} → 𝓘njection₂ (λ (x : 𝔓 N) (_ : Vec⟨ 𝔓 ⟩ N) → Vec⟨ 𝔓 ⟩ (⇑₀ N))
    𝓘njection₂Vec .𝓘njection₂.injection₂ = _,_

    [𝓘njectivity₂,₀,₁]Vec : ∀ {N} {𝔭} {𝔓 : ¶ → Ø 𝔭} → [𝓘njectivity₂,₀,₁] (λ (x : 𝔓 N) (_ : Vec⟨ 𝔓 ⟩ N) → Vec⟨ 𝔓 ⟩ (⇑₀ N)) Proposequality Proposequality
    [𝓘njectivity₂,₀,₁]Vec = ∁

    𝓘njectivity₂,₀,₁Vec :   ∀ {N} {𝔭} {𝔓 : ¶ → Ø 𝔭} → 𝓘njectivity₂,₀,₁   (λ (x : 𝔓 N) (_ : Vec⟨ 𝔓 ⟩ N) → Vec⟨ 𝔓 ⟩ (⇑₀ N)) Proposequality Proposequality
    𝓘njectivity₂,₀,₁Vec .𝓘njectivity₂,₀,₁.injectivity₂,₀,₁ ∅ = ∅

    [𝓘njectivity₂,₀,₂]Vec : ∀ {N} {𝔭} {𝔓 : ¶ → Ø 𝔭} → [𝓘njectivity₂,₀,₂] (λ (x : 𝔓 N) (_ : Vec⟨ 𝔓 ⟩ N) → Vec⟨ 𝔓 ⟩ (⇑₀ N)) Proposequality Proposequality
    [𝓘njectivity₂,₀,₂]Vec = ∁

    𝓘njectivity₂,₀,₂Vec : ∀ {N} {𝔭} {𝔓 : ¶ → Ø 𝔭} → 𝓘njectivity₂,₀,₂ (λ (x : 𝔓 N) (_ : Vec⟨ 𝔓 ⟩ N) → Vec⟨ 𝔓 ⟩ (⇑₀ N)) Proposequality Proposequality
    𝓘njectivity₂,₀,₂Vec .𝓘njectivity₂,₀,₂.injectivity₂,₀,₂ ∅ = ∅

module _ {𝔭} {𝔓 : Ø 𝔭} where

  open Substitunction 𝔓
  open Term 𝔓

  private

    mutual

      𝓼urjectivityExtensionFinExtensionTerm : 𝓼urjectivity (Extension Fin) (Extension Term)
      𝓼urjectivityExtensionFinExtensionTerm x (i y) = i (x y)
      𝓼urjectivityExtensionFinExtensionTerm x leaf = leaf
      𝓼urjectivityExtensionFinExtensionTerm x (l fork r) = 𝓼urjectivityExtensionFinExtensionTerm x l fork 𝓼urjectivityExtensionFinExtensionTerm x r
      𝓼urjectivityExtensionFinExtensionTerm x (function f ts) = function f $ 𝓼urjectivityExtensionFinExtensionTerms x ts

      𝓼urjectivityExtensionFinExtensionTerms : ∀ {N} → 𝓼urjectivity (Extension Fin) (Extension $ Terms N)
      𝓼urjectivityExtensionFinExtensionTerms x ∅ = ∅
      𝓼urjectivityExtensionFinExtensionTerms x (t , ts) = 𝓼urjectivityExtensionFinExtensionTerm x t , 𝓼urjectivityExtensionFinExtensionTerms x ts

  instance

    [𝓢urjectivity]ExtensionFinExtensionTerm : [𝓢urjectivity] (Extension Fin) (Extension Term)
    [𝓢urjectivity]ExtensionFinExtensionTerm = ∁

    𝓢urjectivityExtensionFinExtensionTerm : 𝓢urjectivity (Extension Fin) (Extension Term)
    𝓢urjectivityExtensionFinExtensionTerm .𝓢urjectivity.surjectivity = 𝓼urjectivityExtensionFinExtensionTerm

    [𝓢urjectivity]ExtensionFinExtensionTerms : ∀ {N} → [𝓢urjectivity] (Extension Fin) (Extension $ Terms N)
    [𝓢urjectivity]ExtensionFinExtensionTerms = ∁

    𝓢urjectivityExtensionFinExtensionTerms : ∀ {N} → 𝓢urjectivity (Extension Fin) (Extension $ Terms N)
    𝓢urjectivityExtensionFinExtensionTerms .𝓢urjectivity.surjectivity = 𝓼urjectivityExtensionFinExtensionTerms

  instance

    [𝓣hick]FinTerm : [𝓣hick] Fin Term
    [𝓣hick]FinTerm = ∁

    𝓣hickFinTerm : 𝓣hick Fin Term
    𝓣hickFinTerm .𝓣hick.thick x t = surjectivity (thick x) $ t

    [𝓣hick]FinTerms : ∀ {N} → [𝓣hick] Fin (Terms N)
    [𝓣hick]FinTerms = ∁

    𝓣hickFinTerms : ∀ {N} → 𝓣hick Fin (Terms N)
    𝓣hickFinTerms .𝓣hick.thick x t = surjectivity (thick x) $ t

    [𝓣hin]FinTerm : [𝓣hin] Fin Term
    [𝓣hin]FinTerm = ∁

    𝓣hinFinTerm : 𝓣hin Fin Term
    𝓣hinFinTerm .𝓣hin.thin = surjectivity ∘ thin

    [𝓣hin]FinTerms : ∀ {N} → [𝓣hin] Fin (Terms N)
    [𝓣hin]FinTerms = ∁

    𝓣hinFinTerms : ∀ {N} → 𝓣hin Fin (Terms N)
    𝓣hinFinTerms .𝓣hin.thin = surjectivity ∘ thin

    [𝓘njectivity₂,₁]FinTerm : ∀ {m} → [𝓘njectivity₂,₁] (𝔱hin Fin Term m) Proposequality Proposequality
    [𝓘njectivity₂,₁]FinTerm = ∁

    𝓘njection₂FinTerm : ∀ {m} → 𝓘njection₂ (λ (_ : ¶⟨< ↑ m ⟩) (_ : Term m) → Term (↑ m))
    𝓘njection₂FinTerm {m} .𝓘njection₂.injection₂ = thin

    [𝓘njectivity₂,₁]FinTerms : ∀ {N m} → [𝓘njectivity₂,₁] (𝔱hin Fin (Terms N) m) Proposequality Proposequality
    [𝓘njectivity₂,₁]FinTerms = ∁

    𝓘njection₂FinTerms : ∀ {N m} → 𝓘njection₂ (λ (_ : ¶⟨< ↑ m ⟩) (_ : Terms N m) → Terms N (↑ m))
    𝓘njection₂FinTerms {m} .𝓘njection₂.injection₂ = thin




    𝓘njection₁-TermI : ∀ {n} → 𝓘njection₁ (λ (_ : ¶⟨< n ⟩) → Term n)
    𝓘njection₁-TermI .𝓘njection₁.injection₁ = i

    [𝓘njectivity₁]TermI : ∀ {n} → [𝓘njectivity₁] (λ (_ : ¶⟨< n ⟩) → Term n) Proposequality Proposequality
    [𝓘njectivity₁]TermI = ∁

    𝓘njectivity₁TermI : ∀ {n} → 𝓘njectivity₁ (λ (_ : ¶⟨< n ⟩) → Term n) Proposequality Proposequality
    𝓘njectivity₁TermI {n} .𝓘njectivity₁.injectivity₁ ∅ = ∅

    𝓘njection₂-TermFork : ∀ {n} → 𝓘njection₂ (λ (_ : Term n) (_ : Term n) → Term n)
    𝓘njection₂-TermFork .𝓘njection₂.injection₂ = _fork_

    [𝓘njection₂,₀,₁]-TermFork : ∀ {n} → [𝓘njectivity₂,₀,₁] (λ (_ : Term n) (_ : Term n) → Term n) Proposequality Proposequality
    [𝓘njection₂,₀,₁]-TermFork = ∁

    𝓘njection₂,₀,₁-TermFork : ∀ {n} → 𝓘njectivity₂,₀,₁ (λ (_ : Term n) (_ : Term n) → Term n) Proposequality Proposequality
    𝓘njection₂,₀,₁-TermFork .𝓘njectivity₂,₀,₁.injectivity₂,₀,₁ ∅ = ∅

    [𝓘njection₂,₀,₂]-TermFork : ∀ {n} → [𝓘njectivity₂,₀,₂] (λ (_ : Term n) (_ : Term n) → Term n) Proposequality Proposequality
    [𝓘njection₂,₀,₂]-TermFork = ∁

    𝓘njection₂,₀,₂-TermFork : ∀ {n} → 𝓘njectivity₂,₀,₂ (λ (_ : Term n) (_ : Term n) → Term n) Proposequality Proposequality
    𝓘njection₂,₀,₂-TermFork .𝓘njectivity₂,₀,₂.injectivity₂,₀,₂ ∅ = ∅

    𝓘njection₃TermFunction : ∀ {n} → 𝓘njection₃ (λ (_ : 𝔓) (N : ¶) (_ : Terms N n) → Term n)
    𝓘njection₃TermFunction {n} .𝓘njection₃.injection₃ p N ts = function p ts

    [𝓘njectivity₃,₀,₁]TermFunction : ∀ {n} → [𝓘njectivity₃,₀,₁] (λ (_ : 𝔓) (N : ¶) (_ : Terms N n) → Term n) Proposequality Proposequality
    [𝓘njectivity₃,₀,₁]TermFunction = ∁

    𝓘njectivity₃,₀,₁TermFunction : ∀ {n} → 𝓘njectivity₃,₀,₁ (λ (_ : 𝔓) (N : ¶) (_ : Terms N n) → Term n) Proposequality Proposequality
    𝓘njectivity₃,₀,₁TermFunction .𝓘njectivity₃,₀,₁.injectivity₃,₀,₁ ∅ = ∅

    [𝓘njectivity₃,₀,₂]TermFunction : ∀ {n} → [𝓘njectivity₃,₀,₂] (λ (_ : 𝔓) (N : ¶) (_ : Terms N n) → Term n) Proposequality Proposequality
    [𝓘njectivity₃,₀,₂]TermFunction = ∁

    𝓘njectivity₃,₀,₂TermFunction : ∀ {n} → 𝓘njectivity₃,₀,₂ (λ (_ : 𝔓) (N : ¶) (_ : Terms N n) → Term n) Proposequality Proposequality
    𝓘njectivity₃,₀,₂TermFunction .𝓘njectivity₃,₀,₂.injectivity₃,₀,₂ ∅ = ∅

    𝓘njection₂TermFunction : ∀ {N n} → 𝓘njection₂ (λ (_ : 𝔓) (_ : Terms N n) → Term n)
    𝓘njection₂TermFunction {N} {n} .𝓘njection₂.injection₂ p ts = function p ts

    [𝓘njectivity₂,₀,₂]TermFunction : ∀ {N n} → [𝓘njectivity₂,₀,₂] (λ (_ : 𝔓) (_ : Terms N n) → Term n) Proposequality Proposequality
    [𝓘njectivity₂,₀,₂]TermFunction = ∁

    𝓘njectivity₂,₀,₂TermFunction : ∀ {N n} → 𝓘njectivity₂,₀,₂ (λ (_ : 𝔓) (_ : Terms N n) → Term n) Proposequality Proposequality
    𝓘njectivity₂,₀,₂TermFunction .𝓘njectivity₂,₀,₂.injectivity₂,₀,₂ ∅ = ∅

  mutual

    instance

      𝓘njectivity₂,₁FinTerm : ∀ {m} → 𝓘njectivity₂,₁ (𝔱hin Fin Term m) Proposequality Proposequality -- ⦃ 𝓘njection₂FinTerm {m} ⦄
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ x {i _} {i _} eq = congruity i (injectivity₂,₁ x (injectivity₁[ Proposequality ] eq))
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {i _} {leaf} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {i _} {_ fork _} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {i _} {function _ _} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {leaf} {i _} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {leaf} {leaf} _ = ∅
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {leaf} {_ fork _} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {leaf} {function _ _} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {_ fork _} {i _} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {_ fork _} {leaf} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ x {y₁ fork y₂} {y₃ fork y₄} eq
        rewrite injectivity₂,₁ {_∼₂_ = Proposequality} x {y₁ = y₁} (injectivity₂,₀,₁[ Proposequality ] eq)
              | injectivity₂,₁ {_∼₂_ = Proposequality} x {y₁ = y₂} (injectivity₂,₀,₂[ Proposequality ] eq)
        = ∅
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {y₁ fork y₂} {function x₁ x₂} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {function _ _} {i x₃} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {function _ _} {leaf} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {function _ _} {y₂ fork y₃} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ x {function p1 {N1} ts1} {function p2 {N2} ts2} t₁≡t₂
        rewrite injectivity₃,₀,₁[ Proposequality ] {x₂ = p2} t₁≡t₂
        with injectivity₃,₀,₂[ Proposequality ] {y₂ = N2} t₁≡t₂
      … | ∅
        with injectivity₂,₀,₂[ Proposequality ] {y₂ = thin x ts2} t₁≡t₂
      … | ts₁≡ts₂ = congruity (function p2) (injectivity₂,₁ x ts₁≡ts₂)

      𝓘njectivity₂,₁FinTerms : ∀ {N m} → 𝓘njectivity₂,₁ (𝔱hin Fin (Terms N) m) Proposequality Proposequality -- ⦃ 𝓘njection₂FinTerms {N} {m} ⦄
      𝓘njectivity₂,₁FinTerms .𝓘njectivity₂,₁.injectivity₂,₁ x {∅} {∅} x₁ = ∅
      𝓘njectivity₂,₁FinTerms .𝓘njectivity₂,₁.injectivity₂,₁ x {_ , _} {t₂ , ts₂} eq
        rewrite injectivity₂,₁ {_∼₂_ = Proposequality} x {y₂ = t₂} (injectivity₂,₀,₁[ Proposequality ] eq)
              | injectivity₂,₁ {_∼₂_ = Proposequality} x {y₂ = ts₂} (injectivity₂,₀,₂[ Proposequality ] eq)
        = ∅

  instance

    [𝓒heck]FinTermMaybe : [𝓒heck] Fin Term Maybe
    [𝓒heck]FinTermMaybe = ∁

    [𝓒heck]FinTermsMaybe : ∀ {N} → [𝓒heck] Fin (Terms N) Maybe
    [𝓒heck]FinTermsMaybe = ∁

  mutual

    instance

      𝓒heckFinTermMaybe : 𝓒heck Fin Term Maybe
      𝓒heckFinTermMaybe .𝓒heck.check x (i y) = ⦇ i (check x y) ⦈
      𝓒heckFinTermMaybe .𝓒heck.check x leaf = ⦇ leaf ⦈
      𝓒heckFinTermMaybe .𝓒heck.check x (y₁ fork y₂) = ⦇ _fork_ (check x y₁) (check x y₂) ⦈
      𝓒heckFinTermMaybe .𝓒heck.check x (function p ts) = ⦇ (function p) (check x ts) ⦈

      𝓒heckFinTermsMaybe : ∀ {N} → 𝓒heck Fin (Terms N) Maybe
      𝓒heckFinTermsMaybe .𝓒heck.check _ ∅ = ⦇ ∅ ⦈
      𝓒heckFinTermsMaybe .𝓒heck.check x (t , ts) = ⦇ check x t , check x ts ⦈

  instance

    [𝓣hick/thin=1]FinTermProposequality : [𝓣hick/thin=1] Fin Term Proposequality
    [𝓣hick/thin=1]FinTermProposequality = ∁

    [𝓣hick/thin=1]FinTermsProposequality : ∀ {N} → [𝓣hick/thin=1] Fin (Terms N) Proposequality
    [𝓣hick/thin=1]FinTermsProposequality = ∁

  mutual

    instance

      𝓣hick/thin=1FinTermProposequality : 𝓣hick/thin=1 Fin Term Proposequality
      𝓣hick/thin=1FinTermProposequality .𝓣hick/thin=1.thick/thin=1 x (i y) rewrite thick/thin=1 {_≈_ = Proposequality} x y = ∅ -- congruity i $ thick/thin=1 x y
      𝓣hick/thin=1FinTermProposequality .𝓣hick/thin=1.thick/thin=1 x leaf = ∅
      𝓣hick/thin=1FinTermProposequality .𝓣hick/thin=1.thick/thin=1 x (y₁ fork y₂) = congruity₂ _fork_ (thick/thin=1 x y₁) (thick/thin=1 x y₂)
      𝓣hick/thin=1FinTermProposequality .𝓣hick/thin=1.thick/thin=1 x (function p ts) = congruity (function p) (thick/thin=1 x ts)

      𝓣hick/thin=1FinTermsProposequality : ∀ {N} → 𝓣hick/thin=1 Fin (Terms N) Proposequality
      𝓣hick/thin=1FinTermsProposequality .𝓣hick/thin=1.thick/thin=1 x ∅ = ∅
      𝓣hick/thin=1FinTermsProposequality .𝓣hick/thin=1.thick/thin=1 x (t , ts) = congruity₂ _,_ (thick/thin=1 x t) (thick/thin=1 x ts)

  instance

    [𝓒heck/thin=1]FinTermMaybe : [𝓒heck/thin=1] Fin Term Maybe Proposequality
    [𝓒heck/thin=1]FinTermMaybe = ∁

    [𝓒heck/thin=1]FinTermsMaybe : ∀ {N} → [𝓒heck/thin=1] Fin (Terms N) Maybe Proposequality
    [𝓒heck/thin=1]FinTermsMaybe = ∁

  mutual

    instance

      𝓒heck/thin=1FinTermMaybe : 𝓒heck/thin=1 Fin Term Maybe Proposequality
      𝓒heck/thin=1FinTermMaybe .𝓒heck/thin=1.check/thin=1 x (i y) rewrite check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x y = ∅
      𝓒heck/thin=1FinTermMaybe .𝓒heck/thin=1.check/thin=1 x leaf = ∅
      𝓒heck/thin=1FinTermMaybe .𝓒heck/thin=1.check/thin=1 x (y₁ fork y₂)
        rewrite check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x y₁
              | check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x y₂
        = ∅
      𝓒heck/thin=1FinTermMaybe .𝓒heck/thin=1.check/thin=1 x (function p ys) rewrite check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x ys = ∅

      𝓒heck/thin=1FinTermsMaybe : ∀ {N} → 𝓒heck/thin=1 Fin (Terms N) Maybe Proposequality
      𝓒heck/thin=1FinTermsMaybe .𝓒heck/thin=1.check/thin=1 x ∅ = ∅
      𝓒heck/thin=1FinTermsMaybe .𝓒heck/thin=1.check/thin=1 x (y , ys)
        rewrite check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x y
              | check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x ys
        = ∅

  instance

    IsThickandthinFinTerm : IsThickandthin Fin Term Proposequality Maybe Proposequality
    IsThickandthinFinTerm = ∁

    IsThickandthinFinTerms : ∀ {N} → IsThickandthin Fin (Terms N) Proposequality Maybe Proposequality
    IsThickandthinFinTerms = ∁

  ThickandthinFinTerm : Thickandthin _ _ _ _ _ _
  ThickandthinFinTerm = ∁ Fin Term Proposequality Maybe Proposequality

  ThickandthinFinTerms : ∀ N → Thickandthin _ _ _ _ _ _
  ThickandthinFinTerms N = ∁ Fin (Terms N) Proposequality Maybe Proposequality
