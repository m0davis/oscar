--{-# OPTIONS --show-implicit #-}
--{-# OPTIONS --postfix-projections #-}
--{-# OPTIONS -v30 #-}
--{-# OPTIONS --rewriting #-}
module Oscar.TerminationBughunt where

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

      --𝓣ransitivity²Proposequality : 𝓣ransitivity² Proposequality⟦ 𝔒 ⟧
      --𝓣ransitivity²Proposequality = ∁

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

      --𝓣ransitivity²Proposextensequality : 𝓣ransitivity² Proposextensequality⟦ 𝔓 ⟧
      --𝓣ransitivity²Proposextensequality = ∁

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

  --private
  module _ where

    mutual

      𝓼urjectivitySubstitunctionExtensionTerm : 𝓼urjectivity Substitunction (Extension Term)
      𝓼urjectivitySubstitunctionExtensionTerm σ (i x) = σ x
      𝓼urjectivitySubstitunctionExtensionTerm σ leaf = leaf
      𝓼urjectivitySubstitunctionExtensionTerm σ (τ₁ fork τ₂) = 𝓼urjectivitySubstitunctionExtensionTerm σ τ₁ fork 𝓼urjectivitySubstitunctionExtensionTerm σ τ₂
      𝓼urjectivitySubstitunctionExtensionTerm σ (function p τs) = function p (𝓼urjectivitySubstitunctionExtensionTerms σ τs)

      𝓼urjectivitySubstitunctionExtensionTerms : ∀ {N} → 𝓼urjectivity Substitunction (Extension $ Terms N)
      𝓼urjectivitySubstitunctionExtensionTerms σ ∅ = ∅
      𝓼urjectivitySubstitunctionExtensionTerms σ (τ , τs) = 𝓼urjectivitySubstitunctionExtensionTerm σ τ , 𝓼urjectivitySubstitunctionExtensionTerms σ τs

-- A dependent eliminator.

maybe : ∀ {a b} {A : Set a} {B : Maybe A → Set b} →
        ((x : A) → B (↑ x)) → B ∅ → (x : Maybe A) → B x
maybe j n (↑ x) = j x
maybe j n ∅  = n

-- A non-dependent eliminator.

maybe′ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → B → Maybe A → B
maybe′ = maybe

module _ {𝔭} {𝔓 : Ø 𝔭} where

  open Substitunction 𝔓
  open Term 𝔓
  open Substitist 𝔓
  open Substitunction⌶ (Substitunction⌶ 𝔓 ∋ record {})

  postulate _for_ : ∀ {n} (t' : Term n) (x : Fin (↑ n)) -> Fin (↑ n) -> Term n

  -- _for_ : ∀ {n} (t' : Term n) (x : Fin (↑ n)) -> Fin (↑ n) -> Term n
  -- (t for x) y = maybe′ i t (check {C = Maybe} x y)

postulate
  𝔓 : Ø₀

open Substitunction 𝔓
open Term 𝔓
open Substitist 𝔓
-- open Substitunction⌶ (Substitunction⌶ 𝔓 ∋ record {})

fmapMaybe : ∀ {𝔬₁ 𝔬₂} → 𝓯map Maybe 𝔬₁ 𝔬₂
fmapMaybe f ∅ = ∅
fmapMaybe f (↑ x) = ↑ f x

bindMaybe : ∀ {𝔬₁ 𝔬₂} → 𝓫ind Maybe 𝔬₁ 𝔬₂
bindMaybe ∅ _ = ∅
bindMaybe (↑ x) f = f x

_∃asub_/_ : ∀ {m} (a : ∃ Sub m) (t' : Term m) (x : Fin (↑ m)) → ∃ Sub (↑ m)
(n , σ) ∃asub t' / x = n , x / t' asub σ

postulate
  𝓼urjectivitySubstitunctionExtensionTerm' :
    -- ∀ {x y} → Substitunction x y → Extension Term x y -- surjection x ∼₂ surjection y
    𝓼urjectivity Substitunction (Extension Term)

⋆amguTerm! : ∀ {m} (s t : Term m) (acc : ∃ Sub m) -> Maybe (∃ Sub m)
⋆amguTerm! leaf leaf acc = ↑ acc
⋆amguTerm! leaf (function _ _) acc = ∅
⋆amguTerm! leaf (s' fork t') acc = ∅
⋆amguTerm! (s' fork t') leaf acc = ∅
⋆amguTerm! (s' fork t') (function _ _) acc = ∅
⋆amguTerm! (s1 fork s2) (t1 fork t2) acc = bindMaybe (⋆amguTerm! s1 t1 acc) (⋆amguTerm! s2 t2)
⋆amguTerm! (function fn₁ ts₁) leaf acc = ∅
⋆amguTerm! (function fn₁ {n₁} ts₁) (function fn₂ {n₂} ts₂) acc = ∅
⋆amguTerm! (function fn₁ ts₁) (_ fork _) acc = ∅
⋆amguTerm! (i x) (i y) (m , ∅) = ∅
⋆amguTerm! (i x) t     (m , ∅) = ∅
⋆amguTerm! t     (i x) (m , ∅) = ∅
⋆amguTerm! s     t  (n , _/_asub_ {n = n'} z r σ
                       ) =
  fmapMaybe
  (λ σ' → σ' ∃asub r / z)
  (⋆amguTerm! {m = n'}
    (
      -- § ⦃ 𝓢urjectionIdentity ⦄ ⦃ r = 𝓢urjectivitySubstitunctionExtensionTerm ⦄
      𝓼urjectivitySubstitunctionExtensionTerm'
      (r for z) s
    )
    (
      -- § ⦃ 𝓢urjectionIdentity ⦄ ⦃ r = 𝓢urjectivitySubstitunctionExtensionTerm ⦄
      𝓼urjectivitySubstitunctionExtensionTerm'
      (r for z) t
    )
    (n , σ)
  )
