{-# OPTIONS --allow-unsolved-metas #-}

open import Oscar.Class
open import Oscar.Class.Hmap
open import Oscar.Class.Leftunit
open import Oscar.Class.Reflexivity
open import Oscar.Class.Smap
open import Oscar.Class.Symmetry
open import Oscar.Class.Transextensionality
open import Oscar.Class.Transitivity
open import Oscar.Class.Transleftidentity
open import Oscar.Data.Proposequality
open import Oscar.Data.Substitunction
open import Oscar.Data.Term
open import Oscar.Prelude

module Test.ProblemWithDerivation-4 where

postulate
  A : Set
  B : Set
  _~A~_ : A → A → Set
  _~B~_ : B → B → Set
  s1 : A → B
  f1 : ∀ {x y} → x ~A~ y → s1 x ~B~ s1 y

instance

  𝓢urjectivity1 : Smap.class _~A~_ _~B~_ s1 s1
  𝓢urjectivity1 .⋆ _ _ = f1

test-before : ∀ {x y} → x ~A~ y → s1 x ~B~ s1 y
test-before = smap

-- Oscar.Class.Hmap.Transleftidentity
instance

  Relprop'idFromTransleftidentity : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
    (let _∼_ = Arrow 𝔄 𝔅)
    {ℓ̇} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ̇}
    {transitivity : Transitivity.type _∼_}
    {reflexivity : Reflexivity.type _∼_}
    {ℓ}
    ⦃ _ : Transleftidentity.class _∼_ _∼̇_ reflexivity transitivity ⦄
    ⦃ _ : ∀ {x y} → Symmetry.class (_∼̇_ {x} {y}) ⦄
    → ∀ {m n}
    → Hmap.class (λ (f : m ∼ n) → transitivity f reflexivity)
                 (λ (P : LeftExtensionṖroperty ℓ _∼_ _∼̇_ m) → P)
                 (λ f P → π₀ (π₀ P) f)
                 (λ f P → π₀ (π₀ P) f)
  Relprop'idFromTransleftidentity .⋆ _ (_ , P₁) = P₁ $ symmetry transleftidentity

-- Oscar.Property.Category.Function
module _ {𝔬 : Ł} where

  instance

    postulate TransleftidentityFunction : Transleftidentity.class Function⟦ 𝔬 ⟧ _≡̇_ ¡ (flip _∘′_)

-- Oscar.Property.Functor.SubstitunctionExtensionTerm
module _ {𝔭} {𝔓 : Ø 𝔭} where

  open Substitunction 𝔓
  open Term 𝔓

  instance

    postulate 𝓢urjectivitySubstitunctionExtensionTerm : Smap.class Substitunction (Extension Term) ¡ ¡
    postulate 𝓣ransleftidentitySubstitunction : Transleftidentity.class Substitunction _≡̇_ i (λ f g → smap g ∘ f)

-- Oscar.Property.Setoid.Proposextensequality
module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} where

  instance

    𝓢ymmetryProposextensequality : Symmetry.class Proposextensequality⟦ 𝔓 ⟧
    𝓢ymmetryProposextensequality .⋆ f₁≡̇f₂ x rewrite f₁≡̇f₂ x = ∅

test-after : ∀ {x y} → x ~A~ y → s1 x ~B~ s1 y
test-after = smap -- FIXME this was yellow when we used Symmetry instead of Sym. why?
