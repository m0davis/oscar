{-# OPTIONS --allow-unsolved-metas #-}

open import Oscar.Class
open import Oscar.Class.Smap
open import Oscar.Class.Transitivity
open import Oscar.Class.Reflexivity
open import Oscar.Class.Transleftidentity
open import Oscar.Class.Symmetry
open import Oscar.Class.Hmap
open import Oscar.Data.Proposequality
open import Oscar.Data.Substitunction
open import Oscar.Data.Term
open import Oscar.Prelude

module Test.ProblemWithDerivation-3 where

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

module _ {𝔭} {𝔓 : Ø 𝔭} where

  open Substitunction 𝔓
  open Term 𝔓

test-1-before : ∀ {x y} → x ~A~ y → s1 x ~B~ s1 y
test-1-before {x} {y} = smap

instance

  HmapFromTransleftidentitySymmetry : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
    (let _∼_ = Arrow 𝔄 𝔅)
    {ℓ̇} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ̇}
    {transitivity : Transitivity.type _∼_}
    {reflexivity : Reflexivity.type _∼_}
    {ℓ}
    ⦃ _ : Transleftidentity.class _∼_ _∼̇_ reflexivity transitivity ⦄
    ⦃ _ : ∀ {x y} → 𝓢ymmetry (_∼̇_ {x} {y}) ⦄
    → ∀ {m n}
    → Hmap.class (λ (f : m ∼ n) → transitivity f reflexivity)
                 (λ (P : LeftExtensionṖroperty ℓ _∼_ _∼̇_ m) → P)
                 (λ f P → π₀ (π₀ P) f)
                 (λ f P → π₀ (π₀ P) f)
  HmapFromTransleftidentitySymmetry .⋆ P₁ (π₂ , π₃) = π₃ $ symmetry transleftidentity

instance

    𝓣ransleftidentityExtension :
      ∀ {a} {A : Ø a} {b} {B : A → Ø b}
      → Transleftidentity.class (Extension B) _≡̇_ ¡ (flip _∘′_)
    𝓣ransleftidentityExtension .⋆ _ = ∅

    TransleftidentityFunction :
      ∀ {𝔬}
      → Transleftidentity.class Function⟦ 𝔬 ⟧ _≡̇_ ¡ (flip _∘′_)
    TransleftidentityFunction .⋆ _ = ∅

test-1-after : ∀ {x y} → x ~A~ y → s1 x ~B~ s1 y
test-1-after {x} {y} = smap
