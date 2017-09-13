{-# OPTIONS --allow-unsolved-metas #-}

open import Oscar.Class
open import Oscar.Class.Hmap
open import Oscar.Class.Reflexivity
open import Oscar.Class.Symmetry
open import Oscar.Class.Transitivity
open import Oscar.Class.Transleftidentity
open import Oscar.Prelude

module Test.ProblemWithDerivation-5 where

postulate
  A : Set
  B : Set
  _~A~_ : A → A → Set
  _~B~_ : B → B → Set
  s1 : A → B
  f1 : ∀ {x y} → x ~A~ y → s1 x ~B~ s1 y

instance

  𝓢urjectivity1 : Hmap.class s1 s1 _~A~_ _~B~_
  𝓢urjectivity1 .⋆ _ _ = f1

-- Oscar.Class.Hmap.Transleftidentity
instance
  postulate
    -HmapFromTransleftidentitySymmetry : ∀
      {𝔵} {𝔛 : Ø 𝔵}
      {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
      {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
      (let _∼_ = Arrow 𝔄 𝔅)
      {ℓ̇} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ̇}
      {transitivity : Transitivity.type _∼_}
      {reflexivity : Reflexivity.type _∼_}
      {ℓ}
      ⦃ _ : Transleftidentity.class _∼_ _∼̇_ reflexivity transitivity ⦄
      → ∀ {m n}
      → Hmap.class (λ (f : m ∼ n) → transitivity f reflexivity)
                   (λ (P : LeftExtensionṖroperty ℓ _∼_ _∼̇_ m) → P)
                   (λ f P → π₀ (π₀ P) f)
                   (λ f P → π₀ (π₀ P) f)

test-before : ∀ {x y} → x ~A~ y → s1 x ~B~ s1 y
test-before = hhmap _ _

postulate
  XX : Set
  BB : XX → Set
  EQ : ∀ {x y} → Arrow BB BB x y → Arrow BB BB x y → Set

instance
  postulate
    -transleftidentity : Transleftidentity.class (Arrow BB BB) EQ magic magic

test-after : ∀ {x y} → x ~A~ y → s1 x ~B~ s1 y
test-after {x} {y} = hhmap _ _ -- FIXME
