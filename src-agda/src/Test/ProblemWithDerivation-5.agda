{-# OPTIONS --allow-unsolved-metas #-}

open import Oscar.Class
open import Oscar.Class.Reflexivity
open import Oscar.Class.Symmetry
open import Oscar.Class.Transitivity
open import Oscar.Class.Transleftidentity
open import Oscar.Prelude

module Test.ProblemWithDerivation-5 where

module Map
  {𝔵₁} {𝔛₁ : Ø 𝔵₁}
  {𝔵₂} {𝔛₂ : Ø 𝔵₂}
  {𝔯₁₂} {𝔯₁₂'}
  (ℜ₁₂ : 𝔛₁ → 𝔛₂ → Ø 𝔯₁₂)
  (ℜ₁₂' : 𝔛₁ → 𝔛₂ → Ø 𝔯₁₂')
  = ℭLASS (ℜ₁₂ , ℜ₁₂')
          (∀ P₁ P₂
           → ℜ₁₂ P₁ P₂ → ℜ₁₂' P₁ P₂)

module _
  {𝔵₁} {𝔛₁ : Ø 𝔵₁}
  {𝔵₂} {𝔛₂ : Ø 𝔵₂}
  {𝔯₁₂} {ℜ₁₂ : 𝔛₁ → 𝔛₂ → Ø 𝔯₁₂}
  {𝔯₁₂'} {ℜ₁₂' : 𝔛₁ → 𝔛₂ → Ø 𝔯₁₂'}
  where
  map = Map.method ℜ₁₂ ℜ₁₂'

module _
  {𝔵₁} {𝔛₁ : Ø 𝔵₁}
  {𝔯₁₂} {ℜ₁₂ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁₂}
  {𝔯₁₂'} {ℜ₁₂' : 𝔛₁ → 𝔛₁ → Ø 𝔯₁₂'}
  where
  smap = Map.method ℜ₁₂ ℜ₁₂' -- FIXME this looks like a viable solution; but what if `-MapFromTransleftidentity` builds something addressable by smap (i.e., where 𝔛₁ ≡ 𝔛₂)?

module _
  {𝔵₁} {𝔛₁ : Ø 𝔵₁}
  {𝔵₂} {𝔛₂ : Ø 𝔵₂}
  {𝔯₁₂} {ℜ₁₂ : 𝔛₁ → 𝔛₂ → Ø 𝔯₁₂}
  where
  hmap = Map.method ℜ₁₂ ℜ₁₂

postulate
  A : Set
  B : Set
  _~A~_ : A → A → Set
  _~B~_ : B → B → Set
  s1 : A → B
  f1 : ∀ {x y} → x ~A~ y → s1 x ~B~ s1 y

instance
  𝓢urjectivity1 : Map.class
                    {𝔛₁ = A}
                    {𝔛₂ = A}
                    _~A~_ (λ x y → s1 x ~B~ s1 y)
  𝓢urjectivity1 .⋆ _ _ = f1

-- Oscar.Class.Hmap.Transleftidentity
instance
  postulate
    -MapFromTransleftidentity : ∀
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
      → Map.class {𝔛₁ = Arrow 𝔄 𝔅 m n}
                  {𝔛₂ = LeftExtensionṖroperty ℓ (Arrow 𝔄 𝔅) _∼̇_ m}
                  (λ f P → π₀ (π₀ P) f)
                  (λ f P → π₀ (π₀ P) (transitivity f reflexivity))

test-before : ∀ {x y} → x ~A~ y → s1 x ~B~ s1 y
test-before = map _ _

postulate
  XX : Set
  BB : XX → Set
  EQ : ∀ {x y} → Arrow BB BB x y → Arrow BB BB x y → Set

instance
  postulate
    -transleftidentity : Transleftidentity.class (Arrow BB BB) EQ (λ x₁ → magic) (λ x₁ x₂ x₃ → magic)

test-after : ∀ {x y} → x ~A~ y → s1 x ~B~ s1 y
test-after {x} {y} = map _ _ -- FIXME yellow

test-after-s : ∀ {x y} → x ~A~ y → s1 x ~B~ s1 y
test-after-s {x} {y} = smap _ _

testr : ∀ {m n ℓ}
          (P₁ : Arrow BB BB m n)
          (P₂ : LeftExtensionṖroperty ℓ (Arrow BB BB) EQ m)
          → π₀ (π₀ P₂) P₁ → π₀ (π₀ P₂) (flip {∅̂} {∅̂} {∅̂}
                                         {Arrow (λ z → BB z) (λ z → BB z) m n}
                                         {Arrow (λ z → BB z) (λ z → BB z) n n}
                                         {λ _ _ → Arrow BB BB m n}
                                         (λ _ _ _ → magic) (λ _ → magic) P₁)
testr = map
