
open import Oscar.Prelude
open import Oscar.Class
-- open import Oscar.Class.HasEquivalence -- FIXME make similar to Reflexivity and Surjextensivity
open import Oscar.Class.Reflexivity using (𝓻eflexivity)
open import Oscar.Class.Surjectextensivity using (𝒮urjectextensivity)
open import Oscar.Data.Constraint
import Oscar.Class.Surjection.⋆

open import Oscar.Class.Leftunit
open import Oscar.Data.𝟙

module Oscar.Class.Factsurj3 where

module Factsurj3
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  (𝔓 : π̂ 𝔭 𝔛)
  (_≈_ : ∀̇ π̂² ℓ 𝔓)
  (ℜ : π̂² 𝔯 𝔛)
  (ε : 𝓻eflexivity ℜ)
  (_◃_ : 𝒮urjectextensivity ℜ 𝔓)
  where
  class = ∀ {x} {p : 𝔓 x} → Leftunit.class (flip (_≈_ {x})) (ε {x}) _◃_ p
  type = ∀ {x} {p : 𝔓 x} → Leftunit.type (flip (_≈_ {x})) (ε {x}) _◃_ p
  method = λ ⦃ _ : class ⦄ {x} {p : 𝔓 x} → Leftunit.method (flip (_≈_ {x})) (ε {x}) _◃_ p

module Factsurj3'
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  (𝔓 : π̂ 𝔭 𝔛)
  (_≈_ : ∀̇ π̂² ℓ 𝔓)
  (ℜ : π̂² 𝔯 𝔛)
  (ε : 𝓻eflexivity ℜ)
  (_◃_ : 𝒮urjectextensivity ℜ 𝔓)
  where
  family : ℭlass ((λ {x y} → _◃_ {x} {y}) , (λ {x} → _≈_ {x}))
  family = ∁ ∀ {x} {p : 𝔓 x} → p ≈ (ε ◃ p)
  open ℭLASS ((λ {x y} → _◃_ {x} {y}) , (λ {x} → _≈_ {x})) (∀ {x} {p : 𝔓 x} → p ≈ (ε ◃ p)) public

module _
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  {𝔓 : π̂ 𝔭 𝔛}
  {_≈_ : ∀̇ π̂² ℓ 𝔓}
  {ℜ : π̂² 𝔯 𝔛}
  {ε : 𝓻eflexivity ℜ}
  {_◃_ : 𝒮urjectextensivity ℜ 𝔓}
  ⦃ _ : Factsurj3'.class 𝔓 _≈_ ℜ ε _◃_ ⦄
  where
  instance
    unprimeFactsurj3 : Factsurj3.class 𝔓 _≈_ ℜ ε _◃_
    unprimeFactsurj3 .⋆ = Factsurj3'.method 𝔓 _≈_ ℜ ε _◃_


module Factsurj3''
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  (𝔓 : π̂ 𝔭 𝔛)
  (_≈_ : ∀̇ π̂² ℓ 𝔓)
  (ℜ : π̂² 𝔯 𝔛)
  (ε : 𝓻eflexivity ℜ)
  (_◃_ : 𝒮urjectextensivity ℜ 𝔓)
  where
  family : ℭlass 𝟙
  family = ∁ ∀ {x} {p : 𝔓 x} → p ≈ (ε ◃ p)
  open ℭLASS 𝟙 (∀ {x} {p : 𝔓 x} → p ≈ (ε ◃ p)) public

private

  module Test0
    {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
    (𝔓 : π̂ 𝔭 𝔛)
    (_≈_ : ∀̇ π̂² ℓ 𝔓)
    (_≈'_ : ∀̇ π̂² ℓ 𝔓)
    (ℜ : π̂² 𝔯 𝔛)
    (ε : 𝓻eflexivity ℜ)
    (_◃_ : 𝒮urjectextensivity ℜ 𝔓)
    (_◃'_ : 𝒮urjectextensivity ℜ 𝔓)
    where
    test-class' : ⦃ _ : Factsurj3'.class 𝔓 _≈_ ℜ ε _◃_ ⦄ → Factsurj3'.class 𝔓 _≈_ ℜ ε _◃_
    test-class' = !
    test-method' : ⦃ _ : Factsurj3'.class 𝔓 _≈_ ℜ ε _◃_ ⦄ → Factsurj3'.type 𝔓 _≈_ ℜ ε _◃_
    test-method' = Factsurj3'.method _ _ _ _ _
    test-class : ⦃ _ : Factsurj3.class 𝔓 _≈_ ℜ ε _◃_ ⦄ → Factsurj3.class 𝔓 _≈_ ℜ ε _◃_
    test-class = !
    test-method : ⦃ _ : Factsurj3.class 𝔓 _≈_ ℜ ε _◃_ ⦄ → Factsurj3.type 𝔓 _≈_ ℜ ε _◃_
    test-method = Factsurj3.method 𝔓 _≈_ _ _ _◃_
    test' : ⦃ _ : Factsurj3.class 𝔓 _≈_ ℜ ε _◃_ ⦄ → ⦃ _ : {ε : 𝓻eflexivity ℜ} → Factsurj3.class 𝔓 _≈_ ℜ ε _◃'_ ⦄ → {ε : 𝓻eflexivity ℜ} → Factsurj3.class 𝔓 _≈_ ℜ ε _◃'_
    test' {{i}} {{j}} = magic -- ! -- FIXME
    -- (∁ (_≈_ {.x} .p (_◃_ {.x} {.x} (ε {.x}) .p)))
    -- (∁ (_≈_ { x}  p (_◃_  {x}  {x} (ε  {x})  p)))
    {- _≈_ {.x} .p (_◃_ {.x} {.x} (ε {.x}) .p) = _≈_ { x}  p (_◃_  {x}  {x} (ε  {x})  p)

-}

  module Test1
    {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
    (𝔓 : π̂ 𝔭 𝔛)
    (_≈_ : ∀̇ π̂² ℓ 𝔓)
    (ℜ : π̂² 𝔯 𝔛)
    (_◃_ : 𝒮urjectextensivity ℜ 𝔓)
    where
    test : ⦃ _ : {ε : 𝓻eflexivity ℜ} → Factsurj3.class 𝔓 _≈_ ℜ ε _◃_ ⦄ → {ε : 𝓻eflexivity ℜ} → Factsurj3.class 𝔓 _≈_ ℜ ε _◃_
    test {{i}} = magic -- ! -- FIXME

  module Test2
    {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
    (𝔓 : π̂ 𝔭 𝔛)
    (ℜ : π̂² 𝔯 𝔛)
    (ε : 𝓻eflexivity ℜ)
    (_◃_ : 𝒮urjectextensivity ℜ 𝔓)
    where
    test : ⦃ _ : {_≈_ : ∀̇ π̂² ℓ 𝔓} → Factsurj3.class 𝔓 _≈_ ℜ ε _◃_ ⦄ → {_≈_ : ∀̇ π̂² ℓ 𝔓} → Factsurj3.class 𝔓 _≈_ ℜ ε _◃_
    test = magic -- ! -- FIXME

module factsurj3
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  {𝔓 : π̂ 𝔭 𝔛}
  {_≈_ : ∀̇ π̂² ℓ 𝔓}
  {ℜ : π̂² 𝔯 𝔛}
  {ε : 𝓻eflexivity ℜ}
  {_◃_ : 𝒮urjectextensivity ℜ 𝔓}
  where
  method = Factsurj3.method 𝔓 _≈_ ℜ ε _◃_

open import Oscar.Class.HasEquivalence
open import Oscar.Class.Reflexivity
open import Oscar.Class.Surjectextensivity

module 𝓕actsurj3
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  (𝔓 : π̂ 𝔭 𝔛)
  ⦃ _ : ∀ {x} → HasEquivalence (𝔓 x) ℓ ⦄
  (ℜ : π̂² 𝔯 𝔛)
  ⦃ _ : 𝓡eflexivity ℜ ⦄
  ⦃ _ : 𝓢urjectextensivity ℜ 𝔓 ⦄
  where
  class = Factsurj3.class 𝔓 _≈_ ℜ ε surjectextensivity
  type = Factsurj3.type 𝔓 _≈_ ℜ ε surjectextensivity
  method = Factsurj3.method 𝔓 _≈_ ℜ ε surjectextensivity

module 𝓯actsurj3
  {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
  {𝔓 : π̂ 𝔭 𝔛}
  ⦃ _ : ∀ {x} → HasEquivalence (𝔓 x) ℓ ⦄
  {ℜ : π̂² 𝔯 𝔛}
  ⦃ _ : 𝓡eflexivity ℜ ⦄
  ⦃ _ : 𝓢urjectextensivity ℜ 𝔓 ⦄
  where
  method = 𝓕actsurj3.method 𝔓 ℜ ⦃ ! ⦄ ⦃ ! ⦄

private

  test-class : ∀
    {𝔵 𝔭 𝔯 ℓ} {𝔛 : Ø 𝔵}
    {𝔓 : π̂ 𝔭 𝔛}
    ⦃ _ : ∀ {x} → HasEquivalence (𝔓 x) ℓ ⦄
    {ℜ : π̂² 𝔯 𝔛}
    ⦃ _ : 𝓡eflexivity ℜ ⦄
    ⦃ _ : 𝓢urjectextensivity ℜ 𝔓 ⦄
    → ⦃ _ : 𝓕actsurj3.class 𝔓 ℜ ⦄
    → 𝓕actsurj3.class 𝔓 ℜ
  test-class = !
