evidently, the choice of constraint makes no difference for transextensionality
```agda
open import Oscar.Class.Transitivity
open import Oscar.Data.Proposequality
open import Oscar.Data.Constraint
open import Oscar.Prelude
open import Oscar.Data.𝟙

module Test.ConfusionAboutExtension-4b where

record InnerClass {ℓ} {𝔢} {CONSTRAINTS : Ø 𝔢} (constraints : CONSTRAINTS) (_ : Constraint constraints) (SET-METHOD : Ø ℓ) : Ø ℓ where
  field ⋆ : SET-METHOD

open InnerClass public

module Transextensionality
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  (transitivity : Transitivity.type _∼_)
  (let _∙_ : FlipTransitivity.type _∼_
       _∙_ g f = transitivity f g)
  where

  type : Ø ℓ ∙̂ (𝔯 ∙̂ 𝔬)
  type = ∀ {x y z} {f₁ f₂ : x ∼ y} {g₁ g₂ : y ∼ z} → f₁ ∼̇ f₂ → g₁ ∼̇ g₂ → g₁ ∙ f₁ ∼̇ g₂ ∙ f₂

  class : Ø ℓ ∙̂ (𝔯 ∙̂ 𝔬)
  class = InnerClass -- (𝔒 ,, _∼_ ,, (λ {x y} → _∼̇_ {x} {y}) ,, λ {x y z} → transitivity {x} {y} {z} ,, λ {x y z} {f₁ f₂ : x ∼ y} {g₁ g₂ : y ∼ z} → f₁ ∼̇ f₂ → g₁ ∼̇ g₂ → g₁ ∙ f₁ ∼̇ g₂ ∙ f₂)
                     -- 𝟙
                     -- (λ {x y} → _∼̇_ {x} {y})
                     (λ x y z (f₁ f₂ : x ∼ y) (g₁ g₂ : y ∼ z) → f₁ ∼̇ f₂)
                     ∅
                     type

  record Class : Ø ℓ ∙̂ (𝔯 ∙̂ 𝔬) where
    field method' : type

  method : ⦃ _ : class ⦄ → type
  method ⦃ ⌶ ⦄ = InnerClass.⋆ ⌶

  method' : ⦃ _ : Class ⦄ → type
  method' ⦃ ⌶ ⦄ = Class.method' ⌶

module _ {𝔬} {𝔒 : Ø 𝔬} where
  postulate
    transitivity' : Transitivity.type Proposequality⟦ 𝔒 ⟧

postulate

  Transextensionality--Morphism=Proposequality : ∀
    {a} {A : Ø a}
    {m} {_⊸_ : A → A → Ø m}
    {transitivity : Transitivity.type _⊸_}
    → Transextensionality.class _⊸_ Proposequality transitivity

  Transextensionality--Morphism=Proposequality' : ∀
    {a} {A : Ø a}
    {m} {_⊸_ : A → A → Ø m}
    {transitivity : Transitivity.type _⊸_}
    → Transextensionality.Class _⊸_ Proposequality transitivity

module _
  {a} {A : Ø a}
  where

  postulate
    Transextensionality--Object=Proposequality,Morphism=Proposequality : Transextensionality.class Proposequality⟦ A ⟧ Proposequality transitivity'
    Transextensionality--Object=Proposequality,Morphism=Proposequality' : Transextensionality.Class Proposequality⟦ A ⟧ Proposequality transitivity'

module _
  {a} {A : Ø a}
  where

  TestClass = Transextensionality.class Proposequality⟦ A ⟧ Proposequality transitivity'
  TestClass' = Transextensionality.Class Proposequality⟦ A ⟧ Proposequality transitivity'
  TestType = Transextensionality.type Proposequality⟦ A ⟧ Proposequality transitivity'

  module Test--class--Object=Any where
    instance _ = Transextensionality--Morphism=Proposequality
    _ = TestClass ∋ !
    _ = TestType ∋ Transextensionality.method Proposequality⟦ _ ⟧ Proposequality transitivity'
    _ = TestType ∋ Transextensionality.method Proposequality⟦ _ ⟧ _ transitivity'
    _ = TestType ∋ Transextensionality.method _ Proposequality transitivity'
    _ = TestType ∋ Transextensionality.method Proposequality⟦ A ⟧ Proposequality _

  module Test--Class--Object=Any where
    instance _ = Transextensionality--Morphism=Proposequality'
    _ = TestClass' ∋ !
    _ = TestType ∋ Transextensionality.method' Proposequality⟦ _ ⟧ Proposequality transitivity'
    _ = TestType ∋ Transextensionality.method' Proposequality⟦ A ⟧ _ transitivity'
    _ = TestType ∋ Transextensionality.method' Proposequality⟦ _ ⟧ _ transitivity'
    _ = TestType ∋ Transextensionality.method' Proposequality⟦ A ⟧ Proposequality _

  module Test--class--Object=Proposequality where
    instance _ = Transextensionality--Object=Proposequality,Morphism=Proposequality
    _ = TestClass ∋ !
    _ = TestType ∋ Transextensionality.method _ _ _

  module Test--Class--Object=Proposequality where
    instance _ = Transextensionality--Object=Proposequality,Morphism=Proposequality'
    _ = TestClass' ∋ !
    _ = TestType ∋ Transextensionality.method' _ Proposequality _
    _ = TestType ∋ Transextensionality.method' Proposequality⟦ A ⟧ _ transitivity'
    _ = TestType ∋ Transextensionality.method' Proposequality⟦ _ ⟧ _ transitivity'
    _ = TestType ∋ Transextensionality.method' Proposequality⟦ A ⟧ _ _

  module Test--class--both where
    instance _ = Transextensionality--Morphism=Proposequality
    instance _ = Transextensionality--Object=Proposequality,Morphism=Proposequality
    _ = TestClass ∋ !

  module Test--Class--both where
    instance _ = Transextensionality--Morphism=Proposequality'
    instance _ = Transextensionality--Object=Proposequality,Morphism=Proposequality'
    _ = TestClass' ∋ !
```
