Same as 4 but making explicit use of InnerClass

```agda
open import Oscar.Class.Transitivity
open import Oscar.Data.Proposequality
open import Oscar.Data.Constraint
open import Oscar.Prelude

module Test.ConfusionAboutExtension-4a where

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

  class : Ø ℓ ∙̂ (𝔯 ∙̂ 𝔬)
  class = InnerClass
  {-
                     {ℓ ∙̂ (𝔯 ∙̂ 𝔬)} {(↑̂ ℓ) ∙̂ ((↑̂ 𝔯) ∙̂ (↑̂ 𝔬))} {Σ′ (Set 𝔬)
                                                                (Σ′ (𝔒 → 𝔒 → Ø 𝔯)
                                                                 (Σ ({x y : 𝔒} → x ∼ y → x ∼ y → Ø ℓ)
                                                                  (λ v → {x y z : 𝔒} → x ∼ y → y ∼ z → x ∼ z)))}
  -}
                     (𝔒 ,, _∼_ ,, (λ {x y} → _∼̇_ {x} {y}) , λ {x y z} → transitivity {x} {y} {z})
                     ∅
                     (∀ {x y z} {f₁ f₂ : x ∼ y} {g₁ g₂ : y ∼ z} → f₁ ∼̇ f₂ → g₁ ∼̇ g₂ → g₁ ∙ f₁ ∼̇ g₂ ∙ f₂)

{-
  record class
    (_ : Constraint (𝔒 ,, _∼_ ,, (λ {x y} → _∼̇_ {x} {y}) , λ {x y z} → transitivity {x} {y} {z}))
    : Ø ℓ ∙̂ (𝔯 ∙̂ 𝔬) where
    field ⋆ : ∀ {x y z} {f₁ f₂ : x ∼ y} {g₁ g₂ : y ∼ z} → f₁ ∼̇ f₂ → g₁ ∼̇ g₂ → g₁ ∙ f₁ ∼̇ g₂ ∙ f₂
-}

  type : Ø ℓ ∙̂ (𝔯 ∙̂ 𝔬)
  type = ∀ {x y z} {f₁ f₂ : x ∼ y} {g₁ g₂ : y ∼ z} → f₁ ∼̇ f₂ → g₁ ∼̇ g₂ → g₁ ∙ f₁ ∼̇ g₂ ∙ f₂
  method : ⦃ _ : class ⦄ → type
  method ⦃ ⌶ ⦄ = InnerClass.⋆ ⌶

module _ {𝔬} {𝔒 : Ø 𝔬} where

  transitivity' : Transitivity.type Proposequality⟦ 𝔒 ⟧
  transitivity' ∅ y∼z = y∼z

Transextensionality--Morphism=Proposequality : ∀
  {a} {A : Ø a}
  {m} {_⊸_ : A → A → Ø m}
  {transitivity : Transitivity.type _⊸_}
  → Transextensionality.class _⊸_ Proposequality transitivity
Transextensionality--Morphism=Proposequality .⋆ ∅ ∅ = ∅

module _
  {a} {A : Ø a}
  where

  Transextensionality--Object=Proposequality,Morphism=Proposequality : Transextensionality.class Proposequality⟦ A ⟧ Proposequality transitivity'
  Transextensionality--Object=Proposequality,Morphism=Proposequality .⋆ ∅ ∅ = ∅

module _
  {a} {A : Ø a}
  where

  module _ where
    instance _ = Transextensionality--Morphism=Proposequality
    test-1 : Transextensionality.class Proposequality⟦ A ⟧ Proposequality transitivity'
    test-1 = !
    use-1 : Transextensionality.type Proposequality⟦ A ⟧ (Proposequality) transitivity'
    use-1 = Transextensionality.method Proposequality⟦ _ ⟧ _ transitivity'

  module _ where
    instance _ = Transextensionality--Object=Proposequality,Morphism=Proposequality
    test-2 : Transextensionality.class Proposequality⟦ A ⟧ Proposequality transitivity'
    test-2 = !
    use-2 : Transextensionality.type Proposequality⟦ A ⟧ (Proposequality) transitivity'
    use-2 = Transextensionality.method _ _ _

  module _ where
    instance _ = Transextensionality--Morphism=Proposequality
    instance _ = Transextensionality--Object=Proposequality,Morphism=Proposequality
    test-3 : Transextensionality.class Proposequality⟦ A ⟧ Proposequality transitivity'
    test-3 = !
```
