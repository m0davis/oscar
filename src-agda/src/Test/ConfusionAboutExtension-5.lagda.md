Let's try using an explicit record for Transextensionality (instead of ℭLASS)

```agda

open import Oscar.Class
open import Oscar.Class.Transitivity
open import Oscar.Data.Proposequality
open import Oscar.Data.Constraint
open import Oscar.Prelude

module Test.ConfusionAboutExtension-5 where

module Transextensionality
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  (transitivity : Transitivity.type _∼_)
  (let _∙_ : FlipTransitivity.type _∼_
       _∙_ g f = transitivity f g)
  where
  type = ∀ {x y z} {f₁ f₂ : x ∼ y} {g₁ g₂ : y ∼ z} → f₁ ∼̇ f₂ → g₁ ∼̇ g₂ → g₁ ∙ f₁ ∼̇ g₂ ∙ f₂
  record class
         (setty : Σ′ (Set 𝔬)
                     (Σ′ (𝔒 → 𝔒 → Ø 𝔯)
                      (Σ ({x y : 𝔒} → x ∼ y → x ∼ y → Ø ℓ)
                       (λ v → {x y z : 𝔒} → x ∼ y → y ∼ z → x ∼ z))))
         (_ : Constraint setty)
         : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where
    field
      transextensionality : type

open Transextensionality.class ⦃ … ⦄

module _ {𝔬} {𝔒 : Ø 𝔬} where

  instance

    𝓣ransitivityProposequality : Transitivity.class Proposequality⟦ 𝔒 ⟧
    𝓣ransitivityProposequality .⋆ ∅ y∼z = y∼z

Transextensionality--Morphism=Proposequality : ∀
  {a} {A : Ø a}
  {m} {_⊸_ : A → A → Ø m}
  {transitivity : Transitivity.type _⊸_}
  ⦃ _ : Constraint (A ,, _⊸_ ,, λ {x y z} → transitivity {x} {y} {z}) ⦄
  → Transextensionality.class _⊸_ Proposequality transitivity (A ,, (_⊸_ ,, (Proposequality , (λ {x y z} → transitivity {x} {y} {z})))) ∅
Transextensionality--Morphism=Proposequality .Transextensionality.class.transextensionality ∅ ∅ = ∅

module _
  {a} {A : Ø a}
  where

  Transextensionality--Object=Proposequality,Morphism=Proposequality : Transextensionality.class Proposequality⟦ A ⟧ Proposequality transitivity (A ,, (Proposequality ,, (Proposequality , (λ {x y z} → transitivity {x = x} {y} {z})))) ∅
  Transextensionality--Object=Proposequality,Morphism=Proposequality .Transextensionality.class.transextensionality ∅ ∅ = ∅

module _
  {a} {A : Ø a}
  where

  module _ where
    instance _ = Transextensionality--Morphism=Proposequality
    test-1 : Transextensionality.class Proposequality⟦ A ⟧ Proposequality transitivity (A ,, (Proposequality ,, (Proposequality , (λ {x y z} → transitivity {x = x} {y} {z})))) ∅
    test-1 = !
    use-1 : Transextensionality.type Proposequality⟦ A ⟧ Proposequality transitivity
    use-1 = transextensionality

  module _ where
    instance _ = Transextensionality--Object=Proposequality,Morphism=Proposequality
    test-2 : Transextensionality.class Proposequality⟦ A ⟧ Proposequality transitivity (A ,, (Proposequality ,, (Proposequality , (λ {x y z} → transitivity {x = x} {y} {z})))) ∅
    test-2 = !
    use-2 : Transextensionality.type Proposequality⟦ A ⟧ Proposequality transitivity
    use-2 = transextensionality

--   module _ where
--     instance _ = Transextensionality--Morphism=Proposequality
--     instance _ = Transextensionality--Object=Proposequality,Morphism=Proposequality
--     test-3 : Transextensionality.class Proposequality⟦ A ⟧ Proposequality transitivity
--     test-3 = !
--     -- Transextensionality--Object=Proposequality,Morphism=Proposequality {A = A}
--     -- Transextensionality--Morphism=Proposequality {A = A} {_⊸_ = Proposequality⟦ A ⟧} {transitivity = transitivity}

--   eq? :
--     (λ {x y z} {f₁ f₂ : _} {g₁ g₂ : _} → Transextensionality.class.transextensionality (Transextensionality--Morphism=Proposequality {A = A} {_⊸_ = Proposequality⟦ A ⟧} {transitivity = transitivity}) {x} {y} {z} {f₁} {f₂} {g₁} {g₂})
--     ≡
--     Transextensionality.class.transextensionality (Transextensionality--Object=Proposequality,Morphism=Proposequality {A = A})
--   eq? = {!!}

-- ```
