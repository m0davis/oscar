Let's try getting properties like transextensionality from Category-therory-like objects (such as Precategory, Category, LaxMonoidalFunctor, etc.)

```agda
open import Oscar.Class.Transitivity using (module Transitivity)
open import Oscar.Data.Proposequality
open import Oscar.Data.Constraint
open import Oscar.Prelude

module Test.ConfusionAboutExtension-6 where

module _
{-
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
-}
  where
  record Precategory 𝔬 𝔯 ℓ : Ø ↑̂ (𝔬 ∙̂ 𝔯 ∙̂ ℓ) where
    constructor ∁
    field
      Object : Ø 𝔬
      Morphism : Object → Object → Ø 𝔯
    private _∼_ = Morphism
    field
      Equiv : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ
    private
      infix 4 _∼̇_
      _∼̇_ = Equiv
    field
      transitivity : ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z
    infixr 9 _∙_
    _∙_ : ∀ {x y z} → y ∼ z → x ∼ y → x ∼ z
    _∙_ g f = transitivity f g
    field
      transextensionality : ∀ {x y z} {f₁ f₂ : x ∼ y} {g₁ g₂ : y ∼ z} → f₁ ∼̇ f₂ → g₁ ∼̇ g₂ → (g₁ ∙ f₁) ∼̇ (g₂ ∙ f₂)

Precategory--Morphism=Proposequality : ∀ {𝔬 𝔯 ℓ} → Precategory 𝔬 𝔯 ℓ
Precategory--Morphism=Proposequality
  {a} {A : Ø a}
  {m} {_⊸_ : A → A → Ø m}
  {transitivity : Transitivity.type _⊸_}
  ⦃ _ : Constraint (A ,, _⊸_ ,, λ {x y z} → transitivity {x} {y} {z}) ⦄
  → Transextensionality _⊸_ Proposequality transitivity
Transextensionality--Morphism=Proposequality .Transextensionality.transextensionality ∅ ∅ = ∅

--   = ℭLASS (x ,, y ,, z ,, _∼_) (x ∼ y → y ∼ z → x ∼ z)

-- module Transitivity
--   {𝔬} {𝔒 : Ø 𝔬}
--   {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
--   where
--   class = ∀ {x y z} → Transitivity'.class _∼_ x y z
--   type = ∀ {x y z} → Transitivity'.type _∼_ x y z


-- -- module _
-- --   {𝔬} {𝔒 : Ø 𝔬}
-- --   {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
-- --   {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
-- --   (transitivity : Transitivity.type _∼_)
-- --   (let _∙_ : FlipTransitivity.type _∼_
-- --        _∙_ g f = transitivity f g)
-- --   where
-- --   record Transextensionality ⦃ _ : Constraint (𝔒 ,, _∼_ ,, (λ {x y} → _∼̇_ {x} {y}) , λ {x y z} → transitivity {x} {y} {z}) ⦄ : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where
-- --     field
-- --       transextensionality :
-- --         ∀ {x y z} {f₁ f₂ : x ∼ y} {g₁ g₂ : y ∼ z} → f₁ ∼̇ f₂ → g₁ ∼̇ g₂ → g₁ ∙ f₁ ∼̇ g₂ ∙ f₂

-- -- open Transextensionality ⦃ … ⦄

-- -- module _ {𝔬} {𝔒 : Ø 𝔬} where

-- --   instance

-- --     𝓣ransitivityProposequality : Transitivity.class Proposequality⟦ 𝔒 ⟧
-- --     𝓣ransitivityProposequality .⋆ ∅ y∼z = y∼z

-- -- Transextensionality--Morphism=Proposequality : ∀
-- --   {a} {A : Ø a}
-- --   {m} {_⊸_ : A → A → Ø m}
-- --   {transitivity : Transitivity.type _⊸_}
-- --   ⦃ _ : Constraint (A ,, _⊸_ ,, λ {x y z} → transitivity {x} {y} {z}) ⦄
-- --   → Transextensionality _⊸_ Proposequality transitivity
-- -- Transextensionality--Morphism=Proposequality .Transextensionality.transextensionality ∅ ∅ = ∅

-- -- module _
-- --   {a} {A : Ø a}
-- --   where

-- --   Transextensionality--Object=Proposequality,Morphism=Proposequality : Transextensionality Proposequality⟦ A ⟧ Proposequality transitivity
-- --   Transextensionality--Object=Proposequality,Morphism=Proposequality .Transextensionality.transextensionality ∅ ∅ = ∅

-- -- module _
-- --   {a} {A : Ø a}
-- --   where

-- --   module _ where
-- --     instance _ = Transextensionality--Morphism=Proposequality
-- --     test-1 : Transextensionality Proposequality⟦ A ⟧ Proposequality transitivity
-- --     test-1 = !

-- --   module _ where
-- --     instance _ = Transextensionality--Object=Proposequality,Morphism=Proposequality
-- --     test-2 : Transextensionality Proposequality⟦ A ⟧ Proposequality transitivity
-- --     test-2 = !

-- --   module _ where
-- --     instance _ = Transextensionality--Morphism=Proposequality
-- --     instance _ = Transextensionality--Object=Proposequality,Morphism=Proposequality
-- --     test-3 : Transextensionality Proposequality⟦ A ⟧ Proposequality transitivity
-- --     test-3 = !
-- -- ```
