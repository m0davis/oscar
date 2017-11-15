# Chapter 3. A 2nd life for an old Cat.

```agda
-- {-# OPTIONS --show-implicit #-}

module Meow-3 where
```

## imports

```agda
import Oscar.Property.Functor.SubstitunctionExtensionTerm
open import Oscar.Class.Smap using (smap)
open import Oscar.Data.Constraint
open import Oscar.Data.Descender
open import Oscar.Data.Proposequality
open import Oscar.Data.Substitunction
open import Oscar.Data.Term
open import Oscar.Data.Vec
open import Oscar.Data.¶
open import Oscar.Prelude

module SubstitunctionExtensionTerm {𝔭} (𝔓 : Ø 𝔭) where

  open Substitunction 𝔓 public
  open Term 𝔓 public

  substitunctionExtensionTerm : ∀ {x y} → Substitunction x y → Extension Term x y
  substitunctionExtensionTerm = smap

  substitunctionExtensionTerms : ∀ {N} → ∀ {x y} → Substitunction x y → Extension (Terms N) x y
  substitunctionExtensionTerms = smap
```

## 2nd-order instances

```agda
record ⌶ {ℓ 𝔠} {C : Ø 𝔠} (c : C) ⦃ _ : Constraint c ⦄ (method : Ø ℓ) : Ø ℓ where
  constructor ∁
  field
    ⋆ : method

open ⌶ public
```

## 1-category

I'm adding 𝟏′ for cases where we don't need (or want or just can't have) an instance search (say, because the instance not "properly" (FIXME say what this means) in-scope and we have the `cat` in hand).

```agda
record cat {o m} (O : Ø o) (_↦_ : O → O → Ø m) : Ø ↑̂ (o ∙̂ m) where
  infixr 9 _∙_
  field
    _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
    ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
  private ⌶𝟏 = ⌶ _↦_ ∀ x → x ↦ x
  𝟏 : ⦃ _ : ⌶𝟏 ⦄ → ∀ x → x ↦ x
  𝟏 ⦃ I𝟏 ⦄ = I𝟏 .⋆
  field
    ⦃ ⦃⌶𝟏⦄ ⦄ : ⌶𝟏
  𝟏′ : ∀ x → x ↦ x
  𝟏′ = 𝟏
  field
    𝟏-left-unitary  : ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
    𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f

open cat ⦃ … ⦄ public hiding (⦃⌶𝟏⦄)

infixr 9 cat-∙
cat-∙ : ∀ {o m} {O : Ø o} (_↦_ : O → O → Ø m) ⦃ _ : cat O _↦_ ⦄ → ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
cat-∙ _ = _∙_

syntax cat-∙ _↦_ g f = g ∙[ _↦_ ] f
```

## instances of 1-categories

### function

```agda
module _ {ℓ} where

  instance

    function⌶𝟏 : ⌶ Function⟦ ℓ ⟧ (∀ x → Function⟦ ℓ ⟧ x x)
    function⌶𝟏 .⋆ _ = ¡

    functionCat : cat (Ø ℓ) Function
    functionCat .cat._∙_ = _∘′_
    functionCat .cat.∙-associativity _ _ _ = ∅
    functionCat .cat.⦃⌶𝟏⦄ = !
    functionCat .cat.𝟏-left-unitary _ = ∅
    functionCat .cat.𝟏-right-unitary _ = ∅
```

### equality

```agda
module _ {a} {A : Ø a} where

  instance

    proposequality⌶𝟏 : ⌶ Proposequality⟦ A ⟧ ∀ x → Proposequality⟦ A ⟧ x x
    proposequality⌶𝟏 .⋆ _ = ∅

    proposequalityCat : cat A Proposequality⟦ A ⟧
    proposequalityCat .cat._∙_ ∅ f = f
    proposequalityCat .cat.∙-associativity f g ∅ = ∅
    proposequalityCat .cat.⦃⌶𝟏⦄ = !
    proposequalityCat .cat.𝟏-left-unitary _ = ∅
    proposequalityCat .cat.𝟏-right-unitary ∅ = ∅
```

### extension

```agda
module _ {a} {A : Ø a} {b} {B : A → Ø b} where

  instance

    extension⌶𝟏 : ⌶ (Extension B) ∀ x → Extension B x x
    extension⌶𝟏 .⋆ _ = ¡

    extensionCat : cat A (Extension B)
    extensionCat .cat._∙_ = _∘′_
    extensionCat .cat.∙-associativity _ _ _ = ∅
    extensionCat .cat.⦃⌶𝟏⦄ = !
    extensionCat .cat.𝟏-left-unitary _ = ∅
    extensionCat .cat.𝟏-right-unitary _ = ∅
```

### alist

```agda
module _ {a} {A : ¶ → Ø a} where

  private AList = Descender⟨ A ⟩

  instance

    alist⌶𝟏 : ⌶ AList ∀ x → AList x x
    alist⌶𝟏 .⋆ _ = ∅

    alistCat : cat ¶ AList
    alistCat .cat._∙_ ∅ f = f
    alistCat .cat._∙_ (x , g) f = x , (g ∙ f)
    alistCat .cat.∙-associativity f g ∅ = ∅
    alistCat .cat.∙-associativity f g (x , h) rewrite ∙-associativity f g h = ∅
    alistCat .cat.⦃⌶𝟏⦄ = !
    alistCat .cat.𝟏-left-unitary _ = ∅
    alistCat .cat.𝟏-right-unitary ∅ = ∅
    alistCat .cat.𝟏-right-unitary (x , f) rewrite 𝟏-right-unitary f = ∅
```

## 1-functor

I'm revising the definition from the previous chapter so that the source and target categories are given explicitly. I'm also renaming the exposed operations. In general, I think such operations should use some unicode to distinguish them from variables. `F₁` now seems like a poor choice for the functorial mapping of morphisms, since we might want to use it to name a functor (say, in a natural transformation).

I'm also adding an instance-independent accessor for `𝐹₁`, similar to `𝟏` above.

I reversed the direction of commutativity for simplicity.

```agda
record fun
  {o₁ m₁} {O₁ : Ø o₁} {_↦₁_ : O₁ → O₁ → Ø m₁}
  {o₂ m₂} {O₂ : Ø o₂} {_↦₂_ : O₂ → O₂ → Ø m₂}
  (C₁ : cat O₁ _↦₁_)
  (C₂ : cat O₂ _↦₂_)
  : Ø ↑̂ (o₁ ∙̂ m₁ ∙̂ o₂ ∙̂ m₂) where
  instance
    _ = C₁
    _ = C₂
  field
    𝐹₀ : O₁ → O₂
  private ⌶𝐹₁ = ⌶ _↦₂_ ∀ {x y} → x ↦₁ y → 𝐹₀ x ↦₂ 𝐹₀ y
  𝐹₁ : ⦃ _ : ⌶𝐹₁ ⦄ → ∀ {x y} → x ↦₁ y → 𝐹₀ x ↦₂ 𝐹₀ y
  𝐹₁ ⦃ i𝐹₁ ⦄ = i𝐹₁ .⋆
  field
    ⦃ ⦃⌶𝐹₁⦄ ⦄ : ⌶𝐹₁
  𝐹₁′ : ∀ {x y} → x ↦₁ y → 𝐹₀ x ↦₂ 𝐹₀ y
  𝐹₁′ = 𝐹₁
  field
    𝐹₁-commutativity : ∀ {x y z} (f : x ↦₁ y) (g : y ↦₁ z) → 𝐹₁ g ∙ 𝐹₁ f ≡ 𝐹₁ (g ∙ f)
    𝐹₁-identity : ∀ x → 𝐹₁ (𝟏 x) ≡ 𝟏 _

open fun ⦃ … ⦄ public
```

## beginning of the 2nd life

We'll need to develop some more 1-categorical concepts before introducing the 2-categorical stuff.

### product of categories

```agda
module _
  {o₁ m₁} {O₁ : Ø o₁} {_↦₁_ : O₁ → O₁ → Ø m₁}
  {o₂ m₂} {O₂ : Ø o₂} {_↦₂_ : O₂ → O₂ → Ø m₂}
  (C₁ : cat O₁ _↦₁_)
  (C₂ : cat O₂ _↦₂_)
  where
  instance
    _ = C₁
    _ = C₂
  _⨂_ : cat (O₁ × O₂) (λ {(x₁ , x₂) (y₁ , y₂) → (x₁ ↦₁ y₁) × (x₂ ↦₂ y₂)})
  _⨂_ .cat._∙_ (g₁ , g₂) (f₁ , f₂) = g₁ ∙ f₁ , g₂ ∙ f₂
  _⨂_ .cat.∙-associativity (f₁ , f₂) (g₁ , g₂) (h₁ , h₂) rewrite ∙-associativity f₁ g₁ h₁ | ∙-associativity f₂ g₂ h₂ = ∅
  _⨂_ .cat.⦃⌶𝟏⦄ .⋆ (x₁ , x₂) = 𝟏 x₁ , 𝟏 x₂
  _⨂_ .cat.𝟏-left-unitary (f₁ , f₂) rewrite 𝟏-left-unitary f₁ | 𝟏-left-unitary f₂ = ∅
  _⨂_ .cat.𝟏-right-unitary (f₁ , f₂) rewrite 𝟏-right-unitary f₁ | 𝟏-right-unitary f₂ = ∅
```

-- ### natural transformation

```agda
record trans
  {o₁ m₁} {O₁ : Ø o₁} {_↦₁_ : O₁ → O₁ → Ø m₁}
  {o₂ m₂} {O₂ : Ø o₂} {_↦₂_ : O₂ → O₂ → Ø m₂}
  {C₁ : cat O₁ _↦₁_}
  {C₂ : cat O₂ _↦₂_}
  (F₁ F₂ : fun C₁ C₂)
  : Ø o₁ ∙̂ m₁ ∙̂ m₂ where
  private
    module F₁ = fun F₁
    module F₂ = fun F₂
  instance
    _ = C₁
    _ = C₂
  field
    α : ∀ x → F₁.𝐹₀ x ↦₂ F₂.𝐹₀ x
    α-commutativity : ∀ {x y} (f : x ↦₁ y) → F₂.𝐹₁ f ∙ α x ≡ α y ∙ F₁.𝐹₁ f
```

### inverse morphism

```agda
record inverse
  {o m} {O : Ø o} {_↦_ : O → O → Ø m}
  {x y}
  (f : x ↦ y)
  (C : cat O _↦_)
  : Ø o ∙̂ m where
  instance _ = C
  field
    ⁻¹ : y ↦ x
    ⁻¹-left-inverse : f ∙ ⁻¹ ≡ 𝟏 y
    ⁻¹-right-inverse : ⁻¹ ∙ f  ≡ 𝟏 x
```

### natural isomorphism

```agda
record iso
  {o₁ m₁} {O₁ : Ø o₁} {_↦₁_ : O₁ → O₁ → Ø m₁}
  {o₂ m₂} {O₂ : Ø o₂} {_↦₂_ : O₂ → O₂ → Ø m₂}
  {C₁ : cat O₁ _↦₁_}
  {C₂ : cat O₂ _↦₂_}
  (F₁ F₂ : fun C₁ C₂)
  : Ø o₁ ∙̂ o₂ ∙̂ m₁ ∙̂ m₂ where
  field
    η : trans F₁ F₂
    η-inverse : ∀ x → inverse (trans.α η x) C₂
```

In a bicategory, vertical composition is associative. Let's test to see if this will fit our purposes.

```agda
module Sandbox--BicategoryVerticalCompositionAssociativity where

  postulate
    O : Set -- will serve as objects in the bicategory
    A : O → Set

  _↦̇_ : O → O → Set -- 1-morphism
  x ↦̇ y = A x → A y

  _↦̈_ : ∀ {x y} → x ↦̇ y → x ↦̇ y → Set -- 2-morphism
  f ↦̈ g = ∀ a → f a ≡ g a -- non-strict equality of the 1-morphisms

  _∙∣̈∙_ : ∀ {x y} {f g h : x ↦̇ y} → g ↦̈ h → f ↦̈ g → f ↦̈ h -- vertical composition
  _∙∣̈∙_ β α x rewrite α x | β x = ∅

  ∙∣̈∙-associative : ∀ {x y} {f g h i : x ↦̇ y} (α : f ↦̈ g) (β : g ↦̈ h) (χ : h ↦̈ i)
                    → (χ ∙∣̈∙ β) ∙∣̈∙ α ≡ χ ∙∣̈∙ (β ∙∣̈∙ α)
  ∙∣̈∙-associative α β χ = {!!}
```

There's no way that's going to work.

If a bicategory doesn't work, how about a tricategory? Or does this just push the problem further back?

```agda
module Sandbox--TricategoryVerticalCompositionAssociativity where

  postulate
    O : Set -- will serve as objects in the tricategory
    A : O → Set

  _↦̇_ : O → O → Set -- 1-morphism
  x ↦̇ y = A x → A y

  _↦̈_ : ∀ {x y} → x ↦̇ y → x ↦̇ y → Set -- 2-morphism
  f ↦̈ g = ∀ a → f a ≡ g a -- non-strict equality of the 1-morphisms

  _∙∣̈∙_ : ∀ {x y} {f g h : x ↦̇ y} → g ↦̈ h → f ↦̈ g → f ↦̈ h -- vertical composition of 2-morphisms
  _∙∣̈∙_ β α x rewrite α x | β x = ∅

  _↦⃛_ : ∀ {x y} {f g : x ↦̇ y} → f ↦̈ g → f ↦̈ g → Set
  α ↦⃛ β = ∀ aa → α aa ≡ β aa

  -- there are probably more than just vertical and horizontal in 3-cats
  triple-vertical-comp : ∀ {x y} {f g : x ↦̇ y} {α : f ↦̈ g} {β : f ↦̈ g} {χ : f ↦̈ g} → β ↦⃛ χ → α ↦⃛ β → α ↦⃛ χ
  triple-vertical-comp x₁ x₂ aa = {!!}

  ∙∣̈∙-associative : ∀ {x y} {f g h i : x ↦̇ y} (α : f ↦̈ g) (β : g ↦̈ h) (χ : h ↦̈ i)
                    → (χ ∙∣̈∙ β) ∙∣̈∙ α ≡ χ ∙∣̈∙ (β ∙∣̈∙ α)
  ∙∣̈∙-associative α β χ = {!!}
```

It doesn't look like this is going to work either. I therefore abandon the (commented-out) work below and continue in the next chapter to investigate homotopy type theory as a possible savior here.

-- ### strict 2-category
--
-- This work is incomplete, maybe to be a
--
-- ```agda
-- record strict-2-cat
--   {o m₁ m₂} (O : Ø o) (_↦̇_ : O → O → Ø m₁) (_↦̈_ : ∀ {x y} → x ↦̇ y → x ↦̇ y → Ø m₂)
--   : Ø ↑̂ (o ∙̂ m₁ ∙̂ m₂) where
--   infixr 9 _∙̈_ _∙─̈∙_ _∙∣̈∙_
--   field
--     _∙̇_ : ∀ {x y z} → y ↦̇ z → x ↦̇ y → x ↦̇ z
--     _∙─̈∙_ : ∀ {x y z} {f g : x ↦̇ y} {h i : y ↦̇ z} → h ↦̈ i → f ↦̈ g → (h ∙̇ f) ↦̈ (i ∙̇ g)
--     _∙∣̈∙_ : ∀ {x y} {f g h : x ↦̇ y} → f ↦̈ g → g ↦̈ h → f ↦̈ h
--
--
-- {- This can't work b/c we don't have an appropriate equality sufficient to prove Cat .cat.∙-associativity -}

-- ### Cat
--
-- ```agda
-- Cat : ∀ {o m} {O : Ø o} {_↦_ : O → O → Ø m} → cat (cat O _↦_) fun
-- Cat .cat._∙_ G F .fun.𝐹₀ = G .fun.𝐹₀ ∘ F .fun.𝐹₀
-- Cat .cat._∙_ G F .fun.⦃⌶𝐹₁⦄ .⋆ = G .fun.⦃⌶𝐹₁⦄ .⋆ ∘ F .fun.⦃⌶𝐹₁⦄ .⋆
-- Cat .cat._∙_ G F .fun.𝐹₁-commutativity f g
--   rewrite G .fun.𝐹₁-commutativity (fun.𝐹₁′ F f) (fun.𝐹₁′ F g)
--         | F .fun.𝐹₁-commutativity f g
--   = ∅
-- Cat .cat._∙_ G F .fun.𝐹₁-identity x
--   rewrite
--     F .fun.𝐹₁-identity x
--   | G .fun.𝐹₁-identity (F .fun.𝐹₀ x)
--   = ∅
-- Cat .cat.∙-associativity F G H = {!!}
-- Cat .cat.⦃⌶𝟏⦄ .⋆ = {!!}
-- Cat .cat.𝟏-left-unitary = {!!}
-- Cat .cat.𝟏-right-unitary = {!!}
-- ```



-- Wherein I try some things with bicategories. This is a failed attempt that may eventually be d

-- ## operations on functors

-- ```agda
-- fun-id : ∀ {o m} {O : Ø o} {_↦_ : O → O → Ø m} (C : cat O _↦_) → fun C C
-- fun-id _ .fun.𝐹₀ = ¡
-- fun-id _ .fun.⦃⌶𝐹₁⦄ .⋆ = ¡
-- fun-id _ .fun.𝐹₁-commutativity _ _ = ∅
-- fun-id _ .fun.𝐹₁-identity _ = ∅

-- const-fun : ∀
--   {o₁ m₁} {O₁ : Ø o₁} {_↦₁_ : O₁ → O₁ → Ø m₁}
--   {o₂ m₂} {O₂ : Ø o₂} {_↦₂_ : O₂ → O₂ → Ø m₂}
--   {x y} (f : x ↦₂ y)
--   (C₁ : cat O₁ _↦₁_)
--   (C₂ : cat O₂ _↦₂_)
--   → fun (C₁ ⨂ C₂) C₂
-- const-fun = {!!}
-- {-
-- fun-compose :
--   → fun B C
--   → fun A B
--   → fun A C
-- -}

-- open import Oscar.Class.Symmetry
-- import Oscar.Property.Setoid.Proposequality

-- record const
--   {o m}
--   {Obj : Ø o}
--   {Mor : Obj → Obj → Ø m}
--   {const₀ : Obj}
--   (const₁ : Mor const₀ const₀)
--   : Ø ↑̂ (o ∙̂ m) where
--   field
--     𝐶 : cat Obj Mor
--     is-const : cat.𝟏′ 𝐶 const₀ ≡ const₁

-- fun-apply-const : ∀
--   {o₁ o₂ o₃ m₁ m₂ m₃}
--   {Obj₁ : Ø o₁}
--   {Obj₂ : Ø o₂}
--   {Obj₃ : Ø o₃}
--   {Mor₁ : Obj₁ → Obj₁ → Ø m₁}
--   {Mor₂ : Obj₂ → Obj₂ → Ø m₂}
--   {Mor₃ : Obj₃ → Obj₃ → Ø m₃}
--   {C₁ : cat Obj₁ Mor₁}
--   {C₂ : cat Obj₂ Mor₂}
--   {C₃ : cat Obj₃ Mor₃}
--   → fun (C₁ ⨂ C₂) C₃
--   → (x₂ : Obj₂)
--   → (m₂ : Mor₂ x₂ x₂)
--   → (let instance _ = C₂ in m₂ ∙ m₂ ≡ m₂)
--   → fun C₁ C₃
-- fun-apply-const f x₂ m₂ i .fun.𝐹₀ x₁ = fun.𝐹₀ f (x₁ , x₂)
-- fun-apply-const f x₂ m₂ i .fun.⦃⌶𝐹₁⦄ .⋆ m₁ = fun.𝐹₁′ f (m₁ , m₂)
-- fun-apply-const f x₂ m₂ i .fun.𝐹₁-commutativity f₁ g₁ rewrite symmetry (fun.𝐹₁-commutativity f (f₁ , m₂) (g₁ , m₂)) | i = {!!} -- ∅
-- -- (f .fun.⦃⌶𝐹₁⦄ .⋆ ((.C₁ cat.∙ g₁) f₁ , m₂))
-- -- (f .fun.⦃⌶𝐹₁⦄ .⋆ ((.C₁ cat.∙ g₁) f₁ , (.C₂ cat.∙ m₂) m₂))
-- -- (f .fun.⦃⌶𝐹₁⦄ .⋆ ((.C₁ cat.∙ g₁) f₁ , m₂))
-- -- (f .fun.⦃⌶𝐹₁⦄ .⋆ ((.C₁ cat.∙ g₁) f₁ , (.C₂ cat.∙ m₂) m₂)) -- need m₂ ∙ m₂ ≡ m₂
-- fun-apply-const f x₂ m₂ i .fun.𝐹₁-identity = {!!}

-- fun-apply-const' : ∀
--   {o₁ o₂ o₃ m₁ m₂ m₃}
--   {Obj₁ : Ø o₁}
--   {Obj₂ : Ø o₂}
--   {Obj₃ : Ø o₃}
--   {Mor₁ : Obj₁ → Obj₁ → Ø m₁}
--   {Mor₂ : Obj₂ → Obj₂ → Ø m₂}
--   {Mor₃ : Obj₃ → Obj₃ → Ø m₃}
--   {C₁ : cat Obj₁ Mor₁}
--   {C₂ : cat Obj₂ Mor₂}
--   {C₃ : cat Obj₃ Mor₃}
--   → fun (C₁ ⨂ C₂) C₃
--   → (x₂ : Obj₂)
--   → (m₂ : Mor₂ x₂ x₂)
--   → (let instance _ = C₂ in m₂ ∙ m₂ ≡ m₂)
--   → fun C₁ C₃
-- fun-apply-const' f x₂ m₂ i .fun.𝐹₀ x₁ = fun.𝐹₀ f (x₁ , x₂)
-- fun-apply-const' f x₂ m₂ i .fun.⦃⌶𝐹₁⦄ .⋆ m₁ = fun.𝐹₁′ f (m₁ , m₂)
-- fun-apply-const' f x₂ m₂ i .fun.𝐹₁-commutativity f₁ g₁ rewrite symmetry (fun.𝐹₁-commutativity f (f₁ , m₂) (g₁ , m₂)) | i = {!!} -- ∅
-- -- (f .fun.⦃⌶𝐹₁⦄ .⋆ ((.C₁ cat.∙ g₁) f₁ , m₂))
-- -- (f .fun.⦃⌶𝐹₁⦄ .⋆ ((.C₁ cat.∙ g₁) f₁ , (.C₂ cat.∙ m₂) m₂))
-- -- (f .fun.⦃⌶𝐹₁⦄ .⋆ ((.C₁ cat.∙ g₁) f₁ , m₂))
-- -- (f .fun.⦃⌶𝐹₁⦄ .⋆ ((.C₁ cat.∙ g₁) f₁ , (.C₂ cat.∙ m₂) m₂)) -- need m₂ ∙ m₂ ≡ m₂
-- fun-apply-const' f x₂ m₂ i .fun.𝐹₁-identity = {!!}
-- ```

-- ## definition of bicategory

-- we want something like:

-- goal : fun (L ⨂ R) B → fun A L → fun A R → fun A B

-- _⊗_ : fun A L → fun A' R → fun (A ⨂ A') (L ⨂ R)

-- diagonal : fun (A ⨂ A) X → fun A X

-- _∙_ : fun B C → fun A B → fun A C

-- given : fun (B x y ⨂ B x x) (B x y)
-- a→l : fun (B x y) (B x y) -- fun-id (B x y)
-- a→r : fun (B x y) (B x x) -- const ? (𝟏₁ x)

-- a→l ⊗ a→r : fun (B x y ⨂ B x y) (B x y ⨂ B x x)
-- diagonal (a→l ⊗ a→r) : fun (B x y) (B x y ⨂ B x x)

-- goal lr→b a→l a→r = diagonal (a→l ⊗ a→r)

-- ```agda
-- record bicat {o m₁ m₂} (O : Ø o) (_↦₁_ : O → O → Ø m₁) (_↦₂_ : ∀ {x y} → x ↦₁ y → x ↦₁ y → Ø m₂) : Ø ↑̂ (o ∙̂ m₁ ∙̂ m₂) where
--   field
--     B : ∀ x y → cat (x ↦₁ y) _↦₂_
--     𝟏₁ : ∀ x → x ↦₁ x
--     horiz-∙ : ∀ x y z → fun (B y z ⨂ B x y) (B x z)
--     left-unitor : ∀ (x y : O)
--       (let instance _ = B x x)
--       → iso
--           {!(horiz-∙ x x y)!} -- (fun-apply-const (horiz-∙ x x y) (𝟏₁ x) (𝟏′ (𝟏₁ x)) (𝟏-left-unitary (𝟏′ (𝟏₁ x))))
--           (fun-id (B x y))
-- ```
