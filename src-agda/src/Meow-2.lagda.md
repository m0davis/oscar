# Chapter 2. The fun begins.

```agda
{-# OPTIONS --show-implicit #-}
```

```agda
module Meow-2 where

open import Oscar.Prelude renaming (_∙̂_ to _⊔_; ↑̂_ to lsuc)
open import Oscar.Data.Proposequality
```

We might as well also include these:

```agda
open import Oscar.Data.Constraint
open import Oscar.Data.¶
open import Oscar.Data.Descender
open import Oscar.Data.Substitunction
open import Oscar.Data.Term
open import Oscar.Data.Vec
```

```agda
module GenericInner where

  module _
    {ℓ 𝔠} {C : Ø 𝔠} (c : C) ⦃ _ : Constraint c ⦄ (method : Ø ℓ)
    where
    record ⌶ : Ø ℓ where
      constructor ∁
      field
        ⋆ : method

  open ⌶ public

  record cat {o m} (O : Set o) (_↦_ : O → O → Set m) : Set (lsuc (o ⊔ m)) where
    infixr 9 _∙_
    field
      _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
    private ⌶𝟏 = ⌶ _↦_ ∀ x → x ↦ x
    𝟏 : ⦃ _ : ⌶𝟏 ⦄ → ∀ x → x ↦ x
    𝟏 ⦃ I𝟏 ⦄ = I𝟏 .⋆
    field
      ⦃ ⦃⌶𝟏⦄ ⦄ : ⌶𝟏
      𝟏-left-unitary  : ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f

  open cat ⦃ … ⦄ public hiding (⦃⌶𝟏⦄)

  infixr 9 cat-∙
  cat-∙ : ∀ {o m} {O : Set o} (_↦_ : O → O → Set m) ⦃ _ : cat O _↦_ ⦄ → ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
  cat-∙ _ = _∙_

  syntax cat-∙ _↦_ g f = g ∙[ _↦_ ] f

  module _
    (O₁ : Set)
    (_↦₁_ : O₁ → O₁ → Set)
    ⦃ _ : cat O₁ _↦₁_ ⦄
    (O₂ : Set)
    (_↦₂_ : O₂ → O₂ → Set)
    (_↦₂'_ : O₂ → O₂ → Set)
    ⦃ _ : cat O₂ _↦₂_ ⦄
    ⦃ _ : cat O₂ _↦₂'_ ⦄
    where
    _ : ∀ (x : O₁) → 𝟏 x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary _

    _ : ∀ x → 𝟏 {_↦_ = _↦₂_} x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary _

    _ : ∀ {w x y z} (f : w ↦₁ x) (g : x ↦₁ y) (h : y ↦₁ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
    _ = ∙-associativity

    _ : ∀ {x y z} (f : x ↦₁ y) (h : y ↦₁ z) → (h ∙ 𝟏 _) ∙ f ≡ h ∙ 𝟏 _ ∙ f
    _ = λ f h → ∙-associativity _ _ _

  module _
    (O₁ : Set)
    (_↦₁_ : O₁ → O₁ → Set)
    ⦃ _ : cat O₁ _↦₁_ ⦄
    (O₂ : Set)
    (_↦₂_ : O₂ → O₂ → Set)
    (_↦₂'_ : O₂ → O₂ → Set)
    ⦃ _ : cat O₂ _↦₂_ ⦄
    ⦃ _ : cat O₂ _↦₂'_ ⦄
    (P₁ : O₁ → Set)
    (o₁ : O₁)
    (_P↦₁_ : ∀ {x} → P₁ x → P₁ x → Set)
    ⦃ _ : cat (∃ P₁) (λ {(x₁ , p₁) (x₂ , p₂) → Σ (x₁ ≡ x₂) (λ {∅ → p₁ P↦₁ p₂})}) ⦄
    (P₂ : O₂ → Set)
    (o₂ : O₂)
    (_P↦₂_ : ∀ {x} → P₂ x → P₂ x → Set)
    ⦃ _ : cat (P₂ o₂) _P↦₂_ ⦄
    (O₃ : Set)
    (o₃ : O₃)
    (P₃ : O₃ → Set)
    (_P↦₃_ : ∀ {x} → P₃ x → P₃ x → Set)
    ⦃ _ : ∀ {x} → cat (P₃ x) _P↦₃_ ⦄ -- this approach doesn't work. try something like in `_P↦₁_` instead
    (O₄ : Set)
    (o₄ o₄' : O₄)
    (R₄ : O₄ → O₄ → O₄ → Set)
    ⦃ icat₄ : ∀ {x} → cat O₄ (R₄ x) ⦄ -- this is also troublesome -- TODO: find a solution? the solution found for _P↦₃_ doesn't seem to work here.
    (O₅ : Set)
    (o₅ : O₅)
    (R₅ : O₅ → O₅ → O₅ → Set)
    ⦃ icat₅ : ∀ {x} → cat O₅ (R₅ x) ⦄
    where

    _ : ∀ (x : O₁) → 𝟏 x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary _

    _ : ∀ x → 𝟏 {_↦_ = _↦₂_} x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary _

    _ : ∀ {w x y z} (f : w ↦₁ x) (g : x ↦₁ y) (h : y ↦₁ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
    _ = ∙-associativity

    _ : ∀ {x y z} (f : x ↦₁ y) (h : y ↦₁ z) → (h ∙ 𝟏 _) ∙ f ≡ h ∙ 𝟏 _ ∙ f
    _ = λ f h → ∙-associativity _ _ _

    _ : ∀ {i} (x : P₁ i) → 𝟏 (i Σ., x) ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary _

    _ : ∀ (x : P₂ o₂) → 𝟏 x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary _

    {- FIXME
    _ : ∀ (x : P₃ o₃) → 𝟏 x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)
    -}

    {- FIXME
    _ : ∀ {i} (x : P₃ i) → 𝟏 x ∙ 𝟏 x ≡ 𝟏 x
    _ = {!!}
    -}

    {- FIXME
    _ : 𝟏 o₄ ∙ 𝟏 _ ≡ 𝟏 _
    _ = {!!}
    -}

    _ : R₄ o₄' o₄ o₄
    _ = 𝟏 {_↦_ = R₄ o₄'} ⦃ icat₄ {o₄'} ⦄ ⦃ cat.⦃⌶𝟏⦄ (icat₄ {o₄'}) ⦄ o₄ -- TODO explain why we need to specify the second instance argument

    _ : R₄ o₄' o₄ o₄
    _ = 𝟏 ⦃ ! ⦄ ⦃ cat.⦃⌶𝟏⦄ ! ⦄ o₄

    _ : 𝟏 ⦃ ! ⦄ ⦃ cat.⦃⌶𝟏⦄ ! ⦄ o₄ ∙ 𝟏 ⦃ icat₄ {o₄} ⦄ ⦃ cat.⦃⌶𝟏⦄ ! ⦄ _ ≡ 𝟏 ⦃ icat₄ {o₄} ⦄ ⦃ cat.⦃⌶𝟏⦄ ! ⦄ _
    _ = 𝟏-left-unitary _

  instance

    function⌶𝟏 : ∀ {ℓ} → ⌶ Function⟦ ℓ ⟧ (∀ x → Function⟦ ℓ ⟧ x x)
    function⌶𝟏 .⋆ _ = ¡

    functionCat : ∀ {ℓ} → cat (Ø ℓ) Function
    functionCat .cat._∙_ = _∘′_
    functionCat .cat.∙-associativity _ _ _ = ∅
    functionCat .cat.⦃⌶𝟏⦄ = !
    functionCat .cat.𝟏-left-unitary _ = ∅
    functionCat .cat.𝟏-right-unitary _ = ∅

  module _ where

    _ : 𝟏 Set ∙ 𝟏 _ ≡ 𝟏 _
    _ = 𝟏-left-unitary _

    _ : ∀ x → Function⟦ ∅̂ ⟧ x x
    _ = λ x → 𝟏 x

    _ : 𝟏 Set ∙[ Function ] 𝟏 _ ≡ 𝟏 _
    _ = 𝟏-left-unitary _

  instance

    proposequality⌶𝟏 : ∀ {a} {A : Ø a} → ⌶ Proposequality⟦ A ⟧ ∀ x → Proposequality⟦ A ⟧ x x
    proposequality⌶𝟏 .⋆ _ = ∅

    proposequalityCat : ∀ {a} {A : Ø a} → cat A Proposequality⟦ A ⟧
    proposequalityCat .cat._∙_ ∅ f = f
    proposequalityCat .cat.∙-associativity f g ∅ = ∅
    proposequalityCat .cat.⦃⌶𝟏⦄ = !
    proposequalityCat .cat.𝟏-left-unitary _ = ∅
    proposequalityCat .cat.𝟏-right-unitary ∅ = ∅

  module _ where

    _ : 𝟏 Set ∙[ Function ] 𝟏 _ ≡ 𝟏 _
    _ = 𝟏-left-unitary _

    _ : _∙_ {_↦_ = Function⟦ lsuc ∅̂ ⟧} (𝟏 Set) (𝟏 _) ≡ 𝟏 _
    _ = 𝟏-left-unitary _

    {- FIXME
    _ : 𝟏 Set ∙ 𝟏 _ ≡ 𝟏 _
    _ = {!!} -- 𝟏-left-unitary _
    -}

    _ : 𝟏 Set ∙[ Proposequality ] 𝟏 _ ≡ 𝟏 _
    _ = 𝟏-left-unitary _

    _ : ∀ x → Function⟦ ∅̂ ⟧ x x
    _ = λ x → 𝟏 x

  module _
    (I : Set)
    (A : I → Set)
    where
    _ : ∀ x → A x → A x
    _ = λ x → 𝟏 _

    _ : ∀ x y z → (f : A x → A y) (g : A y → A z) → A x → A z
    _ = λ x y z f g → g ∙ f

-- {- FIXME
  instance

    extension⌶𝟏 : ∀ {a} {A : Ø a} {b} {B : A → Ø b} → ⌶ (Extension B) ∀ x → Extension B x x
    extension⌶𝟏 .⋆ _ = ¡

    extensionCat : ∀ {a} {A : Ø a} {b} {B : A → Ø b} → cat A (Extension B)
    extensionCat .cat._∙_ = _∘′_
    extensionCat .cat.∙-associativity _ _ _ = ∅
    extensionCat .cat.⦃⌶𝟏⦄ = !
    extensionCat .cat.𝟏-left-unitary _ = ∅
    extensionCat .cat.𝟏-right-unitary _ = ∅

  module _
    (I : Set)
    (A : I → Set)
    where
    _ : ∀ x → A x → A x
    _ = λ x → 𝟏 {_↦_ = Function} (A x)

    _ : ∀ x y z → (f : A x → A y) (g : A y → A z) → A x → A z
    _ = λ x y z f g → g ∙[ Function ] f

  module _ {a} {A : ¶ → Set a} where

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

To define the composition operation for the category of `Substitunction` morphisms, it is convenient to use the mapping operation of the functor from the category of `Substitunction` morphisms to the category of `Extension Term` morphisms. This is not circular, but it may be tricky to convince Agda of this.

Let's try a naive approach first and define functors on the basis of categories.

```agda
  record fun
    {o₁ m₁} (O₁ : Set o₁) (_↦₁_ : O₁ → O₁ → Set m₁)
    {o₂ m₂} (O₂ : Set o₂) (_↦₂_ : O₂ → O₂ → Set m₂)
    ⦃ C₁ : cat O₁ _↦₁_ ⦄
    ⦃ C₂ : cat O₂ _↦₂_ ⦄
    : Set (lsuc (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂)) where
    field
      F₀ : O₁ → O₂
      F₁ : ∀ {x y} → x ↦₁ y → F₀ x ↦₂ F₀ y
      F₁-commutativity : ∀ {x y z} (f : x ↦₁ y) (g : y ↦₁ z) → F₁ (g ∙ f) ≡ F₁ g ∙ F₁ f
      F₁-identity : ∀ x → F₁ (𝟏 x) ≡ 𝟏 _

  open fun ⦃ … ⦄ public
```

Here is a failed attempt that I would have thought worked, but there's something apparently wrong in Agda. TODO: produce a simplified test case

The error is

    .y != substitunctionExtensionTermFun .fun.F₀ .y of type ¶
    when checking that the expression f has type
    .Oscar.Data.Fin.¶⟨< .x ⟩ →
    Term (substitunctionExtensionTermFun .fun.F₀ .y)

```agda
{- FIXME
  module _ {𝔭} {𝔓 : Ø 𝔭} where

    open Substitunction 𝔓
    open Term 𝔓

    instance
      substitunction⌶𝟏 : ⌶ Substitunction ∀ x → Substitunction x x
      substitunction⌶𝟏 .⋆ _ = i

      substitunctionCat : cat ¶ Substitunction

      substitunctionExtensionTermFun : fun _ Substitunction _ (Extension Term)

    substitunctionCat .cat._∙_ g f = F₁ {_↦₁_ = Substitunction} {_↦₂_ = Extension Term} ⦃ substitunctionCat ⦄ ⦃ extensionCat ⦄ ⦃ substitunctionExtensionTermFun ⦄ g ∘′ f
    substitunctionCat .cat.∙-associativity = {!!}
    substitunctionCat .cat.⦃⌶𝟏⦄ = {!!}
    substitunctionCat .cat.𝟏-left-unitary = {!!}
    substitunctionCat .cat.𝟏-right-unitary = {!!}

    substitunctionExtensionTermFun .fun.F₀ = ¡
    substitunctionExtensionTermFun .fun.F₁ f = magic
    substitunctionExtensionTermFun .fun.F₁-commutativity = {!!}
    substitunctionExtensionTermFun .fun.F₁-identity = {!!}
-}
```

By moving the definition of `substitunctionExtensionTermFun` such that it is no longer mutually-defined with `substitunctionCat`, we get around the above problem. However, there is another problem below which forces us to give more specification of the sort of functor we want to use than I would have thought necessary.

That is, we must write things like `F₁ {_↦₂_ = Extension Term}` instead of simply `F₁`. I guess the reason is because Agda is eagerly trying to figure out what instance of the functor to choose, but doesn't know if it's the one for ExtensionTerm or ExtensionTerms until after the application. An idea that comes to mind is to use an applicative functor (because there are two arguments to such a thing) but of course the usual version of that doesn't have quite the right shape. TODO is there another concept from category theory that would fit here?

A more straightforward solution is to find a way to get Agda to delay resolving the instance. This then has the feel of what solution we found for `Identity` in categories. Notice that, just as in the case with categories, the `F₁` field does not totally use-up its type-constructors: we are quantifying into `F₀ x ↦₂ F₀ y` rather than `x ↦₂ y`. TODO: try using `⌶` for `F₁`.

In the below, the error is

    .x != (substitunctionExtensionTermsFun {N} .fun.F₀ .x) of type ¶
    when checking that the expression ts has type
    Terms N (substitunctionExtensionTermsFun {N} .fun.F₀ .x)

```agda
{- FIXME
  module _ {𝔭} {𝔓 : Ø 𝔭} where

    open Substitunction 𝔓
    open Term 𝔓

    instance
      substitunction⌶𝟏 : ⌶ Substitunction ∀ x → Substitunction x x
      substitunction⌶𝟏 .⋆ _ = i

      substitunctionCat : cat ¶ Substitunction

      substitunctionExtensionTermFun : fun _ Substitunction _ (Extension Term)
      substitunctionExtensionTermsFun : ∀ {N} → fun _ Substitunction _ (Extension $ Terms N)

      substitunctionExtensionTermFun .fun.F₀ = ¡
      substitunctionExtensionTermFun .fun.F₁ f (i x) = f x
      substitunctionExtensionTermFun .fun.F₁ f leaf = leaf
      substitunctionExtensionTermFun .fun.F₁ f (x₁ fork x₂) = F₁ {_↦₂_ = Extension Term} f x₁ fork F₁ {_↦₂_ = Extension Term} f x₂
      substitunctionExtensionTermFun .fun.F₁ f (function p {N} ts) =
        function p
          (F₁ {_↦₂_ = Extension (Terms N)} f ts) -- FIXME this refines but then does not typecheck
      substitunctionExtensionTermFun .fun.F₁-commutativity = {!!}
      substitunctionExtensionTermFun .fun.F₁-identity = {!!}

      substitunctionExtensionTermsFun .fun.F₀ = ¡
      substitunctionExtensionTermsFun {N} .fun.F₁ f ∅ = ∅
      -- substitunctionExtensionTermsFun {N} .fun.F₁ f (t , ts) = (F₁ f $ t) , {!!} -- NB F₁ f t doesn't work either. FIXME
      substitunctionExtensionTermsFun {N} .fun.F₁ f (t , ts) = F₁ {_↦₂_ = Extension Term} f t , {!!}
      substitunctionExtensionTermsFun {N} .fun.F₁-commutativity = {!!}
      substitunctionExtensionTermsFun {N} .fun.F₁-identity = {!!}

    substitunctionCat .cat._∙_ g f = F₁ {_↦₂_ = Extension Term} g ∘′ f
    substitunctionCat .cat.∙-associativity = {!!}
    substitunctionCat .cat.⦃⌶𝟏⦄ = {!!}
    substitunctionCat .cat.𝟏-left-unitary = {!!}
    substitunctionCat .cat.𝟏-right-unitary = {!!}
-}
```

Before we redefine functors, let's preserve our good work on categories. (We perhaps could have done this by simply hiding `fun`.)

```agda
module GoodCat where

  open GenericInner public
    using
      (⌶; ⋆; cat; module cat; cat-∙
      ;function⌶𝟏; functionCat
      ;proposequality⌶𝟏; proposequalityCat
      ;extension⌶𝟏; extensionCat
      ;alist⌶𝟏; alistCat
      )

  open cat ⦃ … ⦄ public hiding (⦃⌶𝟏⦄)
```

And now to redefine functors.

```agda
module RedefineFun where

  open GoodCat

  record fun
    {o₁ m₁}
    {o₂ m₂} (O₁ : Set o₁) (_↦₁_ : O₁ → O₁ → Set m₁) (O₂ : Set o₂) (_↦₂_ : O₂ → O₂ → Set m₂)
    ⦃ C₁ : cat O₁ _↦₁_ ⦄
    ⦃ C₂ : cat O₂ _↦₂_ ⦄
    : Set (lsuc (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂)) where
    field
      F₀ : O₁ → O₂
    private ⌶F₁ = ⌶ _↦₂_ ∀ {x y} → x ↦₁ y → F₀ x ↦₂ F₀ y
    F₁ : ⦃ _ : ⌶F₁ ⦄ → ∀ {x y} → x ↦₁ y → F₀ x ↦₂ F₀ y
    F₁ ⦃ iF₁ ⦄ = iF₁ .⋆
    field
      ⦃ ⦃⌶F₁⦄ ⦄ : ⌶F₁
      F₁-commutativity : ∀ {x y z} (f : x ↦₁ y) (g : y ↦₁ z) → F₁ (g ∙ f) ≡ F₁ g ∙ F₁ f
      F₁-identity : ∀ x → F₁ (𝟏 x) ≡ 𝟏 _

  open fun ⦃ … ⦄ public
```

Let's now re-try the first (originally failed) attempt at a functor between `Substitunction` and `Extension Term`.

We'll need to introduce a separately-define instance for the functor mapping of morphisms.

The error is similar to what we got before:

    fun.F₀ substitunctionExtensionTermFun x != x of type ¶
    when checking that the expression substitunctionExtensionTerm⌶F₁
    has type
    .Meow-2.RedefineFun.fun.⌶F₁ {∅̂} {𝔭} {∅̂} {𝔭} {¶} {Substitunction}
    {¶} {Extension {∅̂} {¶} {𝔭} (λ z → Term z)} {{substitunctionCat}}
    {{extensionCat {∅̂} {¶} {𝔭} {λ z → Term z}}}
    substitunctionExtensionTermFun

```agda
{- FIXME
  module _ {𝔭} {𝔓 : Ø 𝔭} where

    open Substitunction 𝔓
    open Term 𝔓

    instance
      substitunction⌶𝟏 : ⌶ Substitunction ∀ x → Substitunction x x
      substitunction⌶𝟏 .⋆ _ = i

      substitunctionExtensionTerm⌶F₁ : ⌶ (Extension Term) ∀ {x y} → Substitunction x y → Extension Term x y
      substitunctionExtensionTerm⌶F₁ = {!!}

      substitunctionCat : cat ¶ Substitunction

      substitunctionExtensionTermFun : fun _ Substitunction _ (Extension Term) ⦃ substitunctionCat ⦄ ⦃ extensionCat ⦄

    substitunctionCat .cat._∙_ g f = F₁ {_↦₂_ = {!Extension Term!}} ⦃ substitunctionCat ⦄ ⦃ extensionCat ⦄ ⦃ substitunctionExtensionTermFun ⦄ ⦃ substitunctionExtensionTerm⌶F₁ ⦄ g ∘′ f
    substitunctionCat .cat.∙-associativity = {!!}
    substitunctionCat .cat.⦃⌶𝟏⦄ = {!!}
    substitunctionCat .cat.𝟏-left-unitary = {!!}
    substitunctionCat .cat.𝟏-right-unitary = {!!}

    substitunctionExtensionTermFun .fun.F₀ = ¡
    substitunctionExtensionTermFun .fun.⦃⌶F₁⦄ = !
    substitunctionExtensionTermFun .fun.F₁-commutativity = {!!}
    substitunctionExtensionTermFun .fun.F₁-identity = {!!}
-}
```

How about our second failed attempt?

It fails the same way.

    fun.F₀ substitunctionExtensionTermFun x != x of type ¶
    when checking that the expression substitunctionExtensionTerm⌶F₁
    has type
    .Meow-2.RedefineFun.fun.⌶F₁ {∅̂} {𝔭} {∅̂} {𝔭} {¶} {Substitunction}
    {¶} {Extension {∅̂} {¶} {𝔭} Term} {{substitunctionCat}}
    {{extensionCat {∅̂} {¶} {𝔭} {λ z → Term z}}}
    substitunctionExtensionTermFun

```agda
{- FIXME
  module _ {𝔭} {𝔓 : Ø 𝔭} where

    open Substitunction 𝔓
    open Term 𝔓

    instance

      substitunction⌶𝟏 : ⌶ Substitunction ∀ x → Substitunction x x
      substitunction⌶𝟏 .⋆ _ = i

      substitunctionCat : cat ¶ Substitunction
      substitunctionExtensionTermFun : fun _ Substitunction _ (Extension Term)

      substitunctionExtensionTerm⌶F₁ : ⌶ (Extension Term) ∀ {x y} → Substitunction x y → Extension Term x y
      substitunctionExtensionTerms⌶F₁ : ∀ {N} → ⌶ (Extension $ Terms N) ∀ {x y} → Substitunction x y → Extension (Terms N) x y

      substitunctionExtensionTerm⌶F₁ .⋆ f (i x) = f x
      substitunctionExtensionTerm⌶F₁ .⋆ f leaf = leaf
      substitunctionExtensionTerm⌶F₁ .⋆ f (x₁ fork x₂) =
        F₁ {_↦₂_ = Extension Term} ⦃ r = substitunctionExtensionTermFun ⦄ ⦃ substitunctionExtensionTerm⌶F₁ ⦄ f x₁ -- FIXME
          fork
        {!F₁ {_↦₂_ = Extension Term} f x₂!}
      substitunctionExtensionTerm⌶F₁ .⋆ f (function p {N} ts) =
        function p
          {!(F₁ {_↦₂_ = Extension (Terms N)} f ts)!}

      substitunctionExtensionTerms⌶F₁ .⋆ f ∅ = ∅
      substitunctionExtensionTerms⌶F₁ .⋆ f (t , ts) = F₁ f t , {!!}

      substitunctionExtensionTermsFun : ∀ {N} → fun _ Substitunction _ (Extension $ Terms N)

      substitunctionExtensionTermFun .fun.F₀ = ¡
      substitunctionExtensionTermFun .fun.⦃⌶F₁⦄ = !
      substitunctionExtensionTermFun .fun.F₁-commutativity = {!!}
      substitunctionExtensionTermFun .fun.F₁-identity = {!!}

      substitunctionExtensionTermsFun .fun.F₀ = ¡
      substitunctionExtensionTermsFun .fun.⦃⌶F₁⦄ = !
      substitunctionExtensionTermsFun {N} .fun.F₁-commutativity = {!!}
      substitunctionExtensionTermsFun {N} .fun.F₁-identity = {!!}

    substitunctionCat .cat._∙_ g f = F₁ {_↦₂_ = Extension Term} g ∘′ f
    substitunctionCat .cat.∙-associativity = {!!}
    substitunctionCat .cat.⦃⌶𝟏⦄ = {!!}
    substitunctionCat .cat.𝟏-left-unitary = {!!}
    substitunctionCat .cat.𝟏-right-unitary = {!!}
-}
```

Let's cheat a bit and add-in the use of `F₀` to the functor map type.

This only pushes the problem down the road.

```agda
{- FIXME
  module _ {𝔭} {𝔓 : Ø 𝔭} where

    open Substitunction 𝔓
    open Term 𝔓

    instance

      substitunction⌶𝟏 : ⌶ Substitunction ∀ x → Substitunction x x
      substitunction⌶𝟏 .⋆ _ = i

      substitunctionCat : cat ¶ Substitunction
      substitunctionExtensionTermFun : fun _ Substitunction _ (Extension Term)

      substitunctionExtensionTerm⌶F₁ : ⌶ (Extension Term) ∀ {x y} → Substitunction x y → Extension Term (F₀ {_↦₁_ = Substitunction} {_↦₂_ = Extension Term} x) (F₀ {_↦₁_ = Substitunction} {_↦₂_ = Extension Term} y)
      substitunctionExtensionTerms⌶F₁ : ∀ {N} → ⌶ (Extension $ Terms N) ∀ {x y} → Substitunction x y → Extension (Terms N) x y

      substitunctionExtensionTerm⌶F₁ .⋆ f (i x) = f x -- FIXME
      substitunctionExtensionTerm⌶F₁ .⋆ f leaf = leaf
      substitunctionExtensionTerm⌶F₁ .⋆ f (x₁ fork x₂) =
        F₁ {_↦₂_ = Extension Term} ⦃ r = substitunctionExtensionTermFun ⦄ ⦃ substitunctionExtensionTerm⌶F₁ ⦄ f x₁
        -- FIXME
          fork
        {!F₁ {_↦₂_ = Extension Term} f x₂!}
      substitunctionExtensionTerm⌶F₁ .⋆ f (function p {N} ts) =
        function p
          {!(F₁ {_↦₂_ = Extension (Terms N)} f ts)!}

      substitunctionExtensionTerms⌶F₁ .⋆ f ∅ = ∅
      substitunctionExtensionTerms⌶F₁ .⋆ f (t , ts) = F₁ f t , {!!}

      substitunctionExtensionTermFun .fun.F₀ = ¡
      substitunctionExtensionTermFun .fun.⦃⌶F₁⦄ = !
      substitunctionExtensionTermFun .fun.F₁-commutativity = {!!}
      substitunctionExtensionTermFun .fun.F₁-identity = {!!}

      substitunctionExtensionTermsFun : ∀ {N} → fun _ Substitunction _ (Extension $ Terms N)

      substitunctionExtensionTermsFun .fun.F₀ = ¡
      substitunctionExtensionTermsFun .fun.⦃⌶F₁⦄ = !
      substitunctionExtensionTermsFun {N} .fun.F₁-commutativity = {!!}
      substitunctionExtensionTermsFun {N} .fun.F₁-identity = {!!}

    substitunctionCat .cat._∙_ g f = F₁ {_↦₂_ = Extension Term} g ∘′ f
    substitunctionCat .cat.∙-associativity = {!!}
    substitunctionCat .cat.⦃⌶𝟏⦄ = {!!}
    substitunctionCat .cat.𝟏-left-unitary = {!!}
    substitunctionCat .cat.𝟏-right-unitary = {!!}
-}
```

If we then rearrange the mutually-defined functions, we get a problem with termination checking, which is at least a known problem in Agda (issue #?)

```agda
{- FIXME
  module _ {𝔭} {𝔓 : Ø 𝔭} where

    open Substitunction 𝔓
    open Term 𝔓

    instance

      substitunction⌶𝟏 : ⌶ Substitunction ∀ x → Substitunction x x
      substitunction⌶𝟏 .⋆ _ = i

      substitunctionCat : cat ¶ Substitunction
      substitunctionExtensionTermFun : fun _ Substitunction _ (Extension Term)

      substitunctionExtensionTerm⌶F₁ :
        ⌶ (Extension Term) ∀ {x y} → Substitunction x y → Extension Term x y
        -- ⌶ (Extension Term) ∀ {x y} → Substitunction x y → Extension Term (F₀ {_↦₁_ = Substitunction} {_↦₂_ = Extension Term} x) (F₀ {_↦₁_ = Substitunction} {_↦₂_ = Extension Term} y)
      substitunctionExtensionTerms⌶F₁ : ∀ {N} → ⌶ (Extension $ Terms N) ∀ {x y} → Substitunction x y → Extension (Terms N) x y

      -- we've lifted this from below
      substitunctionExtensionTermFun .fun.F₀ = ¡
      substitunctionExtensionTermFun .fun.⦃⌶F₁⦄ = !
      substitunctionExtensionTermFun .fun.F₁-commutativity = {!!}
      substitunctionExtensionTermFun .fun.F₁-identity = {!!}

      substitunctionExtensionTerm⌶F₁ .⋆ f (i x) = f x -- FIXME
      substitunctionExtensionTerm⌶F₁ .⋆ f leaf = leaf
      substitunctionExtensionTerm⌶F₁ .⋆ f (x₁ fork x₂) =
        F₁ {_↦₂_ = Extension Term} ⦃ r = substitunctionExtensionTermFun ⦄ ⦃ substitunctionExtensionTerm⌶F₁ ⦄ f x₁
        -- FIXME
          fork
        {!F₁ {_↦₂_ = Extension Term} f x₂!}
      substitunctionExtensionTerm⌶F₁ .⋆ f (function p {N} ts) =
        function p
          {!(F₁ {_↦₂_ = Extension (Terms N)} f ts)!}

      substitunctionExtensionTerms⌶F₁ .⋆ f ∅ = ∅
      substitunctionExtensionTerms⌶F₁ .⋆ f (t , ts) = F₁ f t , {!!}

      substitunctionExtensionTermsFun : ∀ {N} → fun _ Substitunction _ (Extension $ Terms N)

      substitunctionExtensionTermsFun .fun.F₀ = ¡
      substitunctionExtensionTermsFun .fun.⦃⌶F₁⦄ = !
      substitunctionExtensionTermsFun {N} .fun.F₁-commutativity = {!!}
      substitunctionExtensionTermsFun {N} .fun.F₁-identity = {!!}

    substitunctionCat .cat._∙_ g f = F₁ {_↦₂_ = Extension Term} g ∘′ f
    substitunctionCat .cat.∙-associativity = {!!}
    substitunctionCat .cat.⦃⌶𝟏⦄ = {!!}
    substitunctionCat .cat.𝟏-left-unitary = {!!}
    substitunctionCat .cat.𝟏-right-unitary = {!!}
-}
```

To get around the termination-checking problem for instances, we simply define the mutual functions w/o instances. For now, I'll get this done by importing previous work.

```agda
  import Oscar.Property.Functor.SubstitunctionExtensionTerm
  open import Oscar.Class.Smap using (smap)

  module _ {𝔭} {𝔓 : Ø 𝔭} where

    open Substitunction 𝔓
    open Term 𝔓

    instance

      substitunction⌶𝟏 : ⌶ Substitunction ∀ x → Substitunction x x
      substitunction⌶𝟏 .⋆ _ = i

      substitunctionExtensionTerm⌶F₁ : ⌶ (Extension Term) ∀ {x y} → Substitunction x y → Extension Term x y
      substitunctionExtensionTerm⌶F₁ .⋆ = smap

      substitunctionExtensionTerms⌶F₁ : ∀ {N} → ⌶ (Extension $ Terms N) ∀ {x y} → Substitunction x y → Extension (Terms N) x y
      substitunctionExtensionTerms⌶F₁ .⋆ = smap

      substitunctionCat : cat ¶ Substitunction
      substitunctionExtensionTermFun : fun _ Substitunction _ (Extension Term)
      substitunctionExtensionTermsFun : ∀ {N} → fun _ Substitunction _ (Extension $ Terms N)

      substitunctionExtensionTermFun .fun.F₀ = ¡
      substitunctionExtensionTermFun .fun.⦃⌶F₁⦄ = !
      substitunctionExtensionTermFun .fun.F₁-commutativity = {!!}
      substitunctionExtensionTermFun .fun.F₁-identity x = {!𝟏-!}

      substitunctionExtensionTermsFun .fun.F₀ = ¡
      substitunctionExtensionTermsFun .fun.⦃⌶F₁⦄ = !
      substitunctionExtensionTermsFun .fun.F₁-commutativity = {!!}
      substitunctionExtensionTermsFun .fun.F₁-identity = {!!}

      substitunctionCat .cat._∙_ g f = F₁ g ∘′ f
      substitunctionCat .cat.∙-associativity = {!!}
      substitunctionCat .cat.⦃⌶𝟏⦄ = !
      substitunctionCat .cat.𝟏-left-unitary = {!!}
      substitunctionCat .cat.𝟏-right-unitary = {!!}
```

At least now we have proceeded without errors, and it's nice that we can simply use `F₁`, but we cannot prove the laws! ...because we're using the wrong "equality". This leads directly to the next item on the TODO: what about Oscar.Property.Category.ExtensionProposextensequality?

At this point, I'd like to develop higher categories. The 2-category is (I think) rich enough to include different notions of equality. To be continued in the next chapter.
