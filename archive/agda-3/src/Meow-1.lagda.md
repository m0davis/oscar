# Chapter 1. A new cat.

```agda
{-# OPTIONS --show-implicit #-}
```

Given a set of categories, can we expose operations on the category (composition of morphism, identity morphism, laws of associativity, identity) without "too much" fuss?

Obviously, if there are two categories with the same morphism but differing methods of composition, the user will need to specify the method (or something else that distinguishes the category). What is a practical situation in which this might arise?

I imagine that the set of categories will be specified by instances. But other possibilities are conceivable. How about a universe of categories specified by some datatype?

What if the set of categories is infinite (i.e. specified using quantification)⁇  What horrors possibly lurk here?

If all goes well (: and it won't :), extend to functors, natural transformations, higher categories, and on and on. Significant mileposts include:

* categories with alternative notions of morphism equality
* categories that define applicative functors

```agda
module Meow-1 where

open import Oscar.Prelude renaming (_∙̂_ to _⊔_; ↑̂_ to lsuc)
open import Oscar.Data.Proposequality
```

# Using First-Order Instances
```agda
module UsingFirstOrderInstances where
```

First, let's make a small `cat`. I arrange the structure so that the operations to be exposed are all and only the fields.

```agda
  record cat {o m} (O : Set o) (_↦_ : O → O → Set m) : Set (o ⊔ m) where
    infixr 9 _∙_
    field
      _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      𝟏 : ∀ x → x ↦ x
      𝟏-left-unitary : ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f
```

Next, let's construct a few categories and go for a test drive.

```agda
  postulate
    O₁ : Set
    _↦₁_ : O₁ → O₁ → Set
    cat₁ : cat O₁ _↦₁_
    O₂ : Set
    _↦₂_ : O₂ → O₂ → Set
    cat₂ : cat O₂ _↦₂_

  module C₁ = cat cat₁
  module C₂ = cat cat₂

  𝟏-isomorphism₁ : ∀ x → C₁.𝟏 x C₁.∙ C₁.𝟏 _ ≡ C₁.𝟏 _
  𝟏-isomorphism₁ x = C₁.𝟏-left-unitary (C₁.𝟏 x)
```

I'd like to be able to write this without the module specifications, i.e. `∀ (x : O₁) → (𝟏 x) ∙ 𝟏 _ ≡ 𝟏 _`.

Let's try using instances!

```agda
  open cat ⦃ … ⦄ public

  instance i-cat₁ = cat₁

  postulate
    {- FIXME
    _ : ∀ (x : O₁) → 𝟏 x ∙ 𝟏 x ≡ 𝟏 x -- yellow
    -}
```

Hmm, that didn't work. The evils of unsolved meta-variables. The unsolved meta is the one associated with the `_↦_` parameter to `cat`.

Notice that we can help Agda:

```agda
    _ : ∀ (x : O₁) → 𝟏 {_↦_ = _↦₁_} x ∙ 𝟏 x ≡ 𝟏 x
```

We'd like the `_↦_` parameter to be solved differently from Agda's builtin unification. Let's explore how this might be possible.

```agda
    {- FIXME
    _ : ∀ (x : O₁)
        → _≡_ {𝔬 = {!!}} {𝔒 = {!!}}
              (_∙_ {m = {!!}} {_↦_ = {!_↦₁_!}} ⦃ {!!!} ⦄ (𝟏 {m = {!!}} {_↦_ = {!!}} ⦃ {!!} ⦄ x) (𝟏 {m = {!!}} {_↦_ = {!!}} ⦃ {!!} ⦄ x))
              (𝟏 {m = {!!}} {_↦_ = {!!}} ⦃ {!!} ⦄ x)
    -}
```

Let's see if using higher-order instances helps.

```agda
  open import Oscar.Class
  open import Oscar.Class.Transitivity
  open import Oscar.Class.Reflexivity

  postulate
    _ : ⦃ _ : Reflexivity.class _↦₁_ ⦄
        ⦃ _ : Transitivity.class _↦₁_ ⦄
        (x : O₁) (let εₓ = reflexivity {x = x})
        → transitivity εₓ εₓ ≡ εₓ
```

Yup, it does. Let's reformulate `cat` using InnerClass.

# Using Second-Order Instance (work in progress)

```agda
module UsingSecondOrderInstance--WorkInProgress where

  open import Oscar.Data.Constraint

  record InnerClass
           {ℓ} {𝔢} {CONSTRAINTS : Ø 𝔢}
           (constraints : CONSTRAINTS) ⦃ _ : Constraint constraints ⦄
           (SET-METHOD : Ø ℓ)
         : Ø ℓ where
    constructor ∁
    field
      ⋆ : SET-METHOD

  open InnerClass public

  record cat {o m} (O : Set o) (_↦_ : O → O → Set m) : Set (lsuc (o ⊔ m)) where
    field
      ⦃ ⦃Identity⦄ ⦄ : InnerClass _↦_ ∀ x → x ↦ x
      ⦃ ⦃Compositionality⦄ ⦄ : InnerClass _↦_ ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
```

Once again, we construct some sample categories.

```agda
  postulate
    O₁ : Set
    _↦₁_ : O₁ → O₁ → Set
    cat₁ : cat O₁ _↦₁_
    O₂ : Set
    _↦₂_ : O₂ → O₂ → Set
    cat₂ : cat O₂ _↦₂_

  module C₁ = cat cat₁
  module C₂ = cat cat₂
```

Similar to `UsingFirstOrderInstances.𝟏-isomorphism₁`, our first test-drive will not use instance search (although this time, we simply postulate rather than proving, since we don't have the laws).

```agda
  postulate
    _ : ∀ x → C₁.⦃Compositionality⦄ .⋆ (C₁.⦃Identity⦄ .⋆ x) (C₁.⦃Identity⦄ .⋆ x) ≡ C₁.⦃Identity⦄ .⋆ x
```

Next, let's define some accessors that invoke instance search.

```agda
  module _
    {o m} {O : Set o} {_↦_ : O → O → Set m}
    ⦃ i-cat : cat O _↦_ ⦄
    where
    𝟏 : ∀ x → x ↦ x
    𝟏 = cat.⦃Identity⦄ i-cat .⋆

    infix 9 _∙_
    _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
    _∙_ = cat.⦃Compositionality⦄ i-cat .⋆
```

Let's see if it works.

```agda
  {- FIXME
  postulate
    _ : ⦃ _ : cat O₁ _↦₁_ ⦄ (x : O₁) → 𝟏 x ∙ 𝟏 x ≡ 𝟏 x
  -}
```

A colossal failure.

Perhaps the problem is in the accessors. I now reformulate them using `InnerClass` rather than `cat`.

```agda
  module _
    {o m} {O : Set o} {_↦_ : O → O → Set m}
    where
    module _
      ⦃ ⦃Identity⦄ : InnerClass _↦_ ∀ x → x ↦ x ⦄
      where
      𝟏' : ∀ x → x ↦ x
      𝟏' = ⦃Identity⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : InnerClass _↦_ ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      where
      infix 9 _∙'_
      _∙'_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      _∙'_ = ⦃Compositionality⦄ .⋆
```

And try once again.

```agda
  postulate
    _ : ⦃ _ : cat O₁ _↦₁_ ⦄ (x : O₁) → 𝟏' x ∙' 𝟏' x ≡ 𝟏' x
```

Yup, that works. How about if the `cat` instance is in scope but not as a lambda-bound variable? (I expect it doesn't work because, for some reason, etas aren't expanded during instance search.)

```agda
  instance _ = cat₁
  {- FIXME
  postulate
    _ : (x : O₁) → 𝟏' x ∙' 𝟏' x ≡ 𝟏' x -- no instance
  -}
```

To be sure that we're on the right track, let's add-in the laws and check that we can prove things like `UsingFirstOrderInstances.𝟏-isomorphism₁`.

First, a new `cat`.

```agda
  record cat' {o m} (O : Set o) (_↦_ : O → O → Set m) : Set (lsuc (o ⊔ m)) where
    field
      ⦃ ⦃Compositionality⦄ ⦄ : InnerClass _↦_ ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      ⦃ ⦃∙-associativity⦄ ⦄  : InnerClass _↦_ ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙' g) ∙' f ≡ h ∙' (g ∙' f)
      ⦃ ⦃Identity⦄ ⦄         : InnerClass _↦_ ∀ x → x ↦ x
      ⦃ ⦃𝟏-left-unitary⦄ ⦄   : InnerClass _↦_ ∀ {x y} (f : x ↦ y) → 𝟏' y ∙' f ≡ f
      ⦃ ⦃𝟏-right-unitary⦄ ⦄  : InnerClass _↦_ ∀ {x y} (f : x ↦ y) → f ∙' 𝟏' x ≡ f
```

And accessors for the laws.

```agda
  module _
    {o m} {O : Set o} {_↦_ : O → O → Set m}
    ⦃ ⦃Compositionality⦄ : InnerClass _↦_ ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
    where
    module _
      ⦃ ⦃∙-associativity⦄ : InnerClass _↦_ ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙' g) ∙' f ≡ h ∙' (g ∙' f) ⦄
      where
      ∙-associativity' : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙' g) ∙' f ≡ h ∙' (g ∙' f)
      ∙-associativity' = ⦃∙-associativity⦄ .⋆
    module _
      ⦃ ⦃Identity⦄ : InnerClass _↦_ ∀ x → x ↦ x ⦄
      where
      module _
        ⦃ ⦃𝟏-left-unitary⦄ : InnerClass _↦_ ∀ {x y} (f : x ↦ y) → 𝟏' y ∙' f ≡ f ⦄
        where
        𝟏-left-unitary' : ∀ {x y} (f : x ↦ y) → 𝟏' y ∙' f ≡ f
        𝟏-left-unitary' = ⦃𝟏-left-unitary⦄ .⋆
      module _
        ⦃ ⦃𝟏-right-unitary⦄ : InnerClass _↦_ ∀ {x y} (f : x ↦ y) → f ∙' 𝟏' x ≡ f ⦄
        where
        𝟏-right-unitary' : ∀ {x y} (f : x ↦ y) → f ∙' 𝟏' x ≡ f
        𝟏-right-unitary' = ⦃𝟏-right-unitary⦄ .⋆
```

And now some testing.

```agda
  𝟏-isomorphism₁ : ⦃ _ : cat' O₁ _↦₁_ ⦄ ⦃ _ : cat' O₂ _↦₂_ ⦄ → ∀ (x : O₁) → 𝟏' x ∙' 𝟏' _ ≡ 𝟏' _
  𝟏-isomorphism₁ x = 𝟏-left-unitary' (𝟏' _)
```

Huzzah!

The below module encapsulates the approach successfully-taken above.

```agda
module SecondOrderSuccess where

  open import Oscar.Data.Constraint

  record InnerClass
           {ℓ} {𝔢} {CONSTRAINTS : Ø 𝔢}
           (constraints : CONSTRAINTS) ⦃ _ : Constraint constraints ⦄
           (SET-METHOD : Ø ℓ)
         : Ø ℓ where
    constructor ∁
    field
      ⋆ : SET-METHOD

  open InnerClass public

  module _
    {o m} {O : Set o} {_↦_ : O → O → Set m}
    where
    module _
      ⦃ ⦃Identity⦄ : InnerClass _↦_ ∀ x → x ↦ x ⦄
      where
      𝟏 : ∀ x → x ↦ x
      𝟏 = ⦃Identity⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : InnerClass _↦_ ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      where
      infix 9 _∙_
      _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      _∙_ = ⦃Compositionality⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : InnerClass _↦_ ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃∙-associativity⦄ : InnerClass _↦_ ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f) ⦄
      where
      ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ∙-associativity = ⦃∙-associativity⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : InnerClass _↦_ ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : InnerClass _↦_ ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-left-unitary⦄ : InnerClass _↦_ ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f ⦄
      where
      𝟏-left-unitary : ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      𝟏-left-unitary = ⦃𝟏-left-unitary⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : InnerClass _↦_ ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : InnerClass _↦_ ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-right-unitary⦄ : InnerClass _↦_ ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f ⦄
      where
      𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f
      𝟏-right-unitary = ⦃𝟏-right-unitary⦄ .⋆

  record cat {o m} (O : Set o) (_↦_ : O → O → Set m) : Set (lsuc (o ⊔ m)) where
    field
      ⦃ ⦃Compositionality⦄ ⦄ : InnerClass _↦_ ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      ⦃ ⦃∙-associativity⦄ ⦄  : InnerClass _↦_ ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ⦃ ⦃Identity⦄ ⦄         : InnerClass _↦_ ∀ x → x ↦ x
      ⦃ ⦃𝟏-left-unitary⦄ ⦄   : InnerClass _↦_ ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      ⦃ ⦃𝟏-right-unitary⦄ ⦄  : InnerClass _↦_ ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f

  module _
    (O₁ : Set)
    (_↦₁_ : O₁ → O₁ → Set)
    ⦃ _ : cat O₁ _↦₁_ ⦄
    (O₂ : Set)
    (_↦₂_ : O₂ → O₂ → Set)
    ⦃ _ : cat O₂ _↦₂_ ⦄
    where
    _ : ∀ (x : O₁) → 𝟏 x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)
```

I wonder if the structure of the `cat`/`InnerClass`-complex can be simplified or particularised somewhat. Using `InnerClass` seems like overkill somehow.

Notice that the exact same `constraints` is used each time. Previous testing has shown that other choices of `constraints` would work as well. An idea is to try changing interface to InnerClass so that `constraints` is the same as `SET-METHOD`, reducing the number of visible arguments by one. Unfortunately, it cannot be as simple as that because we would need `constraints : Ø _` for the revised field `⋆ : constraints` but `CONSTRAINTS : Ø 𝔢` does not guarantee that `CONSTRAINTS ≡ Ø _`. Let's see if we can make that work.

```agda
module ReduceInnerClass where

  open import Oscar.Data.Constraint

  record InnerClass
           {ℓ} (method : Ø ℓ) ⦃ _ : Constraint method ⦄
         : Ø (lsuc ℓ) where
    constructor ∁
    field
      ⋆ : method

  open InnerClass public

  module _
    {o m} {O : Set o} {_↦_ : O → O → Set m}
    where
    module _
      ⦃ ⦃Identity⦄ : InnerClass ∀ x → x ↦ x ⦄
      where
      𝟏 : ∀ x → x ↦ x
      𝟏 = ⦃Identity⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : InnerClass ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      where
      infix 9 _∙_
      _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      _∙_ = ⦃Compositionality⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : InnerClass ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃∙-associativity⦄ : InnerClass ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f) ⦄
      where
      ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ∙-associativity = ⦃∙-associativity⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : InnerClass ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : InnerClass ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-left-unitary⦄ : InnerClass ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f ⦄
      where
      𝟏-left-unitary : ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      𝟏-left-unitary = ⦃𝟏-left-unitary⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : InnerClass ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : InnerClass ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-right-unitary⦄ : InnerClass ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f ⦄
      where
      𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f
      𝟏-right-unitary = ⦃𝟏-right-unitary⦄ .⋆

{- FIXME
  record cat {o m} (O : Set o) (_↦_ : O → O → Set m) : Set (lsuc (o ⊔ m)) where
    field
      ⦃ ⦃Compositionality⦄ ⦄ : InnerClass ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      ⦃ ⦃∙-associativity⦄ ⦄  : InnerClass ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ⦃ ⦃Identity⦄ ⦄         : InnerClass ∀ x → x ↦ x
      ⦃ ⦃𝟏-left-unitary⦄ ⦄   : InnerClass ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      ⦃ ⦃𝟏-right-unitary⦄ ⦄  : InnerClass ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f

  module _
    (O₁ : Set)
    (_↦₁_ : O₁ → O₁ → Set)
    ⦃ _ : cat O₁ _↦₁_ ⦄
    (O₂ : Set)
    (_↦₂_ : O₂ → O₂ → Set)
    ⦃ _ : cat O₂ _↦₂_ ⦄
    where
    _ : ∀ (x : O₁) → 𝟏 x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)
-}
```

The above error is explained (or, anyway, reproduced) by the below `MakeConstraintOnIdentitySameAsMethod`.

Following `SecondOrderSuccess`, here we see that we could get rid of all constraints except for the one on `Identity`.

```agda
module GetRidOfAllConstraintsExceptForIdentity where

  open import Oscar.Data.𝟙
  open import Oscar.Data.Constraint

  record InnerClass
           {ℓ} {𝔢} {CONSTRAINTS : Ø 𝔢}
           (constraints : CONSTRAINTS) ⦃ _ : Constraint constraints ⦄
           (SET-METHOD : Ø ℓ) -- ⦃ _ : Constraint SET-METHOD ⦄
         : Ø ℓ where
    constructor ∁
    field
      ⋆ : SET-METHOD

  open InnerClass public

  module _
    {o m} {O : Set o} {_↦_ : O → O → Set m}
    where
    module _
      ⦃ ⦃Identity⦄ : InnerClass _↦_ ∀ x → x ↦ x ⦄
      where
      𝟏 : ∀ x → x ↦ x
      𝟏 = ⦃Identity⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : InnerClass 𝟙 ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      where
      infix 9 _∙_
      _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      _∙_ = ⦃Compositionality⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : InnerClass 𝟙 ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃∙-associativity⦄ : InnerClass 𝟙 ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f) ⦄
      where
      ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ∙-associativity = ⦃∙-associativity⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : InnerClass 𝟙 ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : InnerClass _↦_ ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-left-unitary⦄ : InnerClass 𝟙 ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f ⦄
      where
      𝟏-left-unitary : ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      𝟏-left-unitary = ⦃𝟏-left-unitary⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : InnerClass 𝟙 ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : InnerClass _↦_ ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-right-unitary⦄ : InnerClass 𝟙 ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f ⦄
      where
      𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f
      𝟏-right-unitary = ⦃𝟏-right-unitary⦄ .⋆

  record cat {o m} (O : Set o) (_↦_ : O → O → Set m) : Set (lsuc (o ⊔ m)) where
    field
      ⦃ ⦃Compositionality⦄ ⦄ : InnerClass 𝟙 ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      ⦃ ⦃∙-associativity⦄ ⦄  : InnerClass 𝟙 ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ⦃ ⦃Identity⦄ ⦄         : InnerClass _↦_ ∀ x → x ↦ x
      ⦃ ⦃𝟏-left-unitary⦄ ⦄   : InnerClass 𝟙 ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      ⦃ ⦃𝟏-right-unitary⦄ ⦄  : InnerClass 𝟙 ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f

  module _
    (O₁ : Set)
    (_↦₁_ : O₁ → O₁ → Set)
    ⦃ _ : cat O₁ _↦₁_ ⦄
    (O₂ : Set)
    (_↦₂_ : O₂ → O₂ → Set)
    ⦃ _ : cat O₂ _↦₂_ ⦄
    where
    _ : ∀ (x : O₁) → 𝟏 x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)

    _ : ∀ {w x y z} (f : w ↦₁ x) (g : x ↦₁ y) (h : y ↦₁ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
    _ = ∙-associativity

    _ : ∀ {x y z} (f : x ↦₁ y) (h : y ↦₁ z) → (h ∙ 𝟏 _) ∙ f ≡ h ∙ (𝟏 _ ∙ f)
    _ = λ f h → ∙-associativity f (𝟏 _) h
```

Alternatively, let's try giving the constraint to composition rather than identity.

```agda
module GetRidOfAllConstraintsExceptForComposition where

  open import Oscar.Data.𝟙
  open import Oscar.Data.Constraint

  record InnerClass
           {ℓ} {𝔢} {CONSTRAINTS : Ø 𝔢}
           (constraints : CONSTRAINTS) ⦃ _ : Constraint constraints ⦄
           (SET-METHOD : Ø ℓ) -- ⦃ _ : Constraint SET-METHOD ⦄
         : Ø ℓ where
    constructor ∁
    field
      ⋆ : SET-METHOD

  open InnerClass public

  module _
    {o m} {O : Set o} {_↦_ : O → O → Set m}
    where
    module _
      ⦃ ⦃Identity⦄ : InnerClass 𝟙 ∀ x → x ↦ x ⦄
      where
      𝟏 : ∀ x → x ↦ x
      𝟏 = ⦃Identity⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : InnerClass _↦_ ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      where
      infix 9 _∙_
      _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      _∙_ = ⦃Compositionality⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : InnerClass _↦_ ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃∙-associativity⦄ : InnerClass 𝟙 ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f) ⦄
      where
      ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ∙-associativity = ⦃∙-associativity⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : InnerClass _↦_ ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : InnerClass 𝟙 ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-left-unitary⦄ : InnerClass 𝟙 ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f ⦄
      where
      𝟏-left-unitary : ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      𝟏-left-unitary = ⦃𝟏-left-unitary⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : InnerClass _↦_ ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : InnerClass 𝟙 ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-right-unitary⦄ : InnerClass 𝟙 ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f ⦄
      where
      𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f
      𝟏-right-unitary = ⦃𝟏-right-unitary⦄ .⋆

{- FIXME
  record cat {o m} (O : Set o) (_↦_ : O → O → Set m) : Set (lsuc (o ⊔ m)) where
    field
      ⦃ ⦃Compositionality⦄ ⦄ : InnerClass _↦_ ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      ⦃ ⦃∙-associativity⦄ ⦄  : InnerClass 𝟙 ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ⦃ ⦃Identity⦄ ⦄         : InnerClass 𝟙 ∀ x → x ↦ x
      ⦃ ⦃𝟏-left-unitary⦄ ⦄   : InnerClass 𝟙 ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      ⦃ ⦃𝟏-right-unitary⦄ ⦄  : InnerClass 𝟙 ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f

  module _
    (O₁ : Set)
    (_↦₁_ : O₁ → O₁ → Set)
    ⦃ _ : cat O₁ _↦₁_ ⦄
    (O₂ : Set)
    (_↦₂_ : O₂ → O₂ → Set)
    ⦃ _ : cat O₂ _↦₂_ ⦄
    where
    _ : ∀ (x : O₁) → 𝟏 x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)
-}
```

And following `GetRidOfAllConstraintsExceptForIdentity`, let's try using the same constraint as the method.

```agda
module MakeConstraintOnIdentitySameAsMethod where

  open import Oscar.Data.𝟙
  open import Oscar.Data.Constraint

  record InnerClass
           {ℓ} {𝔢} {CONSTRAINTS : Ø 𝔢}
           (constraints : CONSTRAINTS) ⦃ _ : Constraint constraints ⦄
           (SET-METHOD : Ø ℓ) -- ⦃ _ : Constraint SET-METHOD ⦄
         : Ø ℓ where
    constructor ∁
    field
      ⋆ : SET-METHOD

  open InnerClass public

  module _
    {o m} {O : Set o} {_↦_ : O → O → Set m}
    where
    module _
      ⦃ ⦃Identity⦄ : InnerClass (∀ x → x ↦ x) ∀ x → x ↦ x ⦄
      where
      𝟏 : ∀ x → x ↦ x
      𝟏 = ⦃Identity⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : InnerClass 𝟙 ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      where
      infix 9 _∙_
      _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      _∙_ = ⦃Compositionality⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : InnerClass 𝟙 ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃∙-associativity⦄ : InnerClass 𝟙 ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f) ⦄
      where
      ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ∙-associativity = ⦃∙-associativity⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : InnerClass 𝟙 ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : InnerClass (∀ x → x ↦ x) ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-left-unitary⦄ : InnerClass 𝟙 ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f ⦄
      where
      𝟏-left-unitary : ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      𝟏-left-unitary = ⦃𝟏-left-unitary⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : InnerClass 𝟙 ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : InnerClass (∀ x → x ↦ x) ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-right-unitary⦄ : InnerClass 𝟙 ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f ⦄
      where
      𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f
      𝟏-right-unitary = ⦃𝟏-right-unitary⦄ .⋆

{- FIXME
  record cat {o m} (O : Set o) (_↦_ : O → O → Set m) : Set (lsuc (o ⊔ m)) where
    field
      ⦃ ⦃Compositionality⦄ ⦄ : InnerClass 𝟙 ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      ⦃ ⦃∙-associativity⦄ ⦄  : InnerClass 𝟙 ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ⦃ ⦃Identity⦄ ⦄         : InnerClass (∀ x → x ↦ x) ∀ x → x ↦ x
      ⦃ ⦃𝟏-left-unitary⦄ ⦄   : InnerClass 𝟙 ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      ⦃ ⦃𝟏-right-unitary⦄ ⦄  : InnerClass 𝟙 ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f

  module _
    (O₁ : Set)
    (_↦₁_ : O₁ → O₁ → Set)
    ⦃ _ : cat O₁ _↦₁_ ⦄
    (O₂ : Set)
    (_↦₂_ : O₂ → O₂ → Set)
    ⦃ _ : cat O₂ _↦₂_ ⦄
    where
    _ : ∀ (x : O₁) → 𝟏 x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)
-}
```

Nope. How about another variation?

In the below, `InnerClass (∀ x y → x ↦ y)` works, but some other variations don't. To summarise:

∀ x y → x ↦ y -- works
λ x y → x ↦ y -- works
λ x y → y ↦ x -- works (I think)
λ x → x ↦ x -- doesn't work
∀ x → x ↦ x -- doesn't work

```agda
module MakeConstraintOnIdentitySameAsMethod-variations where

  open import Oscar.Data.𝟙
  open import Oscar.Data.Constraint

  record InnerClass
           {ℓ} {𝔢} {CONSTRAINTS : Ø 𝔢}
           (constraints : CONSTRAINTS) ⦃ _ : Constraint constraints ⦄
           (SET-METHOD : Ø ℓ)
         : Ø ℓ where
    constructor ∁
    field
      ⋆ : SET-METHOD

  open InnerClass public

  module _
    {o m} {O : Set o} {_↦_ : O → O → Set m}
    where
    module _
      ⦃ ⦃Identity⦄ : InnerClass (∀ x y → x ↦ y) ∀ x → x ↦ x ⦄
      where
      𝟏 : ∀ x → x ↦ x
      𝟏 = ⦃Identity⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : InnerClass 𝟙 ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      where
      infix 9 _∙_
      _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      _∙_ = ⦃Compositionality⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : InnerClass 𝟙 ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃∙-associativity⦄ : InnerClass 𝟙 ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f) ⦄
      where
      ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ∙-associativity = ⦃∙-associativity⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : InnerClass 𝟙 ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : InnerClass (∀ x y → x ↦ y) ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-left-unitary⦄ : InnerClass 𝟙 ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f ⦄
      where
      𝟏-left-unitary : ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      𝟏-left-unitary = ⦃𝟏-left-unitary⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : InnerClass 𝟙 ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : InnerClass (∀ x y → x ↦ y) ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-right-unitary⦄ : InnerClass 𝟙 ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f ⦄
      where
      𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f
      𝟏-right-unitary = ⦃𝟏-right-unitary⦄ .⋆

  record cat {o m} (O : Set o) (_↦_ : O → O → Set m) : Set (lsuc (o ⊔ m)) where
    field
      ⦃ ⦃Compositionality⦄ ⦄ : InnerClass 𝟙 ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      ⦃ ⦃∙-associativity⦄ ⦄  : InnerClass 𝟙 ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ⦃ ⦃Identity⦄ ⦄         : InnerClass (∀ x y → x ↦ y) ∀ x → x ↦ x
      ⦃ ⦃𝟏-left-unitary⦄ ⦄   : InnerClass 𝟙 ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      ⦃ ⦃𝟏-right-unitary⦄ ⦄  : InnerClass 𝟙 ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f

  module _
    (O₁ : Set)
    (_↦₁_ : O₁ → O₁ → Set)
    ⦃ _ : cat O₁ _↦₁_ ⦄
    (O₂ : Set)
    (_↦₂_ : O₂ → O₂ → Set)
    ⦃ _ : cat O₂ _↦₂_ ⦄
    where
    _ : ∀ (x : O₁) → 𝟏 x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)
```

Let's see now if we can come-up with an alias for `InnerClass _↦_`.

In the below, I manage an alias by a little sleight-of-hand: the alias is defined within a module and is effectively usable nowhere else. A version of `cat` is placed inside this module, and an accessor class with the desired interface is placed outside.

```agda
module AliasedInnerClass where

  open import Oscar.Data.Constraint

  record InnerClass
           {ℓ} {𝔢} {CONSTRAINTS : Ø 𝔢}
           (constraints : CONSTRAINTS) ⦃ _ : Constraint constraints ⦄
           (SET-METHOD : Ø ℓ)
         : Ø ℓ where
    constructor ∁
    field
      ⋆ : SET-METHOD

  open InnerClass public

  module _
    {o m} {O : Set o} {_↦_ : O → O → Set m}
    where
    AliasedClass : ∀ {ℓ} → Ø ℓ → Ø ℓ
    AliasedClass {ℓ} = InnerClass {ℓ} _↦_

    module _
      ⦃ ⦃Identity⦄ : AliasedClass ∀ x → x ↦ x ⦄
      where
      𝟏 : ∀ x → x ↦ x
      𝟏 = ⦃Identity⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : AliasedClass ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      where
      infix 9 _∙_
      _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      _∙_ = ⦃Compositionality⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : AliasedClass ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃∙-associativity⦄ : AliasedClass ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f) ⦄
      where
      ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ∙-associativity = ⦃∙-associativity⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : AliasedClass ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : AliasedClass ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-left-unitary⦄ : AliasedClass ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f ⦄
      where
      𝟏-left-unitary : ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      𝟏-left-unitary = ⦃𝟏-left-unitary⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : AliasedClass ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : AliasedClass ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-right-unitary⦄ : AliasedClass ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f ⦄
      where
      𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f
      𝟏-right-unitary = ⦃𝟏-right-unitary⦄ .⋆

    record cat' : Set (lsuc (o ⊔ m)) where
      field
        ⦃ ⦃Compositionality⦄ ⦄ : AliasedClass ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
        ⦃ ⦃∙-associativity⦄ ⦄  : AliasedClass ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
        ⦃ ⦃Identity⦄ ⦄         : AliasedClass ∀ x → x ↦ x
        ⦃ ⦃𝟏-left-unitary⦄ ⦄   : AliasedClass ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
        ⦃ ⦃𝟏-right-unitary⦄ ⦄  : AliasedClass ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f

  cat : ∀ {o m} (O : Set o) (_↦_ : O → O → Set m) → Set (lsuc (o ⊔ m))
  cat _ _↦_ = cat' {_↦_ = _↦_}

  module _
    (O₁ : Set)
    (_↦₁_ : O₁ → O₁ → Set)
    ⦃ _ : cat O₁ _↦₁_ ⦄
    (O₂ : Set)
    (_↦₂_ : O₂ → O₂ → Set)
    ⦃ _ : cat O₂ _↦₂_ ⦄
    where
    _ : ∀ (x : O₁) → 𝟏 x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)
```

Notice that InnerClass isn't used outside of the anonymous module defining `cat'` and, furthermore, isn't used by anything but `AliasedClass`. Let's try stuffing it into that module.

```agda
module StuffedInnerClass where

  open import Oscar.Data.Constraint

  module _
    {o m} {O : Set o} {_↦_ : O → O → Set m}
    where

    record InnerClass
             ⦃ _ : Constraint _↦_ ⦄
             {ℓ}
             (SET-METHOD : Ø ℓ)
           : Ø ℓ where
      constructor ∁
      field
        ⋆ : SET-METHOD

    open InnerClass public

    module _
      ⦃ ⦃Identity⦄ : InnerClass ∀ x → x ↦ x ⦄
      where
      𝟏 : ∀ x → x ↦ x
      𝟏 = ⦃Identity⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : InnerClass ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      where
      infix 9 _∙_
      _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      _∙_ = ⦃Compositionality⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : InnerClass ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃∙-associativity⦄ : InnerClass ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f) ⦄
      where
      ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ∙-associativity = ⦃∙-associativity⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : InnerClass ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : InnerClass ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-left-unitary⦄ : InnerClass ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f ⦄
      where
      𝟏-left-unitary : ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      𝟏-left-unitary = ⦃𝟏-left-unitary⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : InnerClass ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : InnerClass ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-right-unitary⦄ : InnerClass ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f ⦄
      where
      𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f
      𝟏-right-unitary = ⦃𝟏-right-unitary⦄ .⋆

    record cat' : Set (lsuc (o ⊔ m)) where
      field
        ⦃ ⦃Compositionality⦄ ⦄ : InnerClass ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
        ⦃ ⦃∙-associativity⦄ ⦄  : InnerClass ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
        ⦃ ⦃Identity⦄ ⦄         : InnerClass ∀ x → x ↦ x
        ⦃ ⦃𝟏-left-unitary⦄ ⦄   : InnerClass ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
        ⦃ ⦃𝟏-right-unitary⦄ ⦄  : InnerClass ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f

  cat : ∀ {o m} (O : Set o) (_↦_ : O → O → Set m) → Set (lsuc (o ⊔ m))
  cat _ _↦_ = cat' {_↦_ = _↦_}

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
    _ = λ x → 𝟏-left-unitary (𝟏 _)

    _ : ∀ x → 𝟏 {_↦_ = _↦₂_} x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)
```

Below, I'll revise `StuffedInnerClass` to remove the need for the `cat` alias of `cat'`.

```agda
module UnstuffedCat where

  open import Oscar.Data.Constraint

  module _
    {o m} {O : Set o} {_↦_ : O → O → Set m}
    where

    record InnerClass
             ⦃ _ : Constraint _↦_ ⦄
             {ℓ}
             (SET-METHOD : Ø ℓ)
           : Ø ℓ where
      constructor ∁
      field
        ⋆ : SET-METHOD

    open InnerClass public

    module _
      ⦃ ⦃Identity⦄ : InnerClass ∀ x → x ↦ x ⦄
      where
      𝟏 : ∀ x → x ↦ x
      𝟏 = ⦃Identity⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : InnerClass ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      where
      infix 9 _∙_
      _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      _∙_ = ⦃Compositionality⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : InnerClass ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃∙-associativity⦄ : InnerClass ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f) ⦄
      where
      ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ∙-associativity = ⦃∙-associativity⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : InnerClass ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : InnerClass ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-left-unitary⦄ : InnerClass ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f ⦄
      where
      𝟏-left-unitary : ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      𝟏-left-unitary = ⦃𝟏-left-unitary⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : InnerClass ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : InnerClass ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-right-unitary⦄ : InnerClass ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f ⦄
      where
      𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f
      𝟏-right-unitary = ⦃𝟏-right-unitary⦄ .⋆

  record cat {o m} (O : Set o) (_↦_ : O → O → Set m) : Set (lsuc (o ⊔ m)) where
    private I = InnerClass {_↦_ = _↦_}
    field
      ⦃ ⦃Compositionality⦄ ⦄ : I ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      ⦃ ⦃∙-associativity⦄ ⦄  : I ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ⦃ ⦃Identity⦄ ⦄         : I ∀ x → x ↦ x
      ⦃ ⦃𝟏-left-unitary⦄ ⦄   : I ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      ⦃ ⦃𝟏-right-unitary⦄ ⦄  : I ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f

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
    _ = λ x → 𝟏-left-unitary (𝟏 _)

    _ : ∀ x → 𝟏 {_↦_ = _↦₂_} x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)
```

Perhaps a similar trick will work to allow us to pull `InnerClass` out of the anonymous module.

```agda
module OutTheInner where

  open import Oscar.Data.Constraint

  module _
    {o m} {O : Set o} (_↦_ : O → O → Set m)
    where

    record InnerClass
             ⦃ _ : Constraint _↦_ ⦄
             {ℓ}
             (SET-METHOD : Ø ℓ)
           : Ø ℓ where
      constructor ∁
      field
        ⋆ : SET-METHOD

    open InnerClass public

  module _
    {o m} {O : Set o} {_↦_ : O → O → Set m}
    where

    private I = InnerClass _↦_

    module _
      ⦃ ⦃Identity⦄ : I ∀ x → x ↦ x ⦄
      where
      𝟏 : ∀ x → x ↦ x
      𝟏 = ⦃Identity⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : I ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      where
      infix 9 _∙_
      _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      _∙_ = ⦃Compositionality⦄ .⋆

    module _
      ⦃ ⦃Compositionality⦄ : I ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃∙-associativity⦄ : I ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f) ⦄
      where
      ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ∙-associativity = ⦃∙-associativity⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : I ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : I ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-left-unitary⦄ : I ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f ⦄
      where
      𝟏-left-unitary : ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      𝟏-left-unitary = ⦃𝟏-left-unitary⦄ .⋆
    module _
      ⦃ ⦃Compositionality⦄ : I ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z ⦄
      ⦃ ⦃Identity⦄ : I ∀ x → x ↦ x ⦄
      ⦃ ⦃𝟏-right-unitary⦄ : I ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f ⦄
      where
      𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f
      𝟏-right-unitary = ⦃𝟏-right-unitary⦄ .⋆

  record cat {o m} (O : Set o) (_↦_ : O → O → Set m) : Set (lsuc (o ⊔ m)) where
    private I = InnerClass _↦_
    field
      ⦃ ⦃Compositionality⦄ ⦄ : I ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      ⦃ ⦃∙-associativity⦄ ⦄  : I ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ⦃ ⦃Identity⦄ ⦄         : I ∀ x → x ↦ x
      ⦃ ⦃𝟏-left-unitary⦄ ⦄   : I ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      ⦃ ⦃𝟏-right-unitary⦄ ⦄  : I ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f

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
    _ = λ x → 𝟏-left-unitary (𝟏 _)

    _ : ∀ x → 𝟏 {_↦_ = _↦₂_} x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)
```

We know that `Identity` needs some kind of constraint but that `Compositionality` and `∙-associativity` may not.

Let's try reformulating `cat` by only constraining `Identity`. Then perhaps the accessors to the other members of `cat` can be created more easily (i.e. with open ⦃ … ⦄).

```agda
module OnlyConstrainIdentity where

  open import Oscar.Data.Constraint

  module _
    {o m} {O : Set o} (_↦_ : O → O → Set m)
    where

    record InnerClass
             ⦃ _ : Constraint _↦_ ⦄
             {ℓ}
             (SET-METHOD : Ø ℓ)
           : Ø ℓ where
      constructor ∁
      field
        ⋆ : SET-METHOD

    open InnerClass public

  module _
    {o m} {O : Set o} {_↦_ : O → O → Set m}
    where

    private I = InnerClass _↦_

    module _
      ⦃ ⦃Identity⦄ : I ∀ x → x ↦ x ⦄
      where
      𝟏 : ∀ x → x ↦ x
      𝟏 = ⦃Identity⦄ .⋆

  record cat {o m} (O : Set o) (_↦_ : O → O → Set m) : Set (lsuc (o ⊔ m)) where
    private I = InnerClass _↦_
    infixr 9 _∙_
    field
      _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ⦃ ⦃Identity⦄ ⦄ : I ∀ x → x ↦ x
      𝟏-left-unitary  : ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f

  open cat ⦃ … ⦄ public hiding (⦃Identity⦄)

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
    _ = λ x → 𝟏-left-unitary (𝟏 _)

    _ : ∀ x → 𝟏 {_↦_ = _↦₂_} x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)

    _ : ∀ {w x y z} (f : w ↦₁ x) (g : x ↦₁ y) (h : y ↦₁ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
    _ = ∙-associativity

    _ : ∀ {x y z} (f : x ↦₁ y) (h : y ↦₁ z) → (h ∙ 𝟏 _) ∙ f ≡ h ∙ 𝟏 _ ∙ f
    _ = λ f h → ∙-associativity f (𝟏 _) h
```

What stands-out to me about `Identity` is the fact that it is the only one that doesn't use the entire space of the type constructor, viz. `∀ x → x ↦ x` rather than `∀ x y → x ↦ y`. One thought (that I can't quite see how to make work) is to add another type constructor representing the diagonal of `_↦_`, `⌶ : O → Set m`, where we require that `∀ x → ⌶ x ≡ x ↦ x`. Another idea is to try to push `I` closer to `_↦_`.

```agda
module PushICloser-1 where

  open import Oscar.Data.Constraint

  module _
    {o m} {O : Set o} (_↦_ : O → O → Set m) (x : O)
    where

    record InnerClass
             ⦃ _ : Constraint (_↦_ , x) ⦄
             {ℓ}
             (SET-METHOD : Ø ℓ)
           : Ø ℓ where
      constructor ∁
      field
        ⋆ : SET-METHOD

    open InnerClass public

  module _
    {o m} {O : Set o} {_↦_ : O → O → Set m}
    where

    module _
      ⦃ ⦃Identity⦄ : ∀ {x} → InnerClass _↦_ x (x ↦ x) ⦄
      where
      𝟏 : ∀ x → x ↦ x
      𝟏 x = (⦃Identity⦄ {x}) .⋆

  record cat {o m} (O : Set o) (_↦_ : O → O → Set m) : Set (lsuc (o ⊔ m)) where
    infixr 9 _∙_
    field
      _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ⦃ ⦃Identity⦄ ⦄ : ∀ {x} → InnerClass _↦_ x (x ↦ x)
      𝟏-left-unitary  : ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f

  open cat ⦃ … ⦄ public hiding (⦃Identity⦄)

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
    {- FIXME
    _ : ∀ (x : O₁) → 𝟏 x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)
    -}

    _ : ∀ x → 𝟏 {_↦_ = _↦₂_} x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)

    _ : ∀ {w x y z} (f : w ↦₁ x) (g : x ↦₁ y) (h : y ↦₁ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
    _ = ∙-associativity

    _ : ∀ {x y z} (f : x ↦₁ y) (h : y ↦₁ z) → (h ∙ 𝟏 _) ∙ f ≡ h ∙ 𝟏 _ ∙ f
    _ = λ f h → ∙-associativity f (𝟏 _) h
```

That didn't work. Here's another try.

```agda
module PushICloser-2 where

  open import Oscar.Data.Constraint

  module _
    {o m} {O : Set o} (_↦_ : O → O → Set m)
    where

    record InnerClass
             ⦃ _ : Constraint _↦_ ⦄
             {ℓ}
             (SET-METHOD : Ø ℓ)
           : Ø ℓ where
      constructor ∁
      field
        ⋆ : SET-METHOD

    open InnerClass public

  module _
    {o m} {O : Set o} {_↦_ : O → O → Set m}
    where

    module _
      ⦃ ⦃Identity⦄ : ∀ {x} → InnerClass _↦_ (x ↦ x) ⦄
      where
      𝟏 : ∀ x → x ↦ x
      𝟏 x = (⦃Identity⦄ {x}) .⋆

  record cat {o m} (O : Set o) (_↦_ : O → O → Set m) : Set (lsuc (o ⊔ m)) where
    infixr 9 _∙_
    field
      _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ⦃ ⦃Identity⦄ ⦄ : ∀ {x} → InnerClass _↦_ (x ↦ x)
      𝟏-left-unitary  : ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f

  open cat ⦃ … ⦄ public hiding (⦃Identity⦄)

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
    {- FIXME
    _ : ∀ (x : O₁) → 𝟏 x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)
    -}

    _ : ∀ x → 𝟏 {_↦_ = _↦₂_} x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)

    _ : ∀ {w x y z} (f : w ↦₁ x) (g : x ↦₁ y) (h : y ↦₁ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
    _ = ∙-associativity

    _ : ∀ {x y z} (f : x ↦₁ y) (h : y ↦₁ z) → (h ∙ 𝟏 _) ∙ f ≡ h ∙ 𝟏 _ ∙ f
    _ = λ f h → ∙-associativity f (𝟏 _) h
```

That didn't work either. Here's a wild idea: how about pulling `I` out so that it wraps `cat`?

```agda
module PullIOut where

  open import Oscar.Data.Constraint

  module _
    {o m} {O : Set o} (_↦_ : O → O → Set m)
    where

    record InnerClass
             ⦃ _ : Constraint _↦_ ⦄
             {ℓ}
             (SET-METHOD : Ø ℓ)
           : Ø ℓ where
      constructor ∁
      field
        ⋆ : SET-METHOD

    open InnerClass public

  record cat {o m} (O : Set o) (_↦_ : O → O → Set m) : Set (lsuc (o ⊔ m)) where
    infixr 9 _∙_
    field
      _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      𝟏 : ∀ x → x ↦ x
      𝟏-left-unitary  : ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f

  open cat ⦃ … ⦄ public

  module _
    (O₁ : Set)
    (_↦₁_ : O₁ → O₁ → Set)
    ⦃ _ : InnerClass _↦₁_ (cat O₁ _↦₁_) ⦄
    (O₂ : Set)
    (_↦₂_ : O₂ → O₂ → Set)
    (_↦₂'_ : O₂ → O₂ → Set)
    ⦃ _ : InnerClass _↦₂_ (cat O₂ _↦₂_) ⦄
    ⦃ _ : InnerClass _↦₂'_ (cat O₂ _↦₂'_) ⦄
    where
    {- FIXME
    _ : ∀ (x : O₁) → 𝟏 x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)

    _ : ∀ x → 𝟏 {_↦_ = _↦₂_} x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)

    _ : ∀ {w x y z} (f : w ↦₁ x) (g : x ↦₁ y) (h : y ↦₁ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
    _ = ∙-associativity

    _ : ∀ {x y z} (f : x ↦₁ y) (h : y ↦₁ z) → (h ∙ 𝟏 _) ∙ f ≡ h ∙ 𝟏 _ ∙ f
    _ = λ f h → ∙-associativity f (𝟏 _) h
    -}
```

Well, it was worth a shot?

Let's see about putting the field accessor, `𝟏`, inside the `cat` record.

```agda
module MoveAccessorToRecord where

  open import Oscar.Data.Constraint

  module _
    {o m} {O : Set o} (_↦_ : O → O → Set m)
    where

    record InnerClass
             ⦃ _ : Constraint _↦_ ⦄
             {ℓ}
             (SET-METHOD : Ø ℓ)
           : Ø ℓ where
      constructor ∁
      field
        ⋆ : SET-METHOD

    open InnerClass public

  record cat {o m} (O : Set o) (_↦_ : O → O → Set m) : Set (lsuc (o ⊔ m)) where
    private I = InnerClass _↦_
    infixr 9 _∙_
    field
      _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ⦃ ⦃Identity⦄ ⦄ : I ∀ x → x ↦ x
    {- fails
    𝟏 : ∀ x → x ↦ x
    𝟏 = ⦃Identity⦄ .⋆
    -}
    𝟏 : ⦃ _ : I ∀ x → x ↦ x ⦄ → ∀ x → x ↦ x
    -- 𝟏 ⦃ _ ⦄ = ⦃Identity⦄ .⋆ -- works
    𝟏 ⦃ ⦃Identity⦄ ⦄ = ⦃Identity⦄ .⋆ -- works

    field
      𝟏-left-unitary  : ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f

  open cat ⦃ … ⦄ public hiding (⦃Identity⦄)

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
    _ = λ x → 𝟏-left-unitary (𝟏 _)

    _ : ∀ x → 𝟏 {_↦_ = _↦₂_} x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)

    _ : ∀ {w x y z} (f : w ↦₁ x) (g : x ↦₁ y) (h : y ↦₁ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
    _ = ∙-associativity

    _ : ∀ {x y z} (f : x ↦₁ y) (h : y ↦₁ z) → (h ∙ 𝟏 _) ∙ f ≡ h ∙ 𝟏 _ ∙ f
    _ = λ f h → ∙-associativity f (𝟏 _) h
```

Let's cleanup, renaming some things.

```agda
module CleanupCat where

  open import Oscar.Data.Constraint

  module _
    {o m} {O : Ø o} (_↦_ : O → O → Ø m)
    where

    record InnerClass ⦃ _ : Constraint _↦_ ⦄ {ℓ} (method : Ø ℓ) : Ø ℓ where
      constructor ∁
      field
        ⋆ : method

    open InnerClass public

  record cat {o m} (O : Set o) (_↦_ : O → O → Set m) : Set (lsuc (o ⊔ m)) where
    private I = InnerClass _↦_
    infixr 9 _∙_
    field
      _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ⦃ ⦃Identity⦄ ⦄ : I ∀ x → x ↦ x

    𝟏 : ⦃ _ : I ∀ x → x ↦ x ⦄ → ∀ x → x ↦ x
    𝟏 ⦃ _ ⦄ = ⦃Identity⦄ .⋆

    field
      𝟏-left-unitary  : ∀ {x y} (f : x ↦ y) → 𝟏 y ∙ f ≡ f
      𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f

  open cat ⦃ … ⦄ public hiding (⦃Identity⦄)

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
    _ = λ x → 𝟏-left-unitary (𝟏 _)

    _ : ∀ x → 𝟏 {_↦_ = _↦₂_} x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)

    _ : ∀ {w x y z} (f : w ↦₁ x) (g : x ↦₁ y) (h : y ↦₁ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
    _ = ∙-associativity

    _ : ∀ {x y z} (f : x ↦₁ y) (h : y ↦₁ z) → (h ∙ 𝟏 _) ∙ f ≡ h ∙ 𝟏 _ ∙ f
    _ = λ f h → ∙-associativity f (𝟏 _) h
```

TODO: I have a worry that there are two choices of instances for use in the definition of `CleanupCat.cat.𝟏`.

We'll now try specialising InnerClass even further. In the below, we treat two ways of accessing `Identity`.

```agda
module TradeoffToInnerClass where

  open import Oscar.Data.Constraint

  module _
    {o m} {O : Ø o} (_↦_ : O → O → Ø m) ⦃ _ : Constraint _↦_ ⦄
    where
    record IdentityClass : Ø (o ⊔ m) where
      constructor ∁
      field
        ⋆ : ∀ x → x ↦ x

  open IdentityClass public

  module _
    {o m} {O : Set o} {_↦_ : O → O → Set m}
    where
    𝟏' : ⦃ _ : IdentityClass _↦_ ⦄ → ∀ x → x ↦ x
    𝟏' ⦃ ⦃Identity⦄ ⦄ = ⦃Identity⦄ .⋆

  record cat {o m} (O : Set o) (_↦_ : O → O → Set m) : Set (lsuc (o ⊔ m)) where
    infixr 9 _∙_
    field
      _∙_ : ∀ {x y z} → y ↦ z → x ↦ y → x ↦ z
      ∙-associativity : ∀ {w x y z} (f : w ↦ x) (g : x ↦ y) (h : y ↦ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
      ⦃ ⦃Identity⦄ ⦄ : IdentityClass _↦_

    𝟏 : ⦃ _ : IdentityClass _↦_ ⦄ → ∀ x → x ↦ x
    𝟏 ⦃ _ ⦄ = ⦃Identity⦄ .⋆

    field
      𝟏-left-unitary  : ∀ {x y} (f : x ↦ y) → 𝟏' y ∙ f ≡ f
      𝟏-right-unitary : ∀ {x y} (f : x ↦ y) → f ∙ 𝟏 x ≡ f

  open cat ⦃ … ⦄ public hiding (⦃Identity⦄)

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
    _ = λ x → 𝟏-left-unitary (𝟏 _)

    _ : ∀ x → 𝟏 {_↦_ = _↦₂_} x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)

    _ : ∀ {w x y z} (f : w ↦₁ x) (g : x ↦₁ y) (h : y ↦₁ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
    _ = ∙-associativity

    _ : ∀ {x y z} (f : x ↦₁ y) (h : y ↦₁ z) → (h ∙ 𝟏 _) ∙ f ≡ h ∙ 𝟏 _ ∙ f
    _ = λ f h → ∙-associativity f (𝟏 _) h

    _ : ∀ (x : O₁) → 𝟏' x ∙ 𝟏' _ ≡ 𝟏' _
    _ = λ x → 𝟏-left-unitary (𝟏' _)

    _ : ∀ x → 𝟏 {_↦_ = _↦₂_} x ∙ 𝟏' _ ≡ 𝟏' _
    _ = λ x → 𝟏-left-unitary (𝟏' _)

    _ : ∀ {w x y z} (f : w ↦₁ x) (g : x ↦₁ y) (h : y ↦₁ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
    _ = ∙-associativity

    _ : ∀ {x y z} (f : x ↦₁ y) (h : y ↦₁ z) → (h ∙ 𝟏' _) ∙ f ≡ h ∙ 𝟏' _ ∙ f
    _ = λ f h → ∙-associativity f (𝟏' _) h
```

The trouble with the above is that I do not see a way to further simplify, and that by specialising, we have lost the ability to reuse the independent `IdentityClass` class for some other possible purpose. So, let's go back to a general version of the `InnerClass`.

```agda
module GenericInner where

  open import Oscar.Data.Constraint

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
    _ = λ x → 𝟏-left-unitary (𝟏 _)

    _ : ∀ x → 𝟏 {_↦_ = _↦₂_} x ∙ 𝟏 _ ≡ 𝟏 _
    _ = λ x → 𝟏-left-unitary (𝟏 _)

    _ : ∀ {w x y z} (f : w ↦₁ x) (g : x ↦₁ y) (h : y ↦₁ z) → (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
    _ = ∙-associativity

    _ : ∀ {x y z} (f : x ↦₁ y) (h : y ↦₁ z) → (h ∙ 𝟏 _) ∙ f ≡ h ∙ 𝟏 _ ∙ f
    _ = λ f h → ∙-associativity f (𝟏 _) h
```

This file is taking a long time to typecheck. To be continued in the next chapter...
