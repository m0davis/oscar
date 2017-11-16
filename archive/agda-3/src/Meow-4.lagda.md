# Chapter 4. My cat's life in the 3rd dimension.

```agda
{-# OPTIONS --show-implicit #-}
{-# OPTIONS --cubical #-}

module Meow-4 where
```

This chapter began with some intention (I forget what). I am now reading through the Homotopy Type Theory book and every once and a while need to "scratch" some idea. Sections below refer to this book.

# Representing Π-types (§ 1.4).

Can we write dependent functions (in Agda) using a notation similar to the book? I.e. Instead of `(A : Set) (B : A → Set) (C : (x : A) → B x → Set) (x : A) (y : B x) → C x y`, perhaps we can write something like:

    `(A : Set) (B : A → Set) (C : Π (x : A) B x → Set) → Π (x : A) Π (y : B x) → C x y`

Well, I guess I just answered my own question. `Π` is very much like `∀` but with somewhat different precedence rules. Toying with application syntax is not possible currently in Agda. Maybe we can play with `syntax` and achieve something like:

    `(A : Set) (B : A → Set) (C : (x : A) Π (B x) → Set) → (x : A) Π (y : B x) Π (C x y)`

Not sure it's worth it. Takeaway: Π is ∀. Moving on.

# Uniqueness principal for product types (§ 1.5)

Is it provable under no-eta-equality?

```agda
module §1,5 where

  open import Agda.Builtin.Equality

  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      ₀ : A
      ₁ : B
  open _×_

  uniq-× : ∀ (A B : Set) → (x : A × B) → (x .₀ , x .₁) ≡ x
  uniq-× _ _ _ = refl

  record _×'_ (A B : Set) : Set where
    no-eta-equality
    constructor _,_
    field
      ₀ : A
      ₁ : B
  open _×'_

  uniq-×' : ∀ (A B : Set) → (x : A ×' B) → (x .₀ , x .₁) ≡ x
  uniq-×' _ _ (a , b) = refl {x = a , b} -- only provable if we deconstruct
  -- uniq-×' _ _ x = refl {x = x .₀ , x .₁}
```

and now the induction principal for products

```agda
  ind-× : ∀ (A B : Set) (C : A × B → Set)
            → ((x : A) (y : B) → C (x , y))
            → ∀ (p : A × B) → C p
  ind-× _ _ _ g (x , y) = g x y
```

```agda
module §1 where

  open import Agda.Builtin.Equality
  open import Agda.Primitive

  ex : (A : Set) → refl {A = Set} ≡ refl
  ex A = refl {x = refl {x = A}}
```

```agda
module TryWithRegularSet where
  open import Agda.Builtin.Equality

  postulate I : Set

  O : Set
  O = I → I

  mor : O → O → Set
  mor f g = ∀ i → f i ≡ g i

  comp : ∀ {x y z} → mor y z → mor x y → mor x z
  comp {x} {y} {z} g f i rewrite f i = g i

  assoc : ∀ {w x y z} (f : mor w x) (g : mor x y) (h : mor y z) → comp (comp h g) f ≡ comp h (comp g f)
  assoc f g h = {!!}
```

```agda
open import Agda.Primitive
```

```agda
module ExperimentWithLevels where

  open import Agda.Builtin.Nat

  lplus' : Nat → Level → Level
  lplus' zero ℓ = ℓ
  lplus' (suc l) ℓ = lplus' l (lsuc ℓ)

  lplus'' : Nat → Level → Level
  lplus'' zero ℓ = ℓ
  lplus'' (suc l) ℓ = lsuc (lplus' l ℓ)

  record Lifter1' {ℓ} (A : Set ℓ) : Set (lplus' (suc zero) ℓ) where
    constructor lift1
    field
      lower1 : A

  record Lifter1'' {ℓ} (A : Set ℓ) : Set (lplus'' (suc zero) ℓ) where
    constructor lift1
    field
      lower1 : A

  Lifter*' : ∀ {ℓ} (A : Set ℓ) (l : Nat) → Set (lplus' l ℓ)
  Lifter*' {ℓ} A zero = A
  Lifter*' {ℓ} A (suc zero) = Lifter1' A
  Lifter*' {ℓ} A (suc (suc l)) = Lifter*' (Lifter1' A) (suc l)

  demo : (A : Set) → Set (lsuc (lsuc (lsuc lzero)))
  demo A = Lifter*' A 3

  Lifter*'' : ∀ {ℓ} (A : Set ℓ) (l : Nat) → Set (lplus' l ℓ)
  Lifter*'' {ℓ} A zero = A
  Lifter*'' {ℓ} A (suc zero) = Lifter1'' A
  Lifter*'' {ℓ} A (suc (suc l)) = {!Lifter1' (Lifter*'' A (suc l))!}

  {-
  record Lifter' {ℓ} (A : Set ℓ) (l : Nat) : Set (lplus' l ℓ) where
    constructor lift'
    field
      lower' : A
  -}
```

```agda
module TryWithCubical where

  open CubicalPrimitives

--   crefl : ∀ {a} {A : Set a} {x : A} → Partial I -- IsOne1 x x
--   crefl {x = x} = i1 -- λ (i : _) → x
{-
  open import Agda.Builtin.Equality

  postulate I : Set

  O : Set
  O = I → I

  mor : O → O → Set
  mor f g = ∀ i → f i ≡ g i

  comp : ∀ {x y z} → mor y z → mor x y → mor x z
  comp {x} {y} {z} g f i rewrite f i = g i

  assoc : ∀ {w x y z} (f : mor w x) (g : mor x y) (h : mor y z) → comp (comp h g) f ≡ comp h (comp g f)
  assoc f g h = {!!}
-}
```
