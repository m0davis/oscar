This story has a happy ending.

```agda
{-# OPTIONS --show-implicit #-}

open import Agda.Primitive

_$_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $ x = f x

! : ∀ {a} {A : Set a} {{x : A}} → A
! {{x}} = x
```

I've had some difficulty trying to model a "reflexivity" class, in particular when an instance has a functional form.

```agda
module Problem where

  record Reflexivity {a} {A : Set a} {r} (R : A → A → Set r) : Set (a ⊔ r) where
    field
      reflexivity : ∀ {x} → R x x

  open Reflexivity {{...}}

  instance

    ReflexivityExtension : ∀
      {a} {A : Set a} {b} {B : A → Set b} →
      Reflexivity (λ (x y : A) → B x → B x)
    ReflexivityExtension .Reflexivity.reflexivity x = x

  test-reflexivity-extension : ∀ {a} {A : Set a} {b} {B : A → Set b} →
    ∀ {x} → B x → B x
  test-reflexivity-extension {B = B} = reflexivity ⦃ ReflexivityExtension {B = B} ⦄
```

Here are some experiments to find a workaround.

```agda
module Experiments where

  record Unit (A : Set) : Set where
    field
      unit : A

  open Unit {{...}}

  record Plexivity {A : Set} (P : A → Set) : Set where
    field
      plexivity : ∀ {x} → P x

  open Plexivity {{...}}

  record Reflexivity {A : Set} (R : A → A → Set) (x : A) : Set where
    field
      reflexivity : R x x

  open Reflexivity {{...}}

  record Reflexivity' (A : Set1) (R : A → A → Set) : Set1 where
    field
      reflexivity' : ∀ x → R x x

  open Reflexivity' {{...}}

  data Deflexivity {A : Set} (R : A → A → Set) : Set where
    deflexivity : (∀ {x} → R x x) → Deflexivity R

  instance

    UnitExtension : ∀
      {A : Set} {B : A → Set} {x : A} →
      Unit (B x → B x)
    UnitExtension .Unit.unit x = x

    PlexivityExtension : ∀
      {A : Set} {B : A → Set} →
      Plexivity {A = A} (λ x → B x → B x)
    PlexivityExtension .Plexivity.plexivity x = x

    ReflexivityExtension :
      ∀ {A : Set} {B : A → Set} {x : A} →
      Reflexivity (λ (x y : A) → B x → B y) x
    ReflexivityExtension .Reflexivity.reflexivity x = x

    Reflexivity'Extension :
      Reflexivity' Set (λ x y → x → y)
    Reflexivity'Extension .Reflexivity'.reflexivity' A x = x

    DeflexivityExtension : ∀
      {A : Set} {B : A → Set} →
      Deflexivity (λ x y → B x → B y)
    DeflexivityExtension = deflexivity (λ x → x)

  deflate : {A : Set} {R : A → A → Set} ⦃ _ : Deflexivity R ⦄ → ∀ {x} → R x x
  deflate {A} {R} {{deflexivity x}} {x₁} = x

  test-unit-extension : ∀
    {A : Set} {B : A → Set} → ∀ {x} → B x → B x
  test-unit-extension {B = B} {x = x} = unit {A = B x → B x} ⦃ UnitExtension {B = B} ⦄

  test-plexivity-extension : ∀
    {A : Set} {B : A → Set} → ∀ {x} → B x → B x
  test-plexivity-extension {B = B} {x = x} = plexivity {P = λ x' → B x' → B x'} ⦃ PlexivityExtension {B = B} ⦄

  test-reflexivity-extension : ∀
    {A : Set} {B : A → Set} → ∀ {x} → B x → B x
  test-reflexivity-extension {B = B} {x = x} = reflexivity {R = λ x' y' → B x' → B y'}

  test-reflexivity'-extension : ∀
    {A : Set} {B : A → Set} → ∀ {x} → B x → B x
  test-reflexivity'-extension {B = B} {x = x} = reflexivity' _

  test-deflexivity-extension : ∀
    {A : Set} {B : A → Set} → ∀ {x} → B x → B x
  test-deflexivity-extension {B = B} {x = x} = deflate {R = λ x' y' → B x' → B y'}
```

From the above, it looks like `Reflexivity'` is close to a solution. Let's work backwards from the given candidate solution.

```agda
module Solution-1 where

  record Reflexivity (A : Set1) (R : A → A → Set) : Set1 where
    field
      reflexivity : ∀ x → R x x

  open Reflexivity {{...}}

  instance

    ReflexivityExtension : Reflexivity _ λ (x y : Set) → x → y
    ReflexivityExtension .Reflexivity.reflexivity A x = x

  test-1 : ∀ {A : Set} {B : A → Set} → ∀ {x} → B x → B x
  test-1 = reflexivity _

  test-2 : ∀ {A : Set} → A → A
  test-2 = reflexivity _

  test-3 : ∀ {A : Set} {B : A → A → Set} → ∀ {x y} → B x y → B x y
  test-3 = reflexivity _
```

Evidently, we can safely hide some of the arguments and parameters.

```agda
module Solution-2 where

  record Reflexivity {A : Set1} (R : A → A → Set) : Set1 where
    field
      reflexivity : ∀ {x} → R x x

  open Reflexivity {{...}}

  instance

    ReflexivityExtension : Reflexivity λ (x y : Set) → x → y
    ReflexivityExtension .Reflexivity.reflexivity x = x

  test-1 : ∀ {A : Set} {B : A → Set} → ∀ {x} → B x → B x
  test-1 = reflexivity

  test-2 : ∀ {A : Set} → A → A
  test-2 = reflexivity

  test-3 : ∀ {A : Set} {B : A → A → Set} → ∀ {x y} → B x y → B x y
  test-3 = reflexivity
```

Next, add in universe polymorphism.

```agda
module Solution-3 where

  record Reflexivity {a} {A : Set a} {r} (R : A → A → Set r) : Set (a ⊔ r) where
    field
      reflexivity : ∀ {x} → R x x

  open Reflexivity {{...}}

  instance

    ReflexivityExtension : ∀ {a} → Reflexivity λ (x y : Set a) → x → y
    ReflexivityExtension .Reflexivity.reflexivity x = x

  test-1 : ∀ {a b} {A : Set a} {B : A → Set b} → ∀ {x} → B x → B x
  test-1 = reflexivity

  test-2 : ∀ {a} {A : Set a} → A → A
  test-2 = reflexivity

  test-3 : ∀ {a b} {A : Set a} {B : A → A → Set b} → ∀ {x y} → B x y → B x y
  test-3 = reflexivity
```

This is starting to make some sense. The original `Problem.ReflexivityExtension` was trying to define reflexivity for a particular construction of a type which could not be known (because there are infinitely many possibilities) when searching for an instance. All we know at that point is that we have something of the form `X → X` for some `X : Set`. We don't know that `X` was created in some particular way (say `B x`).

Now, some worries. One application I have used for Reflexivity is for the unit term of `Substitunction = λ x y → Fin x → Term y : Nat → Nat → Set`. What if it had been defined with a type like `Term x → Term y`? Could there be a confusion between the identity function and the intended term? Let's try.

First, let's verify that Substitunction still works as expected.

```agda
  postulate
    Nat : Set
    Fin : Nat → Set
    Term : Nat → Set
  Substitunction : Nat → Nat → Set
  Substitunction x y = Fin x → Term y
  postulate
    unitSubstitunction : ∀ {x} → Substitunction x x

  instance

    ReflexivitySubstitunction : Reflexivity Substitunction
    ReflexivitySubstitunction .Reflexivity.reflexivity = unitSubstitunction

  test-substitunction : ∀ {x} → Substitunction x x
  test-substitunction = reflexivity

  infix 4 _≡_
  data _≡_ {a} {A : Set a} (x : A) : A → Set a where
    instance refl : x ≡ x

  test-substitunction-correct : ∀ {x} → test-substitunction {x} ≡ unitSubstitunction {x}
  test-substitunction-correct = refl
```

Next, let's invent an alternative version that looks more like to worrisome case. We'll spell-out more of the terms instead of postulating.

```agda
  data Worry-1 : Nat → Nat → Set where
    zeroWorry-1 : ∀ x y → Worry-1 x y
    unitWorry-1 : ∀ {x} → Worry-1 x x → Worry-1 x x

  instance

    ReflexivityWorry-1 : Reflexivity Worry-1
    ReflexivityWorry-1 .Reflexivity.reflexivity = unitWorry-1 (zeroWorry-1 _ _)

  test-worry-1 : ∀ {x} → Worry-1 x x
  test-worry-1 = reflexivity -- normalises to λ {x} → unitWorry-1 {x} (zeroWorry-1 x x)
```

That worked. Why couldn't `ReflexivityExtension` have been a candidate?

```agda
  test-worry-1' : ∀ {x : Set} → x → x
  test-worry-1' {x} = reflexivity ⦃ ReflexivityExtension ⦄ {x = x}
```

I'm guessing because `Worry-1 x x` is a datatype not having the "→" shape. My worry had stemmed from the fact that the unit type does have that shape, ``.

Let's try constructing a problem where the worrisome case has that shape.

```agda
  data Worry-2 : Nat → Nat → Set where
    zeroWorry-2 : ∀ x y → Worry-2 x y

  postulate
    unitWorry-2a : ∀ {x y} → Worry-2 x x → Worry-2 y y
    unitWorry-2b : ∀ {x y} → Worry-2 x y → Worry-2 x y
    unitWorry-2c : ∀ {x y} → Worry-2 y y → Worry-2 x x

  instance

    ReflexivityWorry-2a : Reflexivity (λ (x y : Nat) → Worry-2 x x → Worry-2 y y)
    ReflexivityWorry-2a .Reflexivity.reflexivity w = unitWorry-2a w

    ReflexivityWorry-2b : Reflexivity (λ (x y : Nat) → Worry-2 x y → Worry-2 x y)
    ReflexivityWorry-2b .Reflexivity.reflexivity w = unitWorry-2b w

    ReflexivityWorry-2c : Reflexivity (λ (x y : Nat) → Worry-2 y y → Worry-2 x x)
    ReflexivityWorry-2c .Reflexivity.reflexivity w = unitWorry-2c w

  test-worry-2a : ∀ {x} → Worry-2 x x → Worry-2 x x
  test-worry-2a = reflexivity {R = λ x y → Worry-2 x x → Worry-2 y y}

  test-worry-2b : ∀ {x} → Worry-2 x x → Worry-2 x x
  test-worry-2b = reflexivity {R = λ x y → Worry-2 x y → Worry-2 x y}

  test-worry-2c : ∀ {x} → Worry-2 x x → Worry-2 x x
  test-worry-2c = reflexivity {R = λ x y → Worry-2 y y → Worry-2 x x}
```

Let's try another example like the above's "2b", but without the postulate. Also, let's try making it more like `Substitunction`, calling it "Wubstitunction". We'll also wrap "Wubstitunction" in an `abstract` block to distinguish it from the "→" (i.e. `ReflexivityExtension`) version.

```agda
  data Worry-3 : Nat → Nat → Set -- we don't need mutuality; it's only for the experiment (see comment below)

  module Wubstitunction where -- if we don't use a named module, later abstract blocks will be able to see through this abstraction

    abstract

      Wubstitunction : Nat → Nat → Set
      Wubstitunction x y = Worry-3 x y → Worry-3 x y

      unwrap : ∀ {x y} → Wubstitunction x y → Worry-3 x y → Worry-3 x y
      unwrap f x = f x

      wrap : ∀ {x y} → (Worry-3 x y → Worry-3 x y) → Wubstitunction x y
      wrap f x = f x

  open Wubstitunction

  data Worry-3 where
    zeroWorry-3 : ∀ x y → Worry-3 x y
    toUnitWorry-3 : ∀ x y → Worry-3 x y → Worry-3 x y
    -- notStrictlyPositiveWorry-3 : ∀ x y → Wubstitunction x y → Worry-3 x y -- this was an experiment

  unitWubstitunction-3 : ∀ {x y} → Wubstitunction x y
  unitWubstitunction-3 = wrap (toUnitWorry-3 _ _)

  instance

    ReflexivityWorry-3 : Reflexivity Worry-3
    ReflexivityWorry-3 .Reflexivity.reflexivity = zeroWorry-3 _ _

    ReflexivityWubstitunction-3 : Reflexivity Wubstitunction
    ReflexivityWubstitunction-3 .Reflexivity.reflexivity = unitWubstitunction-3

  test-worry-3-custom-wubstitunction : ∀ {x} → Wubstitunction x x
  test-worry-3-custom-wubstitunction = reflexivity

  test-worry-3-generic-identity : ∀ {x} → Worry-3 x x → Worry-3 x x
  test-worry-3-generic-identity = reflexivity

  test-unwrap-worry : ∀ {x y} → Wubstitunction x y → Worry-3 x y → Worry-3 x y
  test-unwrap-worry f x = unwrap f x

  test-wrap-worry : ∀ {x y} → (Worry-3 x y → Worry-3 x y) → Wubstitunction x y
  test-wrap-worry f = wrap f

  test-create-a-worry-3a : ∀ {x} → Wubstitunction x x → Worry-3 x x
  test-create-a-worry-3a f = unwrap f reflexivity
                         -- λ {x} f → unwrap {x} {x} f (zeroWorry-3 x x)

  test-create-a-worry-3b : ∀ {x} → Wubstitunction x x → Worry-3 x x
  test-create-a-worry-3b f = reflexivity -- {{ReflexivityWorry-3}}
                         -- λ {x} f → zeroWorry-3 x x

  instance

    ReflexivityNextWorry-3 : Reflexivity (λ x y → Wubstitunction x y → Worry-3 x y)
    ReflexivityNextWorry-3 .Reflexivity.reflexivity f = unwrap f reflexivity

  test-create-a-worry-3c : ∀ {x} → Wubstitunction x x → Worry-3 x x
  test-create-a-worry-3c = reflexivity -- {{ReflexivityNextWorry-3}}
                         -- λ {x} f → unwrap {x} {x} f (zeroWorry-3 x x)

  test-create-a-worry-3d : ∀ {x} → Wubstitunction x x → Worry-3 x x
  test-create-a-worry-3d f = reflexivity $ f
                         -- λ {x} f → unwrap {x} {x} f (zeroWorry-3 x x)

  test-create-a-worry-3e : ∀ {x} → Wubstitunction x x → Worry-3 x x
  test-create-a-worry-3e f = reflexivity
                         -- λ {x} f → zeroWorry-3 x x

  test-create-a-worry-3f : ∀ {x} → Worry-3 x x
  test-create-a-worry-3f = reflexivity
                         -- λ {x} → zeroWorry-3 x x

  test-create-a-worry-3g : ∀ {x} → Wubstitunction x x
  test-create-a-worry-3g = reflexivity
                         -- λ {x} → wrap {x} {x} (toUnitWorry-3 x x)

  test-create-a-worry-3h : ∀ {x} → Worry-3 x x → Worry-3 x x
  test-create-a-worry-3h = reflexivity
                         -- λ {x} x₁ → x₁
```

Notice that unwrapping acts like `_$_` outside the abstraction block. Can we define an appropriate "Applicative" class and thereby instantiate `Wubstitunction` as a member? The idea is to generalise `_$_`.
