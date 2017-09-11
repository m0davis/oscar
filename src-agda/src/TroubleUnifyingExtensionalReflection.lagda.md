Given the below function `g`, I'd like to get Agda to infer the type-constructor `B` when invoking `g`, such as in the expression `g _ x`.

```agda
postulate
  A : Set

g : (B : A → Set) (x : A) → B x → B x
g B1 x1 bx1 = bx1
```

It turns out that my first naive attempt doesn't work so well.

```agda
naively-wanted : (B : A → Set) (x : A) → B x → B x
naively-wanted B1 x1 bx1 = g B1 x1 bx1

but-no-unique-solution : (B : A → Set) (x : A) → B x → B x
but-no-unique-solution B1 x1 bx1 = {!g _ x1 bx1!}
```

I note that though Agda finds no unique solution, all solutions result in the rhs normalising to the same expression. TODO Considering this, can we make Agda smarter? Or can we ask her to try normalising each solution to see if they all result in the same?

```agda
no-unique-solution : (B : A → Set) (x : A) → B x → B x
no-unique-solution B1 x1 bx1 = {!g (λ x2 → B1 {!!}) x1 bx1!}

first-solution : (B : A → Set) (x : A) → B x → B x
first-solution B1 x1 bx1 = g (λ x2 → B1 x2) x1 bx1

second-solution : (B : A → Set) (x : A) → B x → B x
second-solution B1 x1 bx1 = g (λ x2 → B1 x1) x1 bx1
```

By removing the `x1` parameter from the lhs, the second solution is ruled-out, so Agda finds a unique solution.

```agda
unique-solution : (B : A → Set) (x : A) → B x → B x
unique-solution B1 = g (λ x2 → B1 {!!})
```

Let's check that there's no unique solution when introduce just the `x1` parameter.

```agda
no-unique-solution-x1 : (B : A → Set) (x : A) → B x → B x
no-unique-solution-x1 B1 x1 = {!g (λ x2 → B1 {!!}) x1!}
```

This feels like the sort of problem where `_$_` was required. Let's try that.

```agda
_$_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $ x = f x

no-unique-solution-$ : (B : A → Set) (x : A) → B x → B x
no-unique-solution-$ B1 x1 = {!g (λ x2 → B1 {!!}) $ x1!}
```

But `g _` : `(x : A) → B x → B x`, which doesn't have the same shape as `∀ x → B x`. So, let's try a different version of `_$_`.

```agda
_$'_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x → B x) → ∀ x → B x → B x
f $' x = f x

no-unique-solution-$' : (B : A → Set) (x : A) → B x → B x
no-unique-solution-$' B1 x1 = {!g (λ x2 → B1 {!!}) $' x1!}
```

Still no luck.

Here is an attempt at using instance argument resolution to help. Here, we let `B` be resolved indirectly via instance resolution of `R`.

```agda
record R (B : A → Set) : Set where
  field r : (x : A) → B x → B x

open R {{...}}

instance-argument-resolution : (B : A → Set) {{_ : R B}} → (x : A) → B x → B x
instance-argument-resolution B1 x1 = r x1
```

But when the instance is provided in the environment (not in the lhs), Agda once again fails.

```agda
instance

  Rg : {B : A → Set} → R B
  Rg .R.r = g _

instance-environment-non-resolution : (B : A → Set) (x : A) → B x → B x
instance-environment-non-resolution B1 x1 = {!r x1!}
```

Let's take a closer look at the difference between `unique-solution` and `no-unique-solution-x1`.

```agda
closer-look-unique : (B : A → Set) (x : A) → B x → B x
closer-look-unique B1 = g (λ x2 → B1 {!!})

closer-look-non-unique : (B : A → Set) (x : A) → B x → B x
closer-look-non-unique B1 x1 = g (λ x2 → B1 {!!}) x1
```

`show-constraints` reports

    ?8 := _100 x1 x2
    _101 := λ B1 x1 → g (λ x2 → B1 (_100 x1 x2)) x1 [blocked by problem 160]
    [160,163] (_100 x1 x1) = x1 : A
    [160,161,162] x1 = (_100 x1 x1) : A

Yet the solutions are "equivalent".

```agda
closer-look-non-unique-x1 : (B : A → Set) (x : A) → B x → B x
closer-look-non-unique-x1 B1 = λ x1 → g (λ x2 → B1 x1) x1 -- h (λ x2 → B1 {!!}) x1

closer-look-non-unique-x2 : (B : A → Set) (x : A) → B x → B x
closer-look-non-unique-x2 B1 = λ x1 → g (λ x2 → B1 x2) x1 -- h (λ x2 → B1 {!!}) x1

open import Agda.Builtin.Equality

closer-look-same : closer-look-non-unique-x1 ≡ closer-look-non-unique-x2
closer-look-same = refl
```
