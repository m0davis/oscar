```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

Why aren't let-bound variables and top-level definitions (in an instance block) eta-expanded when finding candidates for instance search?

In the code below, I realise that by declaring the `foo` field as `instance`, the test would go through, but generalising that as a solution is fraught with other problems.

```agda
postulate
  Foo : Set
  unfoo : {{_ : Foo}} → Set

record Super : Set where
  field
    {{foo}} : Foo

postulate
  instance super : Super

test-fails : Set
test-fails = {!unfoo!} -- no instance found because the `super` instance is not eta-expanded.
```

A workaround is to use asInstance.

```agda
asInstance : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) → (∀ {{x}} → B x) → B x
asInstance x f = f {{x}}

test-asInstance : Set
test-asInstance = asInstance super unfoo
```

To generalise this to a set of instances:

```
postulate
  Bar : Set
  barInstance : Bar

asInstanceWorkaround-general-one : ∀ {b} {B : Super → Set b} → ({{x : Super}} → B x) → B super
asInstanceWorkaround-general-one x = x

asInstanceWorkaround-general-many : ∀ {b} {B : Super → Bar → Set b} → ({{x : Super}} → {{y : Bar}} → B x y) → B super barInstance
asInstanceWorkaround-general-many x = x -- asInstance super (asInstance barInstance x)

test-asInstance-workaround-one : Set
test-asInstance-workaround-one = asInstanceWorkaround-general-one unfoo

test-asInstance-workaround-many : Set
test-asInstance-workaround-many = asInstanceWorkaround-general-many unfoo

test-asInstance-workaround-many-hardcoded : Set
test-asInstance-workaround-many-hardcoded = asInstance super (asInstance barInstance unfoo)
