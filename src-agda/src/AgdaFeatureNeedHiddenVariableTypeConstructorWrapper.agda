
module AgdaFeatureNeedHiddenVariableTypeConstructorWrapper where

Unwrapped : {A : Set} → (A → Set) → Set₁
Unwrapped B = ∀ {x} → B x → Set

record Unindexed : Set₁ where
  field
    {A} : Set
    {B} : A → Set
    unwrap : Unwrapped B

record Indexed {A : Set} (B : A → Set) : Set₁ where
  field
    unwrap : Unwrapped B

record Generic (A : Set₁) : Set₁ where
  field
    unwrap : A

record Foo (F : Set₁) : Set₁ where
  field
    foo : F → Set

open Foo {{...}}

postulate
  A : Set
  B : A → Set
  unwrapped : Unwrapped B
  indexed : Indexed B
  unindexed : Unindexed
  generic : Generic (Unwrapped B)

postulate

  instance FooUnwrapped : Foo (Unwrapped B)
  instance FooIndexed : Foo (Indexed B)
  instance FooUnindexed : Foo Unindexed
  instance FooGeneric : Foo (Generic (Unwrapped B))

test-unwrapped-lambda-unhide-works : Set
test-unwrapped-lambda-unhide-works = foo (λ {_} → unwrapped)

test-unwrapped-help-instance-works : Set
test-unwrapped-help-instance-works = foo {F = ∀ {_} → _} unwrapped

test-unindexed-works : Set
test-unindexed-works = foo unindexed

test-indexed-works : Set
test-indexed-works = foo indexed

test-generic-works : Set
test-generic-works = foo generic

test-unwrapped-fails : Set
test-unwrapped-fails = {!foo unwrapped!}
{-
No instance of type Foo (B _x_48 → Set) was found in scope.
when checking that unwrapped is a valid argument to a function of
type {F : Set₁} {{r : Foo F}} → F → Set
-}
