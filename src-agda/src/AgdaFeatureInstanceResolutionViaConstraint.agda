
module AgdaFeatureInstanceResolutionViaConstraint where

postulate A : Set
postulate y : A

Appy : (A → Set) → Set
Appy H = H y

record Foo (T : Set) : Set where field foo : T

open Foo ⦃ … ⦄ public

postulate
  S : A → Set

record Failing : Set where
  no-eta-equality

  postulate
    instance FooInstance : {R : A → Set} → Foo (Appy R)

  works1 : Appy S
  works1 = foo ⦃ FooInstance {R = S} ⦄

  fails2 : Appy S
  fails2 = foo ⦃ FooInstance {R = {!!}} ⦄
  {-
    [21] (_R_11 y) =< (S y) : Set
    _12 := λ → Foo.foo FooInstance [blocked by problem 21]
  -}

  fails3 : Appy S
  fails3 = foo

record Succeeds : Set where
  no-eta-equality

  record Bar (B : A → Set) : Set where
    no-eta-equality

  postulate
    instance BarInstance : Bar S
    instance FooInstance : {R : A → Set} ⦃ _ : Bar R ⦄ → Foo (Appy R)

  works1 : Appy S
  works1 = foo ⦃ FooInstance {R = S} ⦄

  works2 : Appy S
  works2 = foo ⦃ FooInstance {R = {!!}} ⦄

  works3 : Appy S
  works3 = foo
