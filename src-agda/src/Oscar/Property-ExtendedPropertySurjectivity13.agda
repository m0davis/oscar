{-# OPTIONS --show-implicit #-}
module Oscar.Property-ExtendedPropertySurjectivity13 where

postulate A : Set
postulate y : A

Appy : (A → Set) → Set
Appy H = H y

record Foo (T : Set) : Set where
  field
    foo : T

open Foo ⦃ … ⦄ public

record Bar (B : A → Set) : Set where
  no-eta-equality

postulate
  S : A → Set

instance
  postulate BarInstance : Bar S
  postulate
    FooInstance : {R : A → Set} ⦃ _ : Bar R ⦄ → Foo (Appy R)

works0 : Appy S
works0 = foo ⦃ FooInstance {R = S} ⦄

works1 : Appy S
works1 = foo ⦃ FooInstance {R = λ x → S x} ⦄

-- works2 : Appy S
-- works2 = foo ⦃ FooInstance {R = λ x → S y} ⦄

fails : Appy S
fails = foo
