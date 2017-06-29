
module Oscar.Property-ExtendedPropertySurjectivity11 where

postulate 𝔛 : Set
postulate y : 𝔛

Appy : (𝔛 → Set) → Set
Appy H = H y

record Foo (T : Set) : Set where
  field
    foo : T

open Foo ⦃ … ⦄ public

instance
  postulate
    FooInstance : {R : 𝔛 → Set} → Foo (Appy R)

module _
  (R : 𝔛 → Set)
  where

  works : Appy R
  works = foo {T = {!!}} ⦃ FooInstance {R = R} ⦄

  fails : Appy R
  fails = foo {T = Appy R} ⦃ FooInstance {R = {!!}} ⦄
