{-# OPTIONS --allow-unsolved-metas #-}

module AgdaFeatureNoInstanceFromHidden where

postulate
  A : Set
  R : A → A → Set

Alrighty : A → Set₁
Alrighty l = ∀ {r} → R l r → Set

record Foo (Q : A → Set₁) : Set₁ where field foo : ∀ {x y} → R x y → Q x → Q y

open Foo {{...}}

postulate
  instance theInstance : Foo Alrighty

works1 : ∀ {x y} → R x y → Alrighty x → Alrighty y
works1 r = foo r

works2 : ∀ {x y} → R x y → Alrighty x → Alrighty y
works2 r ax = works1 r ax

works3 : ∀ {x y} → R x y → Alrighty x → Alrighty y
works3 r ax = foo {{theInstance}} r ax

works4 : ∀ {x y} → R x y → Alrighty x → Alrighty y
works4 r ax = foo r (λ {v} → ax {v})

fails : ∀ {x y} → R x y → Alrighty x → Alrighty y
fails r ax = {!foo r ax!}
{-
No instance of type Foo (λ v → R v _r_81 → Set) was found in scope.
when checking that r ax are valid arguments to a function of type
{Q : A → Set₁} {{r = r₁ : Foo Q}} {x y : A} → R x y → Q x → Q y
-}
