You can't fool the positivity-checker by using abstractions. It turns out that's a good thing.

```agda
-- {-# OPTIONS --no-positivity-check #-}

data ⊥ : Set where

data Bad : Set

abstract
  Fine = Bad → ⊥
  unwrap : Fine → Bad → ⊥
  unwrap f x = f x
  wrap : (Bad → ⊥) → Fine
  wrap = unwrap

data Bad where
  bad : Fine → Bad

self-app : Bad → ⊥
self-app (bad f) = unwrap f (bad f)

absurd : ⊥
absurd = self-app (bad (wrap self-app))
```
