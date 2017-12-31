
```agda
module Type.deprecated.Complexity where

open import Type.Prelude
```

We may also view `Complexity` as the shape of a proof.

```agda
data Complexity : Set where
  c : ∀ {N} → Vec Complexity N → Complexity
```

These are measures of the size of the shape of a proof. they are not to be confused with how long it takes to prove something. although they could be if a given proof system searches monotonically over sizes.

```agda
χ-measure : Complexity → Nat
δ-measure : ∀ {N} → Vec Complexity N → Nat

χ-measure (c {N} δ) = δ-measure δ

δ-measure {.0} [] = zero
δ-measure {.(suc _)} (χ ∷ δ) = suc (χ-measure χ + δ-measure δ)
```
