
```agda
module Type.DeBruijn where

open import Type.Prelude
```

I use DeBruijn indexing to describe parts of a context. A context has a size represented by a natural number. A DeBruijn index on a context of some size N is a number between 0 and N-1, and is meant to represent a signifier of one of the contextual elements. We will sometimes want to talk about a context expanded by the insertion of some element. When we do so, we will also want to carry along an index that points to the same element in the expanded context as it was prior to expansion. In a context of size N there are N + 1 places at which to insert a new element. I say that an index i in a context Γ of size N is weakened from a place f yielding an index i'. That is, `weakenFinFrom {N} p i = i'`.

```agda
weakenFinFrom : ∀ {N} → Fin (suc N) → Fin N → Fin (suc N)
weakenFinFrom zero x = suc x
weakenFinFrom (suc from) zero = zero
weakenFinFrom (suc from) (suc x) = suc (weakenFinFrom from x)
```

Similarly, we may also want to talk about contractions of a context. Or we may want to talk about pidgeons. You are a pigeon. There are some pigeon holes labeled 0,1,...,N. You are given a particular pigeon hole, i. One of the holes that you are not given, labeled h, is removed, and the pigeon holes are relabeled 0,1,...,N-1. What is the new label on your pigeon hole?

```agda
instantiateFinAt : ∀ {N} {h i : Fin (suc N)} → h ≢ i → Fin N
instantiateFinAt {zero} {zero} {zero} h≢i = ⊥-elim (h≢i refl)
instantiateFinAt {zero} {zero} {suc ()} _
instantiateFinAt {zero} {suc ()} {_} _
instantiateFinAt {suc _} {_} {zero} _ = zero -- my label stays at 0
instantiateFinAt {suc _} {zero} {suc i} _ = i -- my label shifts down
instantiateFinAt {suc _} {suc h} {suc i} sh≢si =
  let h≢i : h ≢ i -- the hole lower than mine is not the same as the hole lower than the one removed
      h≢i = λ {refl → sh≢si refl}
  in
  suc (instantiateFinAt h≢i) -- my label is one more then the one lower than me after the change
```
