
Specification of Type Theory (from the HoTT book)

```agda
module TypeTheory-1 where
```



```agda
record _+_ (A B : Set) : Set where
  postulate fun+ : A → B → Set

foo : (A B : Set) → A + B
foo A B = record {}

foo' : (A B : Set) → A → B → Set
foo' A B a b = let open _+_ in {!!} -- _+_.fun+ {!!} a b

module _*_ (A B : Set) where

postulate A B : Set

-- module bar = A * B
```
