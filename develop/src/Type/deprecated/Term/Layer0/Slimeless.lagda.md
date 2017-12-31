```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

# Slimeless Type Theory

```agda
module Type.deprecated.Term.Layer0.Slimeless where
```

I think it will be more fruitful if I shift the question from "do my datatypes construct green slime?" to "could my datatype indices carry more information?" In this regard, I notice that, for example, `ℕIZ` cannot be a universe inhabitant. ℕE, might be or might not be, depending the "sort" (which I have not defined) of its first argument.

Perhaps then it will help to define "sorts" for each `STerm` constructor. I sketch that now:

    ℕF : ι -- ℕF definitely constructs an inhabitant of a universe
    ℕIZ : ℕ -- ℕZ definitely constructs an inhabitant of the type ℕ
    ℕIS : ℕ ▷ ℕ -- ℕIS's first argument definitely must be an inhabitant of ℕ and definitely constructs an inhabitant of ℕ.

I can see two ways to go in defining the sort of ℕE. One is somewhat lazy and would have its type very partially defined:

    ℕE : (ℕ ▷ ι) -- ℕE's first argument definitely must be something that can construct an inhabitant of a universe and be a function of ℕ.
       ▷ ⋆ -- the requirements for ℕE's second argument are elided here, being too complex to state without reference to other parts of the formula
       ▷ (ℕ ▷ ⋆ ▷ ⋆)
       ▷ ℕ
       ▷ ⋆

Another would be more expressive:

    ℕE : (ℕ ▷ ι) -- ℕE's first argument definitely must be something that can construct an inhabitant of a universe and be a function of ℕ.
       ▷ (app (𝓋 0) ℕIZ) -- apply the prior argument to ... what exactly?
       ▷ (ℕ ▷ (app (𝓋 2) (𝓋 0)) ▷ ??) -- the second argument in the third argument must be of the same type as the prior (second) argument -- oops for the (??) -- I had thought it was ℕ at first, but now realise that I cannot even express it properly with `app`.
       ▷ ℕ
       ▷ app (𝓋 3) (𝓋 0)

It seems that either way, I will have to deal with later-on resolving `⋆` or `app _ _`, so it would be better to go with the more expressive approach if I can nail down its structure. At the moment, I don't know what to make of the argument ℕIZ to the second argument of ℕE. Continuing with a few more types according to the expressive approach:

    ΠF : ι ▷ (𝓋 0 ▷ ι) ▷ ι
    ΠI : (⋆ ▷ ⋆) ▷ Π -- here, I quite legitimately (unlike the lazy approach above) elide the requirements
    ΠE : Π ▷ ⋆ ▷ (app ⋆ (𝓋 0)) -- the first argument is a Π-type, but the second argument must be figured by looking inside the first, and similarly for the return type

The degree of expressiveness required then seems so much that it's equivalent to telling the type all that we are trying to extract from it. I therefore favor the lazier approach. We then have

    ΠF : ι ▷ (⋆ ▷ ι) ▷ ι
    ΠI : (⋆ ▷ ⋆) ▷ Π
    ΠE : Π ▷ ⋆ ▷ ⋆

Of course, then there is the matter of:

    𝒰 : ι
    𝓋 : ⋆

I regard rhs of each of the above as constructions of a datatype `Sort : Set`. The constructors of Sort are `ι Π ℕ : Sort` (along with the rest of the types) and `_▷_ : Sort → Sort → Sort`. (Actually, perhaps `ι : Universe → Sort` is more fitting.) We also have `⋆ : Sort`.

Sort-checked scope-checked terms are then `data SSTerm (N : Nat) : Sort → Set`. That is, the type of an SSTerm tells us, in the least, whether it might deliver us a universe inhabitant. We then can be more precise in the indices of Γ ⊢ τ ∈ ℓ, such that we can require τ to be a term of a sort tat can possibly be a universe inhabitant.

I can see that I've been a bit imprecise, maybe even wrong in the above. Slimelessly, I shall continue.

```agda
open import Type.Prelude
open import Type.Universe
```

```agda
module Uncomposable where
```

In this try, I found it odd that the number of `▷`s in the sort is determinative of the number of `suc`s in the `N` index. But this is even more problematic: we cannot compose `SSTerm`s.

```agda
  infixr 10 _▷_
  data Sort : Set where
    ⋆ : Sort
    ι : Nat → Sort
    ΠF ΣF +F 𝟙F 𝟘F ℕF : Sort
    _▷_ : Sort → Sort → Sort

  data SSTerm (N : Nat) : Sort → Set where
    𝓋 : Fin N
      → SSTerm N ⋆
    𝒰 : ∀ ℓ
      → SSTerm N (ι ℓ)
    ΠF : ∀ {ℓ}
       → SSTerm N (ι ℓ)
       → SSTerm (suc N) (⋆ ▷ ι ℓ)
       → SSTerm N (ι ℓ)
    ΠI : SSTerm (suc N) (⋆ ▷ ⋆)
       → SSTerm N ⋆
    ΠE : SSTerm N ΠF
       → SSTerm N ⋆
       → SSTerm N ⋆
    ℕF : ∀ {ℓ}
       → SSTerm N (ι ℓ)
    ℕIᶻ : SSTerm N ℕF
    ℕIˢ : SSTerm N ℕF → SSTerm N ℕF
    ℕE : ∀ {ℓ}
       → SSTerm (suc N) (ℕF ▷ ι ℓ)
       → SSTerm N ⋆
       → SSTerm (suc (suc N)) (ℕF ▷ ⋆ ▷ ⋆)
       → SSTerm N ⋆

  test : SSTerm 0 (ι 0)
  test = ΠF {!!} {!!}
```

In the next try, I also don't quite make it.

```agda
module NotQuite where
```

```agda
  infixr 10 _▷_
  data Sort : Set where
    ι : Nat → Sort
    ΠF ΣF +F 𝟙F 𝟘F ℕF : Sort
    _▷_ : Sort → Sort → Sort

  data SSTerm {N : Nat} (Γ : Vec Sort N) : Sort → Set where
    𝓋 : (v : Fin N)
      → SSTerm Γ (indexVec Γ v)
    𝒰 : ∀ ℓ
      → SSTerm Γ (ι ℓ)
    ΠF : ∀ {ℓ}
       → SSTerm Γ (ι ℓ)
       → SSTerm (ι ℓ ∷ Γ) (ι ℓ)
       → SSTerm Γ (ι ℓ)
    ΠI : ∀ {A B}
       → SSTerm (A ∷ Γ) B
       → SSTerm Γ ΠF
    ΠE : ∀ {A B}
       → SSTerm Γ ΠF
       → SSTerm Γ A
       → SSTerm Γ B
    ℕF : ∀ {ℓ}
       → SSTerm Γ (ι ℓ)
    ℕIᶻ : SSTerm Γ ℕF
    ℕIˢ : SSTerm Γ ℕF → SSTerm Γ ℕF
    ℕE : ∀ {ℓ}
       → SSTerm ({!!} ∷ Γ) (ι ℓ)
       → SSTerm Γ {!!}
       → SSTerm ({!!} ∷ {!!} ∷ Γ) (ℕF ▷ {!!} ▷ {!!})
       → SSTerm Γ {!!}
```

Another go at it.

```agda
module AnotherGoAtIt where
```

```agda
  open import Type.deprecated.Term.Layer-1.SCTerm
  infixr 10 _▷_
  data Kind (N : Nat) : Set where
    ⟦_⟧ : Term N → Kind N
    _▷_ : Kind N → Kind N → Kind N
  data TypeForm (N : Nat) : Kind N → Set where
    ΠF : (A : Term N) (B : Term (suc N)) → TypeForm N (⟦ {!!} ⟧)
--     ℕF : TypeForm ⋆
--     =F : TypeForm (⋆ ▷ ⋆ ▷ ⋆ ▷ ⋆)

-- ```

--   data Context : Nat → Set
--   record Type : Context → Universe → Set
--   data Term : Type → Set
--   data Equal
