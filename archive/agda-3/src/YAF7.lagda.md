
# Wherein I try to address the vexing issue of variables.

```agda
module YAF7 where
```

## Some preliminaries that could be put elsewhere.

```agda
module Preliminary where

  open import Prelude public

  ∃_ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
  ∃_ = Σ _

  data IsYes {a} {P : Set a} : Dec P → Set a where
    yes : (p : P) → IsYes (yes p)

  getProof : ∀ {a} {P : Set a} → {d : Dec P} → IsYes d → P
  getProof (yes p) = p
```

Let's consider structures that might contain a "variable" and see if we can say soething general about "substitution of variables".

```agda
module SimpleVariableExperiment where
```

Here is a simple, tree-like structure with a variable:

```agda
  data VTree (N : Nat) : Set where
    leaf : VTree N
    branch : VTree N → VTree N → VTree N
    variable : Fin N → VTree N
```

The idea is that we might substitute variables for other `VTree`s (possibly containing variables) and possibly reducing the number of variables in the tree. Obviously, for `VTree A 0`, there are only `leaf`s and `branch`es.

Here is a one-variable substitution:

```agda
{-
  substitute-1 : {N : Nat} (t : VTree (suc N))
                           (v : Fin (suc N))
-}
```

No, it actually is easier to do the more general (supposedly harder) thing first.

Let's consider: in a we could substitute up to N variables in a VTree, each with ... what? Could we replace with a VTree of a higher order? I suppose so, but that feels a bit unconstrained.

Let's say we have a substitution operation that replaces exactly N variables in a VTree with exactly N VTrees of order N, resulting in a VTree of order N. We will have another operation that tries to reduce the order of the VTree, and yet another that increases the order. To rearrange variables, we simply make an appropriate substitution.

Now, this sounds like the sort of thing we will need for type theory, however, what about situations where it's not okay to


Placing free variables in the index of the datatype.

() ⊢ a : A                When the context is empty, there are no possible free variables in a or A.
(g₁ : G₁) ⊢ a : A         When the context has one type, there are zero or one free variables in a or A.
(g₁ : G₁ , g₂ : G₂) ⊢ a : A When the context has one type, there are zero or one (but two choices for this) or two free variables in a or A.

So, in general, with a context of size N, there are 2^N possible combinations of occurrence of free variables. We can model this with (Fin N → Bool). Or even (Fin N → Set)? Then freeVar : Fin N → Set = λ n → ∃ λ (f : Fin N → Bool) → f n ≡ true.

Example using single substitution

(1) Γ , x : N ⊢ C : U                given [free vars of C somehow given]
(2) Γ , x : N , y : C ⊢ C : U        weakening from (1) [free vars of C are same as given but now such that (freeVar C y ≡ false)]
(3) Γ , x : N ⊢ x : N                Vble from (1)
(4) Γ , x : N ⊢ succ x : N           N-Intro₂ from (3)
(5) Γ , x : N ⊢ C[succ x / x] : U[succ x / x]    licensed by (2) and (4a)
(6) Γ , x : N , y : N ⊢ C[succ x / x] : U[succ x / x]    weakening from (5)

Example using simultaneous substitution

Γ , x : N , y : N ⊢ c : x < y
Γ , x : N , y : N ⊢ x : N
Γ , x : N , y : N ⊢ succ x : N
Γ , x : N , y : N ⊢ y : N
Γ , x : N , y : N ⊢ succ y : N

Example using single substitution with an elimination


(*) Γ , x : N , y : C ⊢ C[succ x / x] : U [free vars of C[succ x / x] same as C



Okay, we'll try again in YAF8
