
# An argument is a connected series of statements to establish a definite proposition.

```agda
module Type.deprecated.Argument where
```

## No it isn't.

It's a directed acyclic graph, not a series.

From A.2.1 of the HoTT book,

> A context is a list, x₁:A₁,x₂:A₂,...,xₙ:Aₙ, which indicates that the distinct variables x₁,...,xₙ are assumed to have types A₁,...,Aₙ respectively.

I will regard a symbol as an equivalence class of primitives.

A symbolically-checked term is a finite tree of symbols.

The lex of a symbol is a number.

A lexically-checked term is a symbolically-checked term, each of whose nodes bears a lex that determines the number of branches at the term node.

The scope of a lexed symbol is a

A scope-checked term is a lexically-checked term, each of whose nodes bears a scope, which determines ??.

A type-checked term is a scope-checked term, each of whose nodes bears a type, which determines ??.

_[_↤_] : ∀
       → (B : type-checked-term)
       → (a : list term of-length n)
       → (x : list (type-checked-variable-in-context-of-type-checked-term B) of-length n)
       → size a ≡ size x
       → each variable has a ty
       → Σ term λ B' → (B .#ctx -

The simultaneous substitution of an



context ⊢ type ∋ term

context ⊢ type ∈ sort

⊣ context

context :
  ε
  context , type

A substitution is a mapping of a term φ in a context Δ, a variable 𝓋, called the substitutitive index, of type τ, a term ρ, called the replacement, of type τ in a context Γ, such that the minimal argument for τ

type / proof
term

.... such that
substitute :
  Γ ⊢

data ⊣_≝_⊣_ :

```agda
open import Prelude

{-
data Type : Set where
  U : Nat → Type
  Π Σ ∨ 𝟘 𝟙 ℕ ∼ : Type -- Agda regards = as a keyword, so I use ∼ instead
-}
--^ × + 𝟎 𝟏 ∞ =
{-
data Rule : Set where
  F I E C Q : Rule
-}
```
